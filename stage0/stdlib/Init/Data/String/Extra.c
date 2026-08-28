// Lean compiler output
// Module: Init.Data.String.Extra
// Imports: import all Init.Data.ByteArray.Basic public import Init.Data.String.Basic import all Init.Data.String.Basic import Init.Data.String.Search import Init.Data.String.Termination import Init.Data.String.Length
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
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
uint8_t lean_uint8_land(uint8_t, uint8_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint32_t lean_uint8_to_uint32(uint8_t);
uint32_t lean_uint32_shift_left(uint32_t, uint32_t);
uint32_t lean_uint32_lor(uint32_t, uint32_t);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_next_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8DecodeChar_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8DecodeChar_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_validateUTF8(lean_object*);
LEAN_EXPORT lean_object* l_String_validateUTF8___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___closed__0 = (const lean_object*)&l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_removeLeadingSpaces(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_crlfToLf_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_crlfToLf_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_crlfToLf(lean_object*);
LEAN_EXPORT lean_object* l_String_crlfToLf___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_utf8DecodeChar_x3f(lean_object* v_a_1_, lean_object* v_i_2_){
_start:
{
lean_object* v___x_3_; uint8_t v___x_4_; 
v___x_3_ = lean_byte_array_size(v_a_1_);
v___x_4_ = lean_nat_dec_lt(v_i_2_, v___x_3_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; 
v___x_5_ = lean_box(0);
return v___x_5_;
}
else
{
uint8_t v___x_6_; uint8_t v___x_7_; uint8_t v___x_8_; uint8_t v___x_9_; uint8_t v___x_10_; 
v___x_6_ = lean_byte_array_fget(v_a_1_, v_i_2_);
v___x_7_ = 128;
v___x_8_ = lean_uint8_land(v___x_6_, v___x_7_);
v___x_9_ = 0;
v___x_10_ = lean_uint8_dec_eq(v___x_8_, v___x_9_);
if (v___x_10_ == 0)
{
uint8_t v___x_11_; uint8_t v___x_12_; uint8_t v___x_13_; uint8_t v___x_14_; 
v___x_11_ = 224;
v___x_12_ = lean_uint8_land(v___x_6_, v___x_11_);
v___x_13_ = 192;
v___x_14_ = lean_uint8_dec_eq(v___x_12_, v___x_13_);
if (v___x_14_ == 0)
{
uint8_t v___x_15_; uint8_t v___x_16_; uint8_t v___x_17_; 
v___x_15_ = 240;
v___x_16_ = lean_uint8_land(v___x_6_, v___x_15_);
v___x_17_ = lean_uint8_dec_eq(v___x_16_, v___x_11_);
if (v___x_17_ == 0)
{
uint8_t v___x_18_; uint8_t v___x_19_; uint8_t v___x_20_; 
v___x_18_ = 248;
v___x_19_ = lean_uint8_land(v___x_6_, v___x_18_);
v___x_20_ = lean_uint8_dec_eq(v___x_19_, v___x_15_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; 
v___x_21_ = lean_box(0);
return v___x_21_;
}
else
{
lean_object* v___x_22_; lean_object* v___x_23_; uint8_t v___x_24_; 
v___x_22_ = lean_unsigned_to_nat(3u);
v___x_23_ = lean_nat_add(v_i_2_, v___x_22_);
v___x_24_ = lean_nat_dec_lt(v___x_23_, v___x_3_);
if (v___x_24_ == 0)
{
lean_object* v___x_25_; 
lean_dec(v___x_23_);
v___x_25_ = lean_box(0);
return v___x_25_;
}
else
{
lean_object* v___x_26_; lean_object* v___x_27_; uint8_t v___x_28_; uint8_t v___x_29_; uint8_t v___x_30_; 
v___x_26_ = lean_unsigned_to_nat(1u);
v___x_27_ = lean_nat_add(v_i_2_, v___x_26_);
v___x_28_ = lean_byte_array_fget(v_a_1_, v___x_27_);
lean_dec(v___x_27_);
v___x_29_ = lean_uint8_land(v___x_28_, v___x_13_);
v___x_30_ = lean_uint8_dec_eq(v___x_29_, v___x_7_);
if (v___x_30_ == 0)
{
lean_object* v___x_31_; 
lean_dec(v___x_23_);
v___x_31_ = lean_box(0);
return v___x_31_;
}
else
{
lean_object* v___x_32_; lean_object* v___x_33_; uint8_t v___x_34_; uint8_t v___x_35_; uint8_t v___x_36_; 
v___x_32_ = lean_unsigned_to_nat(2u);
v___x_33_ = lean_nat_add(v_i_2_, v___x_32_);
v___x_34_ = lean_byte_array_fget(v_a_1_, v___x_33_);
lean_dec(v___x_33_);
v___x_35_ = lean_uint8_land(v___x_34_, v___x_13_);
v___x_36_ = lean_uint8_dec_eq(v___x_35_, v___x_7_);
if (v___x_36_ == 0)
{
lean_object* v___x_37_; 
lean_dec(v___x_23_);
v___x_37_ = lean_box(0);
return v___x_37_;
}
else
{
uint8_t v___x_38_; uint8_t v___x_39_; uint8_t v___x_40_; 
v___x_38_ = lean_byte_array_fget(v_a_1_, v___x_23_);
lean_dec(v___x_23_);
v___x_39_ = lean_uint8_land(v___x_38_, v___x_13_);
v___x_40_ = lean_uint8_dec_eq(v___x_39_, v___x_7_);
if (v___x_40_ == 0)
{
lean_object* v___x_41_; 
v___x_41_ = lean_box(0);
return v___x_41_;
}
else
{
uint8_t v___x_42_; uint8_t v_b_u2080_43_; uint8_t v___x_44_; uint8_t v_b_u2081_45_; uint8_t v_b_u2082_46_; uint8_t v_b_u2083_47_; uint32_t v___x_48_; uint32_t v___x_49_; uint32_t v___x_50_; uint32_t v___x_51_; uint32_t v___x_52_; uint32_t v___x_53_; uint32_t v___x_54_; uint32_t v___x_55_; uint32_t v___x_56_; uint32_t v___x_57_; uint32_t v___x_58_; uint32_t v___x_59_; uint32_t v_r_60_; uint32_t v___x_61_; uint8_t v___x_62_; 
v___x_42_ = 7;
v_b_u2080_43_ = lean_uint8_land(v___x_6_, v___x_42_);
v___x_44_ = 63;
v_b_u2081_45_ = lean_uint8_land(v___x_28_, v___x_44_);
v_b_u2082_46_ = lean_uint8_land(v___x_34_, v___x_44_);
v_b_u2083_47_ = lean_uint8_land(v___x_38_, v___x_44_);
v___x_48_ = lean_uint8_to_uint32(v_b_u2080_43_);
v___x_49_ = 18;
v___x_50_ = lean_uint32_shift_left(v___x_48_, v___x_49_);
v___x_51_ = lean_uint8_to_uint32(v_b_u2081_45_);
v___x_52_ = 12;
v___x_53_ = lean_uint32_shift_left(v___x_51_, v___x_52_);
v___x_54_ = lean_uint32_lor(v___x_50_, v___x_53_);
v___x_55_ = lean_uint8_to_uint32(v_b_u2082_46_);
v___x_56_ = 6;
v___x_57_ = lean_uint32_shift_left(v___x_55_, v___x_56_);
v___x_58_ = lean_uint32_lor(v___x_54_, v___x_57_);
v___x_59_ = lean_uint8_to_uint32(v_b_u2083_47_);
v_r_60_ = lean_uint32_lor(v___x_58_, v___x_59_);
v___x_61_ = 65536;
v___x_62_ = lean_uint32_dec_lt(v_r_60_, v___x_61_);
if (v___x_62_ == 0)
{
uint32_t v___x_63_; uint8_t v___x_64_; 
v___x_63_ = 1114111;
v___x_64_ = lean_uint32_dec_lt(v___x_63_, v_r_60_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_box_uint32(v_r_60_);
v___x_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
return v___x_66_;
}
else
{
lean_object* v___x_67_; 
v___x_67_ = lean_box(0);
return v___x_67_;
}
}
else
{
lean_object* v___x_68_; 
v___x_68_ = lean_box(0);
return v___x_68_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_69_; lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_69_ = lean_unsigned_to_nat(2u);
v___x_70_ = lean_nat_add(v_i_2_, v___x_69_);
v___x_71_ = lean_nat_dec_lt(v___x_70_, v___x_3_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; 
lean_dec(v___x_70_);
v___x_72_ = lean_box(0);
return v___x_72_;
}
else
{
lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; uint8_t v___x_76_; uint8_t v___x_77_; 
v___x_73_ = lean_unsigned_to_nat(1u);
v___x_74_ = lean_nat_add(v_i_2_, v___x_73_);
v___x_75_ = lean_byte_array_fget(v_a_1_, v___x_74_);
lean_dec(v___x_74_);
v___x_76_ = lean_uint8_land(v___x_75_, v___x_13_);
v___x_77_ = lean_uint8_dec_eq(v___x_76_, v___x_7_);
if (v___x_77_ == 0)
{
lean_object* v___x_78_; 
lean_dec(v___x_70_);
v___x_78_ = lean_box(0);
return v___x_78_;
}
else
{
uint8_t v___x_79_; uint8_t v___x_80_; uint8_t v___x_81_; 
v___x_79_ = lean_byte_array_fget(v_a_1_, v___x_70_);
lean_dec(v___x_70_);
v___x_80_ = lean_uint8_land(v___x_79_, v___x_13_);
v___x_81_ = lean_uint8_dec_eq(v___x_80_, v___x_7_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; 
v___x_82_ = lean_box(0);
return v___x_82_;
}
else
{
uint8_t v___x_83_; uint8_t v_b_u2080_84_; uint8_t v___x_85_; uint8_t v_b_u2081_86_; uint8_t v_b_u2082_87_; uint32_t v___x_88_; uint32_t v___x_89_; uint32_t v___x_90_; uint32_t v___x_91_; uint32_t v___x_92_; uint32_t v___x_93_; uint32_t v___x_94_; uint32_t v___x_95_; uint32_t v_r_96_; uint8_t v___y_98_; uint32_t v___x_102_; uint8_t v___x_103_; 
v___x_83_ = 15;
v_b_u2080_84_ = lean_uint8_land(v___x_6_, v___x_83_);
v___x_85_ = 63;
v_b_u2081_86_ = lean_uint8_land(v___x_75_, v___x_85_);
v_b_u2082_87_ = lean_uint8_land(v___x_79_, v___x_85_);
v___x_88_ = lean_uint8_to_uint32(v_b_u2080_84_);
v___x_89_ = 12;
v___x_90_ = lean_uint32_shift_left(v___x_88_, v___x_89_);
v___x_91_ = lean_uint8_to_uint32(v_b_u2081_86_);
v___x_92_ = 6;
v___x_93_ = lean_uint32_shift_left(v___x_91_, v___x_92_);
v___x_94_ = lean_uint32_lor(v___x_90_, v___x_93_);
v___x_95_ = lean_uint8_to_uint32(v_b_u2082_87_);
v_r_96_ = lean_uint32_lor(v___x_94_, v___x_95_);
v___x_102_ = 2048;
v___x_103_ = lean_uint32_dec_lt(v_r_96_, v___x_102_);
if (v___x_103_ == 0)
{
uint32_t v___x_104_; uint8_t v___x_105_; 
v___x_104_ = 55296;
v___x_105_ = lean_uint32_dec_le(v___x_104_, v_r_96_);
if (v___x_105_ == 0)
{
v___y_98_ = v___x_105_;
goto v___jp_97_;
}
else
{
uint32_t v___x_106_; uint8_t v___x_107_; 
v___x_106_ = 57343;
v___x_107_ = lean_uint32_dec_le(v_r_96_, v___x_106_);
v___y_98_ = v___x_107_;
goto v___jp_97_;
}
}
else
{
lean_object* v___x_108_; 
v___x_108_ = lean_box(0);
return v___x_108_;
}
v___jp_97_:
{
if (v___y_98_ == 0)
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = lean_box_uint32(v_r_96_);
v___x_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
return v___x_100_;
}
else
{
lean_object* v___x_101_; 
v___x_101_ = lean_box(0);
return v___x_101_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_109_ = lean_unsigned_to_nat(1u);
v___x_110_ = lean_nat_add(v_i_2_, v___x_109_);
v___x_111_ = lean_nat_dec_lt(v___x_110_, v___x_3_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; 
lean_dec(v___x_110_);
v___x_112_ = lean_box(0);
return v___x_112_;
}
else
{
uint8_t v___x_113_; uint8_t v___x_114_; uint8_t v___x_115_; 
v___x_113_ = lean_byte_array_fget(v_a_1_, v___x_110_);
lean_dec(v___x_110_);
v___x_114_ = lean_uint8_land(v___x_113_, v___x_13_);
v___x_115_ = lean_uint8_dec_eq(v___x_114_, v___x_7_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; 
v___x_116_ = lean_box(0);
return v___x_116_;
}
else
{
uint8_t v___x_117_; uint8_t v_b_u2080_118_; uint8_t v___x_119_; uint8_t v_b_u2081_120_; uint32_t v___x_121_; uint32_t v___x_122_; uint32_t v___x_123_; uint32_t v___x_124_; uint32_t v_r_125_; uint32_t v___x_126_; uint8_t v___x_127_; 
v___x_117_ = 31;
v_b_u2080_118_ = lean_uint8_land(v___x_6_, v___x_117_);
v___x_119_ = 63;
v_b_u2081_120_ = lean_uint8_land(v___x_113_, v___x_119_);
v___x_121_ = lean_uint8_to_uint32(v_b_u2080_118_);
v___x_122_ = 6;
v___x_123_ = lean_uint32_shift_left(v___x_121_, v___x_122_);
v___x_124_ = lean_uint8_to_uint32(v_b_u2081_120_);
v_r_125_ = lean_uint32_lor(v___x_123_, v___x_124_);
v___x_126_ = 128;
v___x_127_ = lean_uint32_dec_lt(v_r_125_, v___x_126_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lean_box_uint32(v_r_125_);
v___x_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
return v___x_129_;
}
else
{
lean_object* v___x_130_; 
v___x_130_ = lean_box(0);
return v___x_130_;
}
}
}
}
}
else
{
uint32_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_131_ = lean_uint8_to_uint32(v___x_6_);
v___x_132_ = lean_box_uint32(v___x_131_);
v___x_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
return v___x_133_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_utf8DecodeChar_x3f___boxed(lean_object* v_a_134_, lean_object* v_i_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_String_utf8DecodeChar_x3f(v_a_134_, v_i_135_);
lean_dec(v_i_135_);
lean_dec_ref(v_a_134_);
return v_res_136_;
}
}
LEAN_EXPORT uint8_t l_String_validateUTF8(lean_object* v_a_137_){
_start:
{
uint8_t v___x_138_; 
v___x_138_ = lean_string_validate_utf8(v_a_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_String_validateUTF8___boxed(lean_object* v_a_139_){
_start:
{
uint8_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = l_String_validateUTF8(v_a_139_);
lean_dec_ref(v_a_139_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces(lean_object* v_s_142_, lean_object* v_it_143_, lean_object* v_curr_144_, lean_object* v_min_145_){
_start:
{
lean_object* v___x_151_; uint8_t v_decide_152_; 
v___x_151_ = lean_string_utf8_byte_size(v_s_142_);
v_decide_152_ = lean_nat_dec_eq(v_it_143_, v___x_151_);
if (v_decide_152_ == 0)
{
uint32_t v___x_153_; uint32_t v___x_154_; uint8_t v___x_155_; 
v___x_153_ = lean_string_utf8_get_fast(v_s_142_, v_it_143_);
v___x_154_ = 32;
v___x_155_ = lean_uint32_dec_eq(v___x_153_, v___x_154_);
if (v___x_155_ == 0)
{
uint32_t v___x_156_; uint8_t v___x_157_; 
v___x_156_ = 9;
v___x_157_ = lean_uint32_dec_eq(v___x_153_, v___x_156_);
if (v___x_157_ == 0)
{
uint32_t v___x_158_; uint8_t v___x_159_; 
v___x_158_ = 10;
v___x_159_ = lean_uint32_dec_eq(v___x_153_, v___x_158_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_160_ = lean_string_utf8_next_fast(v_s_142_, v_it_143_);
lean_dec(v_it_143_);
v___x_161_ = lean_nat_dec_le(v_curr_144_, v_min_145_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; 
lean_dec(v_curr_144_);
v___x_162_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(v_s_142_, v___x_160_, v_min_145_);
return v___x_162_;
}
else
{
lean_object* v___x_163_; 
v___x_163_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(v_s_142_, v___x_160_, v_curr_144_);
lean_dec(v_curr_144_);
return v___x_163_;
}
}
else
{
lean_object* v___x_164_; lean_object* v___x_165_; 
lean_dec(v_curr_144_);
v___x_164_ = lean_string_utf8_next_fast(v_s_142_, v_it_143_);
lean_dec(v_it_143_);
v___x_165_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(v_s_142_, v___x_164_, v_min_145_);
return v___x_165_;
}
}
else
{
goto v___jp_146_;
}
}
else
{
goto v___jp_146_;
}
}
else
{
lean_dec(v_curr_144_);
lean_dec(v_it_143_);
lean_inc(v_min_145_);
return v_min_145_;
}
v___jp_146_:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = lean_string_utf8_next_fast(v_s_142_, v_it_143_);
lean_dec(v_it_143_);
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = lean_nat_add(v_curr_144_, v___x_148_);
lean_dec(v_curr_144_);
v_it_143_ = v___x_147_;
v_curr_144_ = v___x_149_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(lean_object* v_s_166_, lean_object* v_it_167_, lean_object* v_min_168_){
_start:
{
lean_object* v___x_169_; uint8_t v_decide_170_; 
v___x_169_ = lean_string_utf8_byte_size(v_s_166_);
v_decide_170_ = lean_nat_dec_eq(v_it_167_, v___x_169_);
if (v_decide_170_ == 0)
{
uint32_t v___x_171_; uint32_t v___x_172_; uint8_t v___x_173_; 
v___x_171_ = lean_string_utf8_get_fast(v_s_166_, v_it_167_);
v___x_172_ = 10;
v___x_173_ = lean_uint32_dec_eq(v___x_171_, v___x_172_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; 
v___x_174_ = lean_string_utf8_next_fast(v_s_166_, v_it_167_);
lean_dec(v_it_167_);
v_it_167_ = v___x_174_;
goto _start;
}
else
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_176_ = lean_string_utf8_next_fast(v_s_166_, v_it_167_);
lean_dec(v_it_167_);
v___x_177_ = lean_unsigned_to_nat(0u);
v___x_178_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces(v_s_166_, v___x_176_, v___x_177_, v_min_168_);
return v___x_178_;
}
}
else
{
lean_dec(v_it_167_);
lean_inc(v_min_168_);
return v_min_168_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine___boxed(lean_object* v_s_179_, lean_object* v_it_180_, lean_object* v_min_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(v_s_179_, v_it_180_, v_min_181_);
lean_dec(v_min_181_);
lean_dec_ref(v_s_179_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces___boxed(lean_object* v_s_183_, lean_object* v_it_184_, lean_object* v_curr_185_, lean_object* v_min_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces(v_s_183_, v_it_184_, v_curr_185_, v_min_186_);
lean_dec(v_min_186_);
lean_dec_ref(v_s_183_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg(lean_object* v___x_188_, lean_object* v_s_189_, lean_object* v_a_190_, lean_object* v_b_191_){
_start:
{
uint8_t v_decide_192_; 
v_decide_192_ = lean_nat_dec_eq(v_a_190_, v___x_188_);
if (v_decide_192_ == 0)
{
uint32_t v___x_193_; uint32_t v___x_194_; uint8_t v___x_195_; 
v___x_193_ = lean_string_utf8_get_fast(v_s_189_, v_a_190_);
v___x_194_ = 10;
v___x_195_ = lean_uint32_dec_eq(v___x_193_, v___x_194_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = lean_box(0);
v___x_197_ = lean_string_utf8_next_fast(v_s_189_, v_a_190_);
lean_dec(v_a_190_);
v_a_190_ = v___x_197_;
v_b_191_ = v___x_196_;
goto _start;
}
else
{
lean_object* v___x_199_; 
v___x_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_199_, 0, v_a_190_);
return v___x_199_;
}
}
else
{
lean_dec(v_a_190_);
lean_inc(v_b_191_);
return v_b_191_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg___boxed(lean_object* v___x_200_, lean_object* v_s_201_, lean_object* v_a_202_, lean_object* v_b_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg(v___x_200_, v_s_201_, v_a_202_, v_b_203_);
lean_dec(v_b_203_);
lean_dec_ref(v_s_201_);
lean_dec(v___x_200_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize(lean_object* v_s_205_){
_start:
{
lean_object* v_searcher_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_searcher_206_ = lean_unsigned_to_nat(0u);
v___x_207_ = lean_string_utf8_byte_size(v_s_205_);
lean_inc_ref(v_s_205_);
v___x_208_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_208_, 0, v_s_205_);
lean_ctor_set(v___x_208_, 1, v_searcher_206_);
lean_ctor_set(v___x_208_, 2, v___x_207_);
v___x_209_ = lean_box(0);
v___x_210_ = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg(v___x_207_, v_s_205_, v_searcher_206_, v___x_209_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_dec_ref_known(v___x_208_, 3);
lean_dec_ref(v_s_205_);
return v_searcher_206_;
}
else
{
lean_object* v_val_211_; lean_object* v___x_212_; 
v_val_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_val_211_);
lean_dec_ref_known(v___x_210_, 1);
v___x_212_ = l_String_Slice_Pos_next_x3f(v___x_208_, v_val_211_);
lean_dec(v_val_211_);
lean_dec_ref_known(v___x_208_, 3);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_dec_ref(v_s_205_);
return v_searcher_206_;
}
else
{
lean_object* v_val_213_; lean_object* v___x_214_; 
v_val_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_val_213_);
lean_dec_ref_known(v___x_212_, 1);
v___x_214_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces(v_s_205_, v_val_213_, v_searcher_206_, v___x_207_);
lean_dec_ref(v_s_205_);
return v___x_214_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0(lean_object* v___x_215_, lean_object* v___x_216_, lean_object* v_s_217_, lean_object* v_inst_218_, lean_object* v_R_219_, lean_object* v_a_220_, lean_object* v_b_221_, lean_object* v_c_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg(v___x_215_, v_s_217_, v_a_220_, v_b_221_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___boxed(lean_object* v___x_224_, lean_object* v___x_225_, lean_object* v_s_226_, lean_object* v_inst_227_, lean_object* v_R_228_, lean_object* v_a_229_, lean_object* v_b_230_, lean_object* v_c_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0(v___x_224_, v___x_225_, v_s_226_, v_inst_227_, v_R_228_, v_a_229_, v_b_230_, v_c_231_);
lean_dec(v_b_230_);
lean_dec_ref(v_s_226_);
lean_dec_ref(v___x_225_);
lean_dec(v___x_224_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(lean_object* v_n_233_, lean_object* v_n_234_, lean_object* v_s_235_, lean_object* v_it_236_, lean_object* v_r_237_){
_start:
{
lean_object* v_zero_238_; uint8_t v_isZero_239_; 
v_zero_238_ = lean_unsigned_to_nat(0u);
v_isZero_239_ = lean_nat_dec_eq(v_n_234_, v_zero_238_);
if (v_isZero_239_ == 1)
{
lean_object* v___x_240_; 
lean_dec(v_n_234_);
v___x_240_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine(v_n_233_, v_s_235_, v_it_236_, v_r_237_);
return v___x_240_;
}
else
{
lean_object* v___x_241_; uint8_t v_decide_242_; 
v___x_241_ = lean_string_utf8_byte_size(v_s_235_);
v_decide_242_ = lean_nat_dec_eq(v_it_236_, v___x_241_);
if (v_decide_242_ == 0)
{
lean_object* v_one_243_; lean_object* v_n_244_; uint32_t v___x_248_; uint32_t v___x_249_; uint8_t v___x_250_; 
v_one_243_ = lean_unsigned_to_nat(1u);
v_n_244_ = lean_nat_sub(v_n_234_, v_one_243_);
lean_dec(v_n_234_);
v___x_248_ = lean_string_utf8_get_fast(v_s_235_, v_it_236_);
v___x_249_ = 32;
v___x_250_ = lean_uint32_dec_eq(v___x_248_, v___x_249_);
if (v___x_250_ == 0)
{
uint32_t v___x_251_; uint8_t v___x_252_; 
v___x_251_ = 9;
v___x_252_ = lean_uint32_dec_eq(v___x_248_, v___x_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; 
lean_dec(v_n_244_);
v___x_253_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine(v_n_233_, v_s_235_, v_it_236_, v_r_237_);
return v___x_253_;
}
else
{
goto v___jp_245_;
}
}
else
{
goto v___jp_245_;
}
v___jp_245_:
{
lean_object* v___x_246_; 
v___x_246_ = lean_string_utf8_next_fast(v_s_235_, v_it_236_);
lean_dec(v_it_236_);
v_n_234_ = v_n_244_;
v_it_236_ = v___x_246_;
goto _start;
}
}
else
{
lean_dec(v_it_236_);
lean_dec(v_n_234_);
lean_dec(v_n_233_);
return v_r_237_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine(lean_object* v_n_254_, lean_object* v_s_255_, lean_object* v_it_256_, lean_object* v_r_257_){
_start:
{
lean_object* v___x_258_; uint8_t v_decide_259_; 
v___x_258_ = lean_string_utf8_byte_size(v_s_255_);
v_decide_259_ = lean_nat_dec_eq(v_it_256_, v___x_258_);
if (v_decide_259_ == 0)
{
uint32_t v___x_260_; uint32_t v___x_261_; uint8_t v___x_262_; 
v___x_260_ = lean_string_utf8_get_fast(v_s_255_, v_it_256_);
v___x_261_ = 10;
v___x_262_ = lean_uint32_dec_eq(v___x_260_, v___x_261_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = lean_string_utf8_next_fast(v_s_255_, v_it_256_);
lean_dec(v_it_256_);
v___x_264_ = lean_string_push(v_r_257_, v___x_260_);
v_it_256_ = v___x_263_;
v_r_257_ = v___x_264_;
goto _start;
}
else
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_266_ = lean_string_utf8_next_fast(v_s_255_, v_it_256_);
lean_dec(v_it_256_);
v___x_267_ = lean_string_push(v_r_257_, v___x_261_);
lean_inc(v_n_254_);
v___x_268_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(v_n_254_, v_n_254_, v_s_255_, v___x_266_, v___x_267_);
return v___x_268_;
}
}
else
{
lean_dec(v_it_256_);
lean_dec(v_n_254_);
return v_r_257_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine___boxed(lean_object* v_n_269_, lean_object* v_s_270_, lean_object* v_it_271_, lean_object* v_r_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine(v_n_269_, v_s_270_, v_it_271_, v_r_272_);
lean_dec_ref(v_s_270_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces___boxed(lean_object* v_n_274_, lean_object* v_n_275_, lean_object* v_s_276_, lean_object* v_it_277_, lean_object* v_r_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(v_n_274_, v_n_275_, v_s_276_, v_it_277_, v_r_278_);
lean_dec_ref(v_s_276_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___redArg(lean_object* v_n_280_, lean_object* v_h__1_281_, lean_object* v_h__2_282_){
_start:
{
lean_object* v_zero_283_; uint8_t v_isZero_284_; 
v_zero_283_ = lean_unsigned_to_nat(0u);
v_isZero_284_ = lean_nat_dec_eq(v_n_280_, v_zero_283_);
if (v_isZero_284_ == 1)
{
lean_object* v___x_285_; lean_object* v___x_286_; 
lean_dec(v_h__2_282_);
v___x_285_ = lean_box(0);
v___x_286_ = lean_apply_1(v_h__1_281_, v___x_285_);
return v___x_286_;
}
else
{
lean_object* v_one_287_; lean_object* v_n_288_; lean_object* v___x_289_; 
lean_dec(v_h__1_281_);
v_one_287_ = lean_unsigned_to_nat(1u);
v_n_288_ = lean_nat_sub(v_n_280_, v_one_287_);
v___x_289_ = lean_apply_1(v_h__2_282_, v_n_288_);
return v___x_289_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___redArg___boxed(lean_object* v_n_290_, lean_object* v_h__1_291_, lean_object* v_h__2_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___redArg(v_n_290_, v_h__1_291_, v_h__2_292_);
lean_dec(v_n_290_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter(lean_object* v_motive_294_, lean_object* v_n_295_, lean_object* v_h__1_296_, lean_object* v_h__2_297_){
_start:
{
lean_object* v_zero_298_; uint8_t v_isZero_299_; 
v_zero_298_ = lean_unsigned_to_nat(0u);
v_isZero_299_ = lean_nat_dec_eq(v_n_295_, v_zero_298_);
if (v_isZero_299_ == 1)
{
lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec(v_h__2_297_);
v___x_300_ = lean_box(0);
v___x_301_ = lean_apply_1(v_h__1_296_, v___x_300_);
return v___x_301_;
}
else
{
lean_object* v_one_302_; lean_object* v_n_303_; lean_object* v___x_304_; 
lean_dec(v_h__1_296_);
v_one_302_ = lean_unsigned_to_nat(1u);
v_n_303_ = lean_nat_sub(v_n_295_, v_one_302_);
v___x_304_ = lean_apply_1(v_h__2_297_, v_n_303_);
return v___x_304_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___boxed(lean_object* v_motive_305_, lean_object* v_n_306_, lean_object* v_h__1_307_, lean_object* v_h__2_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter(v_motive_305_, v_n_306_, v_h__1_307_, v_h__2_308_);
lean_dec(v_n_306_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces(lean_object* v_n_311_, lean_object* v_s_312_){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = ((lean_object*)(l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___closed__0));
lean_inc(v_n_311_);
v___x_315_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(v_n_311_, v_n_311_, v_s_312_, v___x_313_, v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___boxed(lean_object* v_n_316_, lean_object* v_s_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces(v_n_316_, v_s_317_);
lean_dec_ref(v_s_317_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_String_removeLeadingSpaces(lean_object* v_s_319_){
_start:
{
lean_object* v_n_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
lean_inc_ref(v_s_319_);
v_n_320_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize(v_s_319_);
v___x_321_ = lean_unsigned_to_nat(0u);
v___x_322_ = lean_nat_dec_eq(v_n_320_, v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; 
v___x_323_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces(v_n_320_, v_s_319_);
lean_dec_ref(v_s_319_);
return v___x_323_;
}
else
{
lean_dec(v_n_320_);
return v_s_319_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_crlfToLf_go(lean_object* v_text_324_, lean_object* v_acc_325_, lean_object* v_accStop_326_, lean_object* v_pos_327_){
_start:
{
uint8_t v___x_328_; 
v___x_328_ = lean_string_utf8_at_end(v_text_324_, v_pos_327_);
if (v___x_328_ == 0)
{
uint32_t v_c_329_; lean_object* v_pos_x27_330_; uint8_t v___y_332_; uint8_t v___y_333_; uint8_t v___y_341_; uint8_t v___x_347_; 
v_c_329_ = lean_string_utf8_get_fast(v_text_324_, v_pos_327_);
v_pos_x27_330_ = lean_string_utf8_next_fast(v_text_324_, v_pos_327_);
v___x_347_ = lean_string_utf8_at_end(v_text_324_, v_pos_x27_330_);
if (v___x_347_ == 0)
{
uint8_t v___x_348_; 
v___x_348_ = 1;
v___y_341_ = v___x_348_;
goto v___jp_340_;
}
else
{
v___y_341_ = v___x_328_;
goto v___jp_340_;
}
v___jp_331_:
{
if (v___y_332_ == 0)
{
lean_dec(v_pos_327_);
v_pos_327_ = v_pos_x27_330_;
goto _start;
}
else
{
if (v___y_333_ == 0)
{
lean_dec(v_pos_327_);
v_pos_327_ = v_pos_x27_330_;
goto _start;
}
else
{
lean_object* v___x_336_; lean_object* v_acc_337_; lean_object* v___x_338_; 
v___x_336_ = lean_string_utf8_extract(v_text_324_, v_accStop_326_, v_pos_327_);
lean_dec(v_pos_327_);
lean_dec(v_accStop_326_);
v_acc_337_ = lean_string_append(v_acc_325_, v___x_336_);
lean_dec_ref(v___x_336_);
v___x_338_ = lean_string_utf8_next_fast(v_text_324_, v_pos_x27_330_);
v_acc_325_ = v_acc_337_;
v_accStop_326_ = v_pos_x27_330_;
v_pos_327_ = v___x_338_;
goto _start;
}
}
}
v___jp_340_:
{
uint32_t v___x_342_; uint8_t v___x_343_; 
v___x_342_ = 13;
v___x_343_ = lean_uint32_dec_eq(v_c_329_, v___x_342_);
if (v___x_343_ == 0)
{
v___y_332_ = v___y_341_;
v___y_333_ = v___x_343_;
goto v___jp_331_;
}
else
{
uint32_t v___x_344_; uint32_t v___x_345_; uint8_t v___x_346_; 
v___x_344_ = lean_string_utf8_get(v_text_324_, v_pos_x27_330_);
v___x_345_ = 10;
v___x_346_ = lean_uint32_dec_eq(v___x_344_, v___x_345_);
v___y_332_ = v___y_341_;
v___y_333_ = v___x_346_;
goto v___jp_331_;
}
}
}
else
{
lean_object* v___x_349_; uint8_t v_decide_350_; 
v___x_349_ = lean_unsigned_to_nat(0u);
v_decide_350_ = lean_nat_dec_eq(v_accStop_326_, v___x_349_);
if (v_decide_350_ == 0)
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = lean_string_utf8_extract(v_text_324_, v_accStop_326_, v_pos_327_);
lean_dec(v_pos_327_);
lean_dec(v_accStop_326_);
v___x_352_ = lean_string_append(v_acc_325_, v___x_351_);
lean_dec_ref(v___x_351_);
return v___x_352_;
}
else
{
lean_dec(v_pos_327_);
lean_dec(v_accStop_326_);
lean_dec_ref(v_acc_325_);
lean_inc_ref(v_text_324_);
return v_text_324_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_crlfToLf_go___boxed(lean_object* v_text_353_, lean_object* v_acc_354_, lean_object* v_accStop_355_, lean_object* v_pos_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l___private_Init_Data_String_Extra_0__String_crlfToLf_go(v_text_353_, v_acc_354_, v_accStop_355_, v_pos_356_);
lean_dec_ref(v_text_353_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_String_crlfToLf(lean_object* v_text_358_){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_359_ = ((lean_object*)(l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___closed__0));
v___x_360_ = lean_unsigned_to_nat(0u);
v___x_361_ = l___private_Init_Data_String_Extra_0__String_crlfToLf_go(v_text_358_, v___x_359_, v___x_360_, v___x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_String_crlfToLf___boxed(lean_object* v_text_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_String_crlfToLf(v_text_362_);
lean_dec_ref(v_text_362_);
return v_res_363_;
}
}
lean_object* runtime_initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Length(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Extra(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_ByteArray_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Extra(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* initialize_Init_Data_String_Length(uint8_t builtin);
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
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Extra(builtin);
}
#ifdef __cplusplus
}
#endif

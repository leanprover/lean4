// Lean compiler output
// Module: Init.Data.String.Extra
// Imports: import all Init.Data.ByteArray.Basic public import Init.Data.String.Basic import all Init.Data.String.Basic import Init.Data.String.Search import Init.Data.String.Termination
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
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_next_x3f(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_83_; uint8_t v_b_u2080_84_; uint8_t v___x_85_; uint8_t v_b_u2081_86_; uint8_t v_b_u2082_87_; uint32_t v___x_88_; uint32_t v___x_89_; uint32_t v___x_90_; uint32_t v___x_91_; uint32_t v___x_92_; uint32_t v___x_93_; uint32_t v___x_94_; uint32_t v___x_95_; uint32_t v_r_96_; uint32_t v___x_97_; uint8_t v___x_98_; 
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
v___x_97_ = 2048;
v___x_98_ = lean_uint32_dec_lt(v_r_96_, v___x_97_);
if (v___x_98_ == 0)
{
uint32_t v___x_99_; uint8_t v___x_100_; 
v___x_99_ = 55296;
v___x_100_ = lean_uint32_dec_le(v___x_99_, v_r_96_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = lean_box_uint32(v_r_96_);
v___x_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
return v___x_102_;
}
else
{
uint32_t v___x_103_; uint8_t v___x_104_; 
v___x_103_ = 57343;
v___x_104_ = lean_uint32_dec_le(v_r_96_, v___x_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_box_uint32(v_r_96_);
v___x_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
return v___x_106_;
}
else
{
lean_object* v___x_107_; 
v___x_107_ = lean_box(0);
return v___x_107_;
}
}
}
else
{
lean_object* v___x_108_; 
v___x_108_ = lean_box(0);
return v___x_108_;
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
lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_146_ = lean_string_utf8_byte_size(v_s_142_);
v___x_147_ = lean_nat_dec_eq(v_it_143_, v___x_146_);
if (v___x_147_ == 0)
{
uint32_t v___x_148_; uint8_t v___y_150_; uint32_t v___x_163_; uint8_t v___x_164_; 
v___x_148_ = lean_string_utf8_get_fast(v_s_142_, v_it_143_);
v___x_163_ = 32;
v___x_164_ = lean_uint32_dec_eq(v___x_148_, v___x_163_);
if (v___x_164_ == 0)
{
uint32_t v___x_165_; uint8_t v___x_166_; 
v___x_165_ = 9;
v___x_166_ = lean_uint32_dec_eq(v___x_148_, v___x_165_);
v___y_150_ = v___x_166_;
goto v___jp_149_;
}
else
{
v___y_150_ = v___x_164_;
goto v___jp_149_;
}
v___jp_149_:
{
if (v___y_150_ == 0)
{
uint32_t v___x_151_; uint8_t v___x_152_; 
v___x_151_ = 10;
v___x_152_ = lean_uint32_dec_eq(v___x_148_, v___x_151_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_153_ = lean_string_utf8_next_fast(v_s_142_, v_it_143_);
lean_dec(v_it_143_);
v___x_154_ = lean_nat_dec_le(v_curr_144_, v_min_145_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; 
lean_dec(v_curr_144_);
v___x_155_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(v_s_142_, v___x_153_, v_min_145_);
return v___x_155_;
}
else
{
lean_object* v___x_156_; 
v___x_156_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(v_s_142_, v___x_153_, v_curr_144_);
lean_dec(v_curr_144_);
return v___x_156_;
}
}
else
{
lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec(v_curr_144_);
v___x_157_ = lean_string_utf8_next_fast(v_s_142_, v_it_143_);
lean_dec(v_it_143_);
v___x_158_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(v_s_142_, v___x_157_, v_min_145_);
return v___x_158_;
}
}
else
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_159_ = lean_string_utf8_next_fast(v_s_142_, v_it_143_);
lean_dec(v_it_143_);
v___x_160_ = lean_unsigned_to_nat(1u);
v___x_161_ = lean_nat_add(v_curr_144_, v___x_160_);
lean_dec(v_curr_144_);
v_it_143_ = v___x_159_;
v_curr_144_ = v___x_161_;
goto _start;
}
}
}
else
{
lean_dec(v_curr_144_);
lean_dec(v_it_143_);
lean_inc(v_min_145_);
return v_min_145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(lean_object* v_s_167_, lean_object* v_it_168_, lean_object* v_min_169_){
_start:
{
lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_170_ = lean_string_utf8_byte_size(v_s_167_);
v___x_171_ = lean_nat_dec_eq(v_it_168_, v___x_170_);
if (v___x_171_ == 0)
{
uint32_t v___x_172_; uint32_t v___x_173_; uint8_t v___x_174_; 
v___x_172_ = lean_string_utf8_get_fast(v_s_167_, v_it_168_);
v___x_173_ = 10;
v___x_174_ = lean_uint32_dec_eq(v___x_172_, v___x_173_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; 
v___x_175_ = lean_string_utf8_next_fast(v_s_167_, v_it_168_);
lean_dec(v_it_168_);
v_it_168_ = v___x_175_;
goto _start;
}
else
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = lean_string_utf8_next_fast(v_s_167_, v_it_168_);
lean_dec(v_it_168_);
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces(v_s_167_, v___x_177_, v___x_178_, v_min_169_);
return v___x_179_;
}
}
else
{
lean_dec(v_it_168_);
lean_inc(v_min_169_);
return v_min_169_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine___boxed(lean_object* v_s_180_, lean_object* v_it_181_, lean_object* v_min_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(v_s_180_, v_it_181_, v_min_182_);
lean_dec(v_min_182_);
lean_dec_ref(v_s_180_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces___boxed(lean_object* v_s_184_, lean_object* v_it_185_, lean_object* v_curr_186_, lean_object* v_min_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces(v_s_184_, v_it_185_, v_curr_186_, v_min_187_);
lean_dec(v_min_187_);
lean_dec_ref(v_s_184_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg(lean_object* v___x_189_, lean_object* v_s_190_, lean_object* v_a_191_, lean_object* v_b_192_){
_start:
{
lean_object* v_startInclusive_193_; lean_object* v_endExclusive_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v_startInclusive_193_ = lean_ctor_get(v___x_189_, 1);
v_endExclusive_194_ = lean_ctor_get(v___x_189_, 2);
v___x_195_ = lean_nat_sub(v_endExclusive_194_, v_startInclusive_193_);
v___x_196_ = lean_nat_dec_eq(v_a_191_, v___x_195_);
lean_dec(v___x_195_);
if (v___x_196_ == 0)
{
uint32_t v___x_197_; uint32_t v___x_198_; uint8_t v___x_199_; 
lean_dec(v_b_192_);
v___x_197_ = lean_string_utf8_get_fast(v_s_190_, v_a_191_);
v___x_198_ = 10;
v___x_199_ = lean_uint32_dec_eq(v___x_197_, v___x_198_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = lean_box(0);
v___x_201_ = lean_string_utf8_next_fast(v_s_190_, v_a_191_);
lean_dec(v_a_191_);
v_a_191_ = v___x_201_;
v_b_192_ = v___x_200_;
goto _start;
}
else
{
lean_object* v___x_203_; 
v___x_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_203_, 0, v_a_191_);
return v___x_203_;
}
}
else
{
lean_dec(v_a_191_);
return v_b_192_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg___boxed(lean_object* v___x_204_, lean_object* v_s_205_, lean_object* v_a_206_, lean_object* v_b_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg(v___x_204_, v_s_205_, v_a_206_, v_b_207_);
lean_dec_ref(v_s_205_);
lean_dec_ref(v___x_204_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize(lean_object* v_s_209_){
_start:
{
lean_object* v_searcher_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v_searcher_210_ = lean_unsigned_to_nat(0u);
v___x_211_ = lean_string_utf8_byte_size(v_s_209_);
lean_inc_ref(v_s_209_);
v___x_212_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_212_, 0, v_s_209_);
lean_ctor_set(v___x_212_, 1, v_searcher_210_);
lean_ctor_set(v___x_212_, 2, v___x_211_);
v___x_213_ = lean_box(0);
v___x_214_ = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg(v___x_212_, v_s_209_, v_searcher_210_, v___x_213_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_dec_ref(v___x_212_);
lean_dec_ref(v_s_209_);
return v_searcher_210_;
}
else
{
lean_object* v_val_215_; lean_object* v___x_216_; 
v_val_215_ = lean_ctor_get(v___x_214_, 0);
lean_inc(v_val_215_);
lean_dec_ref(v___x_214_);
v___x_216_ = l_String_Slice_Pos_next_x3f(v___x_212_, v_val_215_);
lean_dec(v_val_215_);
lean_dec_ref(v___x_212_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_dec_ref(v_s_209_);
return v_searcher_210_;
}
else
{
lean_object* v_val_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v_val_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_val_217_);
lean_dec_ref(v___x_216_);
v___x_218_ = lean_string_length(v_s_209_);
v___x_219_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces(v_s_209_, v_val_217_, v_searcher_210_, v___x_218_);
lean_dec_ref(v_s_209_);
return v___x_219_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0(lean_object* v___x_220_, lean_object* v_s_221_, lean_object* v_inst_222_, lean_object* v_R_223_, lean_object* v_a_224_, lean_object* v_b_225_, lean_object* v_c_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg(v___x_220_, v_s_221_, v_a_224_, v_b_225_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___boxed(lean_object* v___x_228_, lean_object* v_s_229_, lean_object* v_inst_230_, lean_object* v_R_231_, lean_object* v_a_232_, lean_object* v_b_233_, lean_object* v_c_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0(v___x_228_, v_s_229_, v_inst_230_, v_R_231_, v_a_232_, v_b_233_, v_c_234_);
lean_dec_ref(v_s_229_);
lean_dec_ref(v___x_228_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(lean_object* v_n_236_, lean_object* v_n_237_, lean_object* v_s_238_, lean_object* v_it_239_, lean_object* v_r_240_){
_start:
{
lean_object* v_zero_241_; uint8_t v_isZero_242_; 
v_zero_241_ = lean_unsigned_to_nat(0u);
v_isZero_242_ = lean_nat_dec_eq(v_n_237_, v_zero_241_);
if (v_isZero_242_ == 1)
{
lean_object* v___x_243_; 
lean_dec(v_n_237_);
v___x_243_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine(v_n_236_, v_s_238_, v_it_239_, v_r_240_);
return v___x_243_;
}
else
{
lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_244_ = lean_string_utf8_byte_size(v_s_238_);
v___x_245_ = lean_nat_dec_eq(v_it_239_, v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v_one_246_; lean_object* v_n_247_; uint8_t v___y_249_; uint32_t v___x_253_; uint32_t v___x_254_; uint8_t v___x_255_; 
v_one_246_ = lean_unsigned_to_nat(1u);
v_n_247_ = lean_nat_sub(v_n_237_, v_one_246_);
lean_dec(v_n_237_);
v___x_253_ = lean_string_utf8_get_fast(v_s_238_, v_it_239_);
v___x_254_ = 32;
v___x_255_ = lean_uint32_dec_eq(v___x_253_, v___x_254_);
if (v___x_255_ == 0)
{
uint32_t v___x_256_; uint8_t v___x_257_; 
v___x_256_ = 9;
v___x_257_ = lean_uint32_dec_eq(v___x_253_, v___x_256_);
v___y_249_ = v___x_257_;
goto v___jp_248_;
}
else
{
v___y_249_ = v___x_255_;
goto v___jp_248_;
}
v___jp_248_:
{
if (v___y_249_ == 0)
{
lean_object* v___x_250_; 
lean_dec(v_n_247_);
v___x_250_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine(v_n_236_, v_s_238_, v_it_239_, v_r_240_);
return v___x_250_;
}
else
{
lean_object* v___x_251_; 
v___x_251_ = lean_string_utf8_next_fast(v_s_238_, v_it_239_);
lean_dec(v_it_239_);
v_n_237_ = v_n_247_;
v_it_239_ = v___x_251_;
goto _start;
}
}
}
else
{
lean_dec(v_it_239_);
lean_dec(v_n_237_);
lean_dec(v_n_236_);
return v_r_240_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine(lean_object* v_n_258_, lean_object* v_s_259_, lean_object* v_it_260_, lean_object* v_r_261_){
_start:
{
lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_262_ = lean_string_utf8_byte_size(v_s_259_);
v___x_263_ = lean_nat_dec_eq(v_it_260_, v___x_262_);
if (v___x_263_ == 0)
{
uint32_t v___x_264_; uint32_t v___x_265_; uint8_t v___x_266_; 
v___x_264_ = lean_string_utf8_get_fast(v_s_259_, v_it_260_);
v___x_265_ = 10;
v___x_266_ = lean_uint32_dec_eq(v___x_264_, v___x_265_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_string_utf8_next_fast(v_s_259_, v_it_260_);
lean_dec(v_it_260_);
v___x_268_ = lean_string_push(v_r_261_, v___x_264_);
v_it_260_ = v___x_267_;
v_r_261_ = v___x_268_;
goto _start;
}
else
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_270_ = lean_string_utf8_next_fast(v_s_259_, v_it_260_);
lean_dec(v_it_260_);
v___x_271_ = lean_string_push(v_r_261_, v___x_265_);
lean_inc(v_n_258_);
v___x_272_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(v_n_258_, v_n_258_, v_s_259_, v___x_270_, v___x_271_);
return v___x_272_;
}
}
else
{
lean_dec(v_it_260_);
lean_dec(v_n_258_);
return v_r_261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine___boxed(lean_object* v_n_273_, lean_object* v_s_274_, lean_object* v_it_275_, lean_object* v_r_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine(v_n_273_, v_s_274_, v_it_275_, v_r_276_);
lean_dec_ref(v_s_274_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces___boxed(lean_object* v_n_278_, lean_object* v_n_279_, lean_object* v_s_280_, lean_object* v_it_281_, lean_object* v_r_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(v_n_278_, v_n_279_, v_s_280_, v_it_281_, v_r_282_);
lean_dec_ref(v_s_280_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___redArg(lean_object* v_n_284_, lean_object* v_h__1_285_, lean_object* v_h__2_286_){
_start:
{
lean_object* v_zero_287_; uint8_t v_isZero_288_; 
v_zero_287_ = lean_unsigned_to_nat(0u);
v_isZero_288_ = lean_nat_dec_eq(v_n_284_, v_zero_287_);
if (v_isZero_288_ == 1)
{
lean_object* v___x_289_; lean_object* v___x_290_; 
lean_dec(v_h__2_286_);
v___x_289_ = lean_box(0);
v___x_290_ = lean_apply_1(v_h__1_285_, v___x_289_);
return v___x_290_;
}
else
{
lean_object* v_one_291_; lean_object* v_n_292_; lean_object* v___x_293_; 
lean_dec(v_h__1_285_);
v_one_291_ = lean_unsigned_to_nat(1u);
v_n_292_ = lean_nat_sub(v_n_284_, v_one_291_);
v___x_293_ = lean_apply_1(v_h__2_286_, v_n_292_);
return v___x_293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___redArg___boxed(lean_object* v_n_294_, lean_object* v_h__1_295_, lean_object* v_h__2_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___redArg(v_n_294_, v_h__1_295_, v_h__2_296_);
lean_dec(v_n_294_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter(lean_object* v_motive_298_, lean_object* v_n_299_, lean_object* v_h__1_300_, lean_object* v_h__2_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___redArg(v_n_299_, v_h__1_300_, v_h__2_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___boxed(lean_object* v_motive_303_, lean_object* v_n_304_, lean_object* v_h__1_305_, lean_object* v_h__2_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter(v_motive_303_, v_n_304_, v_h__1_305_, v_h__2_306_);
lean_dec(v_n_304_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces(lean_object* v_n_309_, lean_object* v_s_310_){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = lean_unsigned_to_nat(0u);
v___x_312_ = ((lean_object*)(l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___closed__0));
lean_inc(v_n_309_);
v___x_313_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(v_n_309_, v_n_309_, v_s_310_, v___x_311_, v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___boxed(lean_object* v_n_314_, lean_object* v_s_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces(v_n_314_, v_s_315_);
lean_dec_ref(v_s_315_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_String_removeLeadingSpaces(lean_object* v_s_317_){
_start:
{
lean_object* v_n_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
lean_inc_ref(v_s_317_);
v_n_318_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize(v_s_317_);
v___x_319_ = lean_unsigned_to_nat(0u);
v___x_320_ = lean_nat_dec_eq(v_n_318_, v___x_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; 
v___x_321_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces(v_n_318_, v_s_317_);
lean_dec_ref(v_s_317_);
return v___x_321_;
}
else
{
lean_dec(v_n_318_);
return v_s_317_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_crlfToLf_go(lean_object* v_text_322_, lean_object* v_acc_323_, lean_object* v_accStop_324_, lean_object* v_pos_325_){
_start:
{
uint8_t v___x_326_; 
v___x_326_ = lean_string_utf8_at_end(v_text_322_, v_pos_325_);
if (v___x_326_ == 0)
{
uint32_t v_c_327_; lean_object* v_pos_x27_328_; uint8_t v___x_341_; 
v_c_327_ = lean_string_utf8_get_fast(v_text_322_, v_pos_325_);
v_pos_x27_328_ = lean_string_utf8_next_fast(v_text_322_, v_pos_325_);
v___x_341_ = lean_string_utf8_at_end(v_text_322_, v_pos_x27_328_);
if (v___x_341_ == 0)
{
goto v___jp_329_;
}
else
{
if (v___x_326_ == 0)
{
lean_dec(v_pos_325_);
v_pos_325_ = v_pos_x27_328_;
goto _start;
}
else
{
goto v___jp_329_;
}
}
v___jp_329_:
{
uint32_t v___x_330_; uint8_t v___x_331_; 
v___x_330_ = 13;
v___x_331_ = lean_uint32_dec_eq(v_c_327_, v___x_330_);
if (v___x_331_ == 0)
{
lean_dec(v_pos_325_);
v_pos_325_ = v_pos_x27_328_;
goto _start;
}
else
{
uint32_t v___x_333_; uint32_t v___x_334_; uint8_t v___x_335_; 
v___x_333_ = lean_string_utf8_get(v_text_322_, v_pos_x27_328_);
v___x_334_ = 10;
v___x_335_ = lean_uint32_dec_eq(v___x_333_, v___x_334_);
if (v___x_335_ == 0)
{
lean_dec(v_pos_325_);
v_pos_325_ = v_pos_x27_328_;
goto _start;
}
else
{
lean_object* v___x_337_; lean_object* v_acc_338_; lean_object* v___x_339_; 
v___x_337_ = lean_string_utf8_extract(v_text_322_, v_accStop_324_, v_pos_325_);
lean_dec(v_pos_325_);
lean_dec(v_accStop_324_);
v_acc_338_ = lean_string_append(v_acc_323_, v___x_337_);
lean_dec_ref(v___x_337_);
v___x_339_ = lean_string_utf8_next_fast(v_text_322_, v_pos_x27_328_);
v_acc_323_ = v_acc_338_;
v_accStop_324_ = v_pos_x27_328_;
v_pos_325_ = v___x_339_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = lean_nat_dec_eq(v_accStop_324_, v___x_343_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_string_utf8_extract(v_text_322_, v_accStop_324_, v_pos_325_);
lean_dec(v_pos_325_);
lean_dec(v_accStop_324_);
v___x_346_ = lean_string_append(v_acc_323_, v___x_345_);
lean_dec_ref(v___x_345_);
return v___x_346_;
}
else
{
lean_dec(v_pos_325_);
lean_dec(v_accStop_324_);
lean_dec_ref(v_acc_323_);
lean_inc_ref(v_text_322_);
return v_text_322_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_crlfToLf_go___boxed(lean_object* v_text_347_, lean_object* v_acc_348_, lean_object* v_accStop_349_, lean_object* v_pos_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l___private_Init_Data_String_Extra_0__String_crlfToLf_go(v_text_347_, v_acc_348_, v_accStop_349_, v_pos_350_);
lean_dec_ref(v_text_347_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_String_crlfToLf(lean_object* v_text_352_){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_353_ = ((lean_object*)(l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___closed__0));
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = l___private_Init_Data_String_Extra_0__String_crlfToLf_go(v_text_352_, v___x_353_, v___x_354_, v___x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_String_crlfToLf___boxed(lean_object* v_text_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_String_crlfToLf(v_text_356_);
lean_dec_ref(v_text_356_);
return v_res_357_;
}
}
lean_object* runtime_initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Termination(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Extra(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

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
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
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
uint8_t l_String_validateUTF8(lean_object* v_a_137_){
_start:
{
uint8_t v___x_138_; 
v___x_138_ = lean_string_validate_utf8(v_a_137_);
return v___x_138_;
}
}
LEAN_EXPORT void l_String_validateUTF8_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_137_ = stack[0].m_obj;
uint8_t v_res_139_;
v_res_139_ = l_String_validateUTF8(v_a_137_);
stack->m_num = v_res_139_;
}
LEAN_EXPORT lean_object* l_String_validateUTF8___boxed(lean_object* v_a_140_){
_start:
{
uint8_t v_res_141_; lean_object* v_r_142_; 
v_res_141_ = l_String_validateUTF8(v_a_140_);
lean_dec_ref(v_a_140_);
v_r_142_ = lean_box(v_res_141_);
return v_r_142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces(lean_object* v_s_143_, lean_object* v_it_144_, lean_object* v_curr_145_, lean_object* v_min_146_){
_start:
{
lean_object* v___x_152_; uint8_t v_decide_153_; 
v___x_152_ = lean_string_utf8_byte_size(v_s_143_);
v_decide_153_ = lean_nat_dec_eq(v_it_144_, v___x_152_);
if (v_decide_153_ == 0)
{
uint32_t v___x_154_; uint32_t v___x_155_; uint8_t v___x_156_; 
v___x_154_ = lean_string_utf8_get_fast(v_s_143_, v_it_144_);
v___x_155_ = 32;
v___x_156_ = lean_uint32_dec_eq(v___x_154_, v___x_155_);
if (v___x_156_ == 0)
{
uint32_t v___x_157_; uint8_t v___x_158_; 
v___x_157_ = 9;
v___x_158_ = lean_uint32_dec_eq(v___x_154_, v___x_157_);
if (v___x_158_ == 0)
{
uint32_t v___x_159_; uint8_t v___x_160_; 
v___x_159_ = 10;
v___x_160_ = lean_uint32_dec_eq(v___x_154_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = lean_string_utf8_next_fast(v_s_143_, v_it_144_);
lean_dec(v_it_144_);
v___x_162_ = lean_nat_dec_le(v_curr_145_, v_min_146_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; 
lean_dec(v_curr_145_);
v___x_163_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(v_s_143_, v___x_161_, v_min_146_);
return v___x_163_;
}
else
{
lean_object* v___x_164_; 
v___x_164_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(v_s_143_, v___x_161_, v_curr_145_);
lean_dec(v_curr_145_);
return v___x_164_;
}
}
else
{
lean_object* v___x_165_; lean_object* v___x_166_; 
lean_dec(v_curr_145_);
v___x_165_ = lean_string_utf8_next_fast(v_s_143_, v_it_144_);
lean_dec(v_it_144_);
v___x_166_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(v_s_143_, v___x_165_, v_min_146_);
return v___x_166_;
}
}
else
{
goto v___jp_147_;
}
}
else
{
goto v___jp_147_;
}
}
else
{
lean_dec(v_curr_145_);
lean_dec(v_it_144_);
lean_inc(v_min_146_);
return v_min_146_;
}
v___jp_147_:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_string_utf8_next_fast(v_s_143_, v_it_144_);
lean_dec(v_it_144_);
v___x_149_ = lean_unsigned_to_nat(1u);
v___x_150_ = lean_nat_add(v_curr_145_, v___x_149_);
lean_dec(v_curr_145_);
v_it_144_ = v___x_148_;
v_curr_145_ = v___x_150_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(lean_object* v_s_167_, lean_object* v_it_168_, lean_object* v_min_169_){
_start:
{
lean_object* v___x_170_; uint8_t v_decide_171_; 
v___x_170_ = lean_string_utf8_byte_size(v_s_167_);
v_decide_171_ = lean_nat_dec_eq(v_it_168_, v___x_170_);
if (v_decide_171_ == 0)
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
uint8_t v_decide_193_; 
v_decide_193_ = lean_nat_dec_eq(v_a_191_, v___x_189_);
if (v_decide_193_ == 0)
{
uint32_t v___x_194_; uint32_t v___x_195_; uint8_t v___x_196_; 
v___x_194_ = lean_string_utf8_get_fast(v_s_190_, v_a_191_);
v___x_195_ = 10;
v___x_196_ = lean_uint32_dec_eq(v___x_194_, v___x_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = lean_box(0);
v___x_198_ = lean_string_utf8_next_fast(v_s_190_, v_a_191_);
lean_dec(v_a_191_);
v_a_191_ = v___x_198_;
v_b_192_ = v___x_197_;
goto _start;
}
else
{
lean_object* v___x_200_; 
v___x_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_200_, 0, v_a_191_);
return v___x_200_;
}
}
else
{
lean_dec(v_a_191_);
lean_inc(v_b_192_);
return v_b_192_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg___boxed(lean_object* v___x_201_, lean_object* v_s_202_, lean_object* v_a_203_, lean_object* v_b_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg(v___x_201_, v_s_202_, v_a_203_, v_b_204_);
lean_dec(v_b_204_);
lean_dec_ref(v_s_202_);
lean_dec(v___x_201_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize(lean_object* v_s_206_){
_start:
{
lean_object* v_searcher_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v_searcher_207_ = lean_unsigned_to_nat(0u);
v___x_208_ = lean_string_utf8_byte_size(v_s_206_);
lean_inc_ref(v_s_206_);
v___x_209_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_209_, 0, v_s_206_);
lean_ctor_set(v___x_209_, 1, v_searcher_207_);
lean_ctor_set(v___x_209_, 2, v___x_208_);
v___x_210_ = lean_box(0);
v___x_211_ = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg(v___x_208_, v_s_206_, v_searcher_207_, v___x_210_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_dec_ref_known(v___x_209_, 3);
lean_dec_ref(v_s_206_);
return v_searcher_207_;
}
else
{
lean_object* v_val_212_; lean_object* v___x_213_; 
v_val_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_val_212_);
lean_dec_ref_known(v___x_211_, 1);
v___x_213_ = l_String_Slice_Pos_next_x3f(v___x_209_, v_val_212_);
lean_dec(v_val_212_);
lean_dec_ref_known(v___x_209_, 3);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_dec_ref(v_s_206_);
return v_searcher_207_;
}
else
{
lean_object* v_val_214_; lean_object* v___x_215_; 
v_val_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_val_214_);
lean_dec_ref_known(v___x_213_, 1);
v___x_215_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces(v_s_206_, v_val_214_, v_searcher_207_, v___x_208_);
lean_dec_ref(v_s_206_);
return v___x_215_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0(lean_object* v___x_216_, lean_object* v___x_217_, lean_object* v_s_218_, lean_object* v_inst_219_, lean_object* v_R_220_, lean_object* v_a_221_, lean_object* v_b_222_, lean_object* v_c_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg(v___x_216_, v_s_218_, v_a_221_, v_b_222_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___boxed(lean_object* v___x_225_, lean_object* v___x_226_, lean_object* v_s_227_, lean_object* v_inst_228_, lean_object* v_R_229_, lean_object* v_a_230_, lean_object* v_b_231_, lean_object* v_c_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0(v___x_225_, v___x_226_, v_s_227_, v_inst_228_, v_R_229_, v_a_230_, v_b_231_, v_c_232_);
lean_dec(v_b_231_);
lean_dec_ref(v_s_227_);
lean_dec_ref(v___x_226_);
lean_dec(v___x_225_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(lean_object* v_n_234_, lean_object* v_n_235_, lean_object* v_s_236_, lean_object* v_it_237_, lean_object* v_r_238_){
_start:
{
lean_object* v_zero_239_; uint8_t v_isZero_240_; 
v_zero_239_ = lean_unsigned_to_nat(0u);
v_isZero_240_ = lean_nat_dec_eq(v_n_235_, v_zero_239_);
if (v_isZero_240_ == 1)
{
lean_object* v___x_241_; 
lean_dec(v_n_235_);
v___x_241_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine(v_n_234_, v_s_236_, v_it_237_, v_r_238_);
return v___x_241_;
}
else
{
lean_object* v___x_242_; uint8_t v_decide_243_; 
v___x_242_ = lean_string_utf8_byte_size(v_s_236_);
v_decide_243_ = lean_nat_dec_eq(v_it_237_, v___x_242_);
if (v_decide_243_ == 0)
{
lean_object* v_one_244_; lean_object* v_n_245_; uint32_t v___x_249_; uint32_t v___x_250_; uint8_t v___x_251_; 
v_one_244_ = lean_unsigned_to_nat(1u);
v_n_245_ = lean_nat_sub(v_n_235_, v_one_244_);
lean_dec(v_n_235_);
v___x_249_ = lean_string_utf8_get_fast(v_s_236_, v_it_237_);
v___x_250_ = 32;
v___x_251_ = lean_uint32_dec_eq(v___x_249_, v___x_250_);
if (v___x_251_ == 0)
{
uint32_t v___x_252_; uint8_t v___x_253_; 
v___x_252_ = 9;
v___x_253_ = lean_uint32_dec_eq(v___x_249_, v___x_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; 
lean_dec(v_n_245_);
v___x_254_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine(v_n_234_, v_s_236_, v_it_237_, v_r_238_);
return v___x_254_;
}
else
{
goto v___jp_246_;
}
}
else
{
goto v___jp_246_;
}
v___jp_246_:
{
lean_object* v___x_247_; 
v___x_247_ = lean_string_utf8_next_fast(v_s_236_, v_it_237_);
lean_dec(v_it_237_);
v_n_235_ = v_n_245_;
v_it_237_ = v___x_247_;
goto _start;
}
}
else
{
lean_dec(v_it_237_);
lean_dec(v_n_235_);
lean_dec(v_n_234_);
return v_r_238_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine(lean_object* v_n_255_, lean_object* v_s_256_, lean_object* v_it_257_, lean_object* v_r_258_){
_start:
{
lean_object* v___x_259_; uint8_t v_decide_260_; 
v___x_259_ = lean_string_utf8_byte_size(v_s_256_);
v_decide_260_ = lean_nat_dec_eq(v_it_257_, v___x_259_);
if (v_decide_260_ == 0)
{
uint32_t v___x_261_; uint32_t v___x_262_; uint8_t v___x_263_; 
v___x_261_ = lean_string_utf8_get_fast(v_s_256_, v_it_257_);
v___x_262_ = 10;
v___x_263_ = lean_uint32_dec_eq(v___x_261_, v___x_262_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lean_string_utf8_next_fast(v_s_256_, v_it_257_);
lean_dec(v_it_257_);
v___x_265_ = lean_string_push(v_r_258_, v___x_261_);
v_it_257_ = v___x_264_;
v_r_258_ = v___x_265_;
goto _start;
}
else
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_267_ = lean_string_utf8_next_fast(v_s_256_, v_it_257_);
lean_dec(v_it_257_);
v___x_268_ = lean_string_push(v_r_258_, v___x_262_);
lean_inc(v_n_255_);
v___x_269_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(v_n_255_, v_n_255_, v_s_256_, v___x_267_, v___x_268_);
return v___x_269_;
}
}
else
{
lean_dec(v_it_257_);
lean_dec(v_n_255_);
return v_r_258_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine___boxed(lean_object* v_n_270_, lean_object* v_s_271_, lean_object* v_it_272_, lean_object* v_r_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine(v_n_270_, v_s_271_, v_it_272_, v_r_273_);
lean_dec_ref(v_s_271_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces___boxed(lean_object* v_n_275_, lean_object* v_n_276_, lean_object* v_s_277_, lean_object* v_it_278_, lean_object* v_r_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(v_n_275_, v_n_276_, v_s_277_, v_it_278_, v_r_279_);
lean_dec_ref(v_s_277_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___redArg(lean_object* v_n_281_, lean_object* v_h__1_282_, lean_object* v_h__2_283_){
_start:
{
lean_object* v_zero_284_; uint8_t v_isZero_285_; 
v_zero_284_ = lean_unsigned_to_nat(0u);
v_isZero_285_ = lean_nat_dec_eq(v_n_281_, v_zero_284_);
if (v_isZero_285_ == 1)
{
lean_object* v___x_286_; lean_object* v___x_287_; 
lean_dec(v_h__2_283_);
v___x_286_ = lean_box(0);
v___x_287_ = lean_apply_1(v_h__1_282_, v___x_286_);
return v___x_287_;
}
else
{
lean_object* v_one_288_; lean_object* v_n_289_; lean_object* v___x_290_; 
lean_dec(v_h__1_282_);
v_one_288_ = lean_unsigned_to_nat(1u);
v_n_289_ = lean_nat_sub(v_n_281_, v_one_288_);
v___x_290_ = lean_apply_1(v_h__2_283_, v_n_289_);
return v___x_290_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___redArg___boxed(lean_object* v_n_291_, lean_object* v_h__1_292_, lean_object* v_h__2_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___redArg(v_n_291_, v_h__1_292_, v_h__2_293_);
lean_dec(v_n_291_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter(lean_object* v_motive_295_, lean_object* v_n_296_, lean_object* v_h__1_297_, lean_object* v_h__2_298_){
_start:
{
lean_object* v_zero_299_; uint8_t v_isZero_300_; 
v_zero_299_ = lean_unsigned_to_nat(0u);
v_isZero_300_ = lean_nat_dec_eq(v_n_296_, v_zero_299_);
if (v_isZero_300_ == 1)
{
lean_object* v___x_301_; lean_object* v___x_302_; 
lean_dec(v_h__2_298_);
v___x_301_ = lean_box(0);
v___x_302_ = lean_apply_1(v_h__1_297_, v___x_301_);
return v___x_302_;
}
else
{
lean_object* v_one_303_; lean_object* v_n_304_; lean_object* v___x_305_; 
lean_dec(v_h__1_297_);
v_one_303_ = lean_unsigned_to_nat(1u);
v_n_304_ = lean_nat_sub(v_n_296_, v_one_303_);
v___x_305_ = lean_apply_1(v_h__2_298_, v_n_304_);
return v___x_305_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___boxed(lean_object* v_motive_306_, lean_object* v_n_307_, lean_object* v_h__1_308_, lean_object* v_h__2_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter(v_motive_306_, v_n_307_, v_h__1_308_, v_h__2_309_);
lean_dec(v_n_307_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces(lean_object* v_n_312_, lean_object* v_s_313_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_314_ = lean_unsigned_to_nat(0u);
v___x_315_ = ((lean_object*)(l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___closed__0));
lean_inc(v_n_312_);
v___x_316_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(v_n_312_, v_n_312_, v_s_313_, v___x_314_, v___x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___boxed(lean_object* v_n_317_, lean_object* v_s_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces(v_n_317_, v_s_318_);
lean_dec_ref(v_s_318_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_String_removeLeadingSpaces(lean_object* v_s_320_){
_start:
{
lean_object* v_n_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
lean_inc_ref(v_s_320_);
v_n_321_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize(v_s_320_);
v___x_322_ = lean_unsigned_to_nat(0u);
v___x_323_ = lean_nat_dec_eq(v_n_321_, v___x_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; 
v___x_324_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces(v_n_321_, v_s_320_);
lean_dec_ref(v_s_320_);
return v___x_324_;
}
else
{
lean_dec(v_n_321_);
return v_s_320_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_crlfToLf_go(lean_object* v_text_325_, lean_object* v_acc_326_, lean_object* v_accStop_327_, lean_object* v_pos_328_){
_start:
{
uint8_t v___x_329_; 
v___x_329_ = lean_string_utf8_at_end(v_text_325_, v_pos_328_);
if (v___x_329_ == 0)
{
lean_object* v_pos_x27_330_; uint8_t v___y_332_; uint8_t v___x_345_; 
v_pos_x27_330_ = lean_string_utf8_next_fast(v_text_325_, v_pos_328_);
v___x_345_ = lean_string_utf8_at_end(v_text_325_, v_pos_x27_330_);
if (v___x_345_ == 0)
{
goto v___jp_338_;
}
else
{
if (v___x_329_ == 0)
{
v___y_332_ = v___x_329_;
goto v___jp_331_;
}
else
{
goto v___jp_338_;
}
}
v___jp_331_:
{
if (v___y_332_ == 0)
{
lean_dec(v_pos_328_);
v_pos_328_ = v_pos_x27_330_;
goto _start;
}
else
{
lean_object* v___x_334_; lean_object* v_acc_335_; lean_object* v___x_336_; 
v___x_334_ = lean_string_utf8_extract(v_text_325_, v_accStop_327_, v_pos_328_);
lean_dec(v_pos_328_);
lean_dec(v_accStop_327_);
v_acc_335_ = lean_string_append(v_acc_326_, v___x_334_);
lean_dec_ref(v___x_334_);
v___x_336_ = lean_string_utf8_next_fast(v_text_325_, v_pos_x27_330_);
v_acc_326_ = v_acc_335_;
v_accStop_327_ = v_pos_x27_330_;
v_pos_328_ = v___x_336_;
goto _start;
}
}
v___jp_338_:
{
uint32_t v_c_339_; uint32_t v___x_340_; uint8_t v___x_341_; 
v_c_339_ = lean_string_utf8_get_fast(v_text_325_, v_pos_328_);
v___x_340_ = 13;
v___x_341_ = lean_uint32_dec_eq(v_c_339_, v___x_340_);
if (v___x_341_ == 0)
{
v___y_332_ = v___x_329_;
goto v___jp_331_;
}
else
{
uint32_t v___x_342_; uint32_t v___x_343_; uint8_t v___x_344_; 
v___x_342_ = lean_string_utf8_get(v_text_325_, v_pos_x27_330_);
v___x_343_ = 10;
v___x_344_ = lean_uint32_dec_eq(v___x_342_, v___x_343_);
v___y_332_ = v___x_344_;
goto v___jp_331_;
}
}
}
else
{
lean_object* v___x_346_; uint8_t v_decide_347_; 
v___x_346_ = lean_unsigned_to_nat(0u);
v_decide_347_ = lean_nat_dec_eq(v_accStop_327_, v___x_346_);
if (v_decide_347_ == 0)
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_string_utf8_extract(v_text_325_, v_accStop_327_, v_pos_328_);
lean_dec(v_pos_328_);
lean_dec(v_accStop_327_);
v___x_349_ = lean_string_append(v_acc_326_, v___x_348_);
lean_dec_ref(v___x_348_);
return v___x_349_;
}
else
{
lean_dec(v_pos_328_);
lean_dec(v_accStop_327_);
lean_dec_ref(v_acc_326_);
lean_inc_ref(v_text_325_);
return v_text_325_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_crlfToLf_go___boxed(lean_object* v_text_350_, lean_object* v_acc_351_, lean_object* v_accStop_352_, lean_object* v_pos_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l___private_Init_Data_String_Extra_0__String_crlfToLf_go(v_text_350_, v_acc_351_, v_accStop_352_, v_pos_353_);
lean_dec_ref(v_text_350_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_String_crlfToLf(lean_object* v_text_355_){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_356_ = ((lean_object*)(l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___closed__0));
v___x_357_ = lean_unsigned_to_nat(0u);
v___x_358_ = l___private_Init_Data_String_Extra_0__String_crlfToLf_go(v_text_355_, v___x_356_, v___x_357_, v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_String_crlfToLf___boxed(lean_object* v_text_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_String_crlfToLf(v_text_359_);
lean_dec_ref(v_text_359_);
return v_res_360_;
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

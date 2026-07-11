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
uint8_t lean_bool_not(uint8_t);
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
lean_object* v___x_26_; lean_object* v___x_27_; uint8_t v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; uint8_t v___x_31_; uint8_t v___x_32_; uint8_t v___y_34_; uint8_t v___x_67_; uint8_t v___x_68_; uint8_t v___x_69_; 
v___x_26_ = lean_unsigned_to_nat(1u);
v___x_27_ = lean_nat_add(v_i_2_, v___x_26_);
v___x_28_ = lean_byte_array_fget(v_a_1_, v___x_27_);
lean_dec(v___x_27_);
v___x_29_ = lean_unsigned_to_nat(2u);
v___x_30_ = lean_nat_add(v_i_2_, v___x_29_);
v___x_31_ = lean_byte_array_fget(v_a_1_, v___x_30_);
lean_dec(v___x_30_);
v___x_32_ = lean_byte_array_fget(v_a_1_, v___x_23_);
lean_dec(v___x_23_);
v___x_67_ = lean_uint8_land(v___x_28_, v___x_13_);
v___x_68_ = lean_uint8_dec_eq(v___x_67_, v___x_7_);
v___x_69_ = lean_bool_not(v___x_68_);
if (v___x_69_ == 0)
{
uint8_t v___x_70_; uint8_t v___x_71_; uint8_t v___x_72_; 
v___x_70_ = lean_uint8_land(v___x_31_, v___x_13_);
v___x_71_ = lean_uint8_dec_eq(v___x_70_, v___x_7_);
v___x_72_ = lean_bool_not(v___x_71_);
v___y_34_ = v___x_72_;
goto v___jp_33_;
}
else
{
v___y_34_ = v___x_69_;
goto v___jp_33_;
}
v___jp_33_:
{
if (v___y_34_ == 0)
{
uint8_t v___x_35_; uint8_t v___x_36_; uint8_t v___x_37_; 
v___x_35_ = lean_uint8_land(v___x_32_, v___x_13_);
v___x_36_ = lean_uint8_dec_eq(v___x_35_, v___x_7_);
v___x_37_ = lean_bool_not(v___x_36_);
if (v___x_37_ == 0)
{
uint8_t v___x_38_; uint8_t v_b_u2080_39_; uint8_t v___x_40_; uint8_t v_b_u2081_41_; uint8_t v_b_u2082_42_; uint8_t v_b_u2083_43_; uint32_t v___x_44_; uint32_t v___x_45_; uint32_t v___x_46_; uint32_t v___x_47_; uint32_t v___x_48_; uint32_t v___x_49_; uint32_t v___x_50_; uint32_t v___x_51_; uint32_t v___x_52_; uint32_t v___x_53_; uint32_t v___x_54_; uint32_t v___x_55_; uint32_t v_r_56_; uint32_t v___x_57_; uint8_t v___x_58_; 
v___x_38_ = 7;
v_b_u2080_39_ = lean_uint8_land(v___x_6_, v___x_38_);
v___x_40_ = 63;
v_b_u2081_41_ = lean_uint8_land(v___x_28_, v___x_40_);
v_b_u2082_42_ = lean_uint8_land(v___x_31_, v___x_40_);
v_b_u2083_43_ = lean_uint8_land(v___x_32_, v___x_40_);
v___x_44_ = lean_uint8_to_uint32(v_b_u2080_39_);
v___x_45_ = 18;
v___x_46_ = lean_uint32_shift_left(v___x_44_, v___x_45_);
v___x_47_ = lean_uint8_to_uint32(v_b_u2081_41_);
v___x_48_ = 12;
v___x_49_ = lean_uint32_shift_left(v___x_47_, v___x_48_);
v___x_50_ = lean_uint32_lor(v___x_46_, v___x_49_);
v___x_51_ = lean_uint8_to_uint32(v_b_u2082_42_);
v___x_52_ = 6;
v___x_53_ = lean_uint32_shift_left(v___x_51_, v___x_52_);
v___x_54_ = lean_uint32_lor(v___x_50_, v___x_53_);
v___x_55_ = lean_uint8_to_uint32(v_b_u2083_43_);
v_r_56_ = lean_uint32_lor(v___x_54_, v___x_55_);
v___x_57_ = 65536;
v___x_58_ = lean_uint32_dec_lt(v_r_56_, v___x_57_);
if (v___x_58_ == 0)
{
uint32_t v___x_59_; uint8_t v___x_60_; 
v___x_59_ = 1114111;
v___x_60_ = lean_uint32_dec_lt(v___x_59_, v_r_56_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_box_uint32(v_r_56_);
v___x_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
return v___x_62_;
}
else
{
lean_object* v___x_63_; 
v___x_63_ = lean_box(0);
return v___x_63_;
}
}
else
{
lean_object* v___x_64_; 
v___x_64_ = lean_box(0);
return v___x_64_;
}
}
else
{
lean_object* v___x_65_; 
v___x_65_ = lean_box(0);
return v___x_65_;
}
}
else
{
lean_object* v___x_66_; 
v___x_66_ = lean_box(0);
return v___x_66_;
}
}
}
}
}
else
{
lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; 
v___x_73_ = lean_unsigned_to_nat(2u);
v___x_74_ = lean_nat_add(v_i_2_, v___x_73_);
v___x_75_ = lean_nat_dec_lt(v___x_74_, v___x_3_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; 
lean_dec(v___x_74_);
v___x_76_ = lean_box(0);
return v___x_76_;
}
else
{
lean_object* v___x_77_; lean_object* v___x_78_; uint8_t v___x_79_; uint8_t v___x_80_; uint8_t v___y_82_; uint8_t v___x_110_; uint8_t v___x_111_; uint8_t v___x_112_; 
v___x_77_ = lean_unsigned_to_nat(1u);
v___x_78_ = lean_nat_add(v_i_2_, v___x_77_);
v___x_79_ = lean_byte_array_fget(v_a_1_, v___x_78_);
lean_dec(v___x_78_);
v___x_80_ = lean_byte_array_fget(v_a_1_, v___x_74_);
lean_dec(v___x_74_);
v___x_110_ = lean_uint8_land(v___x_79_, v___x_13_);
v___x_111_ = lean_uint8_dec_eq(v___x_110_, v___x_7_);
v___x_112_ = lean_bool_not(v___x_111_);
if (v___x_112_ == 0)
{
uint8_t v___x_113_; uint8_t v___x_114_; uint8_t v___x_115_; 
v___x_113_ = lean_uint8_land(v___x_80_, v___x_13_);
v___x_114_ = lean_uint8_dec_eq(v___x_113_, v___x_7_);
v___x_115_ = lean_bool_not(v___x_114_);
v___y_82_ = v___x_115_;
goto v___jp_81_;
}
else
{
v___y_82_ = v___x_112_;
goto v___jp_81_;
}
v___jp_81_:
{
if (v___y_82_ == 0)
{
uint8_t v___x_83_; uint8_t v_b_u2080_84_; uint8_t v___x_85_; uint8_t v_b_u2081_86_; uint8_t v_b_u2082_87_; uint32_t v___x_88_; uint32_t v___x_89_; uint32_t v___x_90_; uint32_t v___x_91_; uint32_t v___x_92_; uint32_t v___x_93_; uint32_t v___x_94_; uint32_t v___x_95_; uint32_t v_r_96_; uint32_t v___x_97_; uint8_t v___x_98_; 
v___x_83_ = 15;
v_b_u2080_84_ = lean_uint8_land(v___x_6_, v___x_83_);
v___x_85_ = 63;
v_b_u2081_86_ = lean_uint8_land(v___x_79_, v___x_85_);
v_b_u2082_87_ = lean_uint8_land(v___x_80_, v___x_85_);
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
else
{
lean_object* v___x_109_; 
v___x_109_ = lean_box(0);
return v___x_109_;
}
}
}
}
}
else
{
lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_116_ = lean_unsigned_to_nat(1u);
v___x_117_ = lean_nat_add(v_i_2_, v___x_116_);
v___x_118_ = lean_nat_dec_lt(v___x_117_, v___x_3_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; 
lean_dec(v___x_117_);
v___x_119_ = lean_box(0);
return v___x_119_;
}
else
{
uint8_t v___x_120_; uint8_t v___x_121_; uint8_t v___x_122_; uint8_t v___x_123_; 
v___x_120_ = lean_byte_array_fget(v_a_1_, v___x_117_);
lean_dec(v___x_117_);
v___x_121_ = lean_uint8_land(v___x_120_, v___x_13_);
v___x_122_ = lean_uint8_dec_eq(v___x_121_, v___x_7_);
v___x_123_ = lean_bool_not(v___x_122_);
if (v___x_123_ == 0)
{
uint8_t v___x_124_; uint8_t v_b_u2080_125_; uint8_t v___x_126_; uint8_t v_b_u2081_127_; uint32_t v___x_128_; uint32_t v___x_129_; uint32_t v___x_130_; uint32_t v___x_131_; uint32_t v_r_132_; uint32_t v___x_133_; uint8_t v___x_134_; 
v___x_124_ = 31;
v_b_u2080_125_ = lean_uint8_land(v___x_6_, v___x_124_);
v___x_126_ = 63;
v_b_u2081_127_ = lean_uint8_land(v___x_120_, v___x_126_);
v___x_128_ = lean_uint8_to_uint32(v_b_u2080_125_);
v___x_129_ = 6;
v___x_130_ = lean_uint32_shift_left(v___x_128_, v___x_129_);
v___x_131_ = lean_uint8_to_uint32(v_b_u2081_127_);
v_r_132_ = lean_uint32_lor(v___x_130_, v___x_131_);
v___x_133_ = 128;
v___x_134_ = lean_uint32_dec_lt(v_r_132_, v___x_133_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_box_uint32(v_r_132_);
v___x_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
return v___x_136_;
}
else
{
lean_object* v___x_137_; 
v___x_137_ = lean_box(0);
return v___x_137_;
}
}
else
{
lean_object* v___x_138_; 
v___x_138_ = lean_box(0);
return v___x_138_;
}
}
}
}
else
{
uint32_t v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = lean_uint8_to_uint32(v___x_6_);
v___x_140_ = lean_box_uint32(v___x_139_);
v___x_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
return v___x_141_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_utf8DecodeChar_x3f___boxed(lean_object* v_a_142_, lean_object* v_i_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_String_utf8DecodeChar_x3f(v_a_142_, v_i_143_);
lean_dec(v_i_143_);
lean_dec_ref(v_a_142_);
return v_res_144_;
}
}
LEAN_EXPORT uint8_t l_String_validateUTF8(lean_object* v_a_145_){
_start:
{
uint8_t v___x_146_; 
v___x_146_ = lean_string_validate_utf8(v_a_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_String_validateUTF8___boxed(lean_object* v_a_147_){
_start:
{
uint8_t v_res_148_; lean_object* v_r_149_; 
v_res_148_ = l_String_validateUTF8(v_a_147_);
lean_dec_ref(v_a_147_);
v_r_149_ = lean_box(v_res_148_);
return v_r_149_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces(lean_object* v_s_150_, lean_object* v_it_151_, lean_object* v_curr_152_, lean_object* v_min_153_){
_start:
{
lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_154_ = lean_string_utf8_byte_size(v_s_150_);
v___x_155_ = lean_nat_dec_eq(v_it_151_, v___x_154_);
if (v___x_155_ == 0)
{
uint32_t v___x_156_; uint8_t v___y_158_; uint32_t v___x_171_; uint8_t v___x_172_; 
v___x_156_ = lean_string_utf8_get_fast(v_s_150_, v_it_151_);
v___x_171_ = 32;
v___x_172_ = lean_uint32_dec_eq(v___x_156_, v___x_171_);
if (v___x_172_ == 0)
{
uint32_t v___x_173_; uint8_t v___x_174_; 
v___x_173_ = 9;
v___x_174_ = lean_uint32_dec_eq(v___x_156_, v___x_173_);
v___y_158_ = v___x_174_;
goto v___jp_157_;
}
else
{
v___y_158_ = v___x_172_;
goto v___jp_157_;
}
v___jp_157_:
{
if (v___y_158_ == 0)
{
uint32_t v___x_159_; uint8_t v___x_160_; 
v___x_159_ = 10;
v___x_160_ = lean_uint32_dec_eq(v___x_156_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = lean_string_utf8_next_fast(v_s_150_, v_it_151_);
lean_dec(v_it_151_);
v___x_162_ = lean_nat_dec_le(v_curr_152_, v_min_153_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; 
lean_dec(v_curr_152_);
v___x_163_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(v_s_150_, v___x_161_, v_min_153_);
return v___x_163_;
}
else
{
lean_object* v___x_164_; 
v___x_164_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(v_s_150_, v___x_161_, v_curr_152_);
lean_dec(v_curr_152_);
return v___x_164_;
}
}
else
{
lean_object* v___x_165_; lean_object* v___x_166_; 
lean_dec(v_curr_152_);
v___x_165_ = lean_string_utf8_next_fast(v_s_150_, v_it_151_);
lean_dec(v_it_151_);
v___x_166_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(v_s_150_, v___x_165_, v_min_153_);
return v___x_166_;
}
}
else
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_167_ = lean_string_utf8_next_fast(v_s_150_, v_it_151_);
lean_dec(v_it_151_);
v___x_168_ = lean_unsigned_to_nat(1u);
v___x_169_ = lean_nat_add(v_curr_152_, v___x_168_);
lean_dec(v_curr_152_);
v_it_151_ = v___x_167_;
v_curr_152_ = v___x_169_;
goto _start;
}
}
}
else
{
lean_dec(v_curr_152_);
lean_dec(v_it_151_);
lean_inc(v_min_153_);
return v_min_153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(lean_object* v_s_175_, lean_object* v_it_176_, lean_object* v_min_177_){
_start:
{
lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_178_ = lean_string_utf8_byte_size(v_s_175_);
v___x_179_ = lean_nat_dec_eq(v_it_176_, v___x_178_);
if (v___x_179_ == 0)
{
uint32_t v___x_180_; uint32_t v___x_181_; uint8_t v___x_182_; 
v___x_180_ = lean_string_utf8_get_fast(v_s_175_, v_it_176_);
v___x_181_ = 10;
v___x_182_ = lean_uint32_dec_eq(v___x_180_, v___x_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; 
v___x_183_ = lean_string_utf8_next_fast(v_s_175_, v_it_176_);
lean_dec(v_it_176_);
v_it_176_ = v___x_183_;
goto _start;
}
else
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_185_ = lean_string_utf8_next_fast(v_s_175_, v_it_176_);
lean_dec(v_it_176_);
v___x_186_ = lean_unsigned_to_nat(0u);
v___x_187_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces(v_s_175_, v___x_185_, v___x_186_, v_min_177_);
return v___x_187_;
}
}
else
{
lean_dec(v_it_176_);
lean_inc(v_min_177_);
return v_min_177_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine___boxed(lean_object* v_s_188_, lean_object* v_it_189_, lean_object* v_min_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(v_s_188_, v_it_189_, v_min_190_);
lean_dec(v_min_190_);
lean_dec_ref(v_s_188_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces___boxed(lean_object* v_s_192_, lean_object* v_it_193_, lean_object* v_curr_194_, lean_object* v_min_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces(v_s_192_, v_it_193_, v_curr_194_, v_min_195_);
lean_dec(v_min_195_);
lean_dec_ref(v_s_192_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg(lean_object* v___x_197_, lean_object* v_s_198_, lean_object* v_a_199_, lean_object* v_b_200_){
_start:
{
lean_object* v_startInclusive_201_; lean_object* v_endExclusive_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v_startInclusive_201_ = lean_ctor_get(v___x_197_, 1);
v_endExclusive_202_ = lean_ctor_get(v___x_197_, 2);
v___x_203_ = lean_nat_sub(v_endExclusive_202_, v_startInclusive_201_);
v___x_204_ = lean_nat_dec_eq(v_a_199_, v___x_203_);
lean_dec(v___x_203_);
if (v___x_204_ == 0)
{
uint32_t v___x_205_; uint32_t v___x_206_; uint8_t v___x_207_; 
v___x_205_ = lean_string_utf8_get_fast(v_s_198_, v_a_199_);
v___x_206_ = 10;
v___x_207_ = lean_uint32_dec_eq(v___x_205_, v___x_206_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = lean_box(0);
v___x_209_ = lean_string_utf8_next_fast(v_s_198_, v_a_199_);
lean_dec(v_a_199_);
v_a_199_ = v___x_209_;
v_b_200_ = v___x_208_;
goto _start;
}
else
{
lean_object* v___x_211_; 
v___x_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_211_, 0, v_a_199_);
return v___x_211_;
}
}
else
{
lean_dec(v_a_199_);
lean_inc(v_b_200_);
return v_b_200_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg___boxed(lean_object* v___x_212_, lean_object* v_s_213_, lean_object* v_a_214_, lean_object* v_b_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg(v___x_212_, v_s_213_, v_a_214_, v_b_215_);
lean_dec(v_b_215_);
lean_dec_ref(v_s_213_);
lean_dec_ref(v___x_212_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize(lean_object* v_s_217_){
_start:
{
lean_object* v_searcher_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v_searcher_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_string_utf8_byte_size(v_s_217_);
lean_inc_ref(v_s_217_);
v___x_220_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_220_, 0, v_s_217_);
lean_ctor_set(v___x_220_, 1, v_searcher_218_);
lean_ctor_set(v___x_220_, 2, v___x_219_);
v___x_221_ = lean_box(0);
v___x_222_ = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg(v___x_220_, v_s_217_, v_searcher_218_, v___x_221_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_dec_ref_known(v___x_220_, 3);
lean_dec_ref(v_s_217_);
return v_searcher_218_;
}
else
{
lean_object* v_val_223_; lean_object* v___x_224_; 
v_val_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_val_223_);
lean_dec_ref_known(v___x_222_, 1);
v___x_224_ = l_String_Slice_Pos_next_x3f(v___x_220_, v_val_223_);
lean_dec(v_val_223_);
lean_dec_ref_known(v___x_220_, 3);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_dec_ref(v_s_217_);
return v_searcher_218_;
}
else
{
lean_object* v_val_225_; lean_object* v___x_226_; 
v_val_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_val_225_);
lean_dec_ref_known(v___x_224_, 1);
v___x_226_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces(v_s_217_, v_val_225_, v_searcher_218_, v___x_219_);
lean_dec_ref(v_s_217_);
return v___x_226_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0(lean_object* v___x_227_, lean_object* v_s_228_, lean_object* v_inst_229_, lean_object* v_R_230_, lean_object* v_a_231_, lean_object* v_b_232_, lean_object* v_c_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg(v___x_227_, v_s_228_, v_a_231_, v_b_232_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___boxed(lean_object* v___x_235_, lean_object* v_s_236_, lean_object* v_inst_237_, lean_object* v_R_238_, lean_object* v_a_239_, lean_object* v_b_240_, lean_object* v_c_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0(v___x_235_, v_s_236_, v_inst_237_, v_R_238_, v_a_239_, v_b_240_, v_c_241_);
lean_dec(v_b_240_);
lean_dec_ref(v_s_236_);
lean_dec_ref(v___x_235_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(lean_object* v_n_243_, lean_object* v_n_244_, lean_object* v_s_245_, lean_object* v_it_246_, lean_object* v_r_247_){
_start:
{
lean_object* v_zero_248_; uint8_t v_isZero_249_; 
v_zero_248_ = lean_unsigned_to_nat(0u);
v_isZero_249_ = lean_nat_dec_eq(v_n_244_, v_zero_248_);
if (v_isZero_249_ == 1)
{
lean_object* v___x_250_; 
lean_dec(v_n_244_);
v___x_250_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine(v_n_243_, v_s_245_, v_it_246_, v_r_247_);
return v___x_250_;
}
else
{
lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_251_ = lean_string_utf8_byte_size(v_s_245_);
v___x_252_ = lean_nat_dec_eq(v_it_246_, v___x_251_);
if (v___x_252_ == 0)
{
lean_object* v_one_253_; lean_object* v_n_254_; uint8_t v___y_256_; uint32_t v___x_260_; uint32_t v___x_261_; uint8_t v___x_262_; 
v_one_253_ = lean_unsigned_to_nat(1u);
v_n_254_ = lean_nat_sub(v_n_244_, v_one_253_);
lean_dec(v_n_244_);
v___x_260_ = lean_string_utf8_get_fast(v_s_245_, v_it_246_);
v___x_261_ = 32;
v___x_262_ = lean_uint32_dec_eq(v___x_260_, v___x_261_);
if (v___x_262_ == 0)
{
uint32_t v___x_263_; uint8_t v___x_264_; 
v___x_263_ = 9;
v___x_264_ = lean_uint32_dec_eq(v___x_260_, v___x_263_);
v___y_256_ = v___x_264_;
goto v___jp_255_;
}
else
{
v___y_256_ = v___x_262_;
goto v___jp_255_;
}
v___jp_255_:
{
if (v___y_256_ == 0)
{
lean_object* v___x_257_; 
lean_dec(v_n_254_);
v___x_257_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine(v_n_243_, v_s_245_, v_it_246_, v_r_247_);
return v___x_257_;
}
else
{
lean_object* v___x_258_; 
v___x_258_ = lean_string_utf8_next_fast(v_s_245_, v_it_246_);
lean_dec(v_it_246_);
v_n_244_ = v_n_254_;
v_it_246_ = v___x_258_;
goto _start;
}
}
}
else
{
lean_dec(v_it_246_);
lean_dec(v_n_244_);
lean_dec(v_n_243_);
return v_r_247_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine(lean_object* v_n_265_, lean_object* v_s_266_, lean_object* v_it_267_, lean_object* v_r_268_){
_start:
{
lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_269_ = lean_string_utf8_byte_size(v_s_266_);
v___x_270_ = lean_nat_dec_eq(v_it_267_, v___x_269_);
if (v___x_270_ == 0)
{
uint32_t v___x_271_; uint32_t v___x_272_; uint8_t v___x_273_; 
v___x_271_ = lean_string_utf8_get_fast(v_s_266_, v_it_267_);
v___x_272_ = 10;
v___x_273_ = lean_uint32_dec_eq(v___x_271_, v___x_272_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = lean_string_utf8_next_fast(v_s_266_, v_it_267_);
lean_dec(v_it_267_);
v___x_275_ = lean_string_push(v_r_268_, v___x_271_);
v_it_267_ = v___x_274_;
v_r_268_ = v___x_275_;
goto _start;
}
else
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_277_ = lean_string_utf8_next_fast(v_s_266_, v_it_267_);
lean_dec(v_it_267_);
v___x_278_ = lean_string_push(v_r_268_, v___x_272_);
lean_inc(v_n_265_);
v___x_279_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(v_n_265_, v_n_265_, v_s_266_, v___x_277_, v___x_278_);
return v___x_279_;
}
}
else
{
lean_dec(v_it_267_);
lean_dec(v_n_265_);
return v_r_268_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine___boxed(lean_object* v_n_280_, lean_object* v_s_281_, lean_object* v_it_282_, lean_object* v_r_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine(v_n_280_, v_s_281_, v_it_282_, v_r_283_);
lean_dec_ref(v_s_281_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces___boxed(lean_object* v_n_285_, lean_object* v_n_286_, lean_object* v_s_287_, lean_object* v_it_288_, lean_object* v_r_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(v_n_285_, v_n_286_, v_s_287_, v_it_288_, v_r_289_);
lean_dec_ref(v_s_287_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___redArg(lean_object* v_n_291_, lean_object* v_h__1_292_, lean_object* v_h__2_293_){
_start:
{
lean_object* v_zero_294_; uint8_t v_isZero_295_; 
v_zero_294_ = lean_unsigned_to_nat(0u);
v_isZero_295_ = lean_nat_dec_eq(v_n_291_, v_zero_294_);
if (v_isZero_295_ == 1)
{
lean_object* v___x_296_; lean_object* v___x_297_; 
lean_dec(v_h__2_293_);
v___x_296_ = lean_box(0);
v___x_297_ = lean_apply_1(v_h__1_292_, v___x_296_);
return v___x_297_;
}
else
{
lean_object* v_one_298_; lean_object* v_n_299_; lean_object* v___x_300_; 
lean_dec(v_h__1_292_);
v_one_298_ = lean_unsigned_to_nat(1u);
v_n_299_ = lean_nat_sub(v_n_291_, v_one_298_);
v___x_300_ = lean_apply_1(v_h__2_293_, v_n_299_);
return v___x_300_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___redArg___boxed(lean_object* v_n_301_, lean_object* v_h__1_302_, lean_object* v_h__2_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___redArg(v_n_301_, v_h__1_302_, v_h__2_303_);
lean_dec(v_n_301_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter(lean_object* v_motive_305_, lean_object* v_n_306_, lean_object* v_h__1_307_, lean_object* v_h__2_308_){
_start:
{
lean_object* v_zero_309_; uint8_t v_isZero_310_; 
v_zero_309_ = lean_unsigned_to_nat(0u);
v_isZero_310_ = lean_nat_dec_eq(v_n_306_, v_zero_309_);
if (v_isZero_310_ == 1)
{
lean_object* v___x_311_; lean_object* v___x_312_; 
lean_dec(v_h__2_308_);
v___x_311_ = lean_box(0);
v___x_312_ = lean_apply_1(v_h__1_307_, v___x_311_);
return v___x_312_;
}
else
{
lean_object* v_one_313_; lean_object* v_n_314_; lean_object* v___x_315_; 
lean_dec(v_h__1_307_);
v_one_313_ = lean_unsigned_to_nat(1u);
v_n_314_ = lean_nat_sub(v_n_306_, v_one_313_);
v___x_315_ = lean_apply_1(v_h__2_308_, v_n_314_);
return v___x_315_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___boxed(lean_object* v_motive_316_, lean_object* v_n_317_, lean_object* v_h__1_318_, lean_object* v_h__2_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter(v_motive_316_, v_n_317_, v_h__1_318_, v_h__2_319_);
lean_dec(v_n_317_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces(lean_object* v_n_322_, lean_object* v_s_323_){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_324_ = lean_unsigned_to_nat(0u);
v___x_325_ = ((lean_object*)(l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___closed__0));
lean_inc(v_n_322_);
v___x_326_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(v_n_322_, v_n_322_, v_s_323_, v___x_324_, v___x_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___boxed(lean_object* v_n_327_, lean_object* v_s_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces(v_n_327_, v_s_328_);
lean_dec_ref(v_s_328_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_String_removeLeadingSpaces(lean_object* v_s_330_){
_start:
{
lean_object* v_n_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
lean_inc_ref(v_s_330_);
v_n_331_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize(v_s_330_);
v___x_332_ = lean_unsigned_to_nat(0u);
v___x_333_ = lean_nat_dec_eq(v_n_331_, v___x_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; 
v___x_334_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces(v_n_331_, v_s_330_);
lean_dec_ref(v_s_330_);
return v___x_334_;
}
else
{
lean_dec(v_n_331_);
return v_s_330_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_crlfToLf_go(lean_object* v_text_335_, lean_object* v_acc_336_, lean_object* v_accStop_337_, lean_object* v_pos_338_){
_start:
{
uint8_t v___x_339_; 
v___x_339_ = lean_string_utf8_at_end(v_text_335_, v_pos_338_);
if (v___x_339_ == 0)
{
uint32_t v_c_340_; lean_object* v_pos_x27_341_; uint8_t v___x_354_; 
v_c_340_ = lean_string_utf8_get_fast(v_text_335_, v_pos_338_);
v_pos_x27_341_ = lean_string_utf8_next_fast(v_text_335_, v_pos_338_);
v___x_354_ = lean_string_utf8_at_end(v_text_335_, v_pos_x27_341_);
if (v___x_354_ == 0)
{
goto v___jp_342_;
}
else
{
if (v___x_339_ == 0)
{
lean_dec(v_pos_338_);
v_pos_338_ = v_pos_x27_341_;
goto _start;
}
else
{
goto v___jp_342_;
}
}
v___jp_342_:
{
uint32_t v___x_343_; uint8_t v___x_344_; 
v___x_343_ = 13;
v___x_344_ = lean_uint32_dec_eq(v_c_340_, v___x_343_);
if (v___x_344_ == 0)
{
lean_dec(v_pos_338_);
v_pos_338_ = v_pos_x27_341_;
goto _start;
}
else
{
uint32_t v___x_346_; uint32_t v___x_347_; uint8_t v___x_348_; 
v___x_346_ = lean_string_utf8_get(v_text_335_, v_pos_x27_341_);
v___x_347_ = 10;
v___x_348_ = lean_uint32_dec_eq(v___x_346_, v___x_347_);
if (v___x_348_ == 0)
{
lean_dec(v_pos_338_);
v_pos_338_ = v_pos_x27_341_;
goto _start;
}
else
{
lean_object* v___x_350_; lean_object* v_acc_351_; lean_object* v___x_352_; 
v___x_350_ = lean_string_utf8_extract(v_text_335_, v_accStop_337_, v_pos_338_);
lean_dec(v_pos_338_);
lean_dec(v_accStop_337_);
v_acc_351_ = lean_string_append(v_acc_336_, v___x_350_);
lean_dec_ref(v___x_350_);
v___x_352_ = lean_string_utf8_next_fast(v_text_335_, v_pos_x27_341_);
v_acc_336_ = v_acc_351_;
v_accStop_337_ = v_pos_x27_341_;
v_pos_338_ = v___x_352_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_356_ = lean_unsigned_to_nat(0u);
v___x_357_ = lean_nat_dec_eq(v_accStop_337_, v___x_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = lean_string_utf8_extract(v_text_335_, v_accStop_337_, v_pos_338_);
lean_dec(v_pos_338_);
lean_dec(v_accStop_337_);
v___x_359_ = lean_string_append(v_acc_336_, v___x_358_);
lean_dec_ref(v___x_358_);
return v___x_359_;
}
else
{
lean_dec(v_pos_338_);
lean_dec(v_accStop_337_);
lean_dec_ref(v_acc_336_);
lean_inc_ref(v_text_335_);
return v_text_335_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_crlfToLf_go___boxed(lean_object* v_text_360_, lean_object* v_acc_361_, lean_object* v_accStop_362_, lean_object* v_pos_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l___private_Init_Data_String_Extra_0__String_crlfToLf_go(v_text_360_, v_acc_361_, v_accStop_362_, v_pos_363_);
lean_dec_ref(v_text_360_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_String_crlfToLf(lean_object* v_text_365_){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_366_ = ((lean_object*)(l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___closed__0));
v___x_367_ = lean_unsigned_to_nat(0u);
v___x_368_ = l___private_Init_Data_String_Extra_0__String_crlfToLf_go(v_text_365_, v___x_366_, v___x_367_, v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_String_crlfToLf___boxed(lean_object* v_text_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_String_crlfToLf(v_text_369_);
lean_dec_ref(v_text_369_);
return v_res_370_;
}
}
lean_object* runtime_initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Length(uint8_t builtin);
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

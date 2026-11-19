// Lean compiler output
// Module: Init.Data.String.Lossy
// Imports: public import Init.Data.String.Basic public import Init.Data.String.Decode import Init.WFTactics import Init.Omega
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
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
uint8_t lean_uint8_land(uint8_t, uint8_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint8_to_uint32(uint8_t);
uint32_t lean_uint32_shift_left(uint32_t, uint32_t);
uint32_t lean_uint32_lor(uint32_t, uint32_t);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lossy_0__String_skipContinuationBytes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lossy_0__String_skipContinuationBytes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lossy_0__String_fromUTF8Lossy_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lossy_0__String_fromUTF8Lossy_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lossy_0__String_fromUTF8Lossy_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lossy_0__String_fromUTF8Lossy_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_fromUTF8Lossy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_String_fromUTF8Lossy___closed__0 = (const lean_object*)&l_String_fromUTF8Lossy___closed__0_value;
LEAN_EXPORT lean_object* l_String_fromUTF8Lossy(lean_object*);
LEAN_EXPORT lean_object* l_String_fromUTF8Lossy___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lossy_0__String_skipContinuationBytes(lean_object* v_b_1_, lean_object* v_i_2_){
_start:
{
lean_object* v___x_3_; uint8_t v___x_4_; 
v___x_3_ = lean_byte_array_size(v_b_1_);
v___x_4_ = lean_nat_dec_lt(v_i_2_, v___x_3_);
if (v___x_4_ == 0)
{
return v_i_2_;
}
else
{
uint8_t v___x_5_; uint8_t v___x_6_; uint8_t v___x_7_; uint8_t v___x_8_; uint8_t v___x_9_; 
v___x_5_ = lean_byte_array_fget(v_b_1_, v_i_2_);
v___x_6_ = 192;
v___x_7_ = lean_uint8_land(v___x_5_, v___x_6_);
v___x_8_ = 128;
v___x_9_ = lean_uint8_dec_eq(v___x_7_, v___x_8_);
if (v___x_9_ == 0)
{
return v_i_2_;
}
else
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lean_unsigned_to_nat(1u);
v___x_11_ = lean_nat_add(v_i_2_, v___x_10_);
lean_dec(v_i_2_);
v_i_2_ = v___x_11_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lossy_0__String_skipContinuationBytes___boxed(lean_object* v_b_13_, lean_object* v_i_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l___private_Init_Data_String_Lossy_0__String_skipContinuationBytes(v_b_13_, v_i_14_);
lean_dec_ref(v_b_13_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lossy_0__String_fromUTF8Lossy_go(lean_object* v_b_16_, lean_object* v_i_17_, lean_object* v_acc_18_){
_start:
{
uint32_t v___y_20_; lean_object* v___y_21_; uint32_t v_val_26_; lean_object* v___x_44_; uint8_t v___x_45_; 
v___x_44_ = lean_byte_array_size(v_b_16_);
v___x_45_ = lean_nat_dec_lt(v_i_17_, v___x_44_);
if (v___x_45_ == 0)
{
lean_dec(v_i_17_);
return v_acc_18_;
}
else
{
uint8_t v___x_46_; uint8_t v___x_47_; uint8_t v___x_48_; uint8_t v___x_49_; uint8_t v___x_50_; 
v___x_46_ = lean_byte_array_fget(v_b_16_, v_i_17_);
v___x_47_ = 128;
v___x_48_ = lean_uint8_land(v___x_46_, v___x_47_);
v___x_49_ = 0;
v___x_50_ = lean_uint8_dec_eq(v___x_48_, v___x_49_);
if (v___x_50_ == 0)
{
uint8_t v___x_51_; uint8_t v___x_52_; uint8_t v___x_53_; uint8_t v___x_54_; 
v___x_51_ = 224;
v___x_52_ = lean_uint8_land(v___x_46_, v___x_51_);
v___x_53_ = 192;
v___x_54_ = lean_uint8_dec_eq(v___x_52_, v___x_53_);
if (v___x_54_ == 0)
{
uint8_t v___x_55_; uint8_t v___x_56_; uint8_t v___x_57_; 
v___x_55_ = 240;
v___x_56_ = lean_uint8_land(v___x_46_, v___x_55_);
v___x_57_ = lean_uint8_dec_eq(v___x_56_, v___x_51_);
if (v___x_57_ == 0)
{
uint8_t v___x_58_; uint8_t v___x_59_; uint8_t v___x_60_; 
v___x_58_ = 248;
v___x_59_ = lean_uint8_land(v___x_46_, v___x_58_);
v___x_60_ = lean_uint8_dec_eq(v___x_59_, v___x_55_);
if (v___x_60_ == 0)
{
goto v___jp_37_;
}
else
{
lean_object* v___x_61_; lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_61_ = lean_unsigned_to_nat(3u);
v___x_62_ = lean_nat_add(v_i_17_, v___x_61_);
v___x_63_ = lean_nat_dec_lt(v___x_62_, v___x_44_);
if (v___x_63_ == 0)
{
lean_dec(v___x_62_);
goto v___jp_37_;
}
else
{
lean_object* v___x_64_; lean_object* v___x_65_; uint8_t v___x_66_; uint8_t v___x_67_; uint8_t v___x_68_; 
v___x_64_ = lean_unsigned_to_nat(1u);
v___x_65_ = lean_nat_add(v_i_17_, v___x_64_);
v___x_66_ = lean_byte_array_fget(v_b_16_, v___x_65_);
lean_dec(v___x_65_);
v___x_67_ = lean_uint8_land(v___x_66_, v___x_53_);
v___x_68_ = lean_uint8_dec_eq(v___x_67_, v___x_47_);
if (v___x_68_ == 0)
{
lean_dec(v___x_62_);
goto v___jp_37_;
}
else
{
lean_object* v___x_69_; lean_object* v___x_70_; uint8_t v___x_71_; uint8_t v___x_72_; uint8_t v___x_73_; 
v___x_69_ = lean_unsigned_to_nat(2u);
v___x_70_ = lean_nat_add(v_i_17_, v___x_69_);
v___x_71_ = lean_byte_array_fget(v_b_16_, v___x_70_);
lean_dec(v___x_70_);
v___x_72_ = lean_uint8_land(v___x_71_, v___x_53_);
v___x_73_ = lean_uint8_dec_eq(v___x_72_, v___x_47_);
if (v___x_73_ == 0)
{
lean_dec(v___x_62_);
goto v___jp_37_;
}
else
{
uint8_t v___x_74_; uint8_t v___x_75_; uint8_t v___x_76_; 
v___x_74_ = lean_byte_array_fget(v_b_16_, v___x_62_);
lean_dec(v___x_62_);
v___x_75_ = lean_uint8_land(v___x_74_, v___x_53_);
v___x_76_ = lean_uint8_dec_eq(v___x_75_, v___x_47_);
if (v___x_76_ == 0)
{
goto v___jp_37_;
}
else
{
uint8_t v___x_77_; uint8_t v_b_u2080_78_; uint8_t v___x_79_; uint8_t v_b_u2081_80_; uint8_t v_b_u2082_81_; uint8_t v_b_u2083_82_; uint32_t v___x_83_; uint32_t v___x_84_; uint32_t v___x_85_; uint32_t v___x_86_; uint32_t v___x_87_; uint32_t v___x_88_; uint32_t v___x_89_; uint32_t v___x_90_; uint32_t v___x_91_; uint32_t v___x_92_; uint32_t v___x_93_; uint32_t v___x_94_; uint32_t v_r_95_; uint32_t v___x_96_; uint8_t v___x_97_; 
v___x_77_ = 7;
v_b_u2080_78_ = lean_uint8_land(v___x_46_, v___x_77_);
v___x_79_ = 63;
v_b_u2081_80_ = lean_uint8_land(v___x_66_, v___x_79_);
v_b_u2082_81_ = lean_uint8_land(v___x_71_, v___x_79_);
v_b_u2083_82_ = lean_uint8_land(v___x_74_, v___x_79_);
v___x_83_ = lean_uint8_to_uint32(v_b_u2080_78_);
v___x_84_ = 18;
v___x_85_ = lean_uint32_shift_left(v___x_83_, v___x_84_);
v___x_86_ = lean_uint8_to_uint32(v_b_u2081_80_);
v___x_87_ = 12;
v___x_88_ = lean_uint32_shift_left(v___x_86_, v___x_87_);
v___x_89_ = lean_uint32_lor(v___x_85_, v___x_88_);
v___x_90_ = lean_uint8_to_uint32(v_b_u2082_81_);
v___x_91_ = 6;
v___x_92_ = lean_uint32_shift_left(v___x_90_, v___x_91_);
v___x_93_ = lean_uint32_lor(v___x_89_, v___x_92_);
v___x_94_ = lean_uint8_to_uint32(v_b_u2083_82_);
v_r_95_ = lean_uint32_lor(v___x_93_, v___x_94_);
v___x_96_ = 65536;
v___x_97_ = lean_uint32_dec_lt(v_r_95_, v___x_96_);
if (v___x_97_ == 0)
{
uint32_t v___x_98_; uint8_t v___x_99_; 
v___x_98_ = 1114111;
v___x_99_ = lean_uint32_dec_lt(v___x_98_, v_r_95_);
if (v___x_99_ == 0)
{
v_val_26_ = v_r_95_;
goto v___jp_25_;
}
else
{
goto v___jp_37_;
}
}
else
{
goto v___jp_37_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_100_ = lean_unsigned_to_nat(2u);
v___x_101_ = lean_nat_add(v_i_17_, v___x_100_);
v___x_102_ = lean_nat_dec_lt(v___x_101_, v___x_44_);
if (v___x_102_ == 0)
{
lean_dec(v___x_101_);
goto v___jp_37_;
}
else
{
lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; uint8_t v___x_106_; uint8_t v___x_107_; 
v___x_103_ = lean_unsigned_to_nat(1u);
v___x_104_ = lean_nat_add(v_i_17_, v___x_103_);
v___x_105_ = lean_byte_array_fget(v_b_16_, v___x_104_);
lean_dec(v___x_104_);
v___x_106_ = lean_uint8_land(v___x_105_, v___x_53_);
v___x_107_ = lean_uint8_dec_eq(v___x_106_, v___x_47_);
if (v___x_107_ == 0)
{
lean_dec(v___x_101_);
goto v___jp_37_;
}
else
{
uint8_t v___x_108_; uint8_t v___x_109_; uint8_t v___x_110_; 
v___x_108_ = lean_byte_array_fget(v_b_16_, v___x_101_);
lean_dec(v___x_101_);
v___x_109_ = lean_uint8_land(v___x_108_, v___x_53_);
v___x_110_ = lean_uint8_dec_eq(v___x_109_, v___x_47_);
if (v___x_110_ == 0)
{
goto v___jp_37_;
}
else
{
uint8_t v___x_111_; uint8_t v_b_u2080_112_; uint8_t v___x_113_; uint8_t v_b_u2081_114_; uint8_t v_b_u2082_115_; uint32_t v___x_116_; uint32_t v___x_117_; uint32_t v___x_118_; uint32_t v___x_119_; uint32_t v___x_120_; uint32_t v___x_121_; uint32_t v___x_122_; uint32_t v___x_123_; uint32_t v_r_124_; uint32_t v___x_125_; uint8_t v___x_126_; 
v___x_111_ = 15;
v_b_u2080_112_ = lean_uint8_land(v___x_46_, v___x_111_);
v___x_113_ = 63;
v_b_u2081_114_ = lean_uint8_land(v___x_105_, v___x_113_);
v_b_u2082_115_ = lean_uint8_land(v___x_108_, v___x_113_);
v___x_116_ = lean_uint8_to_uint32(v_b_u2080_112_);
v___x_117_ = 12;
v___x_118_ = lean_uint32_shift_left(v___x_116_, v___x_117_);
v___x_119_ = lean_uint8_to_uint32(v_b_u2081_114_);
v___x_120_ = 6;
v___x_121_ = lean_uint32_shift_left(v___x_119_, v___x_120_);
v___x_122_ = lean_uint32_lor(v___x_118_, v___x_121_);
v___x_123_ = lean_uint8_to_uint32(v_b_u2082_115_);
v_r_124_ = lean_uint32_lor(v___x_122_, v___x_123_);
v___x_125_ = 2048;
v___x_126_ = lean_uint32_dec_lt(v_r_124_, v___x_125_);
if (v___x_126_ == 0)
{
uint32_t v___x_127_; uint8_t v___x_128_; 
v___x_127_ = 55296;
v___x_128_ = lean_uint32_dec_le(v___x_127_, v_r_124_);
if (v___x_128_ == 0)
{
v_val_26_ = v_r_124_;
goto v___jp_25_;
}
else
{
uint32_t v___x_129_; uint8_t v___x_130_; 
v___x_129_ = 57343;
v___x_130_ = lean_uint32_dec_le(v_r_124_, v___x_129_);
if (v___x_130_ == 0)
{
v_val_26_ = v_r_124_;
goto v___jp_25_;
}
else
{
goto v___jp_37_;
}
}
}
else
{
goto v___jp_37_;
}
}
}
}
}
}
else
{
lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_131_ = lean_unsigned_to_nat(1u);
v___x_132_ = lean_nat_add(v_i_17_, v___x_131_);
v___x_133_ = lean_nat_dec_lt(v___x_132_, v___x_44_);
if (v___x_133_ == 0)
{
lean_dec(v___x_132_);
goto v___jp_37_;
}
else
{
uint8_t v___x_134_; uint8_t v___x_135_; uint8_t v___x_136_; 
v___x_134_ = lean_byte_array_fget(v_b_16_, v___x_132_);
lean_dec(v___x_132_);
v___x_135_ = lean_uint8_land(v___x_134_, v___x_53_);
v___x_136_ = lean_uint8_dec_eq(v___x_135_, v___x_47_);
if (v___x_136_ == 0)
{
goto v___jp_37_;
}
else
{
uint8_t v___x_137_; uint8_t v_b_u2080_138_; uint8_t v___x_139_; uint8_t v_b_u2081_140_; uint32_t v___x_141_; uint32_t v___x_142_; uint32_t v___x_143_; uint32_t v___x_144_; uint32_t v_r_145_; uint32_t v___x_146_; uint8_t v___x_147_; 
v___x_137_ = 31;
v_b_u2080_138_ = lean_uint8_land(v___x_46_, v___x_137_);
v___x_139_ = 63;
v_b_u2081_140_ = lean_uint8_land(v___x_134_, v___x_139_);
v___x_141_ = lean_uint8_to_uint32(v_b_u2080_138_);
v___x_142_ = 6;
v___x_143_ = lean_uint32_shift_left(v___x_141_, v___x_142_);
v___x_144_ = lean_uint8_to_uint32(v_b_u2081_140_);
v_r_145_ = lean_uint32_lor(v___x_143_, v___x_144_);
v___x_146_ = 128;
v___x_147_ = lean_uint32_dec_lt(v_r_145_, v___x_146_);
if (v___x_147_ == 0)
{
v_val_26_ = v_r_145_;
goto v___jp_25_;
}
else
{
goto v___jp_37_;
}
}
}
}
}
else
{
uint32_t v___x_148_; 
v___x_148_ = lean_uint8_to_uint32(v___x_46_);
v_val_26_ = v___x_148_;
goto v___jp_25_;
}
}
v___jp_19_:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_nat_add(v_i_17_, v___y_21_);
lean_dec(v_i_17_);
v___x_23_ = lean_string_push(v_acc_18_, v___y_20_);
v_i_17_ = v___x_22_;
v_acc_18_ = v___x_23_;
goto _start;
}
v___jp_25_:
{
uint32_t v___x_27_; uint8_t v___x_28_; 
v___x_27_ = 127;
v___x_28_ = lean_uint32_dec_le(v_val_26_, v___x_27_);
if (v___x_28_ == 0)
{
uint32_t v___x_29_; uint8_t v___x_30_; 
v___x_29_ = 2047;
v___x_30_ = lean_uint32_dec_le(v_val_26_, v___x_29_);
if (v___x_30_ == 0)
{
uint32_t v___x_31_; uint8_t v___x_32_; 
v___x_31_ = 65535;
v___x_32_ = lean_uint32_dec_le(v_val_26_, v___x_31_);
if (v___x_32_ == 0)
{
lean_object* v___x_33_; 
v___x_33_ = lean_unsigned_to_nat(4u);
v___y_20_ = v_val_26_;
v___y_21_ = v___x_33_;
goto v___jp_19_;
}
else
{
lean_object* v___x_34_; 
v___x_34_ = lean_unsigned_to_nat(3u);
v___y_20_ = v_val_26_;
v___y_21_ = v___x_34_;
goto v___jp_19_;
}
}
else
{
lean_object* v___x_35_; 
v___x_35_ = lean_unsigned_to_nat(2u);
v___y_20_ = v_val_26_;
v___y_21_ = v___x_35_;
goto v___jp_19_;
}
}
else
{
lean_object* v___x_36_; 
v___x_36_ = lean_unsigned_to_nat(1u);
v___y_20_ = v_val_26_;
v___y_21_ = v___x_36_;
goto v___jp_19_;
}
}
v___jp_37_:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; uint32_t v___x_41_; lean_object* v___x_42_; 
v___x_38_ = lean_unsigned_to_nat(1u);
v___x_39_ = lean_nat_add(v_i_17_, v___x_38_);
lean_dec(v_i_17_);
v___x_40_ = l___private_Init_Data_String_Lossy_0__String_skipContinuationBytes(v_b_16_, v___x_39_);
v___x_41_ = 65533;
v___x_42_ = lean_string_push(v_acc_18_, v___x_41_);
v_i_17_ = v___x_40_;
v_acc_18_ = v___x_42_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lossy_0__String_fromUTF8Lossy_go___boxed(lean_object* v_b_149_, lean_object* v_i_150_, lean_object* v_acc_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l___private_Init_Data_String_Lossy_0__String_fromUTF8Lossy_go(v_b_149_, v_i_150_, v_acc_151_);
lean_dec_ref(v_b_149_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lossy_0__String_fromUTF8Lossy_go_match__1_splitter___redArg(lean_object* v_x_153_, lean_object* v_h__1_154_, lean_object* v_h__2_155_){
_start:
{
if (lean_obj_tag(v_x_153_) == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; 
lean_dec(v_h__1_154_);
v___x_156_ = lean_box(0);
v___x_157_ = lean_apply_1(v_h__2_155_, v___x_156_);
return v___x_157_;
}
else
{
lean_object* v_val_158_; lean_object* v___x_159_; 
lean_dec(v_h__2_155_);
v_val_158_ = lean_ctor_get(v_x_153_, 0);
lean_inc(v_val_158_);
lean_dec_ref_known(v_x_153_, 1);
v___x_159_ = lean_apply_1(v_h__1_154_, v_val_158_);
return v___x_159_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lossy_0__String_fromUTF8Lossy_go_match__1_splitter(lean_object* v_motive_160_, lean_object* v_x_161_, lean_object* v_h__1_162_, lean_object* v_h__2_163_){
_start:
{
if (lean_obj_tag(v_x_161_) == 0)
{
lean_object* v___x_164_; lean_object* v___x_165_; 
lean_dec(v_h__1_162_);
v___x_164_ = lean_box(0);
v___x_165_ = lean_apply_1(v_h__2_163_, v___x_164_);
return v___x_165_;
}
else
{
lean_object* v_val_166_; lean_object* v___x_167_; 
lean_dec(v_h__2_163_);
v_val_166_ = lean_ctor_get(v_x_161_, 0);
lean_inc(v_val_166_);
lean_dec_ref_known(v_x_161_, 1);
v___x_167_ = lean_apply_1(v_h__1_162_, v_val_166_);
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8Lossy(lean_object* v_b_169_){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = lean_unsigned_to_nat(0u);
v___x_171_ = ((lean_object*)(l_String_fromUTF8Lossy___closed__0));
v___x_172_ = l___private_Init_Data_String_Lossy_0__String_fromUTF8Lossy_go(v_b_169_, v___x_170_, v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8Lossy___boxed(lean_object* v_b_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_String_fromUTF8Lossy(v_b_173_);
lean_dec_ref(v_b_173_);
return v_res_174_;
}
}
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Decode(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Lossy(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Decode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Lossy(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Decode(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Lossy(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Decode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lossy(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Lossy(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Lossy(builtin);
}
#ifdef __cplusplus
}
#endif

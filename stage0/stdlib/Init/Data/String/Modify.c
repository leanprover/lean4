// Lean compiler output
// Module: Init.Data.String.Modify
// Imports: public import Init.Data.String.Termination import Init.Data.ByteArray.Lemmas import Init.Data.Char.Lemmas
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
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Char_toUpper___boxed(lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* l_Char_toLower___boxed(lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_Pos_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_toSetOfLE___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_toSetOfLE___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_toSetOfLE(lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_toSetOfLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_pastSet___redArg(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_Pos_pastSet___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_pastSet(lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_pastSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_appendRight___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_appendRight___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_appendRight(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_appendRight___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_modify___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_modify(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_toModifyOfLE___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_toModifyOfLE___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_toModifyOfLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_toModifyOfLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_pastModify___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_pastModify___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_pastModify(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_pastModify___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_Pos_Raw_set___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_set___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_modify(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_modify___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_modify(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_modify___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_map(lean_object*, lean_object*);
static const lean_closure_object l_String_toUpper___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Char_toUpper___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_toUpper___closed__0 = (const lean_object*)&l_String_toUpper___closed__0_value;
LEAN_EXPORT lean_object* l_String_toUpper(lean_object*);
static const lean_closure_object l_String_toLower___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Char_toLower___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_toLower___closed__0 = (const lean_object*)&l_String_toLower___closed__0_value;
LEAN_EXPORT lean_object* l_String_toLower(lean_object*);
LEAN_EXPORT lean_object* l_String_capitalize(lean_object*);
LEAN_EXPORT lean_object* lean_string_capitalize(lean_object*);
LEAN_EXPORT lean_object* l_String_decapitalize(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_set___boxed(lean_object* v_s_5_, lean_object* v_p_6_, lean_object* v_c_7_, lean_object* v_hp_8_){
_start:
{
uint32_t v_c_boxed_9_; lean_object* v_res_10_; 
v_c_boxed_9_ = lean_unbox_uint32(v_c_7_);
lean_dec(v_c_7_);
v_res_10_ = lean_string_utf8_set(v_s_5_, v_p_6_, v_c_boxed_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSetOfLE___redArg(lean_object* v_q_11_){
_start:
{
lean_inc(v_q_11_);
return v_q_11_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSetOfLE___redArg___boxed(lean_object* v_q_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_String_Pos_toSetOfLE___redArg(v_q_12_);
lean_dec(v_q_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSetOfLE(lean_object* v_s_14_, lean_object* v_q_15_, lean_object* v_p_16_, uint32_t v_c_17_, lean_object* v_hp_18_, lean_object* v_hpq_19_){
_start:
{
lean_inc(v_q_15_);
return v_q_15_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSetOfLE___boxed(lean_object* v_s_20_, lean_object* v_q_21_, lean_object* v_p_22_, lean_object* v_c_23_, lean_object* v_hp_24_, lean_object* v_hpq_25_){
_start:
{
uint32_t v_c_boxed_26_; lean_object* v_res_27_; 
v_c_boxed_26_ = lean_unbox_uint32(v_c_23_);
lean_dec(v_c_23_);
v_res_27_ = l_String_Pos_toSetOfLE(v_s_20_, v_q_21_, v_p_22_, v_c_boxed_26_, v_hp_24_, v_hpq_25_);
lean_dec(v_p_22_);
lean_dec(v_q_21_);
lean_dec_ref(v_s_20_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_pastSet___redArg(lean_object* v_p_28_, uint32_t v_c_29_){
_start:
{
uint32_t v___x_30_; uint8_t v___x_31_; 
v___x_30_ = 127;
v___x_31_ = lean_uint32_dec_le(v_c_29_, v___x_30_);
if (v___x_31_ == 0)
{
uint32_t v___x_32_; uint8_t v___x_33_; 
v___x_32_ = 2047;
v___x_33_ = lean_uint32_dec_le(v_c_29_, v___x_32_);
if (v___x_33_ == 0)
{
uint32_t v___x_34_; uint8_t v___x_35_; 
v___x_34_ = 65535;
v___x_35_ = lean_uint32_dec_le(v_c_29_, v___x_34_);
if (v___x_35_ == 0)
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_unsigned_to_nat(4u);
v___x_37_ = lean_nat_add(v_p_28_, v___x_36_);
return v___x_37_;
}
else
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = lean_unsigned_to_nat(3u);
v___x_39_ = lean_nat_add(v_p_28_, v___x_38_);
return v___x_39_;
}
}
else
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = lean_unsigned_to_nat(2u);
v___x_41_ = lean_nat_add(v_p_28_, v___x_40_);
return v___x_41_;
}
}
else
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_unsigned_to_nat(1u);
v___x_43_ = lean_nat_add(v_p_28_, v___x_42_);
return v___x_43_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_pastSet___redArg___boxed(lean_object* v_p_44_, lean_object* v_c_45_){
_start:
{
uint32_t v_c_boxed_46_; lean_object* v_res_47_; 
v_c_boxed_46_ = lean_unbox_uint32(v_c_45_);
lean_dec(v_c_45_);
v_res_47_ = l_String_Pos_pastSet___redArg(v_p_44_, v_c_boxed_46_);
lean_dec(v_p_44_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_pastSet(lean_object* v_s_48_, lean_object* v_p_49_, uint32_t v_c_50_, lean_object* v_hp_51_){
_start:
{
uint32_t v___x_52_; uint8_t v___x_53_; 
v___x_52_ = 127;
v___x_53_ = lean_uint32_dec_le(v_c_50_, v___x_52_);
if (v___x_53_ == 0)
{
uint32_t v___x_54_; uint8_t v___x_55_; 
v___x_54_ = 2047;
v___x_55_ = lean_uint32_dec_le(v_c_50_, v___x_54_);
if (v___x_55_ == 0)
{
uint32_t v___x_56_; uint8_t v___x_57_; 
v___x_56_ = 65535;
v___x_57_ = lean_uint32_dec_le(v_c_50_, v___x_56_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_unsigned_to_nat(4u);
v___x_59_ = lean_nat_add(v_p_49_, v___x_58_);
return v___x_59_;
}
else
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_unsigned_to_nat(3u);
v___x_61_ = lean_nat_add(v_p_49_, v___x_60_);
return v___x_61_;
}
}
else
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_unsigned_to_nat(2u);
v___x_63_ = lean_nat_add(v_p_49_, v___x_62_);
return v___x_63_;
}
}
else
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = lean_unsigned_to_nat(1u);
v___x_65_ = lean_nat_add(v_p_49_, v___x_64_);
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_pastSet___boxed(lean_object* v_s_66_, lean_object* v_p_67_, lean_object* v_c_68_, lean_object* v_hp_69_){
_start:
{
uint32_t v_c_boxed_70_; lean_object* v_res_71_; 
v_c_boxed_70_ = lean_unbox_uint32(v_c_68_);
lean_dec(v_c_68_);
v_res_71_ = l_String_Pos_pastSet(v_s_66_, v_p_67_, v_c_boxed_70_, v_hp_69_);
lean_dec(v_p_67_);
lean_dec_ref(v_s_66_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_appendRight___redArg(lean_object* v_p_72_){
_start:
{
lean_inc(v_p_72_);
return v_p_72_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_appendRight___redArg___boxed(lean_object* v_p_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_String_Pos_appendRight___redArg(v_p_73_);
lean_dec(v_p_73_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_appendRight(lean_object* v_s_75_, lean_object* v_p_76_, lean_object* v_t_77_){
_start:
{
lean_inc(v_p_76_);
return v_p_76_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_appendRight___boxed(lean_object* v_s_78_, lean_object* v_p_79_, lean_object* v_t_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_String_Pos_appendRight(v_s_78_, v_p_79_, v_t_80_);
lean_dec_ref(v_t_80_);
lean_dec(v_p_79_);
lean_dec_ref(v_s_78_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_modify___redArg(lean_object* v_s_82_, lean_object* v_p_83_, lean_object* v_f_84_){
_start:
{
uint32_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; uint32_t v___x_88_; lean_object* v___x_89_; 
v___x_85_ = lean_string_utf8_get_fast(v_s_82_, v_p_83_);
v___x_86_ = lean_box_uint32(v___x_85_);
v___x_87_ = lean_apply_1(v_f_84_, v___x_86_);
v___x_88_ = lean_unbox_uint32(v___x_87_);
lean_dec(v___x_87_);
v___x_89_ = lean_string_utf8_set(v_s_82_, v_p_83_, v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_modify(lean_object* v_s_90_, lean_object* v_p_91_, lean_object* v_f_92_, lean_object* v_hp_93_){
_start:
{
uint32_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; uint32_t v___x_97_; lean_object* v___x_98_; 
v___x_94_ = lean_string_utf8_get_fast(v_s_90_, v_p_91_);
v___x_95_ = lean_box_uint32(v___x_94_);
v___x_96_ = lean_apply_1(v_f_92_, v___x_95_);
v___x_97_ = lean_unbox_uint32(v___x_96_);
lean_dec(v___x_96_);
v___x_98_ = lean_string_utf8_set(v_s_90_, v_p_91_, v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toModifyOfLE___redArg(lean_object* v_q_99_){
_start:
{
lean_inc(v_q_99_);
return v_q_99_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toModifyOfLE___redArg___boxed(lean_object* v_q_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_String_Pos_toModifyOfLE___redArg(v_q_100_);
lean_dec(v_q_100_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toModifyOfLE(lean_object* v_s_102_, lean_object* v_q_103_, lean_object* v_p_104_, lean_object* v_f_105_, lean_object* v_hp_106_, lean_object* v_hpq_107_){
_start:
{
lean_inc(v_q_103_);
return v_q_103_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toModifyOfLE___boxed(lean_object* v_s_108_, lean_object* v_q_109_, lean_object* v_p_110_, lean_object* v_f_111_, lean_object* v_hp_112_, lean_object* v_hpq_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_String_Pos_toModifyOfLE(v_s_108_, v_q_109_, v_p_110_, v_f_111_, v_hp_112_, v_hpq_113_);
lean_dec_ref(v_f_111_);
lean_dec(v_p_110_);
lean_dec(v_q_109_);
lean_dec_ref(v_s_108_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_pastModify___redArg(lean_object* v_s_115_, lean_object* v_p_116_, lean_object* v_f_117_){
_start:
{
uint32_t v___x_118_; lean_object* v___x_119_; lean_object* v_v_120_; uint32_t v___x_121_; uint32_t v___x_122_; uint8_t v___x_123_; 
v___x_118_ = lean_string_utf8_get_fast(v_s_115_, v_p_116_);
v___x_119_ = lean_box_uint32(v___x_118_);
v_v_120_ = lean_apply_1(v_f_117_, v___x_119_);
v___x_121_ = 127;
v___x_122_ = lean_unbox_uint32(v_v_120_);
v___x_123_ = lean_uint32_dec_le(v___x_122_, v___x_121_);
if (v___x_123_ == 0)
{
uint32_t v___x_124_; uint32_t v___x_125_; uint8_t v___x_126_; 
v___x_124_ = 2047;
v___x_125_ = lean_unbox_uint32(v_v_120_);
v___x_126_ = lean_uint32_dec_le(v___x_125_, v___x_124_);
if (v___x_126_ == 0)
{
uint32_t v___x_127_; uint32_t v___x_128_; uint8_t v___x_129_; 
v___x_127_ = 65535;
v___x_128_ = lean_unbox_uint32(v_v_120_);
lean_dec(v_v_120_);
v___x_129_ = lean_uint32_dec_le(v___x_128_, v___x_127_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(4u);
v___x_131_ = lean_nat_add(v_p_116_, v___x_130_);
return v___x_131_;
}
else
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = lean_unsigned_to_nat(3u);
v___x_133_ = lean_nat_add(v_p_116_, v___x_132_);
return v___x_133_;
}
}
else
{
lean_object* v___x_134_; lean_object* v___x_135_; 
lean_dec(v_v_120_);
v___x_134_ = lean_unsigned_to_nat(2u);
v___x_135_ = lean_nat_add(v_p_116_, v___x_134_);
return v___x_135_;
}
}
else
{
lean_object* v___x_136_; lean_object* v___x_137_; 
lean_dec(v_v_120_);
v___x_136_ = lean_unsigned_to_nat(1u);
v___x_137_ = lean_nat_add(v_p_116_, v___x_136_);
return v___x_137_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_pastModify___redArg___boxed(lean_object* v_s_138_, lean_object* v_p_139_, lean_object* v_f_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_String_Pos_pastModify___redArg(v_s_138_, v_p_139_, v_f_140_);
lean_dec(v_p_139_);
lean_dec_ref(v_s_138_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_pastModify(lean_object* v_s_142_, lean_object* v_p_143_, lean_object* v_f_144_, lean_object* v_hp_145_){
_start:
{
uint32_t v___x_146_; lean_object* v___x_147_; lean_object* v_v_148_; uint32_t v___x_149_; uint32_t v___x_150_; uint8_t v___x_151_; 
v___x_146_ = lean_string_utf8_get_fast(v_s_142_, v_p_143_);
v___x_147_ = lean_box_uint32(v___x_146_);
v_v_148_ = lean_apply_1(v_f_144_, v___x_147_);
v___x_149_ = 127;
v___x_150_ = lean_unbox_uint32(v_v_148_);
v___x_151_ = lean_uint32_dec_le(v___x_150_, v___x_149_);
if (v___x_151_ == 0)
{
uint32_t v___x_152_; uint32_t v___x_153_; uint8_t v___x_154_; 
v___x_152_ = 2047;
v___x_153_ = lean_unbox_uint32(v_v_148_);
v___x_154_ = lean_uint32_dec_le(v___x_153_, v___x_152_);
if (v___x_154_ == 0)
{
uint32_t v___x_155_; uint32_t v___x_156_; uint8_t v___x_157_; 
v___x_155_ = 65535;
v___x_156_ = lean_unbox_uint32(v_v_148_);
lean_dec(v_v_148_);
v___x_157_ = lean_uint32_dec_le(v___x_156_, v___x_155_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = lean_unsigned_to_nat(4u);
v___x_159_ = lean_nat_add(v_p_143_, v___x_158_);
return v___x_159_;
}
else
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = lean_unsigned_to_nat(3u);
v___x_161_ = lean_nat_add(v_p_143_, v___x_160_);
return v___x_161_;
}
}
else
{
lean_object* v___x_162_; lean_object* v___x_163_; 
lean_dec(v_v_148_);
v___x_162_ = lean_unsigned_to_nat(2u);
v___x_163_ = lean_nat_add(v_p_143_, v___x_162_);
return v___x_163_;
}
}
else
{
lean_object* v___x_164_; lean_object* v___x_165_; 
lean_dec(v_v_148_);
v___x_164_ = lean_unsigned_to_nat(1u);
v___x_165_ = lean_nat_add(v_p_143_, v___x_164_);
return v___x_165_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_pastModify___boxed(lean_object* v_s_166_, lean_object* v_p_167_, lean_object* v_f_168_, lean_object* v_hp_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_String_Pos_pastModify(v_s_166_, v_p_167_, v_f_168_, v_hp_169_);
lean_dec(v_p_167_);
lean_dec_ref(v_s_166_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_set___boxed(lean_object* v_a_00___x40___internal___hyg_174_, lean_object* v_a_00___x40___internal___hyg_175_, lean_object* v_a_00___x40___internal___hyg_176_){
_start:
{
uint32_t v_a_00___x40___internal___hyg_3__boxed_177_; lean_object* v_res_178_; 
v_a_00___x40___internal___hyg_3__boxed_177_ = lean_unbox_uint32(v_a_00___x40___internal___hyg_176_);
lean_dec(v_a_00___x40___internal___hyg_176_);
v_res_178_ = lean_string_utf8_set(v_a_00___x40___internal___hyg_174_, v_a_00___x40___internal___hyg_175_, v_a_00___x40___internal___hyg_3__boxed_177_);
lean_dec(v_a_00___x40___internal___hyg_175_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_String_set___boxed(lean_object* v_a_00___x40___internal___hyg_182_, lean_object* v_a_00___x40___internal___hyg_183_, lean_object* v_a_00___x40___internal___hyg_184_){
_start:
{
uint32_t v_a_00___x40___internal___hyg_3__boxed_185_; lean_object* v_res_186_; 
v_a_00___x40___internal___hyg_3__boxed_185_ = lean_unbox_uint32(v_a_00___x40___internal___hyg_184_);
lean_dec(v_a_00___x40___internal___hyg_184_);
v_res_186_ = lean_string_utf8_set(v_a_00___x40___internal___hyg_182_, v_a_00___x40___internal___hyg_183_, v_a_00___x40___internal___hyg_3__boxed_185_);
lean_dec(v_a_00___x40___internal___hyg_183_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_modify(lean_object* v_s_187_, lean_object* v_i_188_, lean_object* v_f_189_){
_start:
{
uint32_t v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; uint32_t v___x_193_; lean_object* v___x_194_; 
v___x_190_ = lean_string_utf8_get(v_s_187_, v_i_188_);
v___x_191_ = lean_box_uint32(v___x_190_);
v___x_192_ = lean_apply_1(v_f_189_, v___x_191_);
v___x_193_ = lean_unbox_uint32(v___x_192_);
lean_dec(v___x_192_);
v___x_194_ = lean_string_utf8_set(v_s_187_, v_i_188_, v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_modify___boxed(lean_object* v_s_195_, lean_object* v_i_196_, lean_object* v_f_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_String_Pos_Raw_modify(v_s_195_, v_i_196_, v_f_197_);
lean_dec(v_i_196_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_String_modify(lean_object* v_s_199_, lean_object* v_i_200_, lean_object* v_f_201_){
_start:
{
uint32_t v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; uint32_t v___x_205_; lean_object* v___x_206_; 
v___x_202_ = lean_string_utf8_get(v_s_199_, v_i_200_);
v___x_203_ = lean_box_uint32(v___x_202_);
v___x_204_ = lean_apply_1(v_f_201_, v___x_203_);
v___x_205_ = lean_unbox_uint32(v___x_204_);
lean_dec(v___x_204_);
v___x_206_ = lean_string_utf8_set(v_s_199_, v_i_200_, v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_String_modify___boxed(lean_object* v_s_207_, lean_object* v_i_208_, lean_object* v_f_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_String_modify(v_s_207_, v_i_208_, v_f_209_);
lean_dec(v_i_208_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux(lean_object* v_f_211_, lean_object* v_s_212_, lean_object* v_p_213_){
_start:
{
lean_object* v___x_214_; uint8_t v_decide_215_; 
v___x_214_ = lean_string_utf8_byte_size(v_s_212_);
v_decide_215_ = lean_nat_dec_eq(v_p_213_, v___x_214_);
if (v_decide_215_ == 0)
{
uint32_t v___x_216_; lean_object* v___x_217_; lean_object* v_v_218_; uint32_t v___x_219_; lean_object* v___x_220_; lean_object* v___y_222_; uint32_t v___x_225_; uint32_t v___x_226_; uint8_t v___x_227_; 
v___x_216_ = lean_string_utf8_get_fast(v_s_212_, v_p_213_);
v___x_217_ = lean_box_uint32(v___x_216_);
lean_inc_ref(v_f_211_);
v_v_218_ = lean_apply_1(v_f_211_, v___x_217_);
v___x_219_ = lean_unbox_uint32(v_v_218_);
lean_inc(v_p_213_);
v___x_220_ = lean_string_utf8_set(v_s_212_, v_p_213_, v___x_219_);
v___x_225_ = 127;
v___x_226_ = lean_unbox_uint32(v_v_218_);
v___x_227_ = lean_uint32_dec_le(v___x_226_, v___x_225_);
if (v___x_227_ == 0)
{
uint32_t v___x_228_; uint32_t v___x_229_; uint8_t v___x_230_; 
v___x_228_ = 2047;
v___x_229_ = lean_unbox_uint32(v_v_218_);
v___x_230_ = lean_uint32_dec_le(v___x_229_, v___x_228_);
if (v___x_230_ == 0)
{
uint32_t v___x_231_; uint32_t v___x_232_; uint8_t v___x_233_; 
v___x_231_ = 65535;
v___x_232_ = lean_unbox_uint32(v_v_218_);
lean_dec(v_v_218_);
v___x_233_ = lean_uint32_dec_le(v___x_232_, v___x_231_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; 
v___x_234_ = lean_unsigned_to_nat(4u);
v___y_222_ = v___x_234_;
goto v___jp_221_;
}
else
{
lean_object* v___x_235_; 
v___x_235_ = lean_unsigned_to_nat(3u);
v___y_222_ = v___x_235_;
goto v___jp_221_;
}
}
else
{
lean_object* v___x_236_; 
lean_dec(v_v_218_);
v___x_236_ = lean_unsigned_to_nat(2u);
v___y_222_ = v___x_236_;
goto v___jp_221_;
}
}
else
{
lean_object* v___x_237_; 
lean_dec(v_v_218_);
v___x_237_ = lean_unsigned_to_nat(1u);
v___y_222_ = v___x_237_;
goto v___jp_221_;
}
v___jp_221_:
{
lean_object* v___x_223_; 
v___x_223_ = lean_nat_add(v_p_213_, v___y_222_);
lean_dec(v_p_213_);
v_s_212_ = v___x_220_;
v_p_213_ = v___x_223_;
goto _start;
}
}
else
{
lean_dec(v_p_213_);
lean_dec_ref(v_f_211_);
return v_s_212_;
}
}
}
LEAN_EXPORT lean_object* l_String_map(lean_object* v_f_238_, lean_object* v_s_239_){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = l_String_mapAux(v_f_238_, v_s_239_, v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_String_toUpper(lean_object* v_s_243_){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = ((lean_object*)(l_String_toUpper___closed__0));
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = l_String_mapAux(v___x_244_, v_s_243_, v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_String_toLower(lean_object* v_s_248_){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_249_ = ((lean_object*)(l_String_toLower___closed__0));
v___x_250_ = lean_unsigned_to_nat(0u);
v___x_251_ = l_String_mapAux(v___x_249_, v_s_248_, v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_String_capitalize(lean_object* v_s_252_){
_start:
{
lean_object* v___x_253_; uint32_t v___x_254_; uint32_t v___x_255_; uint8_t v___x_256_; 
v___x_253_ = lean_unsigned_to_nat(0u);
v___x_254_ = lean_string_utf8_get(v_s_252_, v___x_253_);
v___x_255_ = 97;
v___x_256_ = lean_uint32_dec_le(v___x_255_, v___x_254_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; 
v___x_257_ = lean_string_utf8_set(v_s_252_, v___x_253_, v___x_254_);
return v___x_257_;
}
else
{
uint32_t v___x_258_; uint8_t v___x_259_; 
v___x_258_ = 122;
v___x_259_ = lean_uint32_dec_le(v___x_254_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; 
v___x_260_ = lean_string_utf8_set(v_s_252_, v___x_253_, v___x_254_);
return v___x_260_;
}
else
{
uint32_t v___x_261_; uint32_t v___x_262_; lean_object* v___x_263_; 
v___x_261_ = 4294967264;
v___x_262_ = lean_uint32_add(v___x_254_, v___x_261_);
v___x_263_ = lean_string_utf8_set(v_s_252_, v___x_253_, v___x_262_);
return v___x_263_;
}
}
}
}
LEAN_EXPORT lean_object* lean_string_capitalize(lean_object* v_s_264_){
_start:
{
lean_object* v___x_265_; uint32_t v___x_266_; uint32_t v___x_267_; uint8_t v___x_268_; 
v___x_265_ = lean_unsigned_to_nat(0u);
v___x_266_ = lean_string_utf8_get(v_s_264_, v___x_265_);
v___x_267_ = 97;
v___x_268_ = lean_uint32_dec_le(v___x_267_, v___x_266_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
v___x_269_ = lean_string_utf8_set(v_s_264_, v___x_265_, v___x_266_);
return v___x_269_;
}
else
{
uint32_t v___x_270_; uint8_t v___x_271_; 
v___x_270_ = 122;
v___x_271_ = lean_uint32_dec_le(v___x_266_, v___x_270_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; 
v___x_272_ = lean_string_utf8_set(v_s_264_, v___x_265_, v___x_266_);
return v___x_272_;
}
else
{
uint32_t v___x_273_; uint32_t v___x_274_; lean_object* v___x_275_; 
v___x_273_ = 4294967264;
v___x_274_ = lean_uint32_add(v___x_266_, v___x_273_);
v___x_275_ = lean_string_utf8_set(v_s_264_, v___x_265_, v___x_274_);
return v___x_275_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_decapitalize(lean_object* v_s_276_){
_start:
{
lean_object* v___x_277_; uint32_t v___x_278_; uint32_t v___x_279_; uint8_t v___x_280_; 
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = lean_string_utf8_get(v_s_276_, v___x_277_);
v___x_279_ = 65;
v___x_280_ = lean_uint32_dec_le(v___x_279_, v___x_278_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; 
v___x_281_ = lean_string_utf8_set(v_s_276_, v___x_277_, v___x_278_);
return v___x_281_;
}
else
{
uint32_t v___x_282_; uint8_t v___x_283_; 
v___x_282_ = 90;
v___x_283_ = lean_uint32_dec_le(v___x_278_, v___x_282_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; 
v___x_284_ = lean_string_utf8_set(v_s_276_, v___x_277_, v___x_278_);
return v___x_284_;
}
else
{
uint32_t v___x_285_; uint32_t v___x_286_; lean_object* v___x_287_; 
v___x_285_ = 32;
v___x_286_ = lean_uint32_add(v___x_278_, v___x_285_);
v___x_287_ = lean_string_utf8_set(v_s_276_, v___x_277_, v___x_286_);
return v___x_287_;
}
}
}
}
lean_object* runtime_initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ByteArray_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Char_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Modify(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Modify(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Modify(builtin);
}
#ifdef __cplusplus
}
#endif

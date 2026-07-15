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
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Char_toUpper___boxed(lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
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
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = l_Char_utf8Size(v_c_29_);
v___x_31_ = lean_nat_add(v_p_28_, v___x_30_);
lean_dec(v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_pastSet___redArg___boxed(lean_object* v_p_32_, lean_object* v_c_33_){
_start:
{
uint32_t v_c_boxed_34_; lean_object* v_res_35_; 
v_c_boxed_34_ = lean_unbox_uint32(v_c_33_);
lean_dec(v_c_33_);
v_res_35_ = l_String_Pos_pastSet___redArg(v_p_32_, v_c_boxed_34_);
lean_dec(v_p_32_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_pastSet(lean_object* v_s_36_, lean_object* v_p_37_, uint32_t v_c_38_, lean_object* v_hp_39_){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = l_Char_utf8Size(v_c_38_);
v___x_41_ = lean_nat_add(v_p_37_, v___x_40_);
lean_dec(v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_pastSet___boxed(lean_object* v_s_42_, lean_object* v_p_43_, lean_object* v_c_44_, lean_object* v_hp_45_){
_start:
{
uint32_t v_c_boxed_46_; lean_object* v_res_47_; 
v_c_boxed_46_ = lean_unbox_uint32(v_c_44_);
lean_dec(v_c_44_);
v_res_47_ = l_String_Pos_pastSet(v_s_42_, v_p_43_, v_c_boxed_46_, v_hp_45_);
lean_dec(v_p_43_);
lean_dec_ref(v_s_42_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_appendRight___redArg(lean_object* v_p_48_){
_start:
{
lean_inc(v_p_48_);
return v_p_48_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_appendRight___redArg___boxed(lean_object* v_p_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_String_Pos_appendRight___redArg(v_p_49_);
lean_dec(v_p_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_appendRight(lean_object* v_s_51_, lean_object* v_p_52_, lean_object* v_t_53_){
_start:
{
lean_inc(v_p_52_);
return v_p_52_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_appendRight___boxed(lean_object* v_s_54_, lean_object* v_p_55_, lean_object* v_t_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_String_Pos_appendRight(v_s_54_, v_p_55_, v_t_56_);
lean_dec_ref(v_t_56_);
lean_dec(v_p_55_);
lean_dec_ref(v_s_54_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_modify___redArg(lean_object* v_s_58_, lean_object* v_p_59_, lean_object* v_f_60_){
_start:
{
uint32_t v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; uint32_t v___x_64_; lean_object* v___x_65_; 
v___x_61_ = lean_string_utf8_get_fast(v_s_58_, v_p_59_);
v___x_62_ = lean_box_uint32(v___x_61_);
v___x_63_ = lean_apply_1(v_f_60_, v___x_62_);
v___x_64_ = lean_unbox_uint32(v___x_63_);
lean_dec(v___x_63_);
v___x_65_ = lean_string_utf8_set(v_s_58_, v_p_59_, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_modify(lean_object* v_s_66_, lean_object* v_p_67_, lean_object* v_f_68_, lean_object* v_hp_69_){
_start:
{
uint32_t v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; uint32_t v___x_73_; lean_object* v___x_74_; 
v___x_70_ = lean_string_utf8_get_fast(v_s_66_, v_p_67_);
v___x_71_ = lean_box_uint32(v___x_70_);
v___x_72_ = lean_apply_1(v_f_68_, v___x_71_);
v___x_73_ = lean_unbox_uint32(v___x_72_);
lean_dec(v___x_72_);
v___x_74_ = lean_string_utf8_set(v_s_66_, v_p_67_, v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toModifyOfLE___redArg(lean_object* v_q_75_){
_start:
{
lean_inc(v_q_75_);
return v_q_75_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toModifyOfLE___redArg___boxed(lean_object* v_q_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_String_Pos_toModifyOfLE___redArg(v_q_76_);
lean_dec(v_q_76_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toModifyOfLE(lean_object* v_s_78_, lean_object* v_q_79_, lean_object* v_p_80_, lean_object* v_f_81_, lean_object* v_hp_82_, lean_object* v_hpq_83_){
_start:
{
lean_inc(v_q_79_);
return v_q_79_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toModifyOfLE___boxed(lean_object* v_s_84_, lean_object* v_q_85_, lean_object* v_p_86_, lean_object* v_f_87_, lean_object* v_hp_88_, lean_object* v_hpq_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_String_Pos_toModifyOfLE(v_s_84_, v_q_85_, v_p_86_, v_f_87_, v_hp_88_, v_hpq_89_);
lean_dec_ref(v_f_87_);
lean_dec(v_p_86_);
lean_dec(v_q_85_);
lean_dec_ref(v_s_84_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_pastModify___redArg(lean_object* v_s_91_, lean_object* v_p_92_, lean_object* v_f_93_){
_start:
{
uint32_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; uint32_t v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_94_ = lean_string_utf8_get_fast(v_s_91_, v_p_92_);
v___x_95_ = lean_box_uint32(v___x_94_);
v___x_96_ = lean_apply_1(v_f_93_, v___x_95_);
v___x_97_ = lean_unbox_uint32(v___x_96_);
lean_dec(v___x_96_);
v___x_98_ = l_Char_utf8Size(v___x_97_);
v___x_99_ = lean_nat_add(v_p_92_, v___x_98_);
lean_dec(v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_pastModify___redArg___boxed(lean_object* v_s_100_, lean_object* v_p_101_, lean_object* v_f_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_String_Pos_pastModify___redArg(v_s_100_, v_p_101_, v_f_102_);
lean_dec(v_p_101_);
lean_dec_ref(v_s_100_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_pastModify(lean_object* v_s_104_, lean_object* v_p_105_, lean_object* v_f_106_, lean_object* v_hp_107_){
_start:
{
uint32_t v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; uint32_t v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_108_ = lean_string_utf8_get_fast(v_s_104_, v_p_105_);
v___x_109_ = lean_box_uint32(v___x_108_);
v___x_110_ = lean_apply_1(v_f_106_, v___x_109_);
v___x_111_ = lean_unbox_uint32(v___x_110_);
lean_dec(v___x_110_);
v___x_112_ = l_Char_utf8Size(v___x_111_);
v___x_113_ = lean_nat_add(v_p_105_, v___x_112_);
lean_dec(v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_pastModify___boxed(lean_object* v_s_114_, lean_object* v_p_115_, lean_object* v_f_116_, lean_object* v_hp_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_String_Pos_pastModify(v_s_114_, v_p_115_, v_f_116_, v_hp_117_);
lean_dec(v_p_115_);
lean_dec_ref(v_s_114_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_set___boxed(lean_object* v_a_00___x40___internal___hyg_122_, lean_object* v_a_00___x40___internal___hyg_123_, lean_object* v_a_00___x40___internal___hyg_124_){
_start:
{
uint32_t v_a_00___x40___internal___hyg_3__boxed_125_; lean_object* v_res_126_; 
v_a_00___x40___internal___hyg_3__boxed_125_ = lean_unbox_uint32(v_a_00___x40___internal___hyg_124_);
lean_dec(v_a_00___x40___internal___hyg_124_);
v_res_126_ = lean_string_utf8_set(v_a_00___x40___internal___hyg_122_, v_a_00___x40___internal___hyg_123_, v_a_00___x40___internal___hyg_3__boxed_125_);
lean_dec(v_a_00___x40___internal___hyg_123_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_String_set___boxed(lean_object* v_a_00___x40___internal___hyg_130_, lean_object* v_a_00___x40___internal___hyg_131_, lean_object* v_a_00___x40___internal___hyg_132_){
_start:
{
uint32_t v_a_00___x40___internal___hyg_3__boxed_133_; lean_object* v_res_134_; 
v_a_00___x40___internal___hyg_3__boxed_133_ = lean_unbox_uint32(v_a_00___x40___internal___hyg_132_);
lean_dec(v_a_00___x40___internal___hyg_132_);
v_res_134_ = lean_string_utf8_set(v_a_00___x40___internal___hyg_130_, v_a_00___x40___internal___hyg_131_, v_a_00___x40___internal___hyg_3__boxed_133_);
lean_dec(v_a_00___x40___internal___hyg_131_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_modify(lean_object* v_s_135_, lean_object* v_i_136_, lean_object* v_f_137_){
_start:
{
uint32_t v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; uint32_t v___x_141_; lean_object* v___x_142_; 
v___x_138_ = lean_string_utf8_get(v_s_135_, v_i_136_);
v___x_139_ = lean_box_uint32(v___x_138_);
v___x_140_ = lean_apply_1(v_f_137_, v___x_139_);
v___x_141_ = lean_unbox_uint32(v___x_140_);
lean_dec(v___x_140_);
v___x_142_ = lean_string_utf8_set(v_s_135_, v_i_136_, v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_modify___boxed(lean_object* v_s_143_, lean_object* v_i_144_, lean_object* v_f_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_String_Pos_Raw_modify(v_s_143_, v_i_144_, v_f_145_);
lean_dec(v_i_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_String_modify(lean_object* v_s_147_, lean_object* v_i_148_, lean_object* v_f_149_){
_start:
{
uint32_t v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; uint32_t v___x_153_; lean_object* v___x_154_; 
v___x_150_ = lean_string_utf8_get(v_s_147_, v_i_148_);
v___x_151_ = lean_box_uint32(v___x_150_);
v___x_152_ = lean_apply_1(v_f_149_, v___x_151_);
v___x_153_ = lean_unbox_uint32(v___x_152_);
lean_dec(v___x_152_);
v___x_154_ = lean_string_utf8_set(v_s_147_, v_i_148_, v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_String_modify___boxed(lean_object* v_s_155_, lean_object* v_i_156_, lean_object* v_f_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_String_modify(v_s_155_, v_i_156_, v_f_157_);
lean_dec(v_i_156_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux(lean_object* v_f_159_, lean_object* v_s_160_, lean_object* v_p_161_){
_start:
{
lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_162_ = lean_string_utf8_byte_size(v_s_160_);
v___x_163_ = lean_nat_dec_eq(v_p_161_, v___x_162_);
if (v___x_163_ == 0)
{
uint32_t v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; uint32_t v___x_167_; lean_object* v___x_168_; uint32_t v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_164_ = lean_string_utf8_get_fast(v_s_160_, v_p_161_);
v___x_165_ = lean_box_uint32(v___x_164_);
lean_inc_ref(v_f_159_);
v___x_166_ = lean_apply_1(v_f_159_, v___x_165_);
v___x_167_ = lean_unbox_uint32(v___x_166_);
lean_inc(v_p_161_);
v___x_168_ = lean_string_utf8_set(v_s_160_, v_p_161_, v___x_167_);
v___x_169_ = lean_unbox_uint32(v___x_166_);
lean_dec(v___x_166_);
v___x_170_ = l_Char_utf8Size(v___x_169_);
v___x_171_ = lean_nat_add(v_p_161_, v___x_170_);
lean_dec(v___x_170_);
lean_dec(v_p_161_);
v_s_160_ = v___x_168_;
v_p_161_ = v___x_171_;
goto _start;
}
else
{
lean_dec(v_p_161_);
lean_dec_ref(v_f_159_);
return v_s_160_;
}
}
}
LEAN_EXPORT lean_object* l_String_map(lean_object* v_f_173_, lean_object* v_s_174_){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = lean_unsigned_to_nat(0u);
v___x_176_ = l_String_mapAux(v_f_173_, v_s_174_, v___x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_String_toUpper(lean_object* v_s_178_){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = ((lean_object*)(l_String_toUpper___closed__0));
v___x_180_ = lean_unsigned_to_nat(0u);
v___x_181_ = l_String_mapAux(v___x_179_, v_s_178_, v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_String_toLower(lean_object* v_s_183_){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_184_ = ((lean_object*)(l_String_toLower___closed__0));
v___x_185_ = lean_unsigned_to_nat(0u);
v___x_186_ = l_String_mapAux(v___x_184_, v_s_183_, v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_String_capitalize(lean_object* v_s_187_){
_start:
{
lean_object* v___x_188_; uint32_t v___x_189_; uint32_t v___x_190_; uint8_t v___x_191_; 
v___x_188_ = lean_unsigned_to_nat(0u);
v___x_189_ = lean_string_utf8_get(v_s_187_, v___x_188_);
v___x_190_ = 97;
v___x_191_ = lean_uint32_dec_le(v___x_190_, v___x_189_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; 
v___x_192_ = lean_string_utf8_set(v_s_187_, v___x_188_, v___x_189_);
return v___x_192_;
}
else
{
uint32_t v___x_193_; uint8_t v___x_194_; 
v___x_193_ = 122;
v___x_194_ = lean_uint32_dec_le(v___x_189_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; 
v___x_195_ = lean_string_utf8_set(v_s_187_, v___x_188_, v___x_189_);
return v___x_195_;
}
else
{
uint32_t v___x_196_; uint32_t v___x_197_; lean_object* v___x_198_; 
v___x_196_ = 4294967264;
v___x_197_ = lean_uint32_add(v___x_189_, v___x_196_);
v___x_198_ = lean_string_utf8_set(v_s_187_, v___x_188_, v___x_197_);
return v___x_198_;
}
}
}
}
LEAN_EXPORT lean_object* lean_string_capitalize(lean_object* v_s_199_){
_start:
{
lean_object* v___x_200_; uint32_t v___x_201_; uint32_t v___x_202_; uint8_t v___x_203_; 
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = lean_string_utf8_get(v_s_199_, v___x_200_);
v___x_202_ = 97;
v___x_203_ = lean_uint32_dec_le(v___x_202_, v___x_201_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; 
v___x_204_ = lean_string_utf8_set(v_s_199_, v___x_200_, v___x_201_);
return v___x_204_;
}
else
{
uint32_t v___x_205_; uint8_t v___x_206_; 
v___x_205_ = 122;
v___x_206_ = lean_uint32_dec_le(v___x_201_, v___x_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; 
v___x_207_ = lean_string_utf8_set(v_s_199_, v___x_200_, v___x_201_);
return v___x_207_;
}
else
{
uint32_t v___x_208_; uint32_t v___x_209_; lean_object* v___x_210_; 
v___x_208_ = 4294967264;
v___x_209_ = lean_uint32_add(v___x_201_, v___x_208_);
v___x_210_ = lean_string_utf8_set(v_s_199_, v___x_200_, v___x_209_);
return v___x_210_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_decapitalize(lean_object* v_s_211_){
_start:
{
lean_object* v___x_212_; uint32_t v___x_213_; uint32_t v___x_214_; uint8_t v___x_215_; 
v___x_212_ = lean_unsigned_to_nat(0u);
v___x_213_ = lean_string_utf8_get(v_s_211_, v___x_212_);
v___x_214_ = 65;
v___x_215_ = lean_uint32_dec_le(v___x_214_, v___x_213_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; 
v___x_216_ = lean_string_utf8_set(v_s_211_, v___x_212_, v___x_213_);
return v___x_216_;
}
else
{
uint32_t v___x_217_; uint8_t v___x_218_; 
v___x_217_ = 90;
v___x_218_ = lean_uint32_dec_le(v___x_213_, v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; 
v___x_219_ = lean_string_utf8_set(v_s_211_, v___x_212_, v___x_213_);
return v___x_219_;
}
else
{
uint32_t v___x_220_; uint32_t v___x_221_; lean_object* v___x_222_; 
v___x_220_ = 32;
v___x_221_ = lean_uint32_add(v___x_213_, v___x_220_);
v___x_222_ = lean_string_utf8_set(v_s_211_, v___x_212_, v___x_221_);
return v___x_222_;
}
}
}
}
lean_object* runtime_initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

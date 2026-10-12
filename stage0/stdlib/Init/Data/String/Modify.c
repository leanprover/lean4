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
LEAN_EXPORT void l_String_Pos_set_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1_ = stack[0].m_obj;
lean_object* v_p_2_ = stack[1].m_obj;
uint32_t v_c_3_ = stack[2].m_num;
lean_object* v_res_5_;
v_res_5_ = lean_string_utf8_set(v_s_1_, v_p_2_, v_c_3_);
stack->m_obj
 = v_res_5_;
}
LEAN_EXPORT lean_object* l_String_Pos_set___boxed(lean_object* v_s_6_, lean_object* v_p_7_, lean_object* v_c_8_, lean_object* v_hp_9_){
_start:
{
uint32_t v_c_boxed_10_; lean_object* v_res_11_; 
v_c_boxed_10_ = lean_unbox_uint32(v_c_8_);
lean_dec(v_c_8_);
v_res_11_ = lean_string_utf8_set(v_s_6_, v_p_7_, v_c_boxed_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSetOfLE___redArg(lean_object* v_q_12_){
_start:
{
lean_inc(v_q_12_);
return v_q_12_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSetOfLE___redArg___boxed(lean_object* v_q_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_String_Pos_toSetOfLE___redArg(v_q_13_);
lean_dec(v_q_13_);
return v_res_14_;
}
}
lean_object* l_String_Pos_toSetOfLE(lean_object* v_s_15_, lean_object* v_q_16_, lean_object* v_p_17_, uint32_t v_c_18_, lean_object* v_hp_19_, lean_object* v_hpq_20_){
_start:
{
lean_inc(v_q_16_);
return v_q_16_;
}
}
LEAN_EXPORT void l_String_Pos_toSetOfLE_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_15_ = stack[0].m_obj;
lean_object* v_q_16_ = stack[1].m_obj;
lean_object* v_p_17_ = stack[2].m_obj;
uint32_t v_c_18_ = stack[3].m_num;
lean_object* v_res_21_;
v_res_21_ = l_String_Pos_toSetOfLE(v_s_15_, v_q_16_, v_p_17_, v_c_18_, lean_box(0), lean_box(0));
stack->m_obj
 = v_res_21_;
}
LEAN_EXPORT lean_object* l_String_Pos_toSetOfLE___boxed(lean_object* v_s_22_, lean_object* v_q_23_, lean_object* v_p_24_, lean_object* v_c_25_, lean_object* v_hp_26_, lean_object* v_hpq_27_){
_start:
{
uint32_t v_c_boxed_28_; lean_object* v_res_29_; 
v_c_boxed_28_ = lean_unbox_uint32(v_c_25_);
lean_dec(v_c_25_);
v_res_29_ = l_String_Pos_toSetOfLE(v_s_22_, v_q_23_, v_p_24_, v_c_boxed_28_, v_hp_26_, v_hpq_27_);
lean_dec(v_p_24_);
lean_dec(v_q_23_);
lean_dec_ref(v_s_22_);
return v_res_29_;
}
}
lean_object* l_String_Pos_pastSet___redArg(lean_object* v_p_30_, uint32_t v_c_31_){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = l_Char_utf8Size(v_c_31_);
v___x_33_ = lean_nat_add(v_p_30_, v___x_32_);
lean_dec(v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT void l_String_Pos_pastSet___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_30_ = stack[0].m_obj;
uint32_t v_c_31_ = stack[1].m_num;
lean_object* v_res_34_;
v_res_34_ = l_String_Pos_pastSet___redArg(v_p_30_, v_c_31_);
stack->m_obj
 = v_res_34_;
}
LEAN_EXPORT lean_object* l_String_Pos_pastSet___redArg___boxed(lean_object* v_p_35_, lean_object* v_c_36_){
_start:
{
uint32_t v_c_boxed_37_; lean_object* v_res_38_; 
v_c_boxed_37_ = lean_unbox_uint32(v_c_36_);
lean_dec(v_c_36_);
v_res_38_ = l_String_Pos_pastSet___redArg(v_p_35_, v_c_boxed_37_);
lean_dec(v_p_35_);
return v_res_38_;
}
}
lean_object* l_String_Pos_pastSet(lean_object* v_s_39_, lean_object* v_p_40_, uint32_t v_c_41_, lean_object* v_hp_42_){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = l_Char_utf8Size(v_c_41_);
v___x_44_ = lean_nat_add(v_p_40_, v___x_43_);
lean_dec(v___x_43_);
return v___x_44_;
}
}
LEAN_EXPORT void l_String_Pos_pastSet_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_39_ = stack[0].m_obj;
lean_object* v_p_40_ = stack[1].m_obj;
uint32_t v_c_41_ = stack[2].m_num;
lean_object* v_res_45_;
v_res_45_ = l_String_Pos_pastSet(v_s_39_, v_p_40_, v_c_41_, lean_box(0));
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_String_Pos_pastSet___boxed(lean_object* v_s_46_, lean_object* v_p_47_, lean_object* v_c_48_, lean_object* v_hp_49_){
_start:
{
uint32_t v_c_boxed_50_; lean_object* v_res_51_; 
v_c_boxed_50_ = lean_unbox_uint32(v_c_48_);
lean_dec(v_c_48_);
v_res_51_ = l_String_Pos_pastSet(v_s_46_, v_p_47_, v_c_boxed_50_, v_hp_49_);
lean_dec(v_p_47_);
lean_dec_ref(v_s_46_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_appendRight___redArg(lean_object* v_p_52_){
_start:
{
lean_inc(v_p_52_);
return v_p_52_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_appendRight___redArg___boxed(lean_object* v_p_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_String_Pos_appendRight___redArg(v_p_53_);
lean_dec(v_p_53_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_appendRight(lean_object* v_s_55_, lean_object* v_p_56_, lean_object* v_t_57_){
_start:
{
lean_inc(v_p_56_);
return v_p_56_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_appendRight___boxed(lean_object* v_s_58_, lean_object* v_p_59_, lean_object* v_t_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_String_Pos_appendRight(v_s_58_, v_p_59_, v_t_60_);
lean_dec_ref(v_t_60_);
lean_dec(v_p_59_);
lean_dec_ref(v_s_58_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_modify___redArg(lean_object* v_s_62_, lean_object* v_p_63_, lean_object* v_f_64_){
_start:
{
uint32_t v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; uint32_t v___x_68_; lean_object* v___x_69_; 
v___x_65_ = lean_string_utf8_get_fast(v_s_62_, v_p_63_);
v___x_66_ = lean_box_uint32(v___x_65_);
v___x_67_ = lean_apply_1(v_f_64_, v___x_66_);
v___x_68_ = lean_unbox_uint32(v___x_67_);
lean_dec(v___x_67_);
v___x_69_ = lean_string_utf8_set(v_s_62_, v_p_63_, v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_modify(lean_object* v_s_70_, lean_object* v_p_71_, lean_object* v_f_72_, lean_object* v_hp_73_){
_start:
{
uint32_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; uint32_t v___x_77_; lean_object* v___x_78_; 
v___x_74_ = lean_string_utf8_get_fast(v_s_70_, v_p_71_);
v___x_75_ = lean_box_uint32(v___x_74_);
v___x_76_ = lean_apply_1(v_f_72_, v___x_75_);
v___x_77_ = lean_unbox_uint32(v___x_76_);
lean_dec(v___x_76_);
v___x_78_ = lean_string_utf8_set(v_s_70_, v_p_71_, v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toModifyOfLE___redArg(lean_object* v_q_79_){
_start:
{
lean_inc(v_q_79_);
return v_q_79_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toModifyOfLE___redArg___boxed(lean_object* v_q_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_String_Pos_toModifyOfLE___redArg(v_q_80_);
lean_dec(v_q_80_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toModifyOfLE(lean_object* v_s_82_, lean_object* v_q_83_, lean_object* v_p_84_, lean_object* v_f_85_, lean_object* v_hp_86_, lean_object* v_hpq_87_){
_start:
{
lean_inc(v_q_83_);
return v_q_83_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toModifyOfLE___boxed(lean_object* v_s_88_, lean_object* v_q_89_, lean_object* v_p_90_, lean_object* v_f_91_, lean_object* v_hp_92_, lean_object* v_hpq_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_String_Pos_toModifyOfLE(v_s_88_, v_q_89_, v_p_90_, v_f_91_, v_hp_92_, v_hpq_93_);
lean_dec_ref(v_f_91_);
lean_dec(v_p_90_);
lean_dec(v_q_89_);
lean_dec_ref(v_s_88_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_pastModify___redArg(lean_object* v_s_95_, lean_object* v_p_96_, lean_object* v_f_97_){
_start:
{
uint32_t v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; uint32_t v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_98_ = lean_string_utf8_get_fast(v_s_95_, v_p_96_);
v___x_99_ = lean_box_uint32(v___x_98_);
v___x_100_ = lean_apply_1(v_f_97_, v___x_99_);
v___x_101_ = lean_unbox_uint32(v___x_100_);
lean_dec(v___x_100_);
v___x_102_ = l_Char_utf8Size(v___x_101_);
v___x_103_ = lean_nat_add(v_p_96_, v___x_102_);
lean_dec(v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_pastModify___redArg___boxed(lean_object* v_s_104_, lean_object* v_p_105_, lean_object* v_f_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_String_Pos_pastModify___redArg(v_s_104_, v_p_105_, v_f_106_);
lean_dec(v_p_105_);
lean_dec_ref(v_s_104_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_pastModify(lean_object* v_s_108_, lean_object* v_p_109_, lean_object* v_f_110_, lean_object* v_hp_111_){
_start:
{
uint32_t v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; uint32_t v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_112_ = lean_string_utf8_get_fast(v_s_108_, v_p_109_);
v___x_113_ = lean_box_uint32(v___x_112_);
v___x_114_ = lean_apply_1(v_f_110_, v___x_113_);
v___x_115_ = lean_unbox_uint32(v___x_114_);
lean_dec(v___x_114_);
v___x_116_ = l_Char_utf8Size(v___x_115_);
v___x_117_ = lean_nat_add(v_p_109_, v___x_116_);
lean_dec(v___x_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_pastModify___boxed(lean_object* v_s_118_, lean_object* v_p_119_, lean_object* v_f_120_, lean_object* v_hp_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_String_Pos_pastModify(v_s_118_, v_p_119_, v_f_120_, v_hp_121_);
lean_dec(v_p_119_);
lean_dec_ref(v_s_118_);
return v_res_122_;
}
}
LEAN_EXPORT void l_String_Pos_Raw_set_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_123_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_124_ = stack[1].m_obj;
uint32_t v_a_00___x40___internal___hyg_125_ = stack[2].m_num;
lean_object* v_res_126_;
v_res_126_ = lean_string_utf8_set(v_a_00___x40___internal___hyg_123_, v_a_00___x40___internal___hyg_124_, v_a_00___x40___internal___hyg_125_);
stack->m_obj
 = v_res_126_;
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_set___boxed(lean_object* v_a_00___x40___internal___hyg_127_, lean_object* v_a_00___x40___internal___hyg_128_, lean_object* v_a_00___x40___internal___hyg_129_){
_start:
{
uint32_t v_a_00___x40___internal___hyg_3__boxed_130_; lean_object* v_res_131_; 
v_a_00___x40___internal___hyg_3__boxed_130_ = lean_unbox_uint32(v_a_00___x40___internal___hyg_129_);
lean_dec(v_a_00___x40___internal___hyg_129_);
v_res_131_ = lean_string_utf8_set(v_a_00___x40___internal___hyg_127_, v_a_00___x40___internal___hyg_128_, v_a_00___x40___internal___hyg_3__boxed_130_);
lean_dec(v_a_00___x40___internal___hyg_128_);
return v_res_131_;
}
}
LEAN_EXPORT void l_String_set_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_132_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_133_ = stack[1].m_obj;
uint32_t v_a_00___x40___internal___hyg_134_ = stack[2].m_num;
lean_object* v_res_135_;
v_res_135_ = lean_string_utf8_set(v_a_00___x40___internal___hyg_132_, v_a_00___x40___internal___hyg_133_, v_a_00___x40___internal___hyg_134_);
stack->m_obj
 = v_res_135_;
}
LEAN_EXPORT lean_object* l_String_set___boxed(lean_object* v_a_00___x40___internal___hyg_136_, lean_object* v_a_00___x40___internal___hyg_137_, lean_object* v_a_00___x40___internal___hyg_138_){
_start:
{
uint32_t v_a_00___x40___internal___hyg_3__boxed_139_; lean_object* v_res_140_; 
v_a_00___x40___internal___hyg_3__boxed_139_ = lean_unbox_uint32(v_a_00___x40___internal___hyg_138_);
lean_dec(v_a_00___x40___internal___hyg_138_);
v_res_140_ = lean_string_utf8_set(v_a_00___x40___internal___hyg_136_, v_a_00___x40___internal___hyg_137_, v_a_00___x40___internal___hyg_3__boxed_139_);
lean_dec(v_a_00___x40___internal___hyg_137_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_modify(lean_object* v_s_141_, lean_object* v_i_142_, lean_object* v_f_143_){
_start:
{
uint32_t v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; uint32_t v___x_147_; lean_object* v___x_148_; 
v___x_144_ = lean_string_utf8_get(v_s_141_, v_i_142_);
v___x_145_ = lean_box_uint32(v___x_144_);
v___x_146_ = lean_apply_1(v_f_143_, v___x_145_);
v___x_147_ = lean_unbox_uint32(v___x_146_);
lean_dec(v___x_146_);
v___x_148_ = lean_string_utf8_set(v_s_141_, v_i_142_, v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_modify___boxed(lean_object* v_s_149_, lean_object* v_i_150_, lean_object* v_f_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_String_Pos_Raw_modify(v_s_149_, v_i_150_, v_f_151_);
lean_dec(v_i_150_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_String_modify(lean_object* v_s_153_, lean_object* v_i_154_, lean_object* v_f_155_){
_start:
{
uint32_t v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; uint32_t v___x_159_; lean_object* v___x_160_; 
v___x_156_ = lean_string_utf8_get(v_s_153_, v_i_154_);
v___x_157_ = lean_box_uint32(v___x_156_);
v___x_158_ = lean_apply_1(v_f_155_, v___x_157_);
v___x_159_ = lean_unbox_uint32(v___x_158_);
lean_dec(v___x_158_);
v___x_160_ = lean_string_utf8_set(v_s_153_, v_i_154_, v___x_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_String_modify___boxed(lean_object* v_s_161_, lean_object* v_i_162_, lean_object* v_f_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_String_modify(v_s_161_, v_i_162_, v_f_163_);
lean_dec(v_i_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux(lean_object* v_f_165_, lean_object* v_s_166_, lean_object* v_p_167_){
_start:
{
lean_object* v___x_168_; uint8_t v_decide_169_; 
v___x_168_ = lean_string_utf8_byte_size(v_s_166_);
v_decide_169_ = lean_nat_dec_eq(v_p_167_, v___x_168_);
if (v_decide_169_ == 0)
{
uint32_t v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; uint32_t v___x_173_; lean_object* v___x_174_; uint32_t v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_170_ = lean_string_utf8_get_fast(v_s_166_, v_p_167_);
v___x_171_ = lean_box_uint32(v___x_170_);
lean_inc_ref(v_f_165_);
v___x_172_ = lean_apply_1(v_f_165_, v___x_171_);
v___x_173_ = lean_unbox_uint32(v___x_172_);
lean_inc(v_p_167_);
v___x_174_ = lean_string_utf8_set(v_s_166_, v_p_167_, v___x_173_);
v___x_175_ = lean_unbox_uint32(v___x_172_);
lean_dec(v___x_172_);
v___x_176_ = l_Char_utf8Size(v___x_175_);
v___x_177_ = lean_nat_add(v_p_167_, v___x_176_);
lean_dec(v___x_176_);
lean_dec(v_p_167_);
v_s_166_ = v___x_174_;
v_p_167_ = v___x_177_;
goto _start;
}
else
{
lean_dec(v_p_167_);
lean_dec_ref(v_f_165_);
return v_s_166_;
}
}
}
LEAN_EXPORT lean_object* l_String_map(lean_object* v_f_179_, lean_object* v_s_180_){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_unsigned_to_nat(0u);
v___x_182_ = l_String_mapAux(v_f_179_, v_s_180_, v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_String_toUpper(lean_object* v_s_184_){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_185_ = ((lean_object*)(l_String_toUpper___closed__0));
v___x_186_ = lean_unsigned_to_nat(0u);
v___x_187_ = l_String_mapAux(v___x_185_, v_s_184_, v___x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_String_toLower(lean_object* v_s_189_){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_190_ = ((lean_object*)(l_String_toLower___closed__0));
v___x_191_ = lean_unsigned_to_nat(0u);
v___x_192_ = l_String_mapAux(v___x_190_, v_s_189_, v___x_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_String_capitalize(lean_object* v_s_193_){
_start:
{
lean_object* v___x_194_; uint32_t v___x_195_; uint32_t v___x_196_; uint8_t v___x_197_; 
v___x_194_ = lean_unsigned_to_nat(0u);
v___x_195_ = lean_string_utf8_get(v_s_193_, v___x_194_);
v___x_196_ = 97;
v___x_197_ = lean_uint32_dec_le(v___x_196_, v___x_195_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; 
v___x_198_ = lean_string_utf8_set(v_s_193_, v___x_194_, v___x_195_);
return v___x_198_;
}
else
{
uint32_t v___x_199_; uint8_t v___x_200_; 
v___x_199_ = 122;
v___x_200_ = lean_uint32_dec_le(v___x_195_, v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; 
v___x_201_ = lean_string_utf8_set(v_s_193_, v___x_194_, v___x_195_);
return v___x_201_;
}
else
{
uint32_t v___x_202_; uint32_t v___x_203_; lean_object* v___x_204_; 
v___x_202_ = 4294967264;
v___x_203_ = lean_uint32_add(v___x_195_, v___x_202_);
v___x_204_ = lean_string_utf8_set(v_s_193_, v___x_194_, v___x_203_);
return v___x_204_;
}
}
}
}
LEAN_EXPORT lean_object* lean_string_capitalize(lean_object* v_s_205_){
_start:
{
lean_object* v___x_206_; uint32_t v___x_207_; uint32_t v___x_208_; uint8_t v___x_209_; 
v___x_206_ = lean_unsigned_to_nat(0u);
v___x_207_ = lean_string_utf8_get(v_s_205_, v___x_206_);
v___x_208_ = 97;
v___x_209_ = lean_uint32_dec_le(v___x_208_, v___x_207_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; 
v___x_210_ = lean_string_utf8_set(v_s_205_, v___x_206_, v___x_207_);
return v___x_210_;
}
else
{
uint32_t v___x_211_; uint8_t v___x_212_; 
v___x_211_ = 122;
v___x_212_ = lean_uint32_dec_le(v___x_207_, v___x_211_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; 
v___x_213_ = lean_string_utf8_set(v_s_205_, v___x_206_, v___x_207_);
return v___x_213_;
}
else
{
uint32_t v___x_214_; uint32_t v___x_215_; lean_object* v___x_216_; 
v___x_214_ = 4294967264;
v___x_215_ = lean_uint32_add(v___x_207_, v___x_214_);
v___x_216_ = lean_string_utf8_set(v_s_205_, v___x_206_, v___x_215_);
return v___x_216_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_decapitalize(lean_object* v_s_217_){
_start:
{
lean_object* v___x_218_; uint32_t v___x_219_; uint32_t v___x_220_; uint8_t v___x_221_; 
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_string_utf8_get(v_s_217_, v___x_218_);
v___x_220_ = 65;
v___x_221_ = lean_uint32_dec_le(v___x_220_, v___x_219_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; 
v___x_222_ = lean_string_utf8_set(v_s_217_, v___x_218_, v___x_219_);
return v___x_222_;
}
else
{
uint32_t v___x_223_; uint8_t v___x_224_; 
v___x_223_ = 90;
v___x_224_ = lean_uint32_dec_le(v___x_219_, v___x_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; 
v___x_225_ = lean_string_utf8_set(v_s_217_, v___x_218_, v___x_219_);
return v___x_225_;
}
else
{
uint32_t v___x_226_; uint32_t v___x_227_; lean_object* v___x_228_; 
v___x_226_ = 32;
v___x_227_ = lean_uint32_add(v___x_219_, v___x_226_);
v___x_228_ = lean_string_utf8_set(v_s_217_, v___x_218_, v___x_227_);
return v___x_228_;
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

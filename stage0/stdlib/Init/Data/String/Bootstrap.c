// Lean compiler output
// Module: Init.Data.String.Bootstrap
// Imports: public import Init.Data.ByteArray.Bootstrap public import Init.Data.UInt.BasicAux import Init.Data.Char.Basic
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
lean_object* lean_string_mk(lean_object*);
LEAN_EXPORT lean_object* l_String_instOfNatRaw;
static const lean_string_object l_String_instInhabited___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_String_instInhabited___closed__0 = (const lean_object*)&l_String_instInhabited___closed__0_value;
LEAN_EXPORT const lean_object* l_String_instInhabited = (const lean_object*)&l_String_instInhabited___closed__0_value;
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_push___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_singleton(uint32_t);
LEAN_EXPORT lean_object* l_String_singleton___boxed(lean_object*);
lean_object* lean_string_posof(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_Internal_posOf___boxed(lean_object*, lean_object*);
lean_object* lean_string_offsetofpos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_offsetOfPos___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_extract___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_length___boxed(lean_object*);
lean_object* lean_string_pushn(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_pushn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_append___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_next___boxed(lean_object*, lean_object*);
uint8_t lean_string_isempty(lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_isEmpty___boxed(lean_object*);
lean_object* lean_string_foldl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_foldl___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_isprefixof(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_isPrefixOf___boxed(lean_object*, lean_object*);
uint8_t lean_string_any(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_any___boxed(lean_object*, lean_object*);
uint8_t lean_string_contains(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_Internal_contains___boxed(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_get___boxed(lean_object*, lean_object*);
lean_object* lean_string_capitalize(lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_capitalize___boxed(lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_atEnd___boxed(lean_object*, lean_object*);
lean_object* lean_string_nextwhile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_nextWhile___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_trim(lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_trim___boxed(lean_object*);
lean_object* lean_string_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_intercalate___boxed(lean_object*, lean_object*);
uint32_t lean_string_front(lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_front___boxed(lean_object*);
lean_object* lean_string_drop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_drop___boxed(lean_object*, lean_object*);
lean_object* lean_string_dropright(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_dropRight___boxed(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_getUTF8Byte___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_uget_byte_fast(lean_object*, size_t);
LEAN_EXPORT lean_object* l_String_Internal_ugetUTF8Byte___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_mk(lean_object*);
LEAN_EXPORT lean_object* l_String_mk___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_asString(lean_object*);
lean_object* lean_substring_tostring(lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_toString___boxed(lean_object*);
lean_object* lean_substring_drop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_drop___boxed(lean_object*, lean_object*);
uint32_t lean_substring_front(lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_front___boxed(lean_object*);
lean_object* lean_substring_takewhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_takeWhile___boxed(lean_object*, lean_object*);
lean_object* lean_substring_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_extract___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_substring_all(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_all___boxed(lean_object*, lean_object*);
uint8_t lean_substring_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_beq___boxed(lean_object*, lean_object*);
uint8_t lean_substring_isempty(lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_isEmpty___boxed(lean_object*);
uint32_t lean_substring_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_get___boxed(lean_object*, lean_object*);
lean_object* lean_substring_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_prev___boxed(lean_object*, lean_object*);
lean_object* lean_string_pos_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_Internal_sub___boxed(lean_object*, lean_object*);
lean_object* lean_string_pos_min(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_Internal_min___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_toString(uint32_t);
LEAN_EXPORT lean_object* l_Char_toString___boxed(lean_object*);
static lean_object* _init_l_String_instOfNatRaw(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_unsigned_to_nat(0u);
return v___x_1_;
}
}
LEAN_EXPORT void l_String_push_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_4_ = stack[0].m_obj;
uint32_t v_a_00___x40___internal___hyg_5_ = stack[1].m_num;
lean_object* v_res_6_;
v_res_6_ = lean_string_push(v_a_00___x40___internal___hyg_4_, v_a_00___x40___internal___hyg_5_);
stack->m_obj
 = v_res_6_;
}
LEAN_EXPORT lean_object* l_String_push___boxed(lean_object* v_a_00___x40___internal___hyg_7_, lean_object* v_a_00___x40___internal___hyg_8_){
_start:
{
uint32_t v_a_00___x40___internal___hyg_2__boxed_9_; lean_object* v_res_10_; 
v_a_00___x40___internal___hyg_2__boxed_9_ = lean_unbox_uint32(v_a_00___x40___internal___hyg_8_);
lean_dec(v_a_00___x40___internal___hyg_8_);
v_res_10_ = lean_string_push(v_a_00___x40___internal___hyg_7_, v_a_00___x40___internal___hyg_2__boxed_9_);
return v_res_10_;
}
}
lean_object* l_String_singleton(uint32_t v_c_11_){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = ((lean_object*)(l_String_instInhabited___closed__0));
v___x_13_ = lean_string_push(v___x_12_, v_c_11_);
return v___x_13_;
}
}
LEAN_EXPORT void l_String_singleton_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_11_ = stack[0].m_num;
lean_object* v_res_14_;
v_res_14_ = l_String_singleton(v_c_11_);
stack->m_obj
 = v_res_14_;
}
LEAN_EXPORT lean_object* l_String_singleton___boxed(lean_object* v_c_15_){
_start:
{
uint32_t v_c_boxed_16_; lean_object* v_res_17_; 
v_c_boxed_16_ = lean_unbox_uint32(v_c_15_);
lean_dec(v_c_15_);
v_res_17_ = l_String_singleton(v_c_boxed_16_);
return v_res_17_;
}
}
LEAN_EXPORT void l_String_Internal_posOf_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_18_ = stack[0].m_obj;
uint32_t v_c_19_ = stack[1].m_num;
lean_object* v_res_20_;
v_res_20_ = lean_string_posof(v_s_18_, v_c_19_);
stack->m_obj
 = v_res_20_;
}
LEAN_EXPORT lean_object* l_String_Internal_posOf___boxed(lean_object* v_s_21_, lean_object* v_c_22_){
_start:
{
uint32_t v_c_boxed_23_; lean_object* v_res_24_; 
v_c_boxed_23_ = lean_unbox_uint32(v_c_22_);
lean_dec(v_c_22_);
v_res_24_ = lean_string_posof(v_s_21_, v_c_boxed_23_);
return v_res_24_;
}
}
LEAN_EXPORT void l_String_Internal_offsetOfPos_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_25_ = stack[0].m_obj;
lean_object* v_pos_26_ = stack[1].m_obj;
lean_object* v_res_27_;
v_res_27_ = lean_string_offsetofpos(v_s_25_, v_pos_26_);
stack->m_obj
 = v_res_27_;
}
LEAN_EXPORT lean_object* l_String_Internal_offsetOfPos___boxed(lean_object* v_s_28_, lean_object* v_pos_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lean_string_offsetofpos(v_s_28_, v_pos_29_);
return v_res_30_;
}
}
LEAN_EXPORT void l_String_Internal_extract_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_31_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_32_ = stack[1].m_obj;
lean_object* v_a_00___x40___internal___hyg_33_ = stack[2].m_obj;
lean_object* v_res_34_;
v_res_34_ = lean_string_utf8_extract(v_a_00___x40___internal___hyg_31_, v_a_00___x40___internal___hyg_32_, v_a_00___x40___internal___hyg_33_);
stack->m_obj
 = v_res_34_;
}
LEAN_EXPORT lean_object* l_String_Internal_extract___boxed(lean_object* v_a_00___x40___internal___hyg_35_, lean_object* v_a_00___x40___internal___hyg_36_, lean_object* v_a_00___x40___internal___hyg_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = lean_string_utf8_extract(v_a_00___x40___internal___hyg_35_, v_a_00___x40___internal___hyg_36_, v_a_00___x40___internal___hyg_37_);
lean_dec(v_a_00___x40___internal___hyg_37_);
lean_dec(v_a_00___x40___internal___hyg_36_);
lean_dec_ref(v_a_00___x40___internal___hyg_35_);
return v_res_38_;
}
}
LEAN_EXPORT void l_String_Internal_length_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_39_ = stack[0].m_obj;
lean_object* v_res_40_;
v_res_40_ = lean_string_length(v_a_00___x40___internal___hyg_39_);
stack->m_obj
 = v_res_40_;
}
LEAN_EXPORT lean_object* l_String_Internal_length___boxed(lean_object* v_a_00___x40___internal___hyg_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = lean_string_length(v_a_00___x40___internal___hyg_41_);
lean_dec_ref(v_a_00___x40___internal___hyg_41_);
return v_res_42_;
}
}
LEAN_EXPORT void l_String_Internal_pushn_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_43_ = stack[0].m_obj;
uint32_t v_c_44_ = stack[1].m_num;
lean_object* v_n_45_ = stack[2].m_obj;
lean_object* v_res_46_;
v_res_46_ = lean_string_pushn(v_s_43_, v_c_44_, v_n_45_);
stack->m_obj
 = v_res_46_;
}
LEAN_EXPORT lean_object* l_String_Internal_pushn___boxed(lean_object* v_s_47_, lean_object* v_c_48_, lean_object* v_n_49_){
_start:
{
uint32_t v_c_boxed_50_; lean_object* v_res_51_; 
v_c_boxed_50_ = lean_unbox_uint32(v_c_48_);
lean_dec(v_c_48_);
v_res_51_ = lean_string_pushn(v_s_47_, v_c_boxed_50_, v_n_49_);
return v_res_51_;
}
}
LEAN_EXPORT void l_String_Internal_append_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_52_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_53_ = stack[1].m_obj;
lean_object* v_res_54_;
v_res_54_ = lean_string_append(v_a_00___x40___internal___hyg_52_, v_a_00___x40___internal___hyg_53_);
stack->m_obj
 = v_res_54_;
}
LEAN_EXPORT lean_object* l_String_Internal_append___boxed(lean_object* v_a_00___x40___internal___hyg_55_, lean_object* v_a_00___x40___internal___hyg_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = lean_string_append(v_a_00___x40___internal___hyg_55_, v_a_00___x40___internal___hyg_56_);
lean_dec_ref(v_a_00___x40___internal___hyg_56_);
return v_res_57_;
}
}
LEAN_EXPORT void l_String_Internal_next_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_58_ = stack[0].m_obj;
lean_object* v_p_59_ = stack[1].m_obj;
lean_object* v_res_60_;
v_res_60_ = lean_string_utf8_next(v_s_58_, v_p_59_);
stack->m_obj
 = v_res_60_;
}
LEAN_EXPORT lean_object* l_String_Internal_next___boxed(lean_object* v_s_61_, lean_object* v_p_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = lean_string_utf8_next(v_s_61_, v_p_62_);
lean_dec(v_p_62_);
lean_dec_ref(v_s_61_);
return v_res_63_;
}
}
LEAN_EXPORT void l_String_Internal_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_64_ = stack[0].m_obj;
uint8_t v_res_65_;
v_res_65_ = lean_string_isempty(v_s_64_);
stack->m_num = v_res_65_;
}
LEAN_EXPORT lean_object* l_String_Internal_isEmpty___boxed(lean_object* v_s_66_){
_start:
{
uint8_t v_res_67_; lean_object* v_r_68_; 
v_res_67_ = lean_string_isempty(v_s_66_);
v_r_68_ = lean_box(v_res_67_);
return v_r_68_;
}
}
LEAN_EXPORT void l_String_Internal_foldl_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_69_ = stack[0].m_obj;
lean_object* v_init_70_ = stack[1].m_obj;
lean_object* v_s_71_ = stack[2].m_obj;
lean_object* v_res_72_;
v_res_72_ = lean_string_foldl(v_f_69_, v_init_70_, v_s_71_);
stack->m_obj
 = v_res_72_;
}
LEAN_EXPORT lean_object* l_String_Internal_foldl___boxed(lean_object* v_f_73_, lean_object* v_init_74_, lean_object* v_s_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = lean_string_foldl(v_f_73_, v_init_74_, v_s_75_);
return v_res_76_;
}
}
LEAN_EXPORT void l_String_Internal_isPrefixOf_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_77_ = stack[0].m_obj;
lean_object* v_s_78_ = stack[1].m_obj;
uint8_t v_res_79_;
v_res_79_ = lean_string_isprefixof(v_p_77_, v_s_78_);
stack->m_num = v_res_79_;
}
LEAN_EXPORT lean_object* l_String_Internal_isPrefixOf___boxed(lean_object* v_p_80_, lean_object* v_s_81_){
_start:
{
uint8_t v_res_82_; lean_object* v_r_83_; 
v_res_82_ = lean_string_isprefixof(v_p_80_, v_s_81_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT void l_String_Internal_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_84_ = stack[0].m_obj;
lean_object* v_p_85_ = stack[1].m_obj;
uint8_t v_res_86_;
v_res_86_ = lean_string_any(v_s_84_, v_p_85_);
stack->m_num = v_res_86_;
}
LEAN_EXPORT lean_object* l_String_Internal_any___boxed(lean_object* v_s_87_, lean_object* v_p_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = lean_string_any(v_s_87_, v_p_88_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
LEAN_EXPORT void l_String_Internal_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_91_ = stack[0].m_obj;
uint32_t v_c_92_ = stack[1].m_num;
uint8_t v_res_93_;
v_res_93_ = lean_string_contains(v_s_91_, v_c_92_);
stack->m_num = v_res_93_;
}
LEAN_EXPORT lean_object* l_String_Internal_contains___boxed(lean_object* v_s_94_, lean_object* v_c_95_){
_start:
{
uint32_t v_c_boxed_96_; uint8_t v_res_97_; lean_object* v_r_98_; 
v_c_boxed_96_ = lean_unbox_uint32(v_c_95_);
lean_dec(v_c_95_);
v_res_97_ = lean_string_contains(v_s_94_, v_c_boxed_96_);
v_r_98_ = lean_box(v_res_97_);
return v_r_98_;
}
}
LEAN_EXPORT void l_String_Internal_get_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_99_ = stack[0].m_obj;
lean_object* v_p_100_ = stack[1].m_obj;
uint32_t v_res_101_;
v_res_101_ = lean_string_utf8_get(v_s_99_, v_p_100_);
stack->m_num = v_res_101_;
}
LEAN_EXPORT lean_object* l_String_Internal_get___boxed(lean_object* v_s_102_, lean_object* v_p_103_){
_start:
{
uint32_t v_res_104_; lean_object* v_r_105_; 
v_res_104_ = lean_string_utf8_get(v_s_102_, v_p_103_);
lean_dec(v_p_103_);
lean_dec_ref(v_s_102_);
v_r_105_ = lean_box_uint32(v_res_104_);
return v_r_105_;
}
}
LEAN_EXPORT void l_String_Internal_capitalize_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_106_ = stack[0].m_obj;
lean_object* v_res_107_;
v_res_107_ = lean_string_capitalize(v_s_106_);
stack->m_obj
 = v_res_107_;
}
LEAN_EXPORT lean_object* l_String_Internal_capitalize___boxed(lean_object* v_s_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = lean_string_capitalize(v_s_108_);
return v_res_109_;
}
}
LEAN_EXPORT void l_String_Internal_atEnd_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_110_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_111_ = stack[1].m_obj;
uint8_t v_res_112_;
v_res_112_ = lean_string_utf8_at_end(v_a_00___x40___internal___hyg_110_, v_a_00___x40___internal___hyg_111_);
stack->m_num = v_res_112_;
}
LEAN_EXPORT lean_object* l_String_Internal_atEnd___boxed(lean_object* v_a_00___x40___internal___hyg_113_, lean_object* v_a_00___x40___internal___hyg_114_){
_start:
{
uint8_t v_res_115_; lean_object* v_r_116_; 
v_res_115_ = lean_string_utf8_at_end(v_a_00___x40___internal___hyg_113_, v_a_00___x40___internal___hyg_114_);
lean_dec(v_a_00___x40___internal___hyg_114_);
lean_dec_ref(v_a_00___x40___internal___hyg_113_);
v_r_116_ = lean_box(v_res_115_);
return v_r_116_;
}
}
LEAN_EXPORT void l_String_Internal_nextWhile_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_117_ = stack[0].m_obj;
lean_object* v_p_118_ = stack[1].m_obj;
lean_object* v_i_119_ = stack[2].m_obj;
lean_object* v_res_120_;
v_res_120_ = lean_string_nextwhile(v_s_117_, v_p_118_, v_i_119_);
stack->m_obj
 = v_res_120_;
}
LEAN_EXPORT lean_object* l_String_Internal_nextWhile___boxed(lean_object* v_s_121_, lean_object* v_p_122_, lean_object* v_i_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = lean_string_nextwhile(v_s_121_, v_p_122_, v_i_123_);
return v_res_124_;
}
}
LEAN_EXPORT void l_String_Internal_trim_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_125_ = stack[0].m_obj;
lean_object* v_res_126_;
v_res_126_ = lean_string_trim(v_s_125_);
stack->m_obj
 = v_res_126_;
}
LEAN_EXPORT lean_object* l_String_Internal_trim___boxed(lean_object* v_s_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = lean_string_trim(v_s_127_);
return v_res_128_;
}
}
LEAN_EXPORT void l_String_Internal_intercalate_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_129_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_130_ = stack[1].m_obj;
lean_object* v_res_131_;
v_res_131_ = lean_string_intercalate(v_s_129_, v_a_00___x40___internal___hyg_130_);
stack->m_obj
 = v_res_131_;
}
LEAN_EXPORT lean_object* l_String_Internal_intercalate___boxed(lean_object* v_s_132_, lean_object* v_a_00___x40___internal___hyg_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = lean_string_intercalate(v_s_132_, v_a_00___x40___internal___hyg_133_);
return v_res_134_;
}
}
LEAN_EXPORT void l_String_Internal_front_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_135_ = stack[0].m_obj;
uint32_t v_res_136_;
v_res_136_ = lean_string_front(v_s_135_);
stack->m_num = v_res_136_;
}
LEAN_EXPORT lean_object* l_String_Internal_front___boxed(lean_object* v_s_137_){
_start:
{
uint32_t v_res_138_; lean_object* v_r_139_; 
v_res_138_ = lean_string_front(v_s_137_);
v_r_139_ = lean_box_uint32(v_res_138_);
return v_r_139_;
}
}
LEAN_EXPORT void l_String_Internal_drop_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_140_ = stack[0].m_obj;
lean_object* v_n_141_ = stack[1].m_obj;
lean_object* v_res_142_;
v_res_142_ = lean_string_drop(v_s_140_, v_n_141_);
stack->m_obj
 = v_res_142_;
}
LEAN_EXPORT lean_object* l_String_Internal_drop___boxed(lean_object* v_s_143_, lean_object* v_n_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = lean_string_drop(v_s_143_, v_n_144_);
return v_res_145_;
}
}
LEAN_EXPORT void l_String_Internal_dropRight_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_146_ = stack[0].m_obj;
lean_object* v_n_147_ = stack[1].m_obj;
lean_object* v_res_148_;
v_res_148_ = lean_string_dropright(v_s_146_, v_n_147_);
stack->m_obj
 = v_res_148_;
}
LEAN_EXPORT lean_object* l_String_Internal_dropRight___boxed(lean_object* v_s_149_, lean_object* v_n_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = lean_string_dropright(v_s_149_, v_n_150_);
return v_res_151_;
}
}
LEAN_EXPORT void l_String_Internal_getUTF8Byte_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_152_ = stack[0].m_obj;
lean_object* v_n_153_ = stack[1].m_obj;
uint8_t v_res_155_;
v_res_155_ = lean_string_get_byte_fast(v_s_152_, v_n_153_);
stack->m_num = v_res_155_;
}
LEAN_EXPORT lean_object* l_String_Internal_getUTF8Byte___boxed(lean_object* v_s_156_, lean_object* v_n_157_, lean_object* v_h_158_){
_start:
{
uint8_t v_res_159_; lean_object* v_r_160_; 
v_res_159_ = lean_string_get_byte_fast(v_s_156_, v_n_157_);
lean_dec_ref(v_s_156_);
v_r_160_ = lean_box(v_res_159_);
return v_r_160_;
}
}
LEAN_EXPORT void l_String_Internal_ugetUTF8Byte_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_161_ = stack[0].m_obj;
size_t v_n_162_ = stack[1].m_num;
uint8_t v_res_164_;
v_res_164_ = lean_string_uget_byte_fast(v_s_161_, v_n_162_);
stack->m_num = v_res_164_;
}
LEAN_EXPORT lean_object* l_String_Internal_ugetUTF8Byte___boxed(lean_object* v_s_165_, lean_object* v_n_166_, lean_object* v_h_167_){
_start:
{
size_t v_n_boxed_168_; uint8_t v_res_169_; lean_object* v_r_170_; 
v_n_boxed_168_ = lean_unbox_usize(v_n_166_);
lean_dec(v_n_166_);
v_res_169_ = lean_string_uget_byte_fast(v_s_165_, v_n_boxed_168_);
lean_dec_ref(v_s_165_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
LEAN_EXPORT void l_String_mk_0interp(lean_interpreter_value* stack)
{
lean_object* v_data_171_ = stack[0].m_obj;
lean_object* v_res_172_;
v_res_172_ = lean_string_mk(v_data_171_);
stack->m_obj
 = v_res_172_;
}
LEAN_EXPORT lean_object* l_String_mk___boxed(lean_object* v_data_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = lean_string_mk(v_data_173_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_List_asString(lean_object* v_s_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = lean_string_mk(v_s_175_);
return v___x_176_;
}
}
LEAN_EXPORT void l_Substring_Raw_Internal_toString_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_177_ = stack[0].m_obj;
lean_object* v_res_178_;
v_res_178_ = lean_substring_tostring(v_a_00___x40___internal___hyg_177_);
stack->m_obj
 = v_res_178_;
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_toString___boxed(lean_object* v_a_00___x40___internal___hyg_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = lean_substring_tostring(v_a_00___x40___internal___hyg_179_);
return v_res_180_;
}
}
LEAN_EXPORT void l_Substring_Raw_Internal_drop_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_181_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_182_ = stack[1].m_obj;
lean_object* v_res_183_;
v_res_183_ = lean_substring_drop(v_a_00___x40___internal___hyg_181_, v_a_00___x40___internal___hyg_182_);
stack->m_obj
 = v_res_183_;
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_drop___boxed(lean_object* v_a_00___x40___internal___hyg_184_, lean_object* v_a_00___x40___internal___hyg_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = lean_substring_drop(v_a_00___x40___internal___hyg_184_, v_a_00___x40___internal___hyg_185_);
return v_res_186_;
}
}
LEAN_EXPORT void l_Substring_Raw_Internal_front_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_187_ = stack[0].m_obj;
uint32_t v_res_188_;
v_res_188_ = lean_substring_front(v_s_187_);
stack->m_num = v_res_188_;
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_front___boxed(lean_object* v_s_189_){
_start:
{
uint32_t v_res_190_; lean_object* v_r_191_; 
v_res_190_ = lean_substring_front(v_s_189_);
v_r_191_ = lean_box_uint32(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT void l_Substring_Raw_Internal_takeWhile_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_192_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_193_ = stack[1].m_obj;
lean_object* v_res_194_;
v_res_194_ = lean_substring_takewhile(v_a_00___x40___internal___hyg_192_, v_a_00___x40___internal___hyg_193_);
stack->m_obj
 = v_res_194_;
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_takeWhile___boxed(lean_object* v_a_00___x40___internal___hyg_195_, lean_object* v_a_00___x40___internal___hyg_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = lean_substring_takewhile(v_a_00___x40___internal___hyg_195_, v_a_00___x40___internal___hyg_196_);
return v_res_197_;
}
}
LEAN_EXPORT void l_Substring_Raw_Internal_extract_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_198_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_199_ = stack[1].m_obj;
lean_object* v_a_00___x40___internal___hyg_200_ = stack[2].m_obj;
lean_object* v_res_201_;
v_res_201_ = lean_substring_extract(v_a_00___x40___internal___hyg_198_, v_a_00___x40___internal___hyg_199_, v_a_00___x40___internal___hyg_200_);
stack->m_obj
 = v_res_201_;
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_extract___boxed(lean_object* v_a_00___x40___internal___hyg_202_, lean_object* v_a_00___x40___internal___hyg_203_, lean_object* v_a_00___x40___internal___hyg_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = lean_substring_extract(v_a_00___x40___internal___hyg_202_, v_a_00___x40___internal___hyg_203_, v_a_00___x40___internal___hyg_204_);
return v_res_205_;
}
}
LEAN_EXPORT void l_Substring_Raw_Internal_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_206_ = stack[0].m_obj;
lean_object* v_p_207_ = stack[1].m_obj;
uint8_t v_res_208_;
v_res_208_ = lean_substring_all(v_s_206_, v_p_207_);
stack->m_num = v_res_208_;
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_all___boxed(lean_object* v_s_209_, lean_object* v_p_210_){
_start:
{
uint8_t v_res_211_; lean_object* v_r_212_; 
v_res_211_ = lean_substring_all(v_s_209_, v_p_210_);
v_r_212_ = lean_box(v_res_211_);
return v_r_212_;
}
}
LEAN_EXPORT void l_Substring_Raw_Internal_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_ss1_213_ = stack[0].m_obj;
lean_object* v_ss2_214_ = stack[1].m_obj;
uint8_t v_res_215_;
v_res_215_ = lean_substring_beq(v_ss1_213_, v_ss2_214_);
stack->m_num = v_res_215_;
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_beq___boxed(lean_object* v_ss1_216_, lean_object* v_ss2_217_){
_start:
{
uint8_t v_res_218_; lean_object* v_r_219_; 
v_res_218_ = lean_substring_beq(v_ss1_216_, v_ss2_217_);
v_r_219_ = lean_box(v_res_218_);
return v_r_219_;
}
}
LEAN_EXPORT void l_Substring_Raw_Internal_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_ss_220_ = stack[0].m_obj;
uint8_t v_res_221_;
v_res_221_ = lean_substring_isempty(v_ss_220_);
stack->m_num = v_res_221_;
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_isEmpty___boxed(lean_object* v_ss_222_){
_start:
{
uint8_t v_res_223_; lean_object* v_r_224_; 
v_res_223_ = lean_substring_isempty(v_ss_222_);
v_r_224_ = lean_box(v_res_223_);
return v_r_224_;
}
}
LEAN_EXPORT void l_Substring_Raw_Internal_get_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_225_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_226_ = stack[1].m_obj;
uint32_t v_res_227_;
v_res_227_ = lean_substring_get(v_a_00___x40___internal___hyg_225_, v_a_00___x40___internal___hyg_226_);
stack->m_num = v_res_227_;
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_get___boxed(lean_object* v_a_00___x40___internal___hyg_228_, lean_object* v_a_00___x40___internal___hyg_229_){
_start:
{
uint32_t v_res_230_; lean_object* v_r_231_; 
v_res_230_ = lean_substring_get(v_a_00___x40___internal___hyg_228_, v_a_00___x40___internal___hyg_229_);
v_r_231_ = lean_box_uint32(v_res_230_);
return v_r_231_;
}
}
LEAN_EXPORT void l_Substring_Raw_Internal_prev_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_232_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_233_ = stack[1].m_obj;
lean_object* v_res_234_;
v_res_234_ = lean_substring_prev(v_a_00___x40___internal___hyg_232_, v_a_00___x40___internal___hyg_233_);
stack->m_obj
 = v_res_234_;
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_prev___boxed(lean_object* v_a_00___x40___internal___hyg_235_, lean_object* v_a_00___x40___internal___hyg_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = lean_substring_prev(v_a_00___x40___internal___hyg_235_, v_a_00___x40___internal___hyg_236_);
return v_res_237_;
}
}
LEAN_EXPORT void l_String_Pos_Raw_Internal_sub_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_238_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_239_ = stack[1].m_obj;
lean_object* v_res_240_;
v_res_240_ = lean_string_pos_sub(v_a_00___x40___internal___hyg_238_, v_a_00___x40___internal___hyg_239_);
stack->m_obj
 = v_res_240_;
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_Internal_sub___boxed(lean_object* v_a_00___x40___internal___hyg_241_, lean_object* v_a_00___x40___internal___hyg_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = lean_string_pos_sub(v_a_00___x40___internal___hyg_241_, v_a_00___x40___internal___hyg_242_);
return v_res_243_;
}
}
LEAN_EXPORT void l_String_Pos_Raw_Internal_min_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_u2081_244_ = stack[0].m_obj;
lean_object* v_p_u2082_245_ = stack[1].m_obj;
lean_object* v_res_246_;
v_res_246_ = lean_string_pos_min(v_p_u2081_244_, v_p_u2082_245_);
stack->m_obj
 = v_res_246_;
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_Internal_min___boxed(lean_object* v_p_u2081_247_, lean_object* v_p_u2082_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = lean_string_pos_min(v_p_u2081_247_, v_p_u2082_248_);
return v_res_249_;
}
}
lean_object* l_Char_toString(uint32_t v_c_250_){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = ((lean_object*)(l_String_instInhabited___closed__0));
v___x_252_ = lean_string_push(v___x_251_, v_c_250_);
return v___x_252_;
}
}
LEAN_EXPORT void l_Char_toString_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_250_ = stack[0].m_num;
lean_object* v_res_253_;
v_res_253_ = l_Char_toString(v_c_250_);
stack->m_obj
 = v_res_253_;
}
LEAN_EXPORT lean_object* l_Char_toString___boxed(lean_object* v_c_254_){
_start:
{
uint32_t v_c_boxed_255_; lean_object* v_res_256_; 
v_c_boxed_255_ = lean_unbox_uint32(v_c_254_);
lean_dec(v_c_254_);
v_res_256_ = l_Char_toString(v_c_boxed_255_);
return v_res_256_;
}
}
lean_object* runtime_initialize_Init_Data_ByteArray_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Bootstrap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_ByteArray_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_String_instOfNatRaw = _init_l_String_instOfNatRaw();
lean_mark_persistent(l_String_instOfNatRaw);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Bootstrap(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ByteArray_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_BasicAux(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Bootstrap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ByteArray_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Bootstrap(builtin);
}
#ifdef __cplusplus
}
#endif

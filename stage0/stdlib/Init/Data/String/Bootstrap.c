// Lean compiler output
// Module: Init.Data.String.Bootstrap
// Imports: public import Init.Data.ByteArray.Bootstrap import Init.Data.Char.Basic
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
LEAN_EXPORT lean_object* l_String_push___boxed(lean_object* v_a_00___x40___internal___hyg_6_, lean_object* v_a_00___x40___internal___hyg_7_){
_start:
{
uint32_t v_a_00___x40___internal___hyg_2__boxed_8_; lean_object* v_res_9_; 
v_a_00___x40___internal___hyg_2__boxed_8_ = lean_unbox_uint32(v_a_00___x40___internal___hyg_7_);
lean_dec(v_a_00___x40___internal___hyg_7_);
v_res_9_ = lean_string_push(v_a_00___x40___internal___hyg_6_, v_a_00___x40___internal___hyg_2__boxed_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_String_singleton(uint32_t v_c_10_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = ((lean_object*)(l_String_instInhabited___closed__0));
v___x_12_ = lean_string_push(v___x_11_, v_c_10_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_String_singleton___boxed(lean_object* v_c_13_){
_start:
{
uint32_t v_c_boxed_14_; lean_object* v_res_15_; 
v_c_boxed_14_ = lean_unbox_uint32(v_c_13_);
lean_dec(v_c_13_);
v_res_15_ = l_String_singleton(v_c_boxed_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_posOf___boxed(lean_object* v_s_18_, lean_object* v_c_19_){
_start:
{
uint32_t v_c_boxed_20_; lean_object* v_res_21_; 
v_c_boxed_20_ = lean_unbox_uint32(v_c_19_);
lean_dec(v_c_19_);
v_res_21_ = lean_string_posof(v_s_18_, v_c_boxed_20_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_offsetOfPos___boxed(lean_object* v_s_24_, lean_object* v_pos_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lean_string_offsetofpos(v_s_24_, v_pos_25_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_extract___boxed(lean_object* v_a_00___x40___internal___hyg_30_, lean_object* v_a_00___x40___internal___hyg_31_, lean_object* v_a_00___x40___internal___hyg_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lean_string_utf8_extract(v_a_00___x40___internal___hyg_30_, v_a_00___x40___internal___hyg_31_, v_a_00___x40___internal___hyg_32_);
lean_dec(v_a_00___x40___internal___hyg_32_);
lean_dec(v_a_00___x40___internal___hyg_31_);
lean_dec_ref(v_a_00___x40___internal___hyg_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_length___boxed(lean_object* v_a_00___x40___internal___hyg_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lean_string_length(v_a_00___x40___internal___hyg_35_);
lean_dec_ref(v_a_00___x40___internal___hyg_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_pushn___boxed(lean_object* v_s_40_, lean_object* v_c_41_, lean_object* v_n_42_){
_start:
{
uint32_t v_c_boxed_43_; lean_object* v_res_44_; 
v_c_boxed_43_ = lean_unbox_uint32(v_c_41_);
lean_dec(v_c_41_);
v_res_44_ = lean_string_pushn(v_s_40_, v_c_boxed_43_, v_n_42_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_append___boxed(lean_object* v_a_00___x40___internal___hyg_47_, lean_object* v_a_00___x40___internal___hyg_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = lean_string_append(v_a_00___x40___internal___hyg_47_, v_a_00___x40___internal___hyg_48_);
lean_dec_ref(v_a_00___x40___internal___hyg_48_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_next___boxed(lean_object* v_s_52_, lean_object* v_p_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = lean_string_utf8_next(v_s_52_, v_p_53_);
lean_dec(v_p_53_);
lean_dec_ref(v_s_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_isEmpty___boxed(lean_object* v_s_56_){
_start:
{
uint8_t v_res_57_; lean_object* v_r_58_; 
v_res_57_ = lean_string_isempty(v_s_56_);
v_r_58_ = lean_box(v_res_57_);
return v_r_58_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_foldl___boxed(lean_object* v_f_62_, lean_object* v_init_63_, lean_object* v_s_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = lean_string_foldl(v_f_62_, v_init_63_, v_s_64_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_isPrefixOf___boxed(lean_object* v_p_68_, lean_object* v_s_69_){
_start:
{
uint8_t v_res_70_; lean_object* v_r_71_; 
v_res_70_ = lean_string_isprefixof(v_p_68_, v_s_69_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_any___boxed(lean_object* v_s_74_, lean_object* v_p_75_){
_start:
{
uint8_t v_res_76_; lean_object* v_r_77_; 
v_res_76_ = lean_string_any(v_s_74_, v_p_75_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_contains___boxed(lean_object* v_s_80_, lean_object* v_c_81_){
_start:
{
uint32_t v_c_boxed_82_; uint8_t v_res_83_; lean_object* v_r_84_; 
v_c_boxed_82_ = lean_unbox_uint32(v_c_81_);
lean_dec(v_c_81_);
v_res_83_ = lean_string_contains(v_s_80_, v_c_boxed_82_);
v_r_84_ = lean_box(v_res_83_);
return v_r_84_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_get___boxed(lean_object* v_s_87_, lean_object* v_p_88_){
_start:
{
uint32_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = lean_string_utf8_get(v_s_87_, v_p_88_);
lean_dec(v_p_88_);
lean_dec_ref(v_s_87_);
v_r_90_ = lean_box_uint32(v_res_89_);
return v_r_90_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_capitalize___boxed(lean_object* v_s_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = lean_string_capitalize(v_s_92_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_atEnd___boxed(lean_object* v_a_00___x40___internal___hyg_96_, lean_object* v_a_00___x40___internal___hyg_97_){
_start:
{
uint8_t v_res_98_; lean_object* v_r_99_; 
v_res_98_ = lean_string_utf8_at_end(v_a_00___x40___internal___hyg_96_, v_a_00___x40___internal___hyg_97_);
lean_dec(v_a_00___x40___internal___hyg_97_);
lean_dec_ref(v_a_00___x40___internal___hyg_96_);
v_r_99_ = lean_box(v_res_98_);
return v_r_99_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_nextWhile___boxed(lean_object* v_s_103_, lean_object* v_p_104_, lean_object* v_i_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = lean_string_nextwhile(v_s_103_, v_p_104_, v_i_105_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_trim___boxed(lean_object* v_s_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = lean_string_trim(v_s_108_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_intercalate___boxed(lean_object* v_s_112_, lean_object* v_a_00___x40___internal___hyg_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = lean_string_intercalate(v_s_112_, v_a_00___x40___internal___hyg_113_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_front___boxed(lean_object* v_s_116_){
_start:
{
uint32_t v_res_117_; lean_object* v_r_118_; 
v_res_117_ = lean_string_front(v_s_116_);
v_r_118_ = lean_box_uint32(v_res_117_);
return v_r_118_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_drop___boxed(lean_object* v_s_121_, lean_object* v_n_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = lean_string_drop(v_s_121_, v_n_122_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_dropRight___boxed(lean_object* v_s_126_, lean_object* v_n_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = lean_string_dropright(v_s_126_, v_n_127_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_getUTF8Byte___boxed(lean_object* v_s_132_, lean_object* v_n_133_, lean_object* v_h_134_){
_start:
{
uint8_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = lean_string_get_byte_fast(v_s_132_, v_n_133_);
lean_dec_ref(v_s_132_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT lean_object* l_String_mk___boxed(lean_object* v_data_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = lean_string_mk(v_data_138_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_List_asString(lean_object* v_s_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = lean_string_mk(v_s_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_toString___boxed(lean_object* v_a_00___x40___internal___hyg_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = lean_substring_tostring(v_a_00___x40___internal___hyg_143_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_drop___boxed(lean_object* v_a_00___x40___internal___hyg_147_, lean_object* v_a_00___x40___internal___hyg_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = lean_substring_drop(v_a_00___x40___internal___hyg_147_, v_a_00___x40___internal___hyg_148_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_front___boxed(lean_object* v_s_151_){
_start:
{
uint32_t v_res_152_; lean_object* v_r_153_; 
v_res_152_ = lean_substring_front(v_s_151_);
v_r_153_ = lean_box_uint32(v_res_152_);
return v_r_153_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_takeWhile___boxed(lean_object* v_a_00___x40___internal___hyg_156_, lean_object* v_a_00___x40___internal___hyg_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = lean_substring_takewhile(v_a_00___x40___internal___hyg_156_, v_a_00___x40___internal___hyg_157_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_extract___boxed(lean_object* v_a_00___x40___internal___hyg_162_, lean_object* v_a_00___x40___internal___hyg_163_, lean_object* v_a_00___x40___internal___hyg_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = lean_substring_extract(v_a_00___x40___internal___hyg_162_, v_a_00___x40___internal___hyg_163_, v_a_00___x40___internal___hyg_164_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_all___boxed(lean_object* v_s_168_, lean_object* v_p_169_){
_start:
{
uint8_t v_res_170_; lean_object* v_r_171_; 
v_res_170_ = lean_substring_all(v_s_168_, v_p_169_);
v_r_171_ = lean_box(v_res_170_);
return v_r_171_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_beq___boxed(lean_object* v_ss1_174_, lean_object* v_ss2_175_){
_start:
{
uint8_t v_res_176_; lean_object* v_r_177_; 
v_res_176_ = lean_substring_beq(v_ss1_174_, v_ss2_175_);
v_r_177_ = lean_box(v_res_176_);
return v_r_177_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_isEmpty___boxed(lean_object* v_ss_179_){
_start:
{
uint8_t v_res_180_; lean_object* v_r_181_; 
v_res_180_ = lean_substring_isempty(v_ss_179_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_get___boxed(lean_object* v_a_00___x40___internal___hyg_184_, lean_object* v_a_00___x40___internal___hyg_185_){
_start:
{
uint32_t v_res_186_; lean_object* v_r_187_; 
v_res_186_ = lean_substring_get(v_a_00___x40___internal___hyg_184_, v_a_00___x40___internal___hyg_185_);
v_r_187_ = lean_box_uint32(v_res_186_);
return v_r_187_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_prev___boxed(lean_object* v_a_00___x40___internal___hyg_190_, lean_object* v_a_00___x40___internal___hyg_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = lean_substring_prev(v_a_00___x40___internal___hyg_190_, v_a_00___x40___internal___hyg_191_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_Internal_sub___boxed(lean_object* v_a_00___x40___internal___hyg_195_, lean_object* v_a_00___x40___internal___hyg_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = lean_string_pos_sub(v_a_00___x40___internal___hyg_195_, v_a_00___x40___internal___hyg_196_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_Internal_min___boxed(lean_object* v_p_u2081_200_, lean_object* v_p_u2082_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = lean_string_pos_min(v_p_u2081_200_, v_p_u2082_201_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Char_toString(uint32_t v_c_203_){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = ((lean_object*)(l_String_instInhabited___closed__0));
v___x_205_ = lean_string_push(v___x_204_, v_c_203_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Char_toString___boxed(lean_object* v_c_206_){
_start:
{
uint32_t v_c_boxed_207_; lean_object* v_res_208_; 
v_c_boxed_207_ = lean_unbox_uint32(v_c_206_);
lean_dec(v_c_206_);
v_res_208_ = l_Char_toString(v_c_boxed_207_);
return v_res_208_;
}
}
lean_object* runtime_initialize_Init_Data_ByteArray_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Bootstrap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_ByteArray_Bootstrap(builtin);
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
lean_object* initialize_Init_Data_Char_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Bootstrap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ByteArray_Bootstrap(builtin);
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

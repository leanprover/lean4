// Lean compiler output
// Module: Init.Data.String.PosRaw
// Imports: public import Init.Data.ByteArray.Basic import Init.Data.Nat.Simproc import Init.Omega
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Char_utf8Size(uint32_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHSubRaw___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHSubRaw___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_instHSubRaw___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_instHSubRaw___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_instHSubRaw___closed__0 = (const lean_object*)&l_String_instHSubRaw___closed__0_value;
LEAN_EXPORT const lean_object* l_String_instHSubRaw = (const lean_object*)&l_String_instHSubRaw___closed__0_value;
LEAN_EXPORT lean_object* l_String_instHSubRawChar___lam__0(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_instHSubRawChar___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_instHSubRawChar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_instHSubRawChar___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_instHSubRawChar___closed__0 = (const lean_object*)&l_String_instHSubRawChar___closed__0_value;
LEAN_EXPORT const lean_object* l_String_instHSubRawChar = (const lean_object*)&l_String_instHSubRawChar___closed__0_value;
LEAN_EXPORT lean_object* lean_string_pos_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddRawChar___lam__0(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_instHAddRawChar___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_instHAddRawChar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_instHAddRawChar___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_instHAddRawChar___closed__0 = (const lean_object*)&l_String_instHAddRawChar___closed__0_value;
LEAN_EXPORT const lean_object* l_String_instHAddRawChar = (const lean_object*)&l_String_instHAddRawChar___closed__0_value;
LEAN_EXPORT lean_object* l_String_instHAddCharRaw___lam__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddCharRaw___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_instHAddCharRaw___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_instHAddCharRaw___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_instHAddCharRaw___closed__0 = (const lean_object*)&l_String_instHAddCharRaw___closed__0_value;
LEAN_EXPORT const lean_object* l_String_instHAddCharRaw = (const lean_object*)&l_String_instHAddCharRaw___closed__0_value;
LEAN_EXPORT lean_object* l_String_instHAddRaw___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddRaw___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_instHAddRaw___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_instHAddRaw___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_instHAddRaw___closed__0 = (const lean_object*)&l_String_instHAddRaw___closed__0_value;
LEAN_EXPORT const lean_object* l_String_instHAddRaw = (const lean_object*)&l_String_instHAddRaw___closed__0_value;
LEAN_EXPORT lean_object* l_String_instHAddRaw__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddRaw__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_instHAddRaw__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_instHAddRaw__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_instHAddRaw__1___closed__0 = (const lean_object*)&l_String_instHAddRaw__1___closed__0_value;
LEAN_EXPORT const lean_object* l_String_instHAddRaw__1 = (const lean_object*)&l_String_instHAddRaw__1___closed__0_value;
LEAN_EXPORT lean_object* l_String_instLERaw;
LEAN_EXPORT lean_object* l_String_instLTRaw;
LEAN_EXPORT uint8_t l_String_instDecidableLeRaw(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableLeRaw___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableLtRaw(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableLtRaw___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_byteDistance(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_byteDistance___boxed(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_getUTF8Byte___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_getUtf8Byte___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetBy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetBy___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_unoffsetBy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_unoffsetBy___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_increaseBy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_increaseBy___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_decreaseBy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_decreaseBy___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_inc(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_inc___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_dec(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_dec___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_min(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_min___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_string_pos_min(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHSubRaw___lam__0(lean_object* v_p_1_, lean_object* v_s_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_string_utf8_byte_size(v_s_2_);
v___x_4_ = lean_nat_sub(v_p_1_, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_String_instHSubRaw___lam__0___boxed(lean_object* v_p_5_, lean_object* v_s_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_String_instHSubRaw___lam__0(v_p_5_, v_s_6_);
lean_dec_ref(v_s_6_);
lean_dec(v_p_5_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_String_instHSubRawChar___lam__0(lean_object* v_p_10_, uint32_t v_c_11_){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = l_Char_utf8Size(v_c_11_);
v___x_13_ = lean_nat_sub(v_p_10_, v___x_12_);
lean_dec(v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_String_instHSubRawChar___lam__0___boxed(lean_object* v_p_14_, lean_object* v_c_15_){
_start:
{
uint32_t v_c_boxed_16_; lean_object* v_res_17_; 
v_c_boxed_16_ = lean_unbox_uint32(v_c_15_);
lean_dec(v_c_15_);
v_res_17_ = l_String_instHSubRawChar___lam__0(v_p_14_, v_c_boxed_16_);
lean_dec(v_p_14_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* lean_string_pos_sub(lean_object* v_p_u2081_20_, lean_object* v_p_u2082_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lean_nat_sub(v_p_u2081_20_, v_p_u2082_21_);
lean_dec(v_p_u2082_21_);
lean_dec(v_p_u2081_20_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRawChar___lam__0(lean_object* v_p_23_, uint32_t v_c_24_){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = l_Char_utf8Size(v_c_24_);
v___x_26_ = lean_nat_add(v_p_23_, v___x_25_);
lean_dec(v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRawChar___lam__0___boxed(lean_object* v_p_27_, lean_object* v_c_28_){
_start:
{
uint32_t v_c_boxed_29_; lean_object* v_res_30_; 
v_c_boxed_29_ = lean_unbox_uint32(v_c_28_);
lean_dec(v_c_28_);
v_res_30_ = l_String_instHAddRawChar___lam__0(v_p_27_, v_c_boxed_29_);
lean_dec(v_p_27_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddCharRaw___lam__0(uint32_t v_c_33_, lean_object* v_p_34_){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = l_Char_utf8Size(v_c_33_);
v___x_36_ = lean_nat_add(v___x_35_, v_p_34_);
lean_dec(v___x_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddCharRaw___lam__0___boxed(lean_object* v_c_37_, lean_object* v_p_38_){
_start:
{
uint32_t v_c_boxed_39_; lean_object* v_res_40_; 
v_c_boxed_39_ = lean_unbox_uint32(v_c_37_);
lean_dec(v_c_37_);
v_res_40_ = l_String_instHAddCharRaw___lam__0(v_c_boxed_39_, v_p_38_);
lean_dec(v_p_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRaw___lam__0(lean_object* v_s_43_, lean_object* v_p_44_){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_string_utf8_byte_size(v_s_43_);
v___x_46_ = lean_nat_add(v___x_45_, v_p_44_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRaw___lam__0___boxed(lean_object* v_s_47_, lean_object* v_p_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_String_instHAddRaw___lam__0(v_s_47_, v_p_48_);
lean_dec(v_p_48_);
lean_dec_ref(v_s_47_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRaw__1___lam__0(lean_object* v_p_52_, lean_object* v_s_53_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_string_utf8_byte_size(v_s_53_);
v___x_55_ = lean_nat_add(v_p_52_, v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRaw__1___lam__0___boxed(lean_object* v_p_56_, lean_object* v_s_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_String_instHAddRaw__1___lam__0(v_p_56_, v_s_57_);
lean_dec_ref(v_s_57_);
lean_dec(v_p_56_);
return v_res_58_;
}
}
static lean_object* _init_l_String_instLERaw(void){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lean_box(0);
return v___x_61_;
}
}
static lean_object* _init_l_String_instLTRaw(void){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = lean_box(0);
return v___x_62_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLeRaw(lean_object* v_p_u2081_63_, lean_object* v_p_u2082_64_){
_start:
{
uint8_t v___x_65_; 
v___x_65_ = lean_nat_dec_le(v_p_u2081_63_, v_p_u2082_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLeRaw___boxed(lean_object* v_p_u2081_66_, lean_object* v_p_u2082_67_){
_start:
{
uint8_t v_res_68_; lean_object* v_r_69_; 
v_res_68_ = l_String_instDecidableLeRaw(v_p_u2081_66_, v_p_u2082_67_);
lean_dec(v_p_u2082_67_);
lean_dec(v_p_u2081_66_);
v_r_69_ = lean_box(v_res_68_);
return v_r_69_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtRaw(lean_object* v_p_u2081_70_, lean_object* v_p_u2082_71_){
_start:
{
uint8_t v___x_72_; 
v___x_72_ = lean_nat_dec_lt(v_p_u2081_70_, v_p_u2082_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtRaw___boxed(lean_object* v_p_u2081_73_, lean_object* v_p_u2082_74_){
_start:
{
uint8_t v_res_75_; lean_object* v_r_76_; 
v_res_75_ = l_String_instDecidableLtRaw(v_p_u2081_73_, v_p_u2082_74_);
lean_dec(v_p_u2082_74_);
lean_dec(v_p_u2081_73_);
v_r_76_ = lean_box(v_res_75_);
return v_r_76_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_byteDistance(lean_object* v_lo_77_, lean_object* v_hi_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_nat_sub(v_hi_78_, v_lo_77_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_byteDistance___boxed(lean_object* v_lo_80_, lean_object* v_hi_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_String_Pos_Raw_byteDistance(v_lo_80_, v_hi_81_);
lean_dec(v_hi_81_);
lean_dec(v_lo_80_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_String_getUTF8Byte___boxed(lean_object* v_s_86_, lean_object* v_p_87_, lean_object* v_h_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = lean_string_get_byte_fast(v_s_86_, v_p_87_);
lean_dec_ref(v_s_86_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
LEAN_EXPORT lean_object* l_String_getUtf8Byte___boxed(lean_object* v_s_94_, lean_object* v_p_95_, lean_object* v_h_96_){
_start:
{
uint8_t v_res_97_; lean_object* v_r_98_; 
v_res_97_ = lean_string_get_byte_fast(v_s_94_, v_p_95_);
v_r_98_ = lean_box(v_res_97_);
return v_r_98_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetBy(lean_object* v_p_99_, lean_object* v_offset_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = lean_nat_add(v_offset_100_, v_p_99_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetBy___boxed(lean_object* v_p_102_, lean_object* v_offset_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_String_Pos_Raw_offsetBy(v_p_102_, v_offset_103_);
lean_dec(v_offset_103_);
lean_dec(v_p_102_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_unoffsetBy(lean_object* v_p_105_, lean_object* v_offset_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = lean_nat_sub(v_p_105_, v_offset_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_unoffsetBy___boxed(lean_object* v_p_108_, lean_object* v_offset_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_String_Pos_Raw_unoffsetBy(v_p_108_, v_offset_109_);
lean_dec(v_offset_109_);
lean_dec(v_p_108_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_increaseBy(lean_object* v_p_111_, lean_object* v_n_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lean_nat_add(v_p_111_, v_n_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_increaseBy___boxed(lean_object* v_p_114_, lean_object* v_n_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_String_Pos_Raw_increaseBy(v_p_114_, v_n_115_);
lean_dec(v_n_115_);
lean_dec(v_p_114_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_decreaseBy(lean_object* v_p_117_, lean_object* v_n_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = lean_nat_sub(v_p_117_, v_n_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_decreaseBy___boxed(lean_object* v_p_120_, lean_object* v_n_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_String_Pos_Raw_decreaseBy(v_p_120_, v_n_121_);
lean_dec(v_n_121_);
lean_dec(v_p_120_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_inc(lean_object* v_p_123_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(1u);
v___x_125_ = lean_nat_add(v_p_123_, v___x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_inc___boxed(lean_object* v_p_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_String_Pos_Raw_inc(v_p_126_);
lean_dec(v_p_126_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_dec(lean_object* v_p_128_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_unsigned_to_nat(1u);
v___x_130_ = lean_nat_sub(v_p_128_, v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_dec___boxed(lean_object* v_p_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_String_Pos_Raw_dec(v_p_131_);
lean_dec(v_p_131_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_min(lean_object* v_p_u2081_133_, lean_object* v_p_u2082_134_){
_start:
{
uint8_t v___x_135_; 
v___x_135_ = lean_nat_dec_le(v_p_u2081_133_, v_p_u2082_134_);
if (v___x_135_ == 0)
{
lean_inc(v_p_u2082_134_);
return v_p_u2082_134_;
}
else
{
lean_inc(v_p_u2081_133_);
return v_p_u2081_133_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_min___boxed(lean_object* v_p_u2081_136_, lean_object* v_p_u2082_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_String_Pos_Raw_min(v_p_u2081_136_, v_p_u2082_137_);
lean_dec(v_p_u2082_137_);
lean_dec(v_p_u2081_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* lean_string_pos_min(lean_object* v_p_u2081_139_, lean_object* v_p_u2082_140_){
_start:
{
uint8_t v___x_141_; 
v___x_141_ = lean_nat_dec_le(v_p_u2081_139_, v_p_u2082_140_);
if (v___x_141_ == 0)
{
lean_dec(v_p_u2081_139_);
return v_p_u2082_140_;
}
else
{
lean_dec(v_p_u2082_140_);
return v_p_u2081_139_;
}
}
}
lean_object* runtime_initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_PosRaw(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_ByteArray_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_String_instLERaw = _init_l_String_instLERaw();
lean_mark_persistent(l_String_instLERaw);
l_String_instLTRaw = _init_l_String_instLTRaw();
lean_mark_persistent(l_String_instLTRaw);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_PosRaw(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_PosRaw(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ByteArray_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_PosRaw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_PosRaw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_PosRaw(builtin);
}
#ifdef __cplusplus
}
#endif

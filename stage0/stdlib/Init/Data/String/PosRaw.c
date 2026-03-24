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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Char_utf8Size(uint32_t);
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
LEAN_EXPORT uint8_t l_String_instDecidableLtRaw___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableLtRaw___aux__1___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_String_instDecidableLtRaw___aux__1(lean_object* v_p_u2081_70_, lean_object* v_p_u2082_71_){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_nat_add(v_p_u2081_70_, v___x_72_);
v___x_74_ = lean_nat_dec_le(v___x_73_, v_p_u2082_71_);
lean_dec(v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtRaw___aux__1___boxed(lean_object* v_p_u2081_75_, lean_object* v_p_u2082_76_){
_start:
{
uint8_t v_res_77_; lean_object* v_r_78_; 
v_res_77_ = l_String_instDecidableLtRaw___aux__1(v_p_u2081_75_, v_p_u2082_76_);
lean_dec(v_p_u2082_76_);
lean_dec(v_p_u2081_75_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtRaw(lean_object* v_p_u2081_79_, lean_object* v_p_u2082_80_){
_start:
{
uint8_t v___x_81_; 
v___x_81_ = l_String_instDecidableLtRaw___aux__1(v_p_u2081_79_, v_p_u2082_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtRaw___boxed(lean_object* v_p_u2081_82_, lean_object* v_p_u2082_83_){
_start:
{
uint8_t v_res_84_; lean_object* v_r_85_; 
v_res_84_ = l_String_instDecidableLtRaw(v_p_u2081_82_, v_p_u2082_83_);
lean_dec(v_p_u2082_83_);
lean_dec(v_p_u2081_82_);
v_r_85_ = lean_box(v_res_84_);
return v_r_85_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_byteDistance(lean_object* v_lo_86_, lean_object* v_hi_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lean_nat_sub(v_hi_87_, v_lo_86_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_byteDistance___boxed(lean_object* v_lo_89_, lean_object* v_hi_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_String_Pos_Raw_byteDistance(v_lo_89_, v_hi_90_);
lean_dec(v_hi_90_);
lean_dec(v_lo_89_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_String_getUTF8Byte___boxed(lean_object* v_s_95_, lean_object* v_p_96_, lean_object* v_h_97_){
_start:
{
uint8_t v_res_98_; lean_object* v_r_99_; 
v_res_98_ = lean_string_get_byte_fast(v_s_95_, v_p_96_);
lean_dec_ref(v_s_95_);
v_r_99_ = lean_box(v_res_98_);
return v_r_99_;
}
}
LEAN_EXPORT lean_object* l_String_getUtf8Byte___boxed(lean_object* v_s_103_, lean_object* v_p_104_, lean_object* v_h_105_){
_start:
{
uint8_t v_res_106_; lean_object* v_r_107_; 
v_res_106_ = lean_string_get_byte_fast(v_s_103_, v_p_104_);
v_r_107_ = lean_box(v_res_106_);
return v_r_107_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetBy(lean_object* v_p_108_, lean_object* v_offset_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_nat_add(v_offset_109_, v_p_108_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetBy___boxed(lean_object* v_p_111_, lean_object* v_offset_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_String_Pos_Raw_offsetBy(v_p_111_, v_offset_112_);
lean_dec(v_offset_112_);
lean_dec(v_p_111_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_unoffsetBy(lean_object* v_p_114_, lean_object* v_offset_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_nat_sub(v_p_114_, v_offset_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_unoffsetBy___boxed(lean_object* v_p_117_, lean_object* v_offset_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_String_Pos_Raw_unoffsetBy(v_p_117_, v_offset_118_);
lean_dec(v_offset_118_);
lean_dec(v_p_117_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_increaseBy(lean_object* v_p_120_, lean_object* v_n_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = lean_nat_add(v_p_120_, v_n_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_increaseBy___boxed(lean_object* v_p_123_, lean_object* v_n_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_String_Pos_Raw_increaseBy(v_p_123_, v_n_124_);
lean_dec(v_n_124_);
lean_dec(v_p_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_decreaseBy(lean_object* v_p_126_, lean_object* v_n_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = lean_nat_sub(v_p_126_, v_n_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_decreaseBy___boxed(lean_object* v_p_129_, lean_object* v_n_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_String_Pos_Raw_decreaseBy(v_p_129_, v_n_130_);
lean_dec(v_n_130_);
lean_dec(v_p_129_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_inc(lean_object* v_p_132_){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = lean_unsigned_to_nat(1u);
v___x_134_ = lean_nat_add(v_p_132_, v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_inc___boxed(lean_object* v_p_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_String_Pos_Raw_inc(v_p_135_);
lean_dec(v_p_135_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_dec(lean_object* v_p_137_){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_unsigned_to_nat(1u);
v___x_139_ = lean_nat_sub(v_p_137_, v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_dec___boxed(lean_object* v_p_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_String_Pos_Raw_dec(v_p_140_);
lean_dec(v_p_140_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_min(lean_object* v_p_u2081_142_, lean_object* v_p_u2082_143_){
_start:
{
uint8_t v___x_144_; 
v___x_144_ = lean_nat_dec_le(v_p_u2081_142_, v_p_u2082_143_);
if (v___x_144_ == 0)
{
lean_inc(v_p_u2082_143_);
return v_p_u2082_143_;
}
else
{
lean_inc(v_p_u2081_142_);
return v_p_u2081_142_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_min___boxed(lean_object* v_p_u2081_145_, lean_object* v_p_u2082_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_String_Pos_Raw_min(v_p_u2081_145_, v_p_u2082_146_);
lean_dec(v_p_u2082_146_);
lean_dec(v_p_u2081_145_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* lean_string_pos_min(lean_object* v_p_u2081_148_, lean_object* v_p_u2082_149_){
_start:
{
uint8_t v___x_150_; 
v___x_150_ = lean_nat_dec_le(v_p_u2081_148_, v_p_u2082_149_);
if (v___x_150_ == 0)
{
lean_dec(v_p_u2081_148_);
return v_p_u2082_149_;
}
else
{
lean_dec(v_p_u2082_149_);
return v_p_u2081_148_;
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

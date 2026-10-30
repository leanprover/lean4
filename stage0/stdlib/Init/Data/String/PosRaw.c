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
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
uint32_t v___x_12_; uint8_t v___x_13_; 
v___x_12_ = 127;
v___x_13_ = lean_uint32_dec_le(v_c_11_, v___x_12_);
if (v___x_13_ == 0)
{
uint32_t v___x_14_; uint8_t v___x_15_; 
v___x_14_ = 2047;
v___x_15_ = lean_uint32_dec_le(v_c_11_, v___x_14_);
if (v___x_15_ == 0)
{
uint32_t v___x_16_; uint8_t v___x_17_; 
v___x_16_ = 65535;
v___x_17_ = lean_uint32_dec_le(v_c_11_, v___x_16_);
if (v___x_17_ == 0)
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_unsigned_to_nat(4u);
v___x_19_ = lean_nat_sub(v_p_10_, v___x_18_);
return v___x_19_;
}
else
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = lean_unsigned_to_nat(3u);
v___x_21_ = lean_nat_sub(v_p_10_, v___x_20_);
return v___x_21_;
}
}
else
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_unsigned_to_nat(2u);
v___x_23_ = lean_nat_sub(v_p_10_, v___x_22_);
return v___x_23_;
}
}
else
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = lean_unsigned_to_nat(1u);
v___x_25_ = lean_nat_sub(v_p_10_, v___x_24_);
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* l_String_instHSubRawChar___lam__0___boxed(lean_object* v_p_26_, lean_object* v_c_27_){
_start:
{
uint32_t v_c_boxed_28_; lean_object* v_res_29_; 
v_c_boxed_28_ = lean_unbox_uint32(v_c_27_);
lean_dec(v_c_27_);
v_res_29_ = l_String_instHSubRawChar___lam__0(v_p_26_, v_c_boxed_28_);
lean_dec(v_p_26_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* lean_string_pos_sub(lean_object* v_p_u2081_32_, lean_object* v_p_u2082_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lean_nat_sub(v_p_u2081_32_, v_p_u2082_33_);
lean_dec(v_p_u2082_33_);
lean_dec(v_p_u2081_32_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRawChar___lam__0(lean_object* v_p_35_, uint32_t v_c_36_){
_start:
{
uint32_t v___x_37_; uint8_t v___x_38_; 
v___x_37_ = 127;
v___x_38_ = lean_uint32_dec_le(v_c_36_, v___x_37_);
if (v___x_38_ == 0)
{
uint32_t v___x_39_; uint8_t v___x_40_; 
v___x_39_ = 2047;
v___x_40_ = lean_uint32_dec_le(v_c_36_, v___x_39_);
if (v___x_40_ == 0)
{
uint32_t v___x_41_; uint8_t v___x_42_; 
v___x_41_ = 65535;
v___x_42_ = lean_uint32_dec_le(v_c_36_, v___x_41_);
if (v___x_42_ == 0)
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = lean_unsigned_to_nat(4u);
v___x_44_ = lean_nat_add(v_p_35_, v___x_43_);
return v___x_44_;
}
else
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_unsigned_to_nat(3u);
v___x_46_ = lean_nat_add(v_p_35_, v___x_45_);
return v___x_46_;
}
}
else
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_unsigned_to_nat(2u);
v___x_48_ = lean_nat_add(v_p_35_, v___x_47_);
return v___x_48_;
}
}
else
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = lean_unsigned_to_nat(1u);
v___x_50_ = lean_nat_add(v_p_35_, v___x_49_);
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l_String_instHAddRawChar___lam__0___boxed(lean_object* v_p_51_, lean_object* v_c_52_){
_start:
{
uint32_t v_c_boxed_53_; lean_object* v_res_54_; 
v_c_boxed_53_ = lean_unbox_uint32(v_c_52_);
lean_dec(v_c_52_);
v_res_54_ = l_String_instHAddRawChar___lam__0(v_p_51_, v_c_boxed_53_);
lean_dec(v_p_51_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddCharRaw___lam__0(uint32_t v_c_57_, lean_object* v_p_58_){
_start:
{
uint32_t v___x_59_; uint8_t v___x_60_; 
v___x_59_ = 127;
v___x_60_ = lean_uint32_dec_le(v_c_57_, v___x_59_);
if (v___x_60_ == 0)
{
uint32_t v___x_61_; uint8_t v___x_62_; 
v___x_61_ = 2047;
v___x_62_ = lean_uint32_dec_le(v_c_57_, v___x_61_);
if (v___x_62_ == 0)
{
uint32_t v___x_63_; uint8_t v___x_64_; 
v___x_63_ = 65535;
v___x_64_ = lean_uint32_dec_le(v_c_57_, v___x_63_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_unsigned_to_nat(4u);
v___x_66_ = lean_nat_add(v___x_65_, v_p_58_);
return v___x_66_;
}
else
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_unsigned_to_nat(3u);
v___x_68_ = lean_nat_add(v___x_67_, v_p_58_);
return v___x_68_;
}
}
else
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_unsigned_to_nat(2u);
v___x_70_ = lean_nat_add(v___x_69_, v_p_58_);
return v___x_70_;
}
}
else
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_unsigned_to_nat(1u);
v___x_72_ = lean_nat_add(v___x_71_, v_p_58_);
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l_String_instHAddCharRaw___lam__0___boxed(lean_object* v_c_73_, lean_object* v_p_74_){
_start:
{
uint32_t v_c_boxed_75_; lean_object* v_res_76_; 
v_c_boxed_75_ = lean_unbox_uint32(v_c_73_);
lean_dec(v_c_73_);
v_res_76_ = l_String_instHAddCharRaw___lam__0(v_c_boxed_75_, v_p_74_);
lean_dec(v_p_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRaw___lam__0(lean_object* v_s_79_, lean_object* v_p_80_){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = lean_string_utf8_byte_size(v_s_79_);
v___x_82_ = lean_nat_add(v___x_81_, v_p_80_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRaw___lam__0___boxed(lean_object* v_s_83_, lean_object* v_p_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_String_instHAddRaw___lam__0(v_s_83_, v_p_84_);
lean_dec(v_p_84_);
lean_dec_ref(v_s_83_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRaw__1___lam__0(lean_object* v_p_88_, lean_object* v_s_89_){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_string_utf8_byte_size(v_s_89_);
v___x_91_ = lean_nat_add(v_p_88_, v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRaw__1___lam__0___boxed(lean_object* v_p_92_, lean_object* v_s_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_String_instHAddRaw__1___lam__0(v_p_92_, v_s_93_);
lean_dec_ref(v_s_93_);
lean_dec(v_p_92_);
return v_res_94_;
}
}
static lean_object* _init_l_String_instLERaw(void){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lean_box(0);
return v___x_97_;
}
}
static lean_object* _init_l_String_instLTRaw(void){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_box(0);
return v___x_98_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLeRaw(lean_object* v_p_u2081_99_, lean_object* v_p_u2082_100_){
_start:
{
uint8_t v___x_101_; 
v___x_101_ = lean_nat_dec_le(v_p_u2081_99_, v_p_u2082_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLeRaw___boxed(lean_object* v_p_u2081_102_, lean_object* v_p_u2082_103_){
_start:
{
uint8_t v_res_104_; lean_object* v_r_105_; 
v_res_104_ = l_String_instDecidableLeRaw(v_p_u2081_102_, v_p_u2082_103_);
lean_dec(v_p_u2082_103_);
lean_dec(v_p_u2081_102_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtRaw(lean_object* v_p_u2081_106_, lean_object* v_p_u2082_107_){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_108_ = lean_unsigned_to_nat(1u);
v___x_109_ = lean_nat_add(v_p_u2081_106_, v___x_108_);
v___x_110_ = lean_nat_dec_le(v___x_109_, v_p_u2082_107_);
lean_dec(v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtRaw___boxed(lean_object* v_p_u2081_111_, lean_object* v_p_u2082_112_){
_start:
{
uint8_t v_res_113_; lean_object* v_r_114_; 
v_res_113_ = l_String_instDecidableLtRaw(v_p_u2081_111_, v_p_u2082_112_);
lean_dec(v_p_u2082_112_);
lean_dec(v_p_u2081_111_);
v_r_114_ = lean_box(v_res_113_);
return v_r_114_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_byteDistance(lean_object* v_lo_115_, lean_object* v_hi_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = lean_nat_sub(v_hi_116_, v_lo_115_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_byteDistance___boxed(lean_object* v_lo_118_, lean_object* v_hi_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_String_Pos_Raw_byteDistance(v_lo_118_, v_hi_119_);
lean_dec(v_hi_119_);
lean_dec(v_lo_118_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_String_getUTF8Byte___boxed(lean_object* v_s_124_, lean_object* v_p_125_, lean_object* v_h_126_){
_start:
{
uint8_t v_res_127_; lean_object* v_r_128_; 
v_res_127_ = lean_string_get_byte_fast(v_s_124_, v_p_125_);
lean_dec_ref(v_s_124_);
v_r_128_ = lean_box(v_res_127_);
return v_r_128_;
}
}
LEAN_EXPORT lean_object* l_String_getUtf8Byte___boxed(lean_object* v_s_132_, lean_object* v_p_133_, lean_object* v_h_134_){
_start:
{
uint8_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = lean_string_get_byte_fast(v_s_132_, v_p_133_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetBy(lean_object* v_p_137_, lean_object* v_offset_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = lean_nat_add(v_offset_138_, v_p_137_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetBy___boxed(lean_object* v_p_140_, lean_object* v_offset_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_String_Pos_Raw_offsetBy(v_p_140_, v_offset_141_);
lean_dec(v_offset_141_);
lean_dec(v_p_140_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_unoffsetBy(lean_object* v_p_143_, lean_object* v_offset_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = lean_nat_sub(v_p_143_, v_offset_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_unoffsetBy___boxed(lean_object* v_p_146_, lean_object* v_offset_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_String_Pos_Raw_unoffsetBy(v_p_146_, v_offset_147_);
lean_dec(v_offset_147_);
lean_dec(v_p_146_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_increaseBy(lean_object* v_p_149_, lean_object* v_n_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lean_nat_add(v_p_149_, v_n_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_increaseBy___boxed(lean_object* v_p_152_, lean_object* v_n_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_String_Pos_Raw_increaseBy(v_p_152_, v_n_153_);
lean_dec(v_n_153_);
lean_dec(v_p_152_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_decreaseBy(lean_object* v_p_155_, lean_object* v_n_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = lean_nat_sub(v_p_155_, v_n_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_decreaseBy___boxed(lean_object* v_p_158_, lean_object* v_n_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_String_Pos_Raw_decreaseBy(v_p_158_, v_n_159_);
lean_dec(v_n_159_);
lean_dec(v_p_158_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_inc(lean_object* v_p_161_){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_unsigned_to_nat(1u);
v___x_163_ = lean_nat_add(v_p_161_, v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_inc___boxed(lean_object* v_p_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_String_Pos_Raw_inc(v_p_164_);
lean_dec(v_p_164_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_dec(lean_object* v_p_166_){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = lean_unsigned_to_nat(1u);
v___x_168_ = lean_nat_sub(v_p_166_, v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_dec___boxed(lean_object* v_p_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_String_Pos_Raw_dec(v_p_169_);
lean_dec(v_p_169_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_min(lean_object* v_p_u2081_171_, lean_object* v_p_u2082_172_){
_start:
{
uint8_t v___x_173_; 
v___x_173_ = lean_nat_dec_le(v_p_u2081_171_, v_p_u2082_172_);
if (v___x_173_ == 0)
{
lean_inc(v_p_u2082_172_);
return v_p_u2082_172_;
}
else
{
lean_inc(v_p_u2081_171_);
return v_p_u2081_171_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_min___boxed(lean_object* v_p_u2081_174_, lean_object* v_p_u2082_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_String_Pos_Raw_min(v_p_u2081_174_, v_p_u2082_175_);
lean_dec(v_p_u2082_175_);
lean_dec(v_p_u2081_174_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* lean_string_pos_min(lean_object* v_p_u2081_177_, lean_object* v_p_u2082_178_){
_start:
{
uint8_t v___x_179_; 
v___x_179_ = lean_nat_dec_le(v_p_u2081_177_, v_p_u2082_178_);
if (v___x_179_ == 0)
{
lean_dec(v_p_u2081_177_);
return v_p_u2082_178_;
}
else
{
lean_dec(v_p_u2082_178_);
return v_p_u2081_177_;
}
}
}
lean_object* runtime_initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_PosRaw(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

// Lean compiler output
// Module: Lake.Util.String
// Imports: public import Init.Data.ToString.Basic import Init.Data.UInt.Lemmas import Init.Data.String.Basic import Init.Data.Nat.Fold
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
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
uint8_t lean_uint8_add(uint8_t, uint8_t);
uint32_t lean_uint8_to_uint32(uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_mk_empty_byte_array(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_land(uint64_t, uint64_t);
uint8_t lean_uint64_to_uint8(uint64_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lake_lpad_spec__0(uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lake_lpad_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_lpad___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_lpad___closed__0 = (const lean_object*)&l_Lake_lpad___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_lpad(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_lpad___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_rpad(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_rpad___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_zpad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_zpad___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_isHex(lean_object*);
LEAN_EXPORT lean_object* l_Lake_isHex___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Util_String_0__Lake_lowerHexByte(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Util_String_0__Lake_lowerHexByte___boxed(lean_object*);
LEAN_EXPORT uint32_t l___private_Lake_Util_String_0__Lake_lowerHexChar(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Util_String_0__Lake_lowerHexChar___boxed(lean_object*);
static lean_once_cell_t l_Lake_lowerHexUInt64___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_lowerHexUInt64___closed__0;
static lean_once_cell_t l_Lake_lowerHexUInt64___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_lowerHexUInt64___closed__1;
LEAN_EXPORT lean_object* l_Lake_lowerHexUInt64(uint64_t);
LEAN_EXPORT lean_object* l_Lake_lowerHexUInt64___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lake_lpad_spec__0(uint32_t v_c_1_, lean_object* v_x_2_, lean_object* v_x_3_){
_start:
{
lean_object* v_zero_4_; uint8_t v_isZero_5_; 
v_zero_4_ = lean_unsigned_to_nat(0u);
v_isZero_5_ = lean_nat_dec_eq(v_x_2_, v_zero_4_);
if (v_isZero_5_ == 1)
{
lean_dec(v_x_2_);
return v_x_3_;
}
else
{
lean_object* v_one_6_; lean_object* v_n_7_; lean_object* v___x_8_; 
v_one_6_ = lean_unsigned_to_nat(1u);
v_n_7_ = lean_nat_sub(v_x_2_, v_one_6_);
lean_dec(v_x_2_);
v___x_8_ = lean_string_push(v_x_3_, v_c_1_);
v_x_2_ = v_n_7_;
v_x_3_ = v___x_8_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lake_lpad_spec__0___boxed(lean_object* v_c_10_, lean_object* v_x_11_, lean_object* v_x_12_){
_start:
{
uint32_t v_c_boxed_13_; lean_object* v_res_14_; 
v_c_boxed_13_ = lean_unbox_uint32(v_c_10_);
lean_dec(v_c_10_);
v_res_14_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lake_lpad_spec__0(v_c_boxed_13_, v_x_11_, v_x_12_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lake_lpad(lean_object* v_s_16_, uint32_t v_c_17_, lean_object* v_len_18_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_19_ = ((lean_object*)(l_Lake_lpad___closed__0));
v___x_20_ = lean_string_length(v_s_16_);
v___x_21_ = lean_nat_sub(v_len_18_, v___x_20_);
v___x_22_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lake_lpad_spec__0(v_c_17_, v___x_21_, v___x_19_);
v___x_23_ = lean_string_append(v___x_22_, v_s_16_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lake_lpad___boxed(lean_object* v_s_24_, lean_object* v_c_25_, lean_object* v_len_26_){
_start:
{
uint32_t v_c_boxed_27_; lean_object* v_res_28_; 
v_c_boxed_27_ = lean_unbox_uint32(v_c_25_);
lean_dec(v_c_25_);
v_res_28_ = l_Lake_lpad(v_s_24_, v_c_boxed_27_, v_len_26_);
lean_dec(v_len_26_);
lean_dec_ref(v_s_24_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lake_rpad(lean_object* v_s_29_, uint32_t v_c_30_, lean_object* v_len_31_){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_32_ = lean_string_length(v_s_29_);
v___x_33_ = lean_nat_sub(v_len_31_, v___x_32_);
v___x_34_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lake_lpad_spec__0(v_c_30_, v___x_33_, v_s_29_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lake_rpad___boxed(lean_object* v_s_35_, lean_object* v_c_36_, lean_object* v_len_37_){
_start:
{
uint32_t v_c_boxed_38_; lean_object* v_res_39_; 
v_c_boxed_38_ = lean_unbox_uint32(v_c_36_);
lean_dec(v_c_36_);
v_res_39_ = l_Lake_rpad(v_s_35_, v_c_boxed_38_, v_len_37_);
lean_dec(v_len_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lake_zpad(lean_object* v_n_40_, lean_object* v_len_41_){
_start:
{
lean_object* v___x_42_; uint32_t v___x_43_; lean_object* v___x_44_; 
v___x_42_ = l_Nat_reprFast(v_n_40_);
v___x_43_ = 48;
v___x_44_ = l_Lake_lpad(v___x_42_, v___x_43_, v_len_41_);
lean_dec_ref(v___x_42_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lake_zpad___boxed(lean_object* v_n_45_, lean_object* v_len_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lake_zpad(v_n_45_, v_len_46_);
lean_dec(v_len_46_);
return v_res_47_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0___redArg(lean_object* v_s_48_, lean_object* v_n_49_, lean_object* v_i_50_){
_start:
{
lean_object* v_zero_51_; uint8_t v_isZero_52_; 
v_zero_51_ = lean_unsigned_to_nat(0u);
v_isZero_52_ = lean_nat_dec_eq(v_i_50_, v_zero_51_);
if (v_isZero_52_ == 1)
{
lean_dec(v_i_50_);
return v_isZero_52_;
}
else
{
lean_object* v_one_53_; lean_object* v_n_54_; uint8_t v___y_56_; lean_object* v___x_58_; uint8_t v_c_59_; uint8_t v___x_60_; uint8_t v___x_61_; 
v_one_53_ = lean_unsigned_to_nat(1u);
v_n_54_ = lean_nat_sub(v_i_50_, v_one_53_);
v___x_58_ = lean_nat_sub(v_n_49_, v_i_50_);
lean_dec(v_i_50_);
v_c_59_ = lean_string_get_byte_fast(v_s_48_, v___x_58_);
v___x_60_ = 57;
v___x_61_ = lean_uint8_dec_le(v_c_59_, v___x_60_);
if (v___x_61_ == 0)
{
uint8_t v___x_62_; uint8_t v___x_63_; 
v___x_62_ = 102;
v___x_63_ = lean_uint8_dec_le(v_c_59_, v___x_62_);
if (v___x_63_ == 0)
{
uint8_t v___x_64_; uint8_t v___x_65_; 
v___x_64_ = 70;
v___x_65_ = lean_uint8_dec_le(v_c_59_, v___x_64_);
if (v___x_65_ == 0)
{
lean_dec(v_n_54_);
return v___x_65_;
}
else
{
uint8_t v___x_66_; uint8_t v___x_67_; 
v___x_66_ = 65;
v___x_67_ = lean_uint8_dec_le(v___x_66_, v_c_59_);
v___y_56_ = v___x_67_;
goto v___jp_55_;
}
}
else
{
uint8_t v___x_68_; uint8_t v___x_69_; 
v___x_68_ = 97;
v___x_69_ = lean_uint8_dec_le(v___x_68_, v_c_59_);
v___y_56_ = v___x_69_;
goto v___jp_55_;
}
}
else
{
uint8_t v___x_70_; uint8_t v___x_71_; 
v___x_70_ = 48;
v___x_71_ = lean_uint8_dec_le(v___x_70_, v_c_59_);
v___y_56_ = v___x_71_;
goto v___jp_55_;
}
v___jp_55_:
{
if (v___y_56_ == 0)
{
lean_dec(v_n_54_);
return v___y_56_;
}
else
{
v_i_50_ = v_n_54_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0___redArg___boxed(lean_object* v_s_72_, lean_object* v_n_73_, lean_object* v_i_74_){
_start:
{
uint8_t v_res_75_; lean_object* v_r_76_; 
v_res_75_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0___redArg(v_s_72_, v_n_73_, v_i_74_);
lean_dec(v_n_73_);
lean_dec_ref(v_s_72_);
v_r_76_ = lean_box(v_res_75_);
return v_r_76_;
}
}
LEAN_EXPORT uint8_t l_Lake_isHex(lean_object* v_s_77_){
_start:
{
lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_78_ = lean_string_utf8_byte_size(v_s_77_);
v___x_79_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0___redArg(v_s_77_, v___x_78_, v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lake_isHex___boxed(lean_object* v_s_80_){
_start:
{
uint8_t v_res_81_; lean_object* v_r_82_; 
v_res_81_ = l_Lake_isHex(v_s_80_);
lean_dec_ref(v_s_80_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0(lean_object* v_s_83_, lean_object* v_n_84_, lean_object* v_i_85_, lean_object* v_a_86_){
_start:
{
uint8_t v___x_87_; 
v___x_87_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0___redArg(v_s_83_, v_n_84_, v_i_85_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0___boxed(lean_object* v_s_88_, lean_object* v_n_89_, lean_object* v_i_90_, lean_object* v_a_91_){
_start:
{
uint8_t v_res_92_; lean_object* v_r_93_; 
v_res_92_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0(v_s_88_, v_n_89_, v_i_90_, v_a_91_);
lean_dec(v_n_89_);
lean_dec_ref(v_s_88_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Util_String_0__Lake_lowerHexByte(uint8_t v_n_94_){
_start:
{
uint8_t v___x_95_; uint8_t v___x_96_; 
v___x_95_ = 9;
v___x_96_ = lean_uint8_dec_le(v_n_94_, v___x_95_);
if (v___x_96_ == 0)
{
uint8_t v___x_97_; uint8_t v___x_98_; 
v___x_97_ = 87;
v___x_98_ = lean_uint8_add(v_n_94_, v___x_97_);
return v___x_98_;
}
else
{
uint8_t v___x_99_; uint8_t v___x_100_; 
v___x_99_ = 48;
v___x_100_ = lean_uint8_add(v_n_94_, v___x_99_);
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_String_0__Lake_lowerHexByte___boxed(lean_object* v_n_101_){
_start:
{
uint8_t v_n_boxed_102_; uint8_t v_res_103_; lean_object* v_r_104_; 
v_n_boxed_102_ = lean_unbox(v_n_101_);
v_res_103_ = l___private_Lake_Util_String_0__Lake_lowerHexByte(v_n_boxed_102_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
LEAN_EXPORT uint32_t l___private_Lake_Util_String_0__Lake_lowerHexChar(uint8_t v_n_105_){
_start:
{
uint8_t v___x_106_; uint32_t v___x_107_; 
v___x_106_ = l___private_Lake_Util_String_0__Lake_lowerHexByte(v_n_105_);
v___x_107_ = lean_uint8_to_uint32(v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_String_0__Lake_lowerHexChar___boxed(lean_object* v_n_108_){
_start:
{
uint8_t v_n_boxed_109_; uint32_t v_res_110_; lean_object* v_r_111_; 
v_n_boxed_109_ = lean_unbox(v_n_108_);
v_res_110_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v_n_boxed_109_);
v_r_111_ = lean_box_uint32(v_res_110_);
return v_r_111_;
}
}
static lean_object* _init_l_Lake_lowerHexUInt64___closed__0(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_unsigned_to_nat(16u);
v___x_113_ = lean_mk_empty_byte_array(v___x_112_);
return v___x_113_;
}
}
static lean_object* _init_l_Lake_lowerHexUInt64___closed__1(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = lean_obj_once(&l_Lake_lowerHexUInt64___closed__0, &l_Lake_lowerHexUInt64___closed__0_once, _init_l_Lake_lowerHexUInt64___closed__0);
v___x_115_ = lean_string_from_utf8_unchecked(v___x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lake_lowerHexUInt64(uint64_t v_n_116_){
_start:
{
lean_object* v___x_117_; uint64_t v___x_118_; uint64_t v___x_119_; uint64_t v___x_120_; uint64_t v___x_121_; uint8_t v___x_122_; uint32_t v___x_123_; lean_object* v___x_124_; uint64_t v___x_125_; uint64_t v___x_126_; uint64_t v___x_127_; uint8_t v___x_128_; uint32_t v___x_129_; lean_object* v___x_130_; uint64_t v___x_131_; uint64_t v___x_132_; uint64_t v___x_133_; uint8_t v___x_134_; uint32_t v___x_135_; lean_object* v___x_136_; uint64_t v___x_137_; uint64_t v___x_138_; uint64_t v___x_139_; uint8_t v___x_140_; uint32_t v___x_141_; lean_object* v___x_142_; uint64_t v___x_143_; uint64_t v___x_144_; uint64_t v___x_145_; uint8_t v___x_146_; uint32_t v___x_147_; lean_object* v___x_148_; uint64_t v___x_149_; uint64_t v___x_150_; uint64_t v___x_151_; uint8_t v___x_152_; uint32_t v___x_153_; lean_object* v___x_154_; uint64_t v___x_155_; uint64_t v___x_156_; uint64_t v___x_157_; uint8_t v___x_158_; uint32_t v___x_159_; lean_object* v___x_160_; uint64_t v___x_161_; uint64_t v___x_162_; uint64_t v___x_163_; uint8_t v___x_164_; uint32_t v___x_165_; lean_object* v___x_166_; uint64_t v___x_167_; uint64_t v___x_168_; uint64_t v___x_169_; uint8_t v___x_170_; uint32_t v___x_171_; lean_object* v___x_172_; uint64_t v___x_173_; uint64_t v___x_174_; uint64_t v___x_175_; uint8_t v___x_176_; uint32_t v___x_177_; lean_object* v___x_178_; uint64_t v___x_179_; uint64_t v___x_180_; uint64_t v___x_181_; uint8_t v___x_182_; uint32_t v___x_183_; lean_object* v___x_184_; uint64_t v___x_185_; uint64_t v___x_186_; uint64_t v___x_187_; uint8_t v___x_188_; uint32_t v___x_189_; lean_object* v___x_190_; uint64_t v___x_191_; uint64_t v___x_192_; uint64_t v___x_193_; uint8_t v___x_194_; uint32_t v___x_195_; lean_object* v___x_196_; uint64_t v___x_197_; uint64_t v___x_198_; uint64_t v___x_199_; uint8_t v___x_200_; uint32_t v___x_201_; lean_object* v___x_202_; uint64_t v___x_203_; uint64_t v___x_204_; uint64_t v___x_205_; uint8_t v___x_206_; uint32_t v___x_207_; lean_object* v___x_208_; uint64_t v___x_209_; uint8_t v___x_210_; uint32_t v___x_211_; lean_object* v___x_212_; 
v___x_117_ = lean_obj_once(&l_Lake_lowerHexUInt64___closed__1, &l_Lake_lowerHexUInt64___closed__1_once, _init_l_Lake_lowerHexUInt64___closed__1);
v___x_118_ = 60ULL;
v___x_119_ = lean_uint64_shift_right(v_n_116_, v___x_118_);
v___x_120_ = 15ULL;
v___x_121_ = lean_uint64_land(v___x_119_, v___x_120_);
v___x_122_ = lean_uint64_to_uint8(v___x_121_);
v___x_123_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_122_);
v___x_124_ = lean_string_push(v___x_117_, v___x_123_);
v___x_125_ = 56ULL;
v___x_126_ = lean_uint64_shift_right(v_n_116_, v___x_125_);
v___x_127_ = lean_uint64_land(v___x_126_, v___x_120_);
v___x_128_ = lean_uint64_to_uint8(v___x_127_);
v___x_129_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_128_);
v___x_130_ = lean_string_push(v___x_124_, v___x_129_);
v___x_131_ = 52ULL;
v___x_132_ = lean_uint64_shift_right(v_n_116_, v___x_131_);
v___x_133_ = lean_uint64_land(v___x_132_, v___x_120_);
v___x_134_ = lean_uint64_to_uint8(v___x_133_);
v___x_135_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_134_);
v___x_136_ = lean_string_push(v___x_130_, v___x_135_);
v___x_137_ = 48ULL;
v___x_138_ = lean_uint64_shift_right(v_n_116_, v___x_137_);
v___x_139_ = lean_uint64_land(v___x_138_, v___x_120_);
v___x_140_ = lean_uint64_to_uint8(v___x_139_);
v___x_141_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_140_);
v___x_142_ = lean_string_push(v___x_136_, v___x_141_);
v___x_143_ = 44ULL;
v___x_144_ = lean_uint64_shift_right(v_n_116_, v___x_143_);
v___x_145_ = lean_uint64_land(v___x_144_, v___x_120_);
v___x_146_ = lean_uint64_to_uint8(v___x_145_);
v___x_147_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_146_);
v___x_148_ = lean_string_push(v___x_142_, v___x_147_);
v___x_149_ = 40ULL;
v___x_150_ = lean_uint64_shift_right(v_n_116_, v___x_149_);
v___x_151_ = lean_uint64_land(v___x_150_, v___x_120_);
v___x_152_ = lean_uint64_to_uint8(v___x_151_);
v___x_153_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_152_);
v___x_154_ = lean_string_push(v___x_148_, v___x_153_);
v___x_155_ = 36ULL;
v___x_156_ = lean_uint64_shift_right(v_n_116_, v___x_155_);
v___x_157_ = lean_uint64_land(v___x_156_, v___x_120_);
v___x_158_ = lean_uint64_to_uint8(v___x_157_);
v___x_159_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_158_);
v___x_160_ = lean_string_push(v___x_154_, v___x_159_);
v___x_161_ = 32ULL;
v___x_162_ = lean_uint64_shift_right(v_n_116_, v___x_161_);
v___x_163_ = lean_uint64_land(v___x_162_, v___x_120_);
v___x_164_ = lean_uint64_to_uint8(v___x_163_);
v___x_165_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_164_);
v___x_166_ = lean_string_push(v___x_160_, v___x_165_);
v___x_167_ = 28ULL;
v___x_168_ = lean_uint64_shift_right(v_n_116_, v___x_167_);
v___x_169_ = lean_uint64_land(v___x_168_, v___x_120_);
v___x_170_ = lean_uint64_to_uint8(v___x_169_);
v___x_171_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_170_);
v___x_172_ = lean_string_push(v___x_166_, v___x_171_);
v___x_173_ = 24ULL;
v___x_174_ = lean_uint64_shift_right(v_n_116_, v___x_173_);
v___x_175_ = lean_uint64_land(v___x_174_, v___x_120_);
v___x_176_ = lean_uint64_to_uint8(v___x_175_);
v___x_177_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_176_);
v___x_178_ = lean_string_push(v___x_172_, v___x_177_);
v___x_179_ = 20ULL;
v___x_180_ = lean_uint64_shift_right(v_n_116_, v___x_179_);
v___x_181_ = lean_uint64_land(v___x_180_, v___x_120_);
v___x_182_ = lean_uint64_to_uint8(v___x_181_);
v___x_183_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_182_);
v___x_184_ = lean_string_push(v___x_178_, v___x_183_);
v___x_185_ = 16ULL;
v___x_186_ = lean_uint64_shift_right(v_n_116_, v___x_185_);
v___x_187_ = lean_uint64_land(v___x_186_, v___x_120_);
v___x_188_ = lean_uint64_to_uint8(v___x_187_);
v___x_189_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_188_);
v___x_190_ = lean_string_push(v___x_184_, v___x_189_);
v___x_191_ = 12ULL;
v___x_192_ = lean_uint64_shift_right(v_n_116_, v___x_191_);
v___x_193_ = lean_uint64_land(v___x_192_, v___x_120_);
v___x_194_ = lean_uint64_to_uint8(v___x_193_);
v___x_195_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_194_);
v___x_196_ = lean_string_push(v___x_190_, v___x_195_);
v___x_197_ = 8ULL;
v___x_198_ = lean_uint64_shift_right(v_n_116_, v___x_197_);
v___x_199_ = lean_uint64_land(v___x_198_, v___x_120_);
v___x_200_ = lean_uint64_to_uint8(v___x_199_);
v___x_201_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_200_);
v___x_202_ = lean_string_push(v___x_196_, v___x_201_);
v___x_203_ = 4ULL;
v___x_204_ = lean_uint64_shift_right(v_n_116_, v___x_203_);
v___x_205_ = lean_uint64_land(v___x_204_, v___x_120_);
v___x_206_ = lean_uint64_to_uint8(v___x_205_);
v___x_207_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_206_);
v___x_208_ = lean_string_push(v___x_202_, v___x_207_);
v___x_209_ = lean_uint64_land(v_n_116_, v___x_120_);
v___x_210_ = lean_uint64_to_uint8(v___x_209_);
v___x_211_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_210_);
v___x_212_ = lean_string_push(v___x_208_, v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lake_lowerHexUInt64___boxed(lean_object* v_n_213_){
_start:
{
uint64_t v_n_boxed_214_; lean_object* v_res_215_; 
v_n_boxed_214_ = lean_unbox_uint64(v_n_213_);
lean_dec_ref(v_n_213_);
v_res_215_ = l_Lake_lowerHexUInt64(v_n_boxed_214_);
return v_res_215_;
}
}
lean_object* runtime_initialize_Init_Data_ToString_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Fold(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_String(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Fold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_String(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Fold(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_String(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Fold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_String(builtin);
}
#ifdef __cplusplus
}
#endif

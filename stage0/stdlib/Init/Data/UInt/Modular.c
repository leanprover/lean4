// Lean compiler output
// Module: Init.Data.UInt.Modular
// Imports: public import Init.Data.UInt.Basic public import Init.Data.Nat.Gcd import Init.Data.UInt.Lemmas import Init.Data.Nat.Lemmas import Init.Data.Nat.Mod import Init.ByCases import Init.Omega import Init.WFTactics
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
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
uint64_t lean_uint64_mod(uint64_t, uint64_t);
uint64_t lean_uint64_div(uint64_t, uint64_t);
uint8_t lean_uint64_dec_le(uint64_t, uint64_t);
uint64_t lean_uint64_sub(uint64_t, uint64_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint64_t lean_uint64_mul_mod(uint64_t, uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_mulMod___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_UInt64_powMod(uint64_t, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_powMod___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt64_invMod_x3f_go(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt64_invMod_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt64_invMod_x3f(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_invMod_x3f___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_UInt_Modular_0__UInt64_wrapMod___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_wrapMod___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_wrapMod(uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_wrapMod___boxed(lean_object*);
LEAN_EXPORT uint64_t l_UInt64_powModWord(uint64_t, uint64_t, uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_powModWord___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt64_powModChunk(uint64_t, lean_object*, uint64_t, uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_powModChunk___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_UInt64_powModImpl_go(uint64_t, uint64_t, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_powModImpl_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_powModImpl_go_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_powModImpl_go_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_UInt64_powModImpl(uint64_t, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_powModImpl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt64_invModImpl_go(uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_invModImpl_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt64_invModImpl(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_invModImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_powModChunk_match__1_splitter___redArg(lean_object*, uint64_t, uint64_t, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_powModChunk_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_powModChunk_match__1_splitter(lean_object*, lean_object*, uint64_t, uint64_t, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_powModChunk_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt64_mulMod___boxed(lean_object* v_a_4_, lean_object* v_b_5_, lean_object* v_modulus_6_){
_start:
{
uint64_t v_a_boxed_7_; uint64_t v_b_boxed_8_; uint64_t v_modulus_boxed_9_; uint64_t v_res_10_; lean_object* v_r_11_; 
v_a_boxed_7_ = lean_unbox_uint64(v_a_4_);
lean_dec_ref(v_a_4_);
v_b_boxed_8_ = lean_unbox_uint64(v_b_5_);
lean_dec_ref(v_b_5_);
v_modulus_boxed_9_ = lean_unbox_uint64(v_modulus_6_);
lean_dec_ref(v_modulus_6_);
v_res_10_ = lean_uint64_mul_mod(v_a_boxed_7_, v_b_boxed_8_, v_modulus_boxed_9_);
v_r_11_ = lean_box_uint64(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT uint64_t l_UInt64_powMod(uint64_t v_base_12_, lean_object* v_exponent_13_, uint64_t v_modulus_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; uint64_t v___x_19_; 
v___x_15_ = lean_uint64_to_nat(v_base_12_);
v___x_16_ = lean_nat_pow(v___x_15_, v_exponent_13_);
lean_dec(v___x_15_);
v___x_17_ = lean_uint64_to_nat(v_modulus_14_);
v___x_18_ = lean_nat_mod(v___x_16_, v___x_17_);
lean_dec(v___x_17_);
lean_dec(v___x_16_);
v___x_19_ = lean_uint64_of_nat(v___x_18_);
lean_dec(v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_UInt64_powMod___boxed(lean_object* v_base_20_, lean_object* v_exponent_21_, lean_object* v_modulus_22_){
_start:
{
uint64_t v_base_boxed_23_; uint64_t v_modulus_boxed_24_; uint64_t v_res_25_; lean_object* v_r_26_; 
v_base_boxed_23_ = lean_unbox_uint64(v_base_20_);
lean_dec_ref(v_base_20_);
v_modulus_boxed_24_ = lean_unbox_uint64(v_modulus_22_);
lean_dec_ref(v_modulus_22_);
v_res_25_ = l_UInt64_powMod(v_base_boxed_23_, v_exponent_21_, v_modulus_boxed_24_);
lean_dec(v_exponent_21_);
v_r_26_ = lean_box_uint64(v_res_25_);
return v_r_26_;
}
}
LEAN_EXPORT lean_object* l_UInt64_invMod_x3f_go(uint64_t v_modulus_27_, lean_object* v_oldR_28_, lean_object* v_r_29_, lean_object* v_oldS_30_, lean_object* v_s_31_){
_start:
{
lean_object* v___y_33_; lean_object* v___x_36_; uint8_t v___x_37_; 
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = lean_nat_dec_eq(v_r_29_, v___x_36_);
if (v___x_37_ == 0)
{
lean_object* v_quotient_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v_product_41_; uint8_t v___x_42_; 
v_quotient_38_ = lean_nat_div(v_oldR_28_, v_r_29_);
v___x_39_ = lean_nat_mul(v_quotient_38_, v_s_31_);
lean_dec(v_quotient_38_);
v___x_40_ = lean_uint64_to_nat(v_modulus_27_);
v_product_41_ = lean_nat_mod(v___x_39_, v___x_40_);
lean_dec(v___x_39_);
v___x_42_ = lean_nat_dec_le(v_product_41_, v_oldS_30_);
if (v___x_42_ == 0)
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = lean_nat_sub(v_product_41_, v_oldS_30_);
lean_dec(v_oldS_30_);
lean_dec(v_product_41_);
v___x_44_ = lean_nat_sub(v___x_40_, v___x_43_);
lean_dec(v___x_43_);
lean_dec(v___x_40_);
v___y_33_ = v___x_44_;
goto v___jp_32_;
}
else
{
lean_object* v___x_45_; 
lean_dec(v___x_40_);
v___x_45_ = lean_nat_sub(v_oldS_30_, v_product_41_);
lean_dec(v_product_41_);
lean_dec(v_oldS_30_);
v___y_33_ = v___x_45_;
goto v___jp_32_;
}
}
else
{
lean_object* v___x_46_; 
lean_dec(v_s_31_);
lean_dec(v_r_29_);
v___x_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_46_, 0, v_oldR_28_);
lean_ctor_set(v___x_46_, 1, v_oldS_30_);
return v___x_46_;
}
v___jp_32_:
{
lean_object* v___x_34_; 
v___x_34_ = lean_nat_mod(v_oldR_28_, v_r_29_);
lean_dec(v_oldR_28_);
v_oldR_28_ = v_r_29_;
v_r_29_ = v___x_34_;
v_oldS_30_ = v_s_31_;
v_s_31_ = v___y_33_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_UInt64_invMod_x3f_go___boxed(lean_object* v_modulus_47_, lean_object* v_oldR_48_, lean_object* v_r_49_, lean_object* v_oldS_50_, lean_object* v_s_51_){
_start:
{
uint64_t v_modulus_boxed_52_; lean_object* v_res_53_; 
v_modulus_boxed_52_ = lean_unbox_uint64(v_modulus_47_);
lean_dec_ref(v_modulus_47_);
v_res_53_ = l_UInt64_invMod_x3f_go(v_modulus_boxed_52_, v_oldR_48_, v_r_49_, v_oldS_50_, v_s_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_UInt64_invMod_x3f(uint64_t v_a_54_, uint64_t v_modulus_55_){
_start:
{
uint64_t v___x_56_; uint8_t v___x_57_; 
v___x_56_ = 0ULL;
v___x_57_ = lean_uint64_dec_eq(v_modulus_55_, v___x_56_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v_fst_65_; lean_object* v_snd_66_; uint8_t v___x_67_; 
v___x_58_ = lean_unsigned_to_nat(0u);
v___x_59_ = lean_uint64_to_nat(v_a_54_);
v___x_60_ = lean_uint64_to_nat(v_modulus_55_);
v___x_61_ = lean_nat_mod(v___x_59_, v___x_60_);
lean_dec(v___x_59_);
v___x_62_ = lean_unsigned_to_nat(1u);
v___x_63_ = lean_nat_mod(v___x_62_, v___x_60_);
v___x_64_ = l_UInt64_invMod_x3f_go(v_modulus_55_, v___x_61_, v___x_60_, v___x_63_, v___x_58_);
v_fst_65_ = lean_ctor_get(v___x_64_, 0);
lean_inc(v_fst_65_);
v_snd_66_ = lean_ctor_get(v___x_64_, 1);
lean_inc(v_snd_66_);
lean_dec_ref(v___x_64_);
v___x_67_ = lean_nat_dec_eq(v_fst_65_, v___x_62_);
lean_dec(v_fst_65_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; 
lean_dec(v_snd_66_);
v___x_68_ = lean_box(0);
return v___x_68_;
}
else
{
uint64_t v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_69_ = lean_uint64_of_nat(v_snd_66_);
lean_dec(v_snd_66_);
v___x_70_ = lean_box_uint64(v___x_69_);
v___x_71_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
return v___x_71_;
}
}
else
{
lean_object* v___x_72_; 
v___x_72_ = lean_box(0);
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l_UInt64_invMod_x3f___boxed(lean_object* v_a_73_, lean_object* v_modulus_74_){
_start:
{
uint64_t v_a_boxed_75_; uint64_t v_modulus_boxed_76_; lean_object* v_res_77_; 
v_a_boxed_75_ = lean_unbox_uint64(v_a_73_);
lean_dec_ref(v_a_73_);
v_modulus_boxed_76_ = lean_unbox_uint64(v_modulus_74_);
lean_dec_ref(v_modulus_74_);
v_res_77_ = l_UInt64_invMod_x3f(v_a_boxed_75_, v_modulus_boxed_76_);
return v_res_77_;
}
}
static lean_object* _init_l___private_Init_Data_UInt_Modular_0__UInt64_wrapMod___closed__0(void){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_cstr_to_nat("18446744073709551616");
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_wrapMod(uint64_t v_modulus_79_){
_start:
{
uint64_t v___x_80_; uint8_t v___x_81_; 
v___x_80_ = 0ULL;
v___x_81_ = lean_uint64_dec_eq(v_modulus_79_, v___x_80_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; 
v___x_82_ = lean_uint64_to_nat(v_modulus_79_);
return v___x_82_;
}
else
{
lean_object* v___x_83_; 
v___x_83_ = lean_obj_once(&l___private_Init_Data_UInt_Modular_0__UInt64_wrapMod___closed__0, &l___private_Init_Data_UInt_Modular_0__UInt64_wrapMod___closed__0_once, _init_l___private_Init_Data_UInt_Modular_0__UInt64_wrapMod___closed__0);
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_wrapMod___boxed(lean_object* v_modulus_84_){
_start:
{
uint64_t v_modulus_boxed_85_; lean_object* v_res_86_; 
v_modulus_boxed_85_ = lean_unbox_uint64(v_modulus_84_);
lean_dec_ref(v_modulus_84_);
v_res_86_ = l___private_Init_Data_UInt_Modular_0__UInt64_wrapMod(v_modulus_boxed_85_);
return v_res_86_;
}
}
LEAN_EXPORT uint64_t l_UInt64_powModWord(uint64_t v_base_87_, uint64_t v_exponent_88_, uint64_t v_modulus_89_, uint64_t v_result_90_){
_start:
{
uint64_t v___x_91_; uint64_t v___y_93_; uint8_t v___x_99_; 
v___x_91_ = 0ULL;
v___x_99_ = lean_uint64_dec_eq(v_exponent_88_, v___x_91_);
if (v___x_99_ == 0)
{
uint64_t v___x_100_; uint64_t v___x_101_; uint64_t v___x_102_; uint8_t v___x_103_; 
v___x_100_ = 2ULL;
v___x_101_ = lean_uint64_mod(v_exponent_88_, v___x_100_);
v___x_102_ = 1ULL;
v___x_103_ = lean_uint64_dec_eq(v___x_101_, v___x_102_);
if (v___x_103_ == 0)
{
v___y_93_ = v_result_90_;
goto v___jp_92_;
}
else
{
uint64_t v___x_104_; 
v___x_104_ = lean_uint64_mul_mod(v_result_90_, v_base_87_, v_modulus_89_);
v___y_93_ = v___x_104_;
goto v___jp_92_;
}
}
else
{
return v_result_90_;
}
v___jp_92_:
{
uint64_t v___x_94_; uint64_t v_exponent_x27_95_; uint8_t v___x_96_; 
v___x_94_ = 1ULL;
v_exponent_x27_95_ = lean_uint64_shift_right(v_exponent_88_, v___x_94_);
v___x_96_ = lean_uint64_dec_eq(v_exponent_x27_95_, v___x_91_);
if (v___x_96_ == 0)
{
uint64_t v___x_97_; 
v___x_97_ = lean_uint64_mul_mod(v_base_87_, v_base_87_, v_modulus_89_);
v_base_87_ = v___x_97_;
v_exponent_88_ = v_exponent_x27_95_;
v_result_90_ = v___y_93_;
goto _start;
}
else
{
return v___y_93_;
}
}
}
}
LEAN_EXPORT lean_object* l_UInt64_powModWord___boxed(lean_object* v_base_105_, lean_object* v_exponent_106_, lean_object* v_modulus_107_, lean_object* v_result_108_){
_start:
{
uint64_t v_base_boxed_109_; uint64_t v_exponent_boxed_110_; uint64_t v_modulus_boxed_111_; uint64_t v_result_boxed_112_; uint64_t v_res_113_; lean_object* v_r_114_; 
v_base_boxed_109_ = lean_unbox_uint64(v_base_105_);
lean_dec_ref(v_base_105_);
v_exponent_boxed_110_ = lean_unbox_uint64(v_exponent_106_);
lean_dec_ref(v_exponent_106_);
v_modulus_boxed_111_ = lean_unbox_uint64(v_modulus_107_);
lean_dec_ref(v_modulus_107_);
v_result_boxed_112_ = lean_unbox_uint64(v_result_108_);
lean_dec_ref(v_result_108_);
v_res_113_ = l_UInt64_powModWord(v_base_boxed_109_, v_exponent_boxed_110_, v_modulus_boxed_111_, v_result_boxed_112_);
v_r_114_ = lean_box_uint64(v_res_113_);
return v_r_114_;
}
}
LEAN_EXPORT lean_object* l_UInt64_powModChunk(uint64_t v_modulus_115_, lean_object* v_x_116_, uint64_t v_x_117_, uint64_t v_x_118_, uint64_t v_x_119_){
_start:
{
lean_object* v_zero_120_; uint8_t v_isZero_121_; 
v_zero_120_ = lean_unsigned_to_nat(0u);
v_isZero_121_ = lean_nat_dec_eq(v_x_116_, v_zero_120_);
if (v_isZero_121_ == 1)
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
lean_dec(v_x_116_);
v___x_122_ = lean_box_uint64(v_x_117_);
v___x_123_ = lean_box_uint64(v_x_119_);
v___x_124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_124_, 0, v___x_122_);
lean_ctor_set(v___x_124_, 1, v___x_123_);
return v___x_124_;
}
else
{
lean_object* v_one_125_; lean_object* v_n_126_; uint64_t v___y_128_; uint64_t v___x_133_; uint64_t v___x_134_; uint64_t v___x_135_; uint8_t v___x_136_; 
v_one_125_ = lean_unsigned_to_nat(1u);
v_n_126_ = lean_nat_sub(v_x_116_, v_one_125_);
lean_dec(v_x_116_);
v___x_133_ = 2ULL;
v___x_134_ = lean_uint64_mod(v_x_118_, v___x_133_);
v___x_135_ = 1ULL;
v___x_136_ = lean_uint64_dec_eq(v___x_134_, v___x_135_);
if (v___x_136_ == 0)
{
v___y_128_ = v_x_119_;
goto v___jp_127_;
}
else
{
uint64_t v___x_137_; 
v___x_137_ = lean_uint64_mul_mod(v_x_119_, v_x_117_, v_modulus_115_);
v___y_128_ = v___x_137_;
goto v___jp_127_;
}
v___jp_127_:
{
uint64_t v___x_129_; uint64_t v___x_130_; uint64_t v___x_131_; 
v___x_129_ = lean_uint64_mul_mod(v_x_117_, v_x_117_, v_modulus_115_);
v___x_130_ = 1ULL;
v___x_131_ = lean_uint64_shift_right(v_x_118_, v___x_130_);
v_x_116_ = v_n_126_;
v_x_117_ = v___x_129_;
v_x_118_ = v___x_131_;
v_x_119_ = v___y_128_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_UInt64_powModChunk___boxed(lean_object* v_modulus_138_, lean_object* v_x_139_, lean_object* v_x_140_, lean_object* v_x_141_, lean_object* v_x_142_){
_start:
{
uint64_t v_modulus_boxed_143_; uint64_t v_x_79__boxed_144_; uint64_t v_x_80__boxed_145_; uint64_t v_x_81__boxed_146_; lean_object* v_res_147_; 
v_modulus_boxed_143_ = lean_unbox_uint64(v_modulus_138_);
lean_dec_ref(v_modulus_138_);
v_x_79__boxed_144_ = lean_unbox_uint64(v_x_140_);
lean_dec_ref(v_x_140_);
v_x_80__boxed_145_ = lean_unbox_uint64(v_x_141_);
lean_dec_ref(v_x_141_);
v_x_81__boxed_146_ = lean_unbox_uint64(v_x_142_);
lean_dec_ref(v_x_142_);
v_res_147_ = l_UInt64_powModChunk(v_modulus_boxed_143_, v_x_139_, v_x_79__boxed_144_, v_x_80__boxed_145_, v_x_81__boxed_146_);
return v_res_147_;
}
}
LEAN_EXPORT uint64_t l_UInt64_powModImpl_go(uint64_t v_modulus_148_, uint64_t v_base_149_, lean_object* v_exponent_150_, uint64_t v_result_151_){
_start:
{
lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_152_ = lean_obj_once(&l___private_Init_Data_UInt_Modular_0__UInt64_wrapMod___closed__0, &l___private_Init_Data_UInt_Modular_0__UInt64_wrapMod___closed__0_once, _init_l___private_Init_Data_UInt_Modular_0__UInt64_wrapMod___closed__0);
v___x_153_ = lean_nat_dec_lt(v_exponent_150_, v___x_152_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; uint64_t v___x_155_; lean_object* v___x_156_; lean_object* v_fst_157_; lean_object* v_snd_158_; lean_object* v___x_159_; uint64_t v___x_160_; uint64_t v___x_161_; 
v___x_154_ = lean_unsigned_to_nat(64u);
v___x_155_ = lean_uint64_of_nat(v_exponent_150_);
v___x_156_ = l_UInt64_powModChunk(v_modulus_148_, v___x_154_, v_base_149_, v___x_155_, v_result_151_);
v_fst_157_ = lean_ctor_get(v___x_156_, 0);
lean_inc(v_fst_157_);
v_snd_158_ = lean_ctor_get(v___x_156_, 1);
lean_inc(v_snd_158_);
lean_dec_ref(v___x_156_);
v___x_159_ = lean_nat_shiftr(v_exponent_150_, v___x_154_);
lean_dec(v_exponent_150_);
v___x_160_ = lean_unbox_uint64(v_fst_157_);
lean_dec(v_fst_157_);
v___x_161_ = lean_unbox_uint64(v_snd_158_);
lean_dec(v_snd_158_);
v_base_149_ = v___x_160_;
v_exponent_150_ = v___x_159_;
v_result_151_ = v___x_161_;
goto _start;
}
else
{
uint64_t v___x_163_; uint64_t v___x_164_; 
v___x_163_ = lean_uint64_of_nat(v_exponent_150_);
lean_dec(v_exponent_150_);
v___x_164_ = l_UInt64_powModWord(v_base_149_, v___x_163_, v_modulus_148_, v_result_151_);
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l_UInt64_powModImpl_go___boxed(lean_object* v_modulus_165_, lean_object* v_base_166_, lean_object* v_exponent_167_, lean_object* v_result_168_){
_start:
{
uint64_t v_modulus_boxed_169_; uint64_t v_base_boxed_170_; uint64_t v_result_boxed_171_; uint64_t v_res_172_; lean_object* v_r_173_; 
v_modulus_boxed_169_ = lean_unbox_uint64(v_modulus_165_);
lean_dec_ref(v_modulus_165_);
v_base_boxed_170_ = lean_unbox_uint64(v_base_166_);
lean_dec_ref(v_base_166_);
v_result_boxed_171_ = lean_unbox_uint64(v_result_168_);
lean_dec_ref(v_result_168_);
v_res_172_ = l_UInt64_powModImpl_go(v_modulus_boxed_169_, v_base_boxed_170_, v_exponent_167_, v_result_boxed_171_);
v_r_173_ = lean_box_uint64(v_res_172_);
return v_r_173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_powModImpl_go_match__1_splitter___redArg(lean_object* v_x_174_, lean_object* v_h__1_175_){
_start:
{
lean_object* v_fst_176_; lean_object* v_snd_177_; lean_object* v___x_178_; 
v_fst_176_ = lean_ctor_get(v_x_174_, 0);
lean_inc(v_fst_176_);
v_snd_177_ = lean_ctor_get(v_x_174_, 1);
lean_inc(v_snd_177_);
lean_dec_ref(v_x_174_);
v___x_178_ = lean_apply_2(v_h__1_175_, v_fst_176_, v_snd_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_powModImpl_go_match__1_splitter(lean_object* v_motive_179_, lean_object* v_x_180_, lean_object* v_h__1_181_){
_start:
{
lean_object* v_fst_182_; lean_object* v_snd_183_; lean_object* v___x_184_; 
v_fst_182_ = lean_ctor_get(v_x_180_, 0);
lean_inc(v_fst_182_);
v_snd_183_ = lean_ctor_get(v_x_180_, 1);
lean_inc(v_snd_183_);
lean_dec_ref(v_x_180_);
v___x_184_ = lean_apply_2(v_h__1_181_, v_fst_182_, v_snd_183_);
return v___x_184_;
}
}
LEAN_EXPORT uint64_t l_UInt64_powModImpl(uint64_t v_base_185_, lean_object* v_exponent_186_, uint64_t v_modulus_187_){
_start:
{
uint64_t v___x_188_; uint8_t v___x_189_; 
v___x_188_ = 1ULL;
v___x_189_ = lean_uint64_dec_eq(v_modulus_187_, v___x_188_);
if (v___x_189_ == 0)
{
uint64_t v___x_190_; 
v___x_190_ = l_UInt64_powModImpl_go(v_modulus_187_, v_base_185_, v_exponent_186_, v___x_188_);
return v___x_190_;
}
else
{
uint64_t v___x_191_; 
lean_dec(v_exponent_186_);
v___x_191_ = 0ULL;
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* l_UInt64_powModImpl___boxed(lean_object* v_base_192_, lean_object* v_exponent_193_, lean_object* v_modulus_194_){
_start:
{
uint64_t v_base_boxed_195_; uint64_t v_modulus_boxed_196_; uint64_t v_res_197_; lean_object* v_r_198_; 
v_base_boxed_195_ = lean_unbox_uint64(v_base_192_);
lean_dec_ref(v_base_192_);
v_modulus_boxed_196_ = lean_unbox_uint64(v_modulus_194_);
lean_dec_ref(v_modulus_194_);
v_res_197_ = l_UInt64_powModImpl(v_base_boxed_195_, v_exponent_193_, v_modulus_boxed_196_);
v_r_198_ = lean_box_uint64(v_res_197_);
return v_r_198_;
}
}
LEAN_EXPORT lean_object* l_UInt64_invModImpl_go(uint64_t v_modulus_199_, uint64_t v_oldR_200_, uint64_t v_r_201_, uint64_t v_oldS_202_, uint64_t v_s_203_){
_start:
{
uint64_t v___y_205_; uint64_t v___x_208_; uint8_t v___x_209_; 
v___x_208_ = 0ULL;
v___x_209_ = lean_uint64_dec_eq(v_r_201_, v___x_208_);
if (v___x_209_ == 0)
{
uint64_t v___x_210_; uint64_t v_product_211_; uint8_t v___x_212_; 
v___x_210_ = lean_uint64_div(v_oldR_200_, v_r_201_);
v_product_211_ = lean_uint64_mul_mod(v___x_210_, v_s_203_, v_modulus_199_);
v___x_212_ = lean_uint64_dec_le(v_product_211_, v_oldS_202_);
if (v___x_212_ == 0)
{
uint64_t v___x_213_; uint64_t v___x_214_; 
v___x_213_ = lean_uint64_sub(v_product_211_, v_oldS_202_);
v___x_214_ = lean_uint64_sub(v_modulus_199_, v___x_213_);
v___y_205_ = v___x_214_;
goto v___jp_204_;
}
else
{
uint64_t v___x_215_; 
v___x_215_ = lean_uint64_sub(v_oldS_202_, v_product_211_);
v___y_205_ = v___x_215_;
goto v___jp_204_;
}
}
else
{
uint64_t v___x_216_; uint8_t v___x_217_; 
v___x_216_ = 1ULL;
v___x_217_ = lean_uint64_dec_eq(v_oldR_200_, v___x_216_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; 
v___x_218_ = lean_box(0);
return v___x_218_;
}
else
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = lean_box_uint64(v_oldS_202_);
v___x_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
return v___x_220_;
}
}
v___jp_204_:
{
uint64_t v___x_206_; 
v___x_206_ = lean_uint64_mod(v_oldR_200_, v_r_201_);
v_oldR_200_ = v_r_201_;
v_r_201_ = v___x_206_;
v_oldS_202_ = v_s_203_;
v_s_203_ = v___y_205_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_UInt64_invModImpl_go___boxed(lean_object* v_modulus_221_, lean_object* v_oldR_222_, lean_object* v_r_223_, lean_object* v_oldS_224_, lean_object* v_s_225_){
_start:
{
uint64_t v_modulus_boxed_226_; uint64_t v_oldR_boxed_227_; uint64_t v_r_boxed_228_; uint64_t v_oldS_boxed_229_; uint64_t v_s_boxed_230_; lean_object* v_res_231_; 
v_modulus_boxed_226_ = lean_unbox_uint64(v_modulus_221_);
lean_dec_ref(v_modulus_221_);
v_oldR_boxed_227_ = lean_unbox_uint64(v_oldR_222_);
lean_dec_ref(v_oldR_222_);
v_r_boxed_228_ = lean_unbox_uint64(v_r_223_);
lean_dec_ref(v_r_223_);
v_oldS_boxed_229_ = lean_unbox_uint64(v_oldS_224_);
lean_dec_ref(v_oldS_224_);
v_s_boxed_230_ = lean_unbox_uint64(v_s_225_);
lean_dec_ref(v_s_225_);
v_res_231_ = l_UInt64_invModImpl_go(v_modulus_boxed_226_, v_oldR_boxed_227_, v_r_boxed_228_, v_oldS_boxed_229_, v_s_boxed_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_UInt64_invModImpl(uint64_t v_a_232_, uint64_t v_modulus_233_){
_start:
{
uint64_t v___x_234_; uint8_t v___x_235_; 
v___x_234_ = 0ULL;
v___x_235_ = lean_uint64_dec_eq(v_modulus_233_, v___x_234_);
if (v___x_235_ == 0)
{
uint64_t v___x_236_; uint64_t v___x_237_; uint64_t v___x_238_; lean_object* v___x_239_; 
v___x_236_ = lean_uint64_mod(v_a_232_, v_modulus_233_);
v___x_237_ = 1ULL;
v___x_238_ = lean_uint64_mod(v___x_237_, v_modulus_233_);
v___x_239_ = l_UInt64_invModImpl_go(v_modulus_233_, v___x_236_, v_modulus_233_, v___x_238_, v___x_234_);
return v___x_239_;
}
else
{
lean_object* v___x_240_; 
v___x_240_ = lean_box(0);
return v___x_240_;
}
}
}
LEAN_EXPORT lean_object* l_UInt64_invModImpl___boxed(lean_object* v_a_241_, lean_object* v_modulus_242_){
_start:
{
uint64_t v_a_boxed_243_; uint64_t v_modulus_boxed_244_; lean_object* v_res_245_; 
v_a_boxed_243_ = lean_unbox_uint64(v_a_241_);
lean_dec_ref(v_a_241_);
v_modulus_boxed_244_ = lean_unbox_uint64(v_modulus_242_);
lean_dec_ref(v_modulus_242_);
v_res_245_ = l_UInt64_invModImpl(v_a_boxed_243_, v_modulus_boxed_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_powModChunk_match__1_splitter___redArg(lean_object* v_x_246_, uint64_t v_x_247_, uint64_t v_x_248_, uint64_t v_x_249_, lean_object* v_h__1_250_, lean_object* v_h__2_251_){
_start:
{
lean_object* v_zero_252_; uint8_t v_isZero_253_; 
v_zero_252_ = lean_unsigned_to_nat(0u);
v_isZero_253_ = lean_nat_dec_eq(v_x_246_, v_zero_252_);
if (v_isZero_253_ == 1)
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
lean_dec(v_h__2_251_);
v___x_254_ = lean_box_uint64(v_x_247_);
v___x_255_ = lean_box_uint64(v_x_248_);
v___x_256_ = lean_box_uint64(v_x_249_);
v___x_257_ = lean_apply_3(v_h__1_250_, v___x_254_, v___x_255_, v___x_256_);
return v___x_257_;
}
else
{
lean_object* v_one_258_; lean_object* v_n_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
lean_dec(v_h__1_250_);
v_one_258_ = lean_unsigned_to_nat(1u);
v_n_259_ = lean_nat_sub(v_x_246_, v_one_258_);
v___x_260_ = lean_box_uint64(v_x_247_);
v___x_261_ = lean_box_uint64(v_x_248_);
v___x_262_ = lean_box_uint64(v_x_249_);
v___x_263_ = lean_apply_4(v_h__2_251_, v_n_259_, v___x_260_, v___x_261_, v___x_262_);
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_powModChunk_match__1_splitter___redArg___boxed(lean_object* v_x_264_, lean_object* v_x_265_, lean_object* v_x_266_, lean_object* v_x_267_, lean_object* v_h__1_268_, lean_object* v_h__2_269_){
_start:
{
uint64_t v_x_28__boxed_270_; uint64_t v_x_29__boxed_271_; uint64_t v_x_30__boxed_272_; lean_object* v_res_273_; 
v_x_28__boxed_270_ = lean_unbox_uint64(v_x_265_);
lean_dec_ref(v_x_265_);
v_x_29__boxed_271_ = lean_unbox_uint64(v_x_266_);
lean_dec_ref(v_x_266_);
v_x_30__boxed_272_ = lean_unbox_uint64(v_x_267_);
lean_dec_ref(v_x_267_);
v_res_273_ = l___private_Init_Data_UInt_Modular_0__UInt64_powModChunk_match__1_splitter___redArg(v_x_264_, v_x_28__boxed_270_, v_x_29__boxed_271_, v_x_30__boxed_272_, v_h__1_268_, v_h__2_269_);
lean_dec(v_x_264_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_powModChunk_match__1_splitter(lean_object* v_motive_274_, lean_object* v_x_275_, uint64_t v_x_276_, uint64_t v_x_277_, uint64_t v_x_278_, lean_object* v_h__1_279_, lean_object* v_h__2_280_){
_start:
{
lean_object* v_zero_281_; uint8_t v_isZero_282_; 
v_zero_281_ = lean_unsigned_to_nat(0u);
v_isZero_282_ = lean_nat_dec_eq(v_x_275_, v_zero_281_);
if (v_isZero_282_ == 1)
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
lean_dec(v_h__2_280_);
v___x_283_ = lean_box_uint64(v_x_276_);
v___x_284_ = lean_box_uint64(v_x_277_);
v___x_285_ = lean_box_uint64(v_x_278_);
v___x_286_ = lean_apply_3(v_h__1_279_, v___x_283_, v___x_284_, v___x_285_);
return v___x_286_;
}
else
{
lean_object* v_one_287_; lean_object* v_n_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
lean_dec(v_h__1_279_);
v_one_287_ = lean_unsigned_to_nat(1u);
v_n_288_ = lean_nat_sub(v_x_275_, v_one_287_);
v___x_289_ = lean_box_uint64(v_x_276_);
v___x_290_ = lean_box_uint64(v_x_277_);
v___x_291_ = lean_box_uint64(v_x_278_);
v___x_292_ = lean_apply_4(v_h__2_280_, v_n_288_, v___x_289_, v___x_290_, v___x_291_);
return v___x_292_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_powModChunk_match__1_splitter___boxed(lean_object* v_motive_293_, lean_object* v_x_294_, lean_object* v_x_295_, lean_object* v_x_296_, lean_object* v_x_297_, lean_object* v_h__1_298_, lean_object* v_h__2_299_){
_start:
{
uint64_t v_x_58__boxed_300_; uint64_t v_x_59__boxed_301_; uint64_t v_x_60__boxed_302_; lean_object* v_res_303_; 
v_x_58__boxed_300_ = lean_unbox_uint64(v_x_295_);
lean_dec_ref(v_x_295_);
v_x_59__boxed_301_ = lean_unbox_uint64(v_x_296_);
lean_dec_ref(v_x_296_);
v_x_60__boxed_302_ = lean_unbox_uint64(v_x_297_);
lean_dec_ref(v_x_297_);
v_res_303_ = l___private_Init_Data_UInt_Modular_0__UInt64_powModChunk_match__1_splitter(v_motive_293_, v_x_294_, v_x_58__boxed_300_, v_x_59__boxed_301_, v_x_60__boxed_302_, v_h__1_298_, v_h__2_299_);
lean_dec(v_x_294_);
return v_res_303_;
}
}
lean_object* runtime_initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Gcd(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_UInt_Modular(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Gcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Mod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_UInt_Modular(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Gcd(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_UInt_Modular(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Gcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Mod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Modular(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_UInt_Modular(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_UInt_Modular(builtin);
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Init.Data.Nat.Basic
// Imports: public import Init.SimpLemmas public import Init.Data.NeZero public import Init.Grind.Tactics
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_recCompiled___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_recCompiled___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_recCompiled(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_recCompiled___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_recAux___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_recAux___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_recAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_recAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_casesAuxOn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_casesAuxOn___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_casesAuxOn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_casesAuxOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_iterateTR_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_iterateTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_iterateTR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_iterateTR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_repeatTR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_repeatTR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_blt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_blt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_instTransLt;
LEAN_EXPORT lean_object* l_Nat_instTransLe;
LEAN_EXPORT lean_object* l_Nat_instTransLtLe;
LEAN_EXPORT lean_object* l_Nat_instTransLeLt;
LEAN_EXPORT lean_object* l_Nat_min(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_min___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_instMax___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_instMax___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Nat_instMax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_instMax___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Nat_instMax___closed__0 = (const lean_object*)&l_Nat_instMax___closed__0_value;
LEAN_EXPORT const lean_object* l_Nat_instMax = (const lean_object*)&l_Nat_instMax___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_max(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_max___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_iterate_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_iterate_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_iterate_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_iterate_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_repeat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_repeat(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_recCompiled___redArg(lean_object* v_zero_1_, lean_object* v_succ_2_, lean_object* v_x_3_){
_start:
{
lean_object* v_zero_4_; uint8_t v_isZero_5_; 
v_zero_4_ = lean_unsigned_to_nat(0u);
v_isZero_5_ = lean_nat_dec_eq(v_x_3_, v_zero_4_);
if (v_isZero_5_ == 1)
{
lean_dec(v_succ_2_);
lean_inc(v_zero_1_);
return v_zero_1_;
}
else
{
lean_object* v_one_6_; lean_object* v_n_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v_one_6_ = lean_unsigned_to_nat(1u);
v_n_7_ = lean_nat_sub(v_x_3_, v_one_6_);
lean_inc(v_succ_2_);
v___x_8_ = l_Nat_recCompiled___redArg(v_zero_1_, v_succ_2_, v_n_7_);
v___x_9_ = lean_apply_2(v_succ_2_, v_n_7_, v___x_8_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_recCompiled___redArg___boxed(lean_object* v_zero_10_, lean_object* v_succ_11_, lean_object* v_x_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Nat_recCompiled___redArg(v_zero_10_, v_succ_11_, v_x_12_);
lean_dec(v_x_12_);
lean_dec(v_zero_10_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Nat_recCompiled(lean_object* v_motive_14_, lean_object* v_zero_15_, lean_object* v_succ_16_, lean_object* v_x_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Nat_recCompiled___redArg(v_zero_15_, v_succ_16_, v_x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Nat_recCompiled___boxed(lean_object* v_motive_19_, lean_object* v_zero_20_, lean_object* v_succ_21_, lean_object* v_x_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Nat_recCompiled(v_motive_19_, v_zero_20_, v_succ_21_, v_x_22_);
lean_dec(v_x_22_);
lean_dec(v_zero_20_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Nat_recAux___redArg(lean_object* v_zero_24_, lean_object* v_succ_25_, lean_object* v_t_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Nat_recCompiled___redArg(v_zero_24_, v_succ_25_, v_t_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Nat_recAux___redArg___boxed(lean_object* v_zero_28_, lean_object* v_succ_29_, lean_object* v_t_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Nat_recAux___redArg(v_zero_28_, v_succ_29_, v_t_30_);
lean_dec(v_t_30_);
lean_dec(v_zero_28_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Nat_recAux(lean_object* v_motive_32_, lean_object* v_zero_33_, lean_object* v_succ_34_, lean_object* v_t_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Nat_recCompiled___redArg(v_zero_33_, v_succ_34_, v_t_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Nat_recAux___boxed(lean_object* v_motive_37_, lean_object* v_zero_38_, lean_object* v_succ_39_, lean_object* v_t_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Nat_recAux(v_motive_37_, v_zero_38_, v_succ_39_, v_t_40_);
lean_dec(v_t_40_);
lean_dec(v_zero_38_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Nat_casesAuxOn___redArg(lean_object* v_t_42_, lean_object* v_zero_43_, lean_object* v_succ_44_){
_start:
{
lean_object* v_zero_45_; uint8_t v_isZero_46_; 
v_zero_45_ = lean_unsigned_to_nat(0u);
v_isZero_46_ = lean_nat_dec_eq(v_t_42_, v_zero_45_);
if (v_isZero_46_ == 1)
{
lean_dec(v_succ_44_);
lean_inc(v_zero_43_);
return v_zero_43_;
}
else
{
lean_object* v_one_47_; lean_object* v_n_48_; lean_object* v___x_49_; 
v_one_47_ = lean_unsigned_to_nat(1u);
v_n_48_ = lean_nat_sub(v_t_42_, v_one_47_);
v___x_49_ = lean_apply_1(v_succ_44_, v_n_48_);
return v___x_49_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_casesAuxOn___redArg___boxed(lean_object* v_t_50_, lean_object* v_zero_51_, lean_object* v_succ_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Nat_casesAuxOn___redArg(v_t_50_, v_zero_51_, v_succ_52_);
lean_dec(v_zero_51_);
lean_dec(v_t_50_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Nat_casesAuxOn(lean_object* v_motive_54_, lean_object* v_t_55_, lean_object* v_zero_56_, lean_object* v_succ_57_){
_start:
{
lean_object* v_zero_58_; uint8_t v_isZero_59_; 
v_zero_58_ = lean_unsigned_to_nat(0u);
v_isZero_59_ = lean_nat_dec_eq(v_t_55_, v_zero_58_);
if (v_isZero_59_ == 1)
{
lean_dec(v_succ_57_);
lean_inc(v_zero_56_);
return v_zero_56_;
}
else
{
lean_object* v_one_60_; lean_object* v_n_61_; lean_object* v___x_62_; 
v_one_60_ = lean_unsigned_to_nat(1u);
v_n_61_ = lean_nat_sub(v_t_55_, v_one_60_);
v___x_62_ = lean_apply_1(v_succ_57_, v_n_61_);
return v___x_62_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_casesAuxOn___boxed(lean_object* v_motive_63_, lean_object* v_t_64_, lean_object* v_zero_65_, lean_object* v_succ_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Nat_casesAuxOn(v_motive_63_, v_t_64_, v_zero_65_, v_succ_66_);
lean_dec(v_zero_65_);
lean_dec(v_t_64_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_iterateTR_loop___redArg(lean_object* v_f_68_, lean_object* v_x_69_, lean_object* v_x_70_){
_start:
{
lean_object* v_zero_71_; uint8_t v_isZero_72_; 
v_zero_71_ = lean_unsigned_to_nat(0u);
v_isZero_72_ = lean_nat_dec_eq(v_x_69_, v_zero_71_);
if (v_isZero_72_ == 1)
{
lean_dec(v_x_69_);
lean_dec(v_f_68_);
return v_x_70_;
}
else
{
lean_object* v_one_73_; lean_object* v_n_74_; lean_object* v___x_75_; 
v_one_73_ = lean_unsigned_to_nat(1u);
v_n_74_ = lean_nat_sub(v_x_69_, v_one_73_);
lean_dec(v_x_69_);
lean_inc(v_f_68_);
v___x_75_ = lean_apply_1(v_f_68_, v_x_70_);
v_x_69_ = v_n_74_;
v_x_70_ = v___x_75_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_iterateTR_loop(lean_object* v_00_u03b1_77_, lean_object* v_f_78_, lean_object* v_x_79_, lean_object* v_x_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l___private_Init_Data_Nat_Basic_0__Nat_iterateTR_loop___redArg(v_f_78_, v_x_79_, v_x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Nat_iterateTR___redArg(lean_object* v_f_82_, lean_object* v_n_83_, lean_object* v_a_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l___private_Init_Data_Nat_Basic_0__Nat_iterateTR_loop___redArg(v_f_82_, v_n_83_, v_a_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Nat_iterateTR(lean_object* v_00_u03b1_86_, lean_object* v_f_87_, lean_object* v_n_88_, lean_object* v_a_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l___private_Init_Data_Nat_Basic_0__Nat_iterateTR_loop___redArg(v_f_87_, v_n_88_, v_a_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Nat_repeatTR___redArg(lean_object* v_f_91_, lean_object* v_n_92_, lean_object* v_a_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = l___private_Init_Data_Nat_Basic_0__Nat_iterateTR_loop___redArg(v_f_91_, v_n_92_, v_a_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Nat_repeatTR(lean_object* v_00_u03b1_95_, lean_object* v_f_96_, lean_object* v_n_97_, lean_object* v_a_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l___private_Init_Data_Nat_Basic_0__Nat_iterateTR_loop___redArg(v_f_96_, v_n_97_, v_a_98_);
return v___x_99_;
}
}
LEAN_EXPORT uint8_t l_Nat_blt(lean_object* v_a_100_, lean_object* v_b_101_){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_102_ = lean_unsigned_to_nat(1u);
v___x_103_ = lean_nat_add(v_a_100_, v___x_102_);
v___x_104_ = lean_nat_dec_le(v___x_103_, v_b_101_);
lean_dec(v___x_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Nat_blt___boxed(lean_object* v_a_105_, lean_object* v_b_106_){
_start:
{
uint8_t v_res_107_; lean_object* v_r_108_; 
v_res_107_ = l_Nat_blt(v_a_105_, v_b_106_);
lean_dec(v_b_106_);
lean_dec(v_a_105_);
v_r_108_ = lean_box(v_res_107_);
return v_r_108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter___redArg(lean_object* v_x_109_, lean_object* v_x_110_, lean_object* v_h__1_111_, lean_object* v_h__2_112_, lean_object* v_h__3_113_, lean_object* v_h__4_114_){
_start:
{
lean_object* v_zero_115_; uint8_t v_isZero_116_; 
v_zero_115_ = lean_unsigned_to_nat(0u);
v_isZero_116_ = lean_nat_dec_eq(v_x_109_, v_zero_115_);
if (v_isZero_116_ == 1)
{
uint8_t v_isZero_117_; 
lean_dec(v_h__4_114_);
lean_dec(v_h__3_113_);
v_isZero_117_ = lean_nat_dec_eq(v_x_110_, v_zero_115_);
if (v_isZero_117_ == 1)
{
lean_object* v___x_118_; lean_object* v___x_119_; 
lean_dec(v_h__2_112_);
v___x_118_ = lean_box(0);
v___x_119_ = lean_apply_1(v_h__1_111_, v___x_118_);
return v___x_119_;
}
else
{
lean_object* v_one_120_; lean_object* v_n_121_; lean_object* v___x_122_; 
lean_dec(v_h__1_111_);
v_one_120_ = lean_unsigned_to_nat(1u);
v_n_121_ = lean_nat_sub(v_x_110_, v_one_120_);
v___x_122_ = lean_apply_1(v_h__2_112_, v_n_121_);
return v___x_122_;
}
}
else
{
lean_object* v_one_123_; lean_object* v_n_124_; uint8_t v_isZero_125_; 
lean_dec(v_h__2_112_);
lean_dec(v_h__1_111_);
v_one_123_ = lean_unsigned_to_nat(1u);
v_n_124_ = lean_nat_sub(v_x_109_, v_one_123_);
v_isZero_125_ = lean_nat_dec_eq(v_x_110_, v_zero_115_);
if (v_isZero_125_ == 1)
{
lean_object* v___x_126_; 
lean_dec(v_h__4_114_);
v___x_126_ = lean_apply_1(v_h__3_113_, v_n_124_);
return v___x_126_;
}
else
{
lean_object* v_n_127_; lean_object* v___x_128_; 
lean_dec(v_h__3_113_);
v_n_127_ = lean_nat_sub(v_x_110_, v_one_123_);
v___x_128_ = lean_apply_2(v_h__4_114_, v_n_124_, v_n_127_);
return v___x_128_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter___redArg___boxed(lean_object* v_x_129_, lean_object* v_x_130_, lean_object* v_h__1_131_, lean_object* v_h__2_132_, lean_object* v_h__3_133_, lean_object* v_h__4_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter___redArg(v_x_129_, v_x_130_, v_h__1_131_, v_h__2_132_, v_h__3_133_, v_h__4_134_);
lean_dec(v_x_130_);
lean_dec(v_x_129_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter(lean_object* v_motive_136_, lean_object* v_x_137_, lean_object* v_x_138_, lean_object* v_h__1_139_, lean_object* v_h__2_140_, lean_object* v_h__3_141_, lean_object* v_h__4_142_){
_start:
{
lean_object* v_zero_143_; uint8_t v_isZero_144_; 
v_zero_143_ = lean_unsigned_to_nat(0u);
v_isZero_144_ = lean_nat_dec_eq(v_x_137_, v_zero_143_);
if (v_isZero_144_ == 1)
{
uint8_t v_isZero_145_; 
lean_dec(v_h__4_142_);
lean_dec(v_h__3_141_);
v_isZero_145_ = lean_nat_dec_eq(v_x_138_, v_zero_143_);
if (v_isZero_145_ == 1)
{
lean_object* v___x_146_; lean_object* v___x_147_; 
lean_dec(v_h__2_140_);
v___x_146_ = lean_box(0);
v___x_147_ = lean_apply_1(v_h__1_139_, v___x_146_);
return v___x_147_;
}
else
{
lean_object* v_one_148_; lean_object* v_n_149_; lean_object* v___x_150_; 
lean_dec(v_h__1_139_);
v_one_148_ = lean_unsigned_to_nat(1u);
v_n_149_ = lean_nat_sub(v_x_138_, v_one_148_);
v___x_150_ = lean_apply_1(v_h__2_140_, v_n_149_);
return v___x_150_;
}
}
else
{
lean_object* v_one_151_; lean_object* v_n_152_; uint8_t v_isZero_153_; 
lean_dec(v_h__2_140_);
lean_dec(v_h__1_139_);
v_one_151_ = lean_unsigned_to_nat(1u);
v_n_152_ = lean_nat_sub(v_x_137_, v_one_151_);
v_isZero_153_ = lean_nat_dec_eq(v_x_138_, v_zero_143_);
if (v_isZero_153_ == 1)
{
lean_object* v___x_154_; 
lean_dec(v_h__4_142_);
v___x_154_ = lean_apply_1(v_h__3_141_, v_n_152_);
return v___x_154_;
}
else
{
lean_object* v_n_155_; lean_object* v___x_156_; 
lean_dec(v_h__3_141_);
v_n_155_ = lean_nat_sub(v_x_138_, v_one_151_);
v___x_156_ = lean_apply_2(v_h__4_142_, v_n_152_, v_n_155_);
return v___x_156_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter___boxed(lean_object* v_motive_157_, lean_object* v_x_158_, lean_object* v_x_159_, lean_object* v_h__1_160_, lean_object* v_h__2_161_, lean_object* v_h__3_162_, lean_object* v_h__4_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter(v_motive_157_, v_x_158_, v_x_159_, v_h__1_160_, v_h__2_161_, v_h__3_162_, v_h__4_163_);
lean_dec(v_x_159_);
lean_dec(v_x_158_);
return v_res_164_;
}
}
static lean_object* _init_l_Nat_instTransLt(void){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = lean_box(0);
return v___x_165_;
}
}
static lean_object* _init_l_Nat_instTransLe(void){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lean_box(0);
return v___x_166_;
}
}
static lean_object* _init_l_Nat_instTransLtLe(void){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lean_box(0);
return v___x_167_;
}
}
static lean_object* _init_l_Nat_instTransLeLt(void){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = lean_box(0);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Nat_min(lean_object* v_n_169_, lean_object* v_m_170_){
_start:
{
uint8_t v___x_171_; 
v___x_171_ = lean_nat_dec_le(v_n_169_, v_m_170_);
if (v___x_171_ == 0)
{
lean_inc(v_m_170_);
return v_m_170_;
}
else
{
lean_inc(v_n_169_);
return v_n_169_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_min___boxed(lean_object* v_n_172_, lean_object* v_m_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Nat_min(v_n_172_, v_m_173_);
lean_dec(v_m_173_);
lean_dec(v_n_172_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Nat_instMax___lam__0(lean_object* v_x_175_, lean_object* v_y_176_){
_start:
{
uint8_t v___x_177_; 
v___x_177_ = lean_nat_dec_le(v_x_175_, v_y_176_);
if (v___x_177_ == 0)
{
lean_inc(v_x_175_);
return v_x_175_;
}
else
{
lean_inc(v_y_176_);
return v_y_176_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_instMax___lam__0___boxed(lean_object* v_x_178_, lean_object* v_y_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Nat_instMax___lam__0(v_x_178_, v_y_179_);
lean_dec(v_y_179_);
lean_dec(v_x_178_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Nat_max(lean_object* v_n_183_, lean_object* v_m_184_){
_start:
{
uint8_t v___x_185_; 
v___x_185_ = lean_nat_dec_le(v_n_183_, v_m_184_);
if (v___x_185_ == 0)
{
lean_inc(v_n_183_);
return v_n_183_;
}
else
{
lean_inc(v_m_184_);
return v_m_184_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_max___boxed(lean_object* v_n_186_, lean_object* v_m_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Nat_max(v_n_186_, v_m_187_);
lean_dec(v_m_187_);
lean_dec(v_n_186_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_iterate_match__1_splitter___redArg(lean_object* v_x_189_, lean_object* v_x_190_, lean_object* v_h__1_191_, lean_object* v_h__2_192_){
_start:
{
lean_object* v_zero_193_; uint8_t v_isZero_194_; 
v_zero_193_ = lean_unsigned_to_nat(0u);
v_isZero_194_ = lean_nat_dec_eq(v_x_189_, v_zero_193_);
if (v_isZero_194_ == 1)
{
lean_object* v___x_195_; 
lean_dec(v_h__2_192_);
v___x_195_ = lean_apply_1(v_h__1_191_, v_x_190_);
return v___x_195_;
}
else
{
lean_object* v_one_196_; lean_object* v_n_197_; lean_object* v___x_198_; 
lean_dec(v_h__1_191_);
v_one_196_ = lean_unsigned_to_nat(1u);
v_n_197_ = lean_nat_sub(v_x_189_, v_one_196_);
v___x_198_ = lean_apply_2(v_h__2_192_, v_n_197_, v_x_190_);
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_iterate_match__1_splitter___redArg___boxed(lean_object* v_x_199_, lean_object* v_x_200_, lean_object* v_h__1_201_, lean_object* v_h__2_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l___private_Init_Data_Nat_Basic_0__Nat_iterate_match__1_splitter___redArg(v_x_199_, v_x_200_, v_h__1_201_, v_h__2_202_);
lean_dec(v_x_199_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_iterate_match__1_splitter(lean_object* v_00_u03b1_204_, lean_object* v_motive_205_, lean_object* v_x_206_, lean_object* v_x_207_, lean_object* v_h__1_208_, lean_object* v_h__2_209_){
_start:
{
lean_object* v_zero_210_; uint8_t v_isZero_211_; 
v_zero_210_ = lean_unsigned_to_nat(0u);
v_isZero_211_ = lean_nat_dec_eq(v_x_206_, v_zero_210_);
if (v_isZero_211_ == 1)
{
lean_object* v___x_212_; 
lean_dec(v_h__2_209_);
v___x_212_ = lean_apply_1(v_h__1_208_, v_x_207_);
return v___x_212_;
}
else
{
lean_object* v_one_213_; lean_object* v_n_214_; lean_object* v___x_215_; 
lean_dec(v_h__1_208_);
v_one_213_ = lean_unsigned_to_nat(1u);
v_n_214_ = lean_nat_sub(v_x_206_, v_one_213_);
v___x_215_ = lean_apply_2(v_h__2_209_, v_n_214_, v_x_207_);
return v___x_215_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_iterate_match__1_splitter___boxed(lean_object* v_00_u03b1_216_, lean_object* v_motive_217_, lean_object* v_x_218_, lean_object* v_x_219_, lean_object* v_h__1_220_, lean_object* v_h__2_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l___private_Init_Data_Nat_Basic_0__Nat_iterate_match__1_splitter(v_00_u03b1_216_, v_motive_217_, v_x_218_, v_x_219_, v_h__1_220_, v_h__2_221_);
lean_dec(v_x_218_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Nat_repeat___redArg(lean_object* v_f_223_, lean_object* v_n_224_, lean_object* v_a_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l___private_Init_Data_Nat_Basic_0__Nat_iterateTR_loop___redArg(v_f_223_, v_n_224_, v_a_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Nat_repeat(lean_object* v_00_u03b1_227_, lean_object* v_f_228_, lean_object* v_n_229_, lean_object* v_a_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l___private_Init_Data_Nat_Basic_0__Nat_iterateTR_loop___redArg(v_f_228_, v_n_229_, v_a_230_);
return v___x_231_;
}
}
lean_object* runtime_initialize_Init_SimpLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_NeZero(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Nat_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_SimpLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_NeZero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Nat_instTransLt = _init_l_Nat_instTransLt();
l_Nat_instTransLe = _init_l_Nat_instTransLe();
l_Nat_instTransLtLe = _init_l_Nat_instTransLtLe();
l_Nat_instTransLeLt = _init_l_Nat_instTransLeLt();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Nat_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_SimpLemmas(uint8_t builtin);
lean_object* initialize_Init_Data_NeZero(uint8_t builtin);
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Nat_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_SimpLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_NeZero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Nat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Nat_Basic(builtin);
}
#ifdef __cplusplus
}
#endif

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
LEAN_EXPORT lean_object* l_Nat_repeat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_repeat___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_repeat(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_repeat___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeat_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeat_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeat_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeat_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Nat_repeat___redArg(lean_object* v_f_68_, lean_object* v_x_69_, lean_object* v_x_70_){
_start:
{
lean_object* v_zero_71_; uint8_t v_isZero_72_; 
v_zero_71_ = lean_unsigned_to_nat(0u);
v_isZero_72_ = lean_nat_dec_eq(v_x_69_, v_zero_71_);
if (v_isZero_72_ == 1)
{
lean_dec(v_f_68_);
lean_inc(v_x_70_);
return v_x_70_;
}
else
{
lean_object* v_one_73_; lean_object* v_n_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v_one_73_ = lean_unsigned_to_nat(1u);
v_n_74_ = lean_nat_sub(v_x_69_, v_one_73_);
lean_inc(v_f_68_);
v___x_75_ = l_Nat_repeat___redArg(v_f_68_, v_n_74_, v_x_70_);
lean_dec(v_n_74_);
v___x_76_ = lean_apply_1(v_f_68_, v___x_75_);
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_repeat___redArg___boxed(lean_object* v_f_77_, lean_object* v_x_78_, lean_object* v_x_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Nat_repeat___redArg(v_f_77_, v_x_78_, v_x_79_);
lean_dec(v_x_79_);
lean_dec(v_x_78_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Nat_repeat(lean_object* v_00_u03b1_81_, lean_object* v_f_82_, lean_object* v_x_83_, lean_object* v_x_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Nat_repeat___redArg(v_f_82_, v_x_83_, v_x_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Nat_repeat___boxed(lean_object* v_00_u03b1_86_, lean_object* v_f_87_, lean_object* v_x_88_, lean_object* v_x_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Nat_repeat(v_00_u03b1_86_, v_f_87_, v_x_88_, v_x_89_);
lean_dec(v_x_89_);
lean_dec(v_x_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___redArg(lean_object* v_f_91_, lean_object* v_x_92_, lean_object* v_x_93_){
_start:
{
lean_object* v_zero_94_; uint8_t v_isZero_95_; 
v_zero_94_ = lean_unsigned_to_nat(0u);
v_isZero_95_ = lean_nat_dec_eq(v_x_92_, v_zero_94_);
if (v_isZero_95_ == 1)
{
lean_dec(v_x_92_);
lean_dec(v_f_91_);
return v_x_93_;
}
else
{
lean_object* v_one_96_; lean_object* v_n_97_; lean_object* v___x_98_; 
v_one_96_ = lean_unsigned_to_nat(1u);
v_n_97_ = lean_nat_sub(v_x_92_, v_one_96_);
lean_dec(v_x_92_);
lean_inc(v_f_91_);
v___x_98_ = lean_apply_1(v_f_91_, v_x_93_);
v_x_92_ = v_n_97_;
v_x_93_ = v___x_98_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_object* v_00_u03b1_100_, lean_object* v_f_101_, lean_object* v_x_102_, lean_object* v_x_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___redArg(v_f_101_, v_x_102_, v_x_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Nat_repeatTR___redArg(lean_object* v_f_105_, lean_object* v_n_106_, lean_object* v_a_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___redArg(v_f_105_, v_n_106_, v_a_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Nat_repeatTR(lean_object* v_00_u03b1_109_, lean_object* v_f_110_, lean_object* v_n_111_, lean_object* v_a_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___redArg(v_f_110_, v_n_111_, v_a_112_);
return v___x_113_;
}
}
LEAN_EXPORT uint8_t l_Nat_blt(lean_object* v_a_114_, lean_object* v_b_115_){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_116_ = lean_unsigned_to_nat(1u);
v___x_117_ = lean_nat_add(v_a_114_, v___x_116_);
v___x_118_ = lean_nat_dec_le(v___x_117_, v_b_115_);
lean_dec(v___x_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Nat_blt___boxed(lean_object* v_a_119_, lean_object* v_b_120_){
_start:
{
uint8_t v_res_121_; lean_object* v_r_122_; 
v_res_121_ = l_Nat_blt(v_a_119_, v_b_120_);
lean_dec(v_b_120_);
lean_dec(v_a_119_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter___redArg(lean_object* v_x_123_, lean_object* v_x_124_, lean_object* v_h__1_125_, lean_object* v_h__2_126_, lean_object* v_h__3_127_, lean_object* v_h__4_128_){
_start:
{
lean_object* v_zero_129_; uint8_t v_isZero_130_; 
v_zero_129_ = lean_unsigned_to_nat(0u);
v_isZero_130_ = lean_nat_dec_eq(v_x_123_, v_zero_129_);
if (v_isZero_130_ == 1)
{
uint8_t v_isZero_131_; 
lean_dec(v_h__4_128_);
lean_dec(v_h__3_127_);
v_isZero_131_ = lean_nat_dec_eq(v_x_124_, v_zero_129_);
if (v_isZero_131_ == 1)
{
lean_object* v___x_132_; lean_object* v___x_133_; 
lean_dec(v_h__2_126_);
v___x_132_ = lean_box(0);
v___x_133_ = lean_apply_1(v_h__1_125_, v___x_132_);
return v___x_133_;
}
else
{
lean_object* v_one_134_; lean_object* v_n_135_; lean_object* v___x_136_; 
lean_dec(v_h__1_125_);
v_one_134_ = lean_unsigned_to_nat(1u);
v_n_135_ = lean_nat_sub(v_x_124_, v_one_134_);
v___x_136_ = lean_apply_1(v_h__2_126_, v_n_135_);
return v___x_136_;
}
}
else
{
lean_object* v_one_137_; lean_object* v_n_138_; uint8_t v_isZero_139_; 
lean_dec(v_h__2_126_);
lean_dec(v_h__1_125_);
v_one_137_ = lean_unsigned_to_nat(1u);
v_n_138_ = lean_nat_sub(v_x_123_, v_one_137_);
v_isZero_139_ = lean_nat_dec_eq(v_x_124_, v_zero_129_);
if (v_isZero_139_ == 1)
{
lean_object* v___x_140_; 
lean_dec(v_h__4_128_);
v___x_140_ = lean_apply_1(v_h__3_127_, v_n_138_);
return v___x_140_;
}
else
{
lean_object* v_n_141_; lean_object* v___x_142_; 
lean_dec(v_h__3_127_);
v_n_141_ = lean_nat_sub(v_x_124_, v_one_137_);
v___x_142_ = lean_apply_2(v_h__4_128_, v_n_138_, v_n_141_);
return v___x_142_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter___redArg___boxed(lean_object* v_x_143_, lean_object* v_x_144_, lean_object* v_h__1_145_, lean_object* v_h__2_146_, lean_object* v_h__3_147_, lean_object* v_h__4_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter___redArg(v_x_143_, v_x_144_, v_h__1_145_, v_h__2_146_, v_h__3_147_, v_h__4_148_);
lean_dec(v_x_144_);
lean_dec(v_x_143_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter(lean_object* v_motive_150_, lean_object* v_x_151_, lean_object* v_x_152_, lean_object* v_h__1_153_, lean_object* v_h__2_154_, lean_object* v_h__3_155_, lean_object* v_h__4_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter___redArg(v_x_151_, v_x_152_, v_h__1_153_, v_h__2_154_, v_h__3_155_, v_h__4_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter___boxed(lean_object* v_motive_158_, lean_object* v_x_159_, lean_object* v_x_160_, lean_object* v_h__1_161_, lean_object* v_h__2_162_, lean_object* v_h__3_163_, lean_object* v_h__4_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter(v_motive_158_, v_x_159_, v_x_160_, v_h__1_161_, v_h__2_162_, v_h__3_163_, v_h__4_164_);
lean_dec(v_x_160_);
lean_dec(v_x_159_);
return v_res_165_;
}
}
static lean_object* _init_l_Nat_instTransLt(void){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lean_box(0);
return v___x_166_;
}
}
static lean_object* _init_l_Nat_instTransLe(void){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lean_box(0);
return v___x_167_;
}
}
static lean_object* _init_l_Nat_instTransLtLe(void){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = lean_box(0);
return v___x_168_;
}
}
static lean_object* _init_l_Nat_instTransLeLt(void){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = lean_box(0);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Nat_min(lean_object* v_n_170_, lean_object* v_m_171_){
_start:
{
uint8_t v___x_172_; 
v___x_172_ = lean_nat_dec_le(v_n_170_, v_m_171_);
if (v___x_172_ == 0)
{
lean_inc(v_m_171_);
return v_m_171_;
}
else
{
lean_inc(v_n_170_);
return v_n_170_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_min___boxed(lean_object* v_n_173_, lean_object* v_m_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Nat_min(v_n_173_, v_m_174_);
lean_dec(v_m_174_);
lean_dec(v_n_173_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Nat_instMax___lam__0(lean_object* v_x_176_, lean_object* v_y_177_){
_start:
{
uint8_t v___x_178_; 
v___x_178_ = lean_nat_dec_le(v_x_176_, v_y_177_);
if (v___x_178_ == 0)
{
lean_inc(v_x_176_);
return v_x_176_;
}
else
{
lean_inc(v_y_177_);
return v_y_177_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_instMax___lam__0___boxed(lean_object* v_x_179_, lean_object* v_y_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Nat_instMax___lam__0(v_x_179_, v_y_180_);
lean_dec(v_y_180_);
lean_dec(v_x_179_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Nat_max(lean_object* v_n_184_, lean_object* v_m_185_){
_start:
{
uint8_t v___x_186_; 
v___x_186_ = lean_nat_dec_le(v_n_184_, v_m_185_);
if (v___x_186_ == 0)
{
lean_inc(v_n_184_);
return v_n_184_;
}
else
{
lean_inc(v_m_185_);
return v_m_185_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_max___boxed(lean_object* v_n_187_, lean_object* v_m_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Nat_max(v_n_187_, v_m_188_);
lean_dec(v_m_188_);
lean_dec(v_n_187_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeat_match__1_splitter___redArg(lean_object* v_x_190_, lean_object* v_x_191_, lean_object* v_h__1_192_, lean_object* v_h__2_193_){
_start:
{
lean_object* v_zero_194_; uint8_t v_isZero_195_; 
v_zero_194_ = lean_unsigned_to_nat(0u);
v_isZero_195_ = lean_nat_dec_eq(v_x_190_, v_zero_194_);
if (v_isZero_195_ == 1)
{
lean_object* v___x_196_; 
lean_dec(v_h__2_193_);
v___x_196_ = lean_apply_1(v_h__1_192_, v_x_191_);
return v___x_196_;
}
else
{
lean_object* v_one_197_; lean_object* v_n_198_; lean_object* v___x_199_; 
lean_dec(v_h__1_192_);
v_one_197_ = lean_unsigned_to_nat(1u);
v_n_198_ = lean_nat_sub(v_x_190_, v_one_197_);
v___x_199_ = lean_apply_2(v_h__2_193_, v_n_198_, v_x_191_);
return v___x_199_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeat_match__1_splitter___redArg___boxed(lean_object* v_x_200_, lean_object* v_x_201_, lean_object* v_h__1_202_, lean_object* v_h__2_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l___private_Init_Data_Nat_Basic_0__Nat_repeat_match__1_splitter___redArg(v_x_200_, v_x_201_, v_h__1_202_, v_h__2_203_);
lean_dec(v_x_200_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeat_match__1_splitter(lean_object* v_00_u03b1_205_, lean_object* v_motive_206_, lean_object* v_x_207_, lean_object* v_x_208_, lean_object* v_h__1_209_, lean_object* v_h__2_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l___private_Init_Data_Nat_Basic_0__Nat_repeat_match__1_splitter___redArg(v_x_207_, v_x_208_, v_h__1_209_, v_h__2_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeat_match__1_splitter___boxed(lean_object* v_00_u03b1_212_, lean_object* v_motive_213_, lean_object* v_x_214_, lean_object* v_x_215_, lean_object* v_h__1_216_, lean_object* v_h__2_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l___private_Init_Data_Nat_Basic_0__Nat_repeat_match__1_splitter(v_00_u03b1_212_, v_motive_213_, v_x_214_, v_x_215_, v_h__1_216_, v_h__2_217_);
lean_dec(v_x_214_);
return v_res_218_;
}
}
lean_object* runtime_initialize_Init_SimpLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_NeZero(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Nat_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

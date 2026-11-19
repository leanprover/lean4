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
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___redArg(lean_object* v_f_68_, lean_object* v_x_69_, lean_object* v_x_70_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_object* v_00_u03b1_77_, lean_object* v_f_78_, lean_object* v_x_79_, lean_object* v_x_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___redArg(v_f_78_, v_x_79_, v_x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Nat_repeatTR___redArg(lean_object* v_f_82_, lean_object* v_n_83_, lean_object* v_a_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___redArg(v_f_82_, v_n_83_, v_a_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Nat_repeatTR(lean_object* v_00_u03b1_86_, lean_object* v_f_87_, lean_object* v_n_88_, lean_object* v_a_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___redArg(v_f_87_, v_n_88_, v_a_89_);
return v___x_90_;
}
}
LEAN_EXPORT uint8_t l_Nat_blt(lean_object* v_a_91_, lean_object* v_b_92_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_93_ = lean_unsigned_to_nat(1u);
v___x_94_ = lean_nat_add(v_a_91_, v___x_93_);
v___x_95_ = lean_nat_dec_le(v___x_94_, v_b_92_);
lean_dec(v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Nat_blt___boxed(lean_object* v_a_96_, lean_object* v_b_97_){
_start:
{
uint8_t v_res_98_; lean_object* v_r_99_; 
v_res_98_ = l_Nat_blt(v_a_96_, v_b_97_);
lean_dec(v_b_97_);
lean_dec(v_a_96_);
v_r_99_ = lean_box(v_res_98_);
return v_r_99_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter___redArg(lean_object* v_x_100_, lean_object* v_x_101_, lean_object* v_h__1_102_, lean_object* v_h__2_103_, lean_object* v_h__3_104_, lean_object* v_h__4_105_){
_start:
{
lean_object* v_zero_106_; uint8_t v_isZero_107_; 
v_zero_106_ = lean_unsigned_to_nat(0u);
v_isZero_107_ = lean_nat_dec_eq(v_x_100_, v_zero_106_);
if (v_isZero_107_ == 1)
{
uint8_t v_isZero_108_; 
lean_dec(v_h__4_105_);
lean_dec(v_h__3_104_);
v_isZero_108_ = lean_nat_dec_eq(v_x_101_, v_zero_106_);
if (v_isZero_108_ == 1)
{
lean_object* v___x_109_; lean_object* v___x_110_; 
lean_dec(v_h__2_103_);
v___x_109_ = lean_box(0);
v___x_110_ = lean_apply_1(v_h__1_102_, v___x_109_);
return v___x_110_;
}
else
{
lean_object* v_one_111_; lean_object* v_n_112_; lean_object* v___x_113_; 
lean_dec(v_h__1_102_);
v_one_111_ = lean_unsigned_to_nat(1u);
v_n_112_ = lean_nat_sub(v_x_101_, v_one_111_);
v___x_113_ = lean_apply_1(v_h__2_103_, v_n_112_);
return v___x_113_;
}
}
else
{
lean_object* v_one_114_; lean_object* v_n_115_; uint8_t v_isZero_116_; 
lean_dec(v_h__2_103_);
lean_dec(v_h__1_102_);
v_one_114_ = lean_unsigned_to_nat(1u);
v_n_115_ = lean_nat_sub(v_x_100_, v_one_114_);
v_isZero_116_ = lean_nat_dec_eq(v_x_101_, v_zero_106_);
if (v_isZero_116_ == 1)
{
lean_object* v___x_117_; 
lean_dec(v_h__4_105_);
v___x_117_ = lean_apply_1(v_h__3_104_, v_n_115_);
return v___x_117_;
}
else
{
lean_object* v_n_118_; lean_object* v___x_119_; 
lean_dec(v_h__3_104_);
v_n_118_ = lean_nat_sub(v_x_101_, v_one_114_);
v___x_119_ = lean_apply_2(v_h__4_105_, v_n_115_, v_n_118_);
return v___x_119_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter___redArg___boxed(lean_object* v_x_120_, lean_object* v_x_121_, lean_object* v_h__1_122_, lean_object* v_h__2_123_, lean_object* v_h__3_124_, lean_object* v_h__4_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter___redArg(v_x_120_, v_x_121_, v_h__1_122_, v_h__2_123_, v_h__3_124_, v_h__4_125_);
lean_dec(v_x_121_);
lean_dec(v_x_120_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter(lean_object* v_motive_127_, lean_object* v_x_128_, lean_object* v_x_129_, lean_object* v_h__1_130_, lean_object* v_h__2_131_, lean_object* v_h__3_132_, lean_object* v_h__4_133_){
_start:
{
lean_object* v_zero_134_; uint8_t v_isZero_135_; 
v_zero_134_ = lean_unsigned_to_nat(0u);
v_isZero_135_ = lean_nat_dec_eq(v_x_128_, v_zero_134_);
if (v_isZero_135_ == 1)
{
uint8_t v_isZero_136_; 
lean_dec(v_h__4_133_);
lean_dec(v_h__3_132_);
v_isZero_136_ = lean_nat_dec_eq(v_x_129_, v_zero_134_);
if (v_isZero_136_ == 1)
{
lean_object* v___x_137_; lean_object* v___x_138_; 
lean_dec(v_h__2_131_);
v___x_137_ = lean_box(0);
v___x_138_ = lean_apply_1(v_h__1_130_, v___x_137_);
return v___x_138_;
}
else
{
lean_object* v_one_139_; lean_object* v_n_140_; lean_object* v___x_141_; 
lean_dec(v_h__1_130_);
v_one_139_ = lean_unsigned_to_nat(1u);
v_n_140_ = lean_nat_sub(v_x_129_, v_one_139_);
v___x_141_ = lean_apply_1(v_h__2_131_, v_n_140_);
return v___x_141_;
}
}
else
{
lean_object* v_one_142_; lean_object* v_n_143_; uint8_t v_isZero_144_; 
lean_dec(v_h__2_131_);
lean_dec(v_h__1_130_);
v_one_142_ = lean_unsigned_to_nat(1u);
v_n_143_ = lean_nat_sub(v_x_128_, v_one_142_);
v_isZero_144_ = lean_nat_dec_eq(v_x_129_, v_zero_134_);
if (v_isZero_144_ == 1)
{
lean_object* v___x_145_; 
lean_dec(v_h__4_133_);
v___x_145_ = lean_apply_1(v_h__3_132_, v_n_143_);
return v___x_145_;
}
else
{
lean_object* v_n_146_; lean_object* v___x_147_; 
lean_dec(v_h__3_132_);
v_n_146_ = lean_nat_sub(v_x_129_, v_one_142_);
v___x_147_ = lean_apply_2(v_h__4_133_, v_n_143_, v_n_146_);
return v___x_147_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter___boxed(lean_object* v_motive_148_, lean_object* v_x_149_, lean_object* v_x_150_, lean_object* v_h__1_151_, lean_object* v_h__2_152_, lean_object* v_h__3_153_, lean_object* v_h__4_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter(v_motive_148_, v_x_149_, v_x_150_, v_h__1_151_, v_h__2_152_, v_h__3_153_, v_h__4_154_);
lean_dec(v_x_150_);
lean_dec(v_x_149_);
return v_res_155_;
}
}
static lean_object* _init_l_Nat_instTransLt(void){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = lean_box(0);
return v___x_156_;
}
}
static lean_object* _init_l_Nat_instTransLe(void){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = lean_box(0);
return v___x_157_;
}
}
static lean_object* _init_l_Nat_instTransLtLe(void){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = lean_box(0);
return v___x_158_;
}
}
static lean_object* _init_l_Nat_instTransLeLt(void){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = lean_box(0);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Nat_min(lean_object* v_n_160_, lean_object* v_m_161_){
_start:
{
uint8_t v___x_162_; 
v___x_162_ = lean_nat_dec_le(v_n_160_, v_m_161_);
if (v___x_162_ == 0)
{
lean_inc(v_m_161_);
return v_m_161_;
}
else
{
lean_inc(v_n_160_);
return v_n_160_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_min___boxed(lean_object* v_n_163_, lean_object* v_m_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Nat_min(v_n_163_, v_m_164_);
lean_dec(v_m_164_);
lean_dec(v_n_163_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Nat_instMax___lam__0(lean_object* v_x_166_, lean_object* v_y_167_){
_start:
{
uint8_t v___x_168_; 
v___x_168_ = lean_nat_dec_le(v_x_166_, v_y_167_);
if (v___x_168_ == 0)
{
lean_inc(v_x_166_);
return v_x_166_;
}
else
{
lean_inc(v_y_167_);
return v_y_167_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_instMax___lam__0___boxed(lean_object* v_x_169_, lean_object* v_y_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Nat_instMax___lam__0(v_x_169_, v_y_170_);
lean_dec(v_y_170_);
lean_dec(v_x_169_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Nat_max(lean_object* v_n_174_, lean_object* v_m_175_){
_start:
{
uint8_t v___x_176_; 
v___x_176_ = lean_nat_dec_le(v_n_174_, v_m_175_);
if (v___x_176_ == 0)
{
lean_inc(v_n_174_);
return v_n_174_;
}
else
{
lean_inc(v_m_175_);
return v_m_175_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_max___boxed(lean_object* v_n_177_, lean_object* v_m_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Nat_max(v_n_177_, v_m_178_);
lean_dec(v_m_178_);
lean_dec(v_n_177_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeat_match__1_splitter___redArg(lean_object* v_x_180_, lean_object* v_x_181_, lean_object* v_h__1_182_, lean_object* v_h__2_183_){
_start:
{
lean_object* v_zero_184_; uint8_t v_isZero_185_; 
v_zero_184_ = lean_unsigned_to_nat(0u);
v_isZero_185_ = lean_nat_dec_eq(v_x_180_, v_zero_184_);
if (v_isZero_185_ == 1)
{
lean_object* v___x_186_; 
lean_dec(v_h__2_183_);
v___x_186_ = lean_apply_1(v_h__1_182_, v_x_181_);
return v___x_186_;
}
else
{
lean_object* v_one_187_; lean_object* v_n_188_; lean_object* v___x_189_; 
lean_dec(v_h__1_182_);
v_one_187_ = lean_unsigned_to_nat(1u);
v_n_188_ = lean_nat_sub(v_x_180_, v_one_187_);
v___x_189_ = lean_apply_2(v_h__2_183_, v_n_188_, v_x_181_);
return v___x_189_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeat_match__1_splitter___redArg___boxed(lean_object* v_x_190_, lean_object* v_x_191_, lean_object* v_h__1_192_, lean_object* v_h__2_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l___private_Init_Data_Nat_Basic_0__Nat_repeat_match__1_splitter___redArg(v_x_190_, v_x_191_, v_h__1_192_, v_h__2_193_);
lean_dec(v_x_190_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeat_match__1_splitter(lean_object* v_00_u03b1_195_, lean_object* v_motive_196_, lean_object* v_x_197_, lean_object* v_x_198_, lean_object* v_h__1_199_, lean_object* v_h__2_200_){
_start:
{
lean_object* v_zero_201_; uint8_t v_isZero_202_; 
v_zero_201_ = lean_unsigned_to_nat(0u);
v_isZero_202_ = lean_nat_dec_eq(v_x_197_, v_zero_201_);
if (v_isZero_202_ == 1)
{
lean_object* v___x_203_; 
lean_dec(v_h__2_200_);
v___x_203_ = lean_apply_1(v_h__1_199_, v_x_198_);
return v___x_203_;
}
else
{
lean_object* v_one_204_; lean_object* v_n_205_; lean_object* v___x_206_; 
lean_dec(v_h__1_199_);
v_one_204_ = lean_unsigned_to_nat(1u);
v_n_205_ = lean_nat_sub(v_x_197_, v_one_204_);
v___x_206_ = lean_apply_2(v_h__2_200_, v_n_205_, v_x_198_);
return v___x_206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeat_match__1_splitter___boxed(lean_object* v_00_u03b1_207_, lean_object* v_motive_208_, lean_object* v_x_209_, lean_object* v_x_210_, lean_object* v_h__1_211_, lean_object* v_h__2_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l___private_Init_Data_Nat_Basic_0__Nat_repeat_match__1_splitter(v_00_u03b1_207_, v_motive_208_, v_x_209_, v_x_210_, v_h__1_211_, v_h__2_212_);
lean_dec(v_x_209_);
return v_res_213_;
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

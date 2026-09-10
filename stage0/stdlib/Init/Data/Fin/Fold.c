// Lean compiler output
// Module: Init.Data.Fin.Fold
// Imports: public import Init.Control.Lawful.Basic public import Init.Ext import Init.Data.Fin.Lemmas import Init.Data.Nat.Lemmas import Init.Omega import Init.TacticsExtra import Init.WFTactics import Init.Hints
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Fin_succ___redArg(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldl___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldl___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldl_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldl_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldl_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldl_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldlTR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldlTR___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldlTR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldlTR___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldr_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldr_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldr_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldrM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldrM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldrM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldl_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldl_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldl_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldl_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldl___redArg___lam__0(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_i_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = l_Fin_succ___redArg(v_i_3_);
v___x_5_ = lean_apply_2(v_x_1_, v_x_2_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldl___redArg___lam__0___boxed(lean_object* v_x_6_, lean_object* v_x_7_, lean_object* v_i_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Fin_foldl___redArg___lam__0(v_x_6_, v_x_7_, v_i_8_);
lean_dec(v_i_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldl___redArg(lean_object* v_x_10_, lean_object* v_x_11_, lean_object* v_x_12_){
_start:
{
lean_object* v_zero_13_; uint8_t v_isZero_14_; 
v_zero_13_ = lean_unsigned_to_nat(0u);
v_isZero_14_ = lean_nat_dec_eq(v_x_10_, v_zero_13_);
if (v_isZero_14_ == 1)
{
lean_dec(v_x_11_);
lean_dec(v_x_10_);
return v_x_12_;
}
else
{
lean_object* v___f_15_; lean_object* v_one_16_; lean_object* v_n_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
lean_inc(v_x_11_);
v___f_15_ = lean_alloc_closure((void*)(l_Fin_foldl___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_15_, 0, v_x_11_);
v_one_16_ = lean_unsigned_to_nat(1u);
v_n_17_ = lean_nat_sub(v_x_10_, v_one_16_);
lean_dec(v_x_10_);
v___x_18_ = lean_nat_add(v_n_17_, v_one_16_);
v___x_19_ = lean_nat_mod(v_zero_13_, v___x_18_);
lean_dec(v___x_18_);
v___x_20_ = lean_apply_2(v_x_11_, v_x_12_, v___x_19_);
v_x_10_ = v_n_17_;
v_x_11_ = v___f_15_;
v_x_12_ = v___x_20_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Fin_foldl(lean_object* v_00_u03b1_22_, lean_object* v_x_23_, lean_object* v_x_24_, lean_object* v_x_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Fin_foldl___redArg(v_x_23_, v_x_24_, v_x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldl_loop___redArg(lean_object* v_n_27_, lean_object* v_f_28_, lean_object* v_x_29_, lean_object* v_i_30_){
_start:
{
uint8_t v___x_31_; 
v___x_31_ = lean_nat_dec_lt(v_i_30_, v_n_27_);
if (v___x_31_ == 0)
{
lean_dec(v_i_30_);
lean_dec(v_f_28_);
return v_x_29_;
}
else
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
lean_inc(v_f_28_);
lean_inc(v_i_30_);
v___x_32_ = lean_apply_2(v_f_28_, v_x_29_, v_i_30_);
v___x_33_ = lean_unsigned_to_nat(1u);
v___x_34_ = lean_nat_add(v_i_30_, v___x_33_);
lean_dec(v_i_30_);
v_x_29_ = v___x_32_;
v_i_30_ = v___x_34_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Fin_foldl_loop___redArg___boxed(lean_object* v_n_36_, lean_object* v_f_37_, lean_object* v_x_38_, lean_object* v_i_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Fin_foldl_loop___redArg(v_n_36_, v_f_37_, v_x_38_, v_i_39_);
lean_dec(v_n_36_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldl_loop(lean_object* v_00_u03b1_41_, lean_object* v_n_42_, lean_object* v_f_43_, lean_object* v_x_44_, lean_object* v_i_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Fin_foldl_loop___redArg(v_n_42_, v_f_43_, v_x_44_, v_i_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldl_loop___boxed(lean_object* v_00_u03b1_47_, lean_object* v_n_48_, lean_object* v_f_49_, lean_object* v_x_50_, lean_object* v_i_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Fin_foldl_loop(v_00_u03b1_47_, v_n_48_, v_f_49_, v_x_50_, v_i_51_);
lean_dec(v_n_48_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldlTR___redArg(lean_object* v_n_53_, lean_object* v_f_54_, lean_object* v_init_55_){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lean_unsigned_to_nat(0u);
v___x_57_ = l_Fin_foldl_loop___redArg(v_n_53_, v_f_54_, v_init_55_, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldlTR___redArg___boxed(lean_object* v_n_58_, lean_object* v_f_59_, lean_object* v_init_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Fin_foldlTR___redArg(v_n_58_, v_f_59_, v_init_60_);
lean_dec(v_n_58_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldlTR(lean_object* v_00_u03b1_62_, lean_object* v_n_63_, lean_object* v_f_64_, lean_object* v_init_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = lean_unsigned_to_nat(0u);
v___x_67_ = l_Fin_foldl_loop___redArg(v_n_63_, v_f_64_, v_init_65_, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldlTR___boxed(lean_object* v_00_u03b1_68_, lean_object* v_n_69_, lean_object* v_f_70_, lean_object* v_init_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Fin_foldlTR(v_00_u03b1_68_, v_n_69_, v_f_70_, v_init_71_);
lean_dec(v_n_69_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldr_loop___redArg(lean_object* v_f_73_, lean_object* v_i_74_, lean_object* v_a_75_){
_start:
{
lean_object* v_zero_76_; uint8_t v_isZero_77_; 
v_zero_76_ = lean_unsigned_to_nat(0u);
v_isZero_77_ = lean_nat_dec_eq(v_i_74_, v_zero_76_);
if (v_isZero_77_ == 1)
{
lean_dec(v_i_74_);
lean_dec(v_f_73_);
return v_a_75_;
}
else
{
lean_object* v_one_78_; lean_object* v_n_79_; lean_object* v___x_80_; 
v_one_78_ = lean_unsigned_to_nat(1u);
v_n_79_ = lean_nat_sub(v_i_74_, v_one_78_);
lean_dec(v_i_74_);
lean_inc(v_f_73_);
lean_inc(v_n_79_);
v___x_80_ = lean_apply_2(v_f_73_, v_n_79_, v_a_75_);
v_i_74_ = v_n_79_;
v_a_75_ = v___x_80_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Fin_foldr_loop(lean_object* v_00_u03b1_82_, lean_object* v_n_83_, lean_object* v_f_84_, lean_object* v_i_85_, lean_object* v_a_86_, lean_object* v_a_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Fin_foldr_loop___redArg(v_f_84_, v_i_85_, v_a_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldr_loop___boxed(lean_object* v_00_u03b1_89_, lean_object* v_n_90_, lean_object* v_f_91_, lean_object* v_i_92_, lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Fin_foldr_loop(v_00_u03b1_89_, v_n_90_, v_f_91_, v_i_92_, v_a_93_, v_a_94_);
lean_dec(v_n_90_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldr___redArg(lean_object* v_n_96_, lean_object* v_f_97_, lean_object* v_init_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Fin_foldr_loop___redArg(v_f_97_, v_n_96_, v_init_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldr(lean_object* v_00_u03b1_100_, lean_object* v_n_101_, lean_object* v_f_102_, lean_object* v_init_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Fin_foldr_loop___redArg(v_f_102_, v_n_101_, v_init_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg___lam__0___boxed(lean_object* v_i_105_, lean_object* v_inst_106_, lean_object* v_n_107_, lean_object* v_f_108_, lean_object* v_x_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg___lam__0(v_i_105_, v_inst_106_, v_n_107_, v_f_108_, v_x_109_);
lean_dec(v_i_105_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg(lean_object* v_inst_111_, lean_object* v_n_112_, lean_object* v_f_113_, lean_object* v_x_114_, lean_object* v_i_115_){
_start:
{
lean_object* v_toApplicative_116_; lean_object* v_toBind_117_; lean_object* v_toPure_118_; uint8_t v___x_119_; 
v_toApplicative_116_ = lean_ctor_get(v_inst_111_, 0);
v_toBind_117_ = lean_ctor_get(v_inst_111_, 1);
lean_inc(v_toBind_117_);
v_toPure_118_ = lean_ctor_get(v_toApplicative_116_, 1);
v___x_119_ = lean_nat_dec_lt(v_i_115_, v_n_112_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; 
lean_inc(v_toPure_118_);
lean_dec(v_toBind_117_);
lean_dec(v_i_115_);
lean_dec(v_f_113_);
lean_dec(v_n_112_);
lean_dec_ref(v_inst_111_);
v___x_120_ = lean_apply_2(v_toPure_118_, lean_box(0), v_x_114_);
return v___x_120_;
}
else
{
lean_object* v___f_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
lean_inc(v_f_113_);
lean_inc(v_i_115_);
v___f_121_ = lean_alloc_closure((void*)(l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_121_, 0, v_i_115_);
lean_closure_set(v___f_121_, 1, v_inst_111_);
lean_closure_set(v___f_121_, 2, v_n_112_);
lean_closure_set(v___f_121_, 3, v_f_113_);
v___x_122_ = lean_apply_2(v_f_113_, v_x_114_, v_i_115_);
v___x_123_ = lean_apply_4(v_toBind_117_, lean_box(0), lean_box(0), v___x_122_, v___f_121_);
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg___lam__0(lean_object* v_i_124_, lean_object* v_inst_125_, lean_object* v_n_126_, lean_object* v_f_127_, lean_object* v_x_128_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = lean_unsigned_to_nat(1u);
v___x_130_ = lean_nat_add(v_i_124_, v___x_129_);
v___x_131_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg(v_inst_125_, v_n_126_, v_f_127_, v_x_128_, v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop(lean_object* v_m_132_, lean_object* v_00_u03b1_133_, lean_object* v_inst_134_, lean_object* v_n_135_, lean_object* v_f_136_, lean_object* v_x_137_, lean_object* v_i_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg(v_inst_134_, v_n_135_, v_f_136_, v_x_137_, v_i_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldlM___redArg(lean_object* v_inst_140_, lean_object* v_n_141_, lean_object* v_f_142_, lean_object* v_init_143_){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg(v_inst_140_, v_n_141_, v_f_142_, v_init_143_, v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldlM(lean_object* v_m_146_, lean_object* v_00_u03b1_147_, lean_object* v_inst_148_, lean_object* v_n_149_, lean_object* v_f_150_, lean_object* v_init_151_){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_unsigned_to_nat(0u);
v___x_153_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg(v_inst_148_, v_n_149_, v_f_150_, v_init_151_, v___x_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___redArg___boxed(lean_object* v_inst_154_, lean_object* v_f_155_, lean_object* v_a_156_, lean_object* v_a_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___redArg(v_inst_154_, v_f_155_, v_a_156_, v_a_157_);
lean_dec(v_a_156_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___redArg(lean_object* v_inst_159_, lean_object* v_f_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v_toApplicative_163_; lean_object* v_toBind_164_; lean_object* v_toPure_165_; lean_object* v_zero_166_; uint8_t v_isZero_167_; 
v_toApplicative_163_ = lean_ctor_get(v_inst_159_, 0);
v_toBind_164_ = lean_ctor_get(v_inst_159_, 1);
lean_inc(v_toBind_164_);
v_toPure_165_ = lean_ctor_get(v_toApplicative_163_, 1);
v_zero_166_ = lean_unsigned_to_nat(0u);
v_isZero_167_ = lean_nat_dec_eq(v_a_161_, v_zero_166_);
if (v_isZero_167_ == 1)
{
lean_object* v___x_168_; 
lean_inc(v_toPure_165_);
lean_dec(v_toBind_164_);
lean_dec(v_f_160_);
lean_dec_ref(v_inst_159_);
v___x_168_ = lean_apply_2(v_toPure_165_, lean_box(0), v_a_162_);
return v___x_168_;
}
else
{
lean_object* v_one_169_; lean_object* v_n_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v_one_169_ = lean_unsigned_to_nat(1u);
v_n_170_ = lean_nat_sub(v_a_161_, v_one_169_);
lean_inc(v_f_160_);
lean_inc(v_n_170_);
v___x_171_ = lean_apply_2(v_f_160_, v_n_170_, v_a_162_);
v___x_172_ = lean_alloc_closure((void*)(l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___redArg___boxed), 4, 3);
lean_closure_set(v___x_172_, 0, v_inst_159_);
lean_closure_set(v___x_172_, 1, v_f_160_);
lean_closure_set(v___x_172_, 2, v_n_170_);
v___x_173_ = lean_apply_4(v_toBind_164_, lean_box(0), lean_box(0), v___x_171_, v___x_172_);
return v___x_173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop(lean_object* v_m_174_, lean_object* v_00_u03b1_175_, lean_object* v_inst_176_, lean_object* v_n_177_, lean_object* v_f_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___redArg(v_inst_176_, v_f_178_, v_a_179_, v_a_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___boxed(lean_object* v_m_182_, lean_object* v_00_u03b1_183_, lean_object* v_inst_184_, lean_object* v_n_185_, lean_object* v_f_186_, lean_object* v_a_187_, lean_object* v_a_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop(v_m_182_, v_00_u03b1_183_, v_inst_184_, v_n_185_, v_f_186_, v_a_187_, v_a_188_);
lean_dec(v_a_187_);
lean_dec(v_n_185_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop_match__1_splitter___redArg(lean_object* v_x_190_, lean_object* v_x_191_, lean_object* v_h__1_192_, lean_object* v_h__2_193_){
_start:
{
lean_object* v_zero_194_; uint8_t v_isZero_195_; 
v_zero_194_ = lean_unsigned_to_nat(0u);
v_isZero_195_ = lean_nat_dec_eq(v_x_190_, v_zero_194_);
if (v_isZero_195_ == 1)
{
lean_object* v___x_196_; 
lean_dec(v_h__2_193_);
v___x_196_ = lean_apply_2(v_h__1_192_, lean_box(0), v_x_191_);
return v___x_196_;
}
else
{
lean_object* v_one_197_; lean_object* v_n_198_; lean_object* v___x_199_; 
lean_dec(v_h__1_192_);
v_one_197_ = lean_unsigned_to_nat(1u);
v_n_198_ = lean_nat_sub(v_x_190_, v_one_197_);
v___x_199_ = lean_apply_3(v_h__2_193_, v_n_198_, lean_box(0), v_x_191_);
return v___x_199_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop_match__1_splitter___redArg___boxed(lean_object* v_x_200_, lean_object* v_x_201_, lean_object* v_h__1_202_, lean_object* v_h__2_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop_match__1_splitter___redArg(v_x_200_, v_x_201_, v_h__1_202_, v_h__2_203_);
lean_dec(v_x_200_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop_match__1_splitter(lean_object* v_00_u03b1_205_, lean_object* v_n_206_, lean_object* v_motive_207_, lean_object* v_x_208_, lean_object* v_x_209_, lean_object* v_h__1_210_, lean_object* v_h__2_211_){
_start:
{
lean_object* v_zero_212_; uint8_t v_isZero_213_; 
v_zero_212_ = lean_unsigned_to_nat(0u);
v_isZero_213_ = lean_nat_dec_eq(v_x_208_, v_zero_212_);
if (v_isZero_213_ == 1)
{
lean_object* v___x_214_; 
lean_dec(v_h__2_211_);
v___x_214_ = lean_apply_2(v_h__1_210_, lean_box(0), v_x_209_);
return v___x_214_;
}
else
{
lean_object* v_one_215_; lean_object* v_n_216_; lean_object* v___x_217_; 
lean_dec(v_h__1_210_);
v_one_215_ = lean_unsigned_to_nat(1u);
v_n_216_ = lean_nat_sub(v_x_208_, v_one_215_);
v___x_217_ = lean_apply_3(v_h__2_211_, v_n_216_, lean_box(0), v_x_209_);
return v___x_217_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop_match__1_splitter___boxed(lean_object* v_00_u03b1_218_, lean_object* v_n_219_, lean_object* v_motive_220_, lean_object* v_x_221_, lean_object* v_x_222_, lean_object* v_h__1_223_, lean_object* v_h__2_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop_match__1_splitter(v_00_u03b1_218_, v_n_219_, v_motive_220_, v_x_221_, v_x_222_, v_h__1_223_, v_h__2_224_);
lean_dec(v_x_221_);
lean_dec(v_n_219_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldrM___redArg(lean_object* v_inst_226_, lean_object* v_n_227_, lean_object* v_f_228_, lean_object* v_init_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___redArg(v_inst_226_, v_f_228_, v_n_227_, v_init_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldrM___redArg___boxed(lean_object* v_inst_231_, lean_object* v_n_232_, lean_object* v_f_233_, lean_object* v_init_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Fin_foldrM___redArg(v_inst_231_, v_n_232_, v_f_233_, v_init_234_);
lean_dec(v_n_232_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldrM(lean_object* v_m_236_, lean_object* v_00_u03b1_237_, lean_object* v_inst_238_, lean_object* v_n_239_, lean_object* v_f_240_, lean_object* v_init_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___redArg(v_inst_238_, v_f_240_, v_n_239_, v_init_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldrM___boxed(lean_object* v_m_243_, lean_object* v_00_u03b1_244_, lean_object* v_inst_245_, lean_object* v_n_246_, lean_object* v_f_247_, lean_object* v_init_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Fin_foldrM(v_m_243_, v_00_u03b1_244_, v_inst_245_, v_n_246_, v_f_247_, v_init_248_);
lean_dec(v_n_246_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldl_match__1_splitter___redArg(lean_object* v_x_250_, lean_object* v_x_251_, lean_object* v_x_252_, lean_object* v_h__1_253_, lean_object* v_h__2_254_){
_start:
{
lean_object* v_zero_255_; uint8_t v_isZero_256_; 
v_zero_255_ = lean_unsigned_to_nat(0u);
v_isZero_256_ = lean_nat_dec_eq(v_x_250_, v_zero_255_);
if (v_isZero_256_ == 1)
{
lean_object* v___x_257_; 
lean_dec(v_h__2_254_);
v___x_257_ = lean_apply_2(v_h__1_253_, v_x_251_, v_x_252_);
return v___x_257_;
}
else
{
lean_object* v_one_258_; lean_object* v_n_259_; lean_object* v___x_260_; 
lean_dec(v_h__1_253_);
v_one_258_ = lean_unsigned_to_nat(1u);
v_n_259_ = lean_nat_sub(v_x_250_, v_one_258_);
v___x_260_ = lean_apply_3(v_h__2_254_, v_n_259_, v_x_251_, v_x_252_);
return v___x_260_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldl_match__1_splitter___redArg___boxed(lean_object* v_x_261_, lean_object* v_x_262_, lean_object* v_x_263_, lean_object* v_h__1_264_, lean_object* v_h__2_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l___private_Init_Data_Fin_Fold_0__Fin_foldl_match__1_splitter___redArg(v_x_261_, v_x_262_, v_x_263_, v_h__1_264_, v_h__2_265_);
lean_dec(v_x_261_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldl_match__1_splitter(lean_object* v_00_u03b1_267_, lean_object* v_motive_268_, lean_object* v_x_269_, lean_object* v_x_270_, lean_object* v_x_271_, lean_object* v_h__1_272_, lean_object* v_h__2_273_){
_start:
{
lean_object* v_zero_274_; uint8_t v_isZero_275_; 
v_zero_274_ = lean_unsigned_to_nat(0u);
v_isZero_275_ = lean_nat_dec_eq(v_x_269_, v_zero_274_);
if (v_isZero_275_ == 1)
{
lean_object* v___x_276_; 
lean_dec(v_h__2_273_);
v___x_276_ = lean_apply_2(v_h__1_272_, v_x_270_, v_x_271_);
return v___x_276_;
}
else
{
lean_object* v_one_277_; lean_object* v_n_278_; lean_object* v___x_279_; 
lean_dec(v_h__1_272_);
v_one_277_ = lean_unsigned_to_nat(1u);
v_n_278_ = lean_nat_sub(v_x_269_, v_one_277_);
v___x_279_ = lean_apply_3(v_h__2_273_, v_n_278_, v_x_270_, v_x_271_);
return v___x_279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldl_match__1_splitter___boxed(lean_object* v_00_u03b1_280_, lean_object* v_motive_281_, lean_object* v_x_282_, lean_object* v_x_283_, lean_object* v_x_284_, lean_object* v_h__1_285_, lean_object* v_h__2_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l___private_Init_Data_Fin_Fold_0__Fin_foldl_match__1_splitter(v_00_u03b1_280_, v_motive_281_, v_x_282_, v_x_283_, v_x_284_, v_h__1_285_, v_h__2_286_);
lean_dec(v_x_282_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter___redArg(lean_object* v_x_288_, lean_object* v_x_289_, lean_object* v_h__1_290_, lean_object* v_h__2_291_){
_start:
{
lean_object* v_zero_292_; uint8_t v_isZero_293_; 
v_zero_292_ = lean_unsigned_to_nat(0u);
v_isZero_293_ = lean_nat_dec_eq(v_x_288_, v_zero_292_);
if (v_isZero_293_ == 1)
{
lean_object* v___x_294_; 
lean_dec(v_h__2_291_);
v___x_294_ = lean_apply_2(v_h__1_290_, lean_box(0), v_x_289_);
return v___x_294_;
}
else
{
lean_object* v_one_295_; lean_object* v_n_296_; lean_object* v___x_297_; 
lean_dec(v_h__1_290_);
v_one_295_ = lean_unsigned_to_nat(1u);
v_n_296_ = lean_nat_sub(v_x_288_, v_one_295_);
v___x_297_ = lean_apply_3(v_h__2_291_, v_n_296_, lean_box(0), v_x_289_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter___redArg___boxed(lean_object* v_x_298_, lean_object* v_x_299_, lean_object* v_h__1_300_, lean_object* v_h__2_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter___redArg(v_x_298_, v_x_299_, v_h__1_300_, v_h__2_301_);
lean_dec(v_x_298_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter(lean_object* v_00_u03b1_303_, lean_object* v_n_304_, lean_object* v_motive_305_, lean_object* v_x_306_, lean_object* v_x_307_, lean_object* v_x_308_, lean_object* v_h__1_309_, lean_object* v_h__2_310_){
_start:
{
lean_object* v_zero_311_; uint8_t v_isZero_312_; 
v_zero_311_ = lean_unsigned_to_nat(0u);
v_isZero_312_ = lean_nat_dec_eq(v_x_306_, v_zero_311_);
if (v_isZero_312_ == 1)
{
lean_object* v___x_313_; 
lean_dec(v_h__2_310_);
v___x_313_ = lean_apply_2(v_h__1_309_, lean_box(0), v_x_308_);
return v___x_313_;
}
else
{
lean_object* v_one_314_; lean_object* v_n_315_; lean_object* v___x_316_; 
lean_dec(v_h__1_309_);
v_one_314_ = lean_unsigned_to_nat(1u);
v_n_315_ = lean_nat_sub(v_x_306_, v_one_314_);
v___x_316_ = lean_apply_3(v_h__2_310_, v_n_315_, lean_box(0), v_x_308_);
return v___x_316_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter___boxed(lean_object* v_00_u03b1_317_, lean_object* v_n_318_, lean_object* v_motive_319_, lean_object* v_x_320_, lean_object* v_x_321_, lean_object* v_x_322_, lean_object* v_h__1_323_, lean_object* v_h__2_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter(v_00_u03b1_317_, v_n_318_, v_motive_319_, v_x_320_, v_x_321_, v_x_322_, v_h__1_323_, v_h__2_324_);
lean_dec(v_x_320_);
lean_dec(v_n_318_);
return v_res_325_;
}
}
lean_object* runtime_initialize_Init_Control_Lawful_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Hints(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Fin_Fold(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Control_Lawful_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Hints(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Fin_Fold(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Control_Lawful_Basic(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
lean_object* initialize_Init_Hints(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Fin_Fold(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Lawful_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Hints(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Fold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Fin_Fold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Fin_Fold(builtin);
}
#ifdef __cplusplus
}
#endif

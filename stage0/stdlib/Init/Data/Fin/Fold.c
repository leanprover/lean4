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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldl_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldl_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldl_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldl_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldl_loop___redArg(lean_object* v_n_1_, lean_object* v_f_2_, lean_object* v_x_3_, lean_object* v_i_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_nat_dec_lt(v_i_4_, v_n_1_);
if (v___x_5_ == 0)
{
lean_dec(v_i_4_);
lean_dec(v_f_2_);
return v_x_3_;
}
else
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
lean_inc(v_f_2_);
lean_inc(v_i_4_);
v___x_6_ = lean_apply_2(v_f_2_, v_x_3_, v_i_4_);
v___x_7_ = lean_unsigned_to_nat(1u);
v___x_8_ = lean_nat_add(v_i_4_, v___x_7_);
lean_dec(v_i_4_);
v_x_3_ = v___x_6_;
v_i_4_ = v___x_8_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldl_loop___redArg___boxed(lean_object* v_n_10_, lean_object* v_f_11_, lean_object* v_x_12_, lean_object* v_i_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l___private_Init_Data_Fin_Fold_0__Fin_foldl_loop___redArg(v_n_10_, v_f_11_, v_x_12_, v_i_13_);
lean_dec(v_n_10_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldl_loop(lean_object* v_00_u03b1_15_, lean_object* v_n_16_, lean_object* v_f_17_, lean_object* v_x_18_, lean_object* v_i_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l___private_Init_Data_Fin_Fold_0__Fin_foldl_loop___redArg(v_n_16_, v_f_17_, v_x_18_, v_i_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldl_loop___boxed(lean_object* v_00_u03b1_21_, lean_object* v_n_22_, lean_object* v_f_23_, lean_object* v_x_24_, lean_object* v_i_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l___private_Init_Data_Fin_Fold_0__Fin_foldl_loop(v_00_u03b1_21_, v_n_22_, v_f_23_, v_x_24_, v_i_25_);
lean_dec(v_n_22_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldl___redArg(lean_object* v_n_27_, lean_object* v_f_28_, lean_object* v_init_29_){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = lean_unsigned_to_nat(0u);
v___x_31_ = l___private_Init_Data_Fin_Fold_0__Fin_foldl_loop___redArg(v_n_27_, v_f_28_, v_init_29_, v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldl___redArg___boxed(lean_object* v_n_32_, lean_object* v_f_33_, lean_object* v_init_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Fin_foldl___redArg(v_n_32_, v_f_33_, v_init_34_);
lean_dec(v_n_32_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldl(lean_object* v_00_u03b1_36_, lean_object* v_n_37_, lean_object* v_f_38_, lean_object* v_init_39_){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = lean_unsigned_to_nat(0u);
v___x_41_ = l___private_Init_Data_Fin_Fold_0__Fin_foldl_loop___redArg(v_n_37_, v_f_38_, v_init_39_, v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldl___boxed(lean_object* v_00_u03b1_42_, lean_object* v_n_43_, lean_object* v_f_44_, lean_object* v_init_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Fin_foldl(v_00_u03b1_42_, v_n_43_, v_f_44_, v_init_45_);
lean_dec(v_n_43_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldr_loop___redArg(lean_object* v_f_47_, lean_object* v_i_48_, lean_object* v_a_49_){
_start:
{
lean_object* v_zero_50_; uint8_t v_isZero_51_; 
v_zero_50_ = lean_unsigned_to_nat(0u);
v_isZero_51_ = lean_nat_dec_eq(v_i_48_, v_zero_50_);
if (v_isZero_51_ == 1)
{
lean_dec(v_i_48_);
lean_dec(v_f_47_);
return v_a_49_;
}
else
{
lean_object* v_one_52_; lean_object* v_n_53_; lean_object* v___x_54_; 
v_one_52_ = lean_unsigned_to_nat(1u);
v_n_53_ = lean_nat_sub(v_i_48_, v_one_52_);
lean_dec(v_i_48_);
lean_inc(v_f_47_);
lean_inc(v_n_53_);
v___x_54_ = lean_apply_2(v_f_47_, v_n_53_, v_a_49_);
v_i_48_ = v_n_53_;
v_a_49_ = v___x_54_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Fin_foldr_loop(lean_object* v_00_u03b1_56_, lean_object* v_n_57_, lean_object* v_f_58_, lean_object* v_i_59_, lean_object* v_a_60_, lean_object* v_a_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Fin_foldr_loop___redArg(v_f_58_, v_i_59_, v_a_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldr_loop___boxed(lean_object* v_00_u03b1_63_, lean_object* v_n_64_, lean_object* v_f_65_, lean_object* v_i_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Fin_foldr_loop(v_00_u03b1_63_, v_n_64_, v_f_65_, v_i_66_, v_a_67_, v_a_68_);
lean_dec(v_n_64_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldr___redArg(lean_object* v_n_70_, lean_object* v_f_71_, lean_object* v_init_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Fin_foldr_loop___redArg(v_f_71_, v_n_70_, v_init_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldr(lean_object* v_00_u03b1_74_, lean_object* v_n_75_, lean_object* v_f_76_, lean_object* v_init_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Fin_foldr_loop___redArg(v_f_76_, v_n_75_, v_init_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg___lam__0___boxed(lean_object* v_i_79_, lean_object* v_inst_80_, lean_object* v_n_81_, lean_object* v_f_82_, lean_object* v_x_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg___lam__0(v_i_79_, v_inst_80_, v_n_81_, v_f_82_, v_x_83_);
lean_dec(v_i_79_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg(lean_object* v_inst_85_, lean_object* v_n_86_, lean_object* v_f_87_, lean_object* v_x_88_, lean_object* v_i_89_){
_start:
{
uint8_t v___x_90_; 
v___x_90_ = lean_nat_dec_lt(v_i_89_, v_n_86_);
if (v___x_90_ == 0)
{
lean_object* v_toApplicative_91_; lean_object* v_toPure_92_; lean_object* v___x_93_; 
lean_dec(v_i_89_);
lean_dec(v_f_87_);
lean_dec(v_n_86_);
v_toApplicative_91_ = lean_ctor_get(v_inst_85_, 0);
lean_inc_ref(v_toApplicative_91_);
lean_dec_ref(v_inst_85_);
v_toPure_92_ = lean_ctor_get(v_toApplicative_91_, 1);
lean_inc(v_toPure_92_);
lean_dec_ref(v_toApplicative_91_);
v___x_93_ = lean_apply_2(v_toPure_92_, lean_box(0), v_x_88_);
return v___x_93_;
}
else
{
lean_object* v_toBind_94_; lean_object* v___f_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v_toBind_94_ = lean_ctor_get(v_inst_85_, 1);
lean_inc(v_toBind_94_);
lean_inc(v_f_87_);
lean_inc(v_i_89_);
v___f_95_ = lean_alloc_closure((void*)(l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_95_, 0, v_i_89_);
lean_closure_set(v___f_95_, 1, v_inst_85_);
lean_closure_set(v___f_95_, 2, v_n_86_);
lean_closure_set(v___f_95_, 3, v_f_87_);
v___x_96_ = lean_apply_2(v_f_87_, v_x_88_, v_i_89_);
v___x_97_ = lean_apply_4(v_toBind_94_, lean_box(0), lean_box(0), v___x_96_, v___f_95_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg___lam__0(lean_object* v_i_98_, lean_object* v_inst_99_, lean_object* v_n_100_, lean_object* v_f_101_, lean_object* v_x_102_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = lean_unsigned_to_nat(1u);
v___x_104_ = lean_nat_add(v_i_98_, v___x_103_);
v___x_105_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg(v_inst_99_, v_n_100_, v_f_101_, v_x_102_, v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop(lean_object* v_m_106_, lean_object* v_00_u03b1_107_, lean_object* v_inst_108_, lean_object* v_n_109_, lean_object* v_f_110_, lean_object* v_x_111_, lean_object* v_i_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg(v_inst_108_, v_n_109_, v_f_110_, v_x_111_, v_i_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldlM___redArg(lean_object* v_inst_114_, lean_object* v_n_115_, lean_object* v_f_116_, lean_object* v_init_117_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg(v_inst_114_, v_n_115_, v_f_116_, v_init_117_, v___x_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldlM(lean_object* v_m_120_, lean_object* v_00_u03b1_121_, lean_object* v_inst_122_, lean_object* v_n_123_, lean_object* v_f_124_, lean_object* v_init_125_){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg(v_inst_122_, v_n_123_, v_f_124_, v_init_125_, v___x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___redArg___boxed(lean_object* v_inst_128_, lean_object* v_f_129_, lean_object* v_a_130_, lean_object* v_a_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___redArg(v_inst_128_, v_f_129_, v_a_130_, v_a_131_);
lean_dec(v_a_130_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___redArg(lean_object* v_inst_133_, lean_object* v_f_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v_toApplicative_137_; lean_object* v_toBind_138_; lean_object* v_toPure_139_; lean_object* v_zero_140_; uint8_t v_isZero_141_; 
v_toApplicative_137_ = lean_ctor_get(v_inst_133_, 0);
v_toBind_138_ = lean_ctor_get(v_inst_133_, 1);
lean_inc(v_toBind_138_);
v_toPure_139_ = lean_ctor_get(v_toApplicative_137_, 1);
v_zero_140_ = lean_unsigned_to_nat(0u);
v_isZero_141_ = lean_nat_dec_eq(v_a_135_, v_zero_140_);
if (v_isZero_141_ == 1)
{
lean_object* v___x_142_; 
lean_inc(v_toPure_139_);
lean_dec(v_toBind_138_);
lean_dec(v_f_134_);
lean_dec_ref(v_inst_133_);
v___x_142_ = lean_apply_2(v_toPure_139_, lean_box(0), v_a_136_);
return v___x_142_;
}
else
{
lean_object* v_one_143_; lean_object* v_n_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v_one_143_ = lean_unsigned_to_nat(1u);
v_n_144_ = lean_nat_sub(v_a_135_, v_one_143_);
lean_inc(v_f_134_);
lean_inc(v_n_144_);
v___x_145_ = lean_apply_2(v_f_134_, v_n_144_, v_a_136_);
v___x_146_ = lean_alloc_closure((void*)(l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___redArg___boxed), 4, 3);
lean_closure_set(v___x_146_, 0, v_inst_133_);
lean_closure_set(v___x_146_, 1, v_f_134_);
lean_closure_set(v___x_146_, 2, v_n_144_);
v___x_147_ = lean_apply_4(v_toBind_138_, lean_box(0), lean_box(0), v___x_145_, v___x_146_);
return v___x_147_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop(lean_object* v_m_148_, lean_object* v_00_u03b1_149_, lean_object* v_inst_150_, lean_object* v_n_151_, lean_object* v_f_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___redArg(v_inst_150_, v_f_152_, v_a_153_, v_a_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___boxed(lean_object* v_m_156_, lean_object* v_00_u03b1_157_, lean_object* v_inst_158_, lean_object* v_n_159_, lean_object* v_f_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop(v_m_156_, v_00_u03b1_157_, v_inst_158_, v_n_159_, v_f_160_, v_a_161_, v_a_162_);
lean_dec(v_a_161_);
lean_dec(v_n_159_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop_match__1_splitter___redArg(lean_object* v_x_164_, lean_object* v_x_165_, lean_object* v_h__1_166_, lean_object* v_h__2_167_){
_start:
{
lean_object* v_zero_168_; uint8_t v_isZero_169_; 
v_zero_168_ = lean_unsigned_to_nat(0u);
v_isZero_169_ = lean_nat_dec_eq(v_x_164_, v_zero_168_);
if (v_isZero_169_ == 1)
{
lean_object* v___x_170_; 
lean_dec(v_h__2_167_);
v___x_170_ = lean_apply_2(v_h__1_166_, lean_box(0), v_x_165_);
return v___x_170_;
}
else
{
lean_object* v_one_171_; lean_object* v_n_172_; lean_object* v___x_173_; 
lean_dec(v_h__1_166_);
v_one_171_ = lean_unsigned_to_nat(1u);
v_n_172_ = lean_nat_sub(v_x_164_, v_one_171_);
v___x_173_ = lean_apply_3(v_h__2_167_, v_n_172_, lean_box(0), v_x_165_);
return v___x_173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop_match__1_splitter___redArg___boxed(lean_object* v_x_174_, lean_object* v_x_175_, lean_object* v_h__1_176_, lean_object* v_h__2_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop_match__1_splitter___redArg(v_x_174_, v_x_175_, v_h__1_176_, v_h__2_177_);
lean_dec(v_x_174_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop_match__1_splitter(lean_object* v_00_u03b1_179_, lean_object* v_n_180_, lean_object* v_motive_181_, lean_object* v_x_182_, lean_object* v_x_183_, lean_object* v_h__1_184_, lean_object* v_h__2_185_){
_start:
{
lean_object* v_zero_186_; uint8_t v_isZero_187_; 
v_zero_186_ = lean_unsigned_to_nat(0u);
v_isZero_187_ = lean_nat_dec_eq(v_x_182_, v_zero_186_);
if (v_isZero_187_ == 1)
{
lean_object* v___x_188_; 
lean_dec(v_h__2_185_);
v___x_188_ = lean_apply_2(v_h__1_184_, lean_box(0), v_x_183_);
return v___x_188_;
}
else
{
lean_object* v_one_189_; lean_object* v_n_190_; lean_object* v___x_191_; 
lean_dec(v_h__1_184_);
v_one_189_ = lean_unsigned_to_nat(1u);
v_n_190_ = lean_nat_sub(v_x_182_, v_one_189_);
v___x_191_ = lean_apply_3(v_h__2_185_, v_n_190_, lean_box(0), v_x_183_);
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop_match__1_splitter___boxed(lean_object* v_00_u03b1_192_, lean_object* v_n_193_, lean_object* v_motive_194_, lean_object* v_x_195_, lean_object* v_x_196_, lean_object* v_h__1_197_, lean_object* v_h__2_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop_match__1_splitter(v_00_u03b1_192_, v_n_193_, v_motive_194_, v_x_195_, v_x_196_, v_h__1_197_, v_h__2_198_);
lean_dec(v_x_195_);
lean_dec(v_n_193_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldrM___redArg(lean_object* v_inst_200_, lean_object* v_n_201_, lean_object* v_f_202_, lean_object* v_init_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___redArg(v_inst_200_, v_f_202_, v_n_201_, v_init_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldrM___redArg___boxed(lean_object* v_inst_205_, lean_object* v_n_206_, lean_object* v_f_207_, lean_object* v_init_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Fin_foldrM___redArg(v_inst_205_, v_n_206_, v_f_207_, v_init_208_);
lean_dec(v_n_206_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldrM(lean_object* v_m_210_, lean_object* v_00_u03b1_211_, lean_object* v_inst_212_, lean_object* v_n_213_, lean_object* v_f_214_, lean_object* v_init_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___redArg(v_inst_212_, v_f_214_, v_n_213_, v_init_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldrM___boxed(lean_object* v_m_217_, lean_object* v_00_u03b1_218_, lean_object* v_inst_219_, lean_object* v_n_220_, lean_object* v_f_221_, lean_object* v_init_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Fin_foldrM(v_m_217_, v_00_u03b1_218_, v_inst_219_, v_n_220_, v_f_221_, v_init_222_);
lean_dec(v_n_220_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter___redArg(lean_object* v_x_224_, lean_object* v_x_225_, lean_object* v_h__1_226_, lean_object* v_h__2_227_){
_start:
{
lean_object* v_zero_228_; uint8_t v_isZero_229_; 
v_zero_228_ = lean_unsigned_to_nat(0u);
v_isZero_229_ = lean_nat_dec_eq(v_x_224_, v_zero_228_);
if (v_isZero_229_ == 1)
{
lean_object* v___x_230_; 
lean_dec(v_h__2_227_);
v___x_230_ = lean_apply_2(v_h__1_226_, lean_box(0), v_x_225_);
return v___x_230_;
}
else
{
lean_object* v_one_231_; lean_object* v_n_232_; lean_object* v___x_233_; 
lean_dec(v_h__1_226_);
v_one_231_ = lean_unsigned_to_nat(1u);
v_n_232_ = lean_nat_sub(v_x_224_, v_one_231_);
v___x_233_ = lean_apply_3(v_h__2_227_, v_n_232_, lean_box(0), v_x_225_);
return v___x_233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter___redArg___boxed(lean_object* v_x_234_, lean_object* v_x_235_, lean_object* v_h__1_236_, lean_object* v_h__2_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter___redArg(v_x_234_, v_x_235_, v_h__1_236_, v_h__2_237_);
lean_dec(v_x_234_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter(lean_object* v_00_u03b1_239_, lean_object* v_n_240_, lean_object* v_motive_241_, lean_object* v_x_242_, lean_object* v_x_243_, lean_object* v_x_244_, lean_object* v_h__1_245_, lean_object* v_h__2_246_){
_start:
{
lean_object* v_zero_247_; uint8_t v_isZero_248_; 
v_zero_247_ = lean_unsigned_to_nat(0u);
v_isZero_248_ = lean_nat_dec_eq(v_x_242_, v_zero_247_);
if (v_isZero_248_ == 1)
{
lean_object* v___x_249_; 
lean_dec(v_h__2_246_);
v___x_249_ = lean_apply_2(v_h__1_245_, lean_box(0), v_x_244_);
return v___x_249_;
}
else
{
lean_object* v_one_250_; lean_object* v_n_251_; lean_object* v___x_252_; 
lean_dec(v_h__1_245_);
v_one_250_ = lean_unsigned_to_nat(1u);
v_n_251_ = lean_nat_sub(v_x_242_, v_one_250_);
v___x_252_ = lean_apply_3(v_h__2_246_, v_n_251_, lean_box(0), v_x_244_);
return v___x_252_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter___boxed(lean_object* v_00_u03b1_253_, lean_object* v_n_254_, lean_object* v_motive_255_, lean_object* v_x_256_, lean_object* v_x_257_, lean_object* v_x_258_, lean_object* v_h__1_259_, lean_object* v_h__2_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter(v_00_u03b1_253_, v_n_254_, v_motive_255_, v_x_256_, v_x_257_, v_x_258_, v_h__1_259_, v_h__2_260_);
lean_dec(v_x_256_);
lean_dec(v_n_254_);
return v_res_261_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Fin_Fold(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

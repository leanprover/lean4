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
lean_object* v___f_15_; lean_object* v_one_16_; lean_object* v_n_17_; lean_object* v___x_18_; 
lean_inc(v_x_11_);
v___f_15_ = lean_alloc_closure((void*)(l_Fin_foldl___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_15_, 0, v_x_11_);
v_one_16_ = lean_unsigned_to_nat(1u);
v_n_17_ = lean_nat_sub(v_x_10_, v_one_16_);
lean_dec(v_x_10_);
v___x_18_ = lean_apply_2(v_x_11_, v_x_12_, v_zero_13_);
v_x_10_ = v_n_17_;
v_x_11_ = v___f_15_;
v_x_12_ = v___x_18_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Fin_foldl(lean_object* v_00_u03b1_20_, lean_object* v_x_21_, lean_object* v_x_22_, lean_object* v_x_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Fin_foldl___redArg(v_x_21_, v_x_22_, v_x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldl_loop___redArg(lean_object* v_n_25_, lean_object* v_f_26_, lean_object* v_x_27_, lean_object* v_i_28_){
_start:
{
uint8_t v___x_29_; 
v___x_29_ = lean_nat_dec_lt(v_i_28_, v_n_25_);
if (v___x_29_ == 0)
{
lean_dec(v_i_28_);
lean_dec(v_f_26_);
return v_x_27_;
}
else
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
lean_inc(v_f_26_);
lean_inc(v_i_28_);
v___x_30_ = lean_apply_2(v_f_26_, v_x_27_, v_i_28_);
v___x_31_ = lean_unsigned_to_nat(1u);
v___x_32_ = lean_nat_add(v_i_28_, v___x_31_);
lean_dec(v_i_28_);
v_x_27_ = v___x_30_;
v_i_28_ = v___x_32_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Fin_foldl_loop___redArg___boxed(lean_object* v_n_34_, lean_object* v_f_35_, lean_object* v_x_36_, lean_object* v_i_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Fin_foldl_loop___redArg(v_n_34_, v_f_35_, v_x_36_, v_i_37_);
lean_dec(v_n_34_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldl_loop(lean_object* v_00_u03b1_39_, lean_object* v_n_40_, lean_object* v_f_41_, lean_object* v_x_42_, lean_object* v_i_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Fin_foldl_loop___redArg(v_n_40_, v_f_41_, v_x_42_, v_i_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldl_loop___boxed(lean_object* v_00_u03b1_45_, lean_object* v_n_46_, lean_object* v_f_47_, lean_object* v_x_48_, lean_object* v_i_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Fin_foldl_loop(v_00_u03b1_45_, v_n_46_, v_f_47_, v_x_48_, v_i_49_);
lean_dec(v_n_46_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldlTR___redArg(lean_object* v_n_51_, lean_object* v_f_52_, lean_object* v_init_53_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_unsigned_to_nat(0u);
v___x_55_ = l_Fin_foldl_loop___redArg(v_n_51_, v_f_52_, v_init_53_, v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldlTR___redArg___boxed(lean_object* v_n_56_, lean_object* v_f_57_, lean_object* v_init_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Fin_foldlTR___redArg(v_n_56_, v_f_57_, v_init_58_);
lean_dec(v_n_56_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldlTR(lean_object* v_00_u03b1_60_, lean_object* v_n_61_, lean_object* v_f_62_, lean_object* v_init_63_){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = lean_unsigned_to_nat(0u);
v___x_65_ = l_Fin_foldl_loop___redArg(v_n_61_, v_f_62_, v_init_63_, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldlTR___boxed(lean_object* v_00_u03b1_66_, lean_object* v_n_67_, lean_object* v_f_68_, lean_object* v_init_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Fin_foldlTR(v_00_u03b1_66_, v_n_67_, v_f_68_, v_init_69_);
lean_dec(v_n_67_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldr_loop___redArg(lean_object* v_f_71_, lean_object* v_i_72_, lean_object* v_a_73_){
_start:
{
lean_object* v_zero_74_; uint8_t v_isZero_75_; 
v_zero_74_ = lean_unsigned_to_nat(0u);
v_isZero_75_ = lean_nat_dec_eq(v_i_72_, v_zero_74_);
if (v_isZero_75_ == 1)
{
lean_dec(v_i_72_);
lean_dec(v_f_71_);
return v_a_73_;
}
else
{
lean_object* v_one_76_; lean_object* v_n_77_; lean_object* v___x_78_; 
v_one_76_ = lean_unsigned_to_nat(1u);
v_n_77_ = lean_nat_sub(v_i_72_, v_one_76_);
lean_dec(v_i_72_);
lean_inc(v_f_71_);
lean_inc(v_n_77_);
v___x_78_ = lean_apply_2(v_f_71_, v_n_77_, v_a_73_);
v_i_72_ = v_n_77_;
v_a_73_ = v___x_78_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Fin_foldr_loop(lean_object* v_00_u03b1_80_, lean_object* v_n_81_, lean_object* v_f_82_, lean_object* v_i_83_, lean_object* v_a_84_, lean_object* v_a_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Fin_foldr_loop___redArg(v_f_82_, v_i_83_, v_a_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldr_loop___boxed(lean_object* v_00_u03b1_87_, lean_object* v_n_88_, lean_object* v_f_89_, lean_object* v_i_90_, lean_object* v_a_91_, lean_object* v_a_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Fin_foldr_loop(v_00_u03b1_87_, v_n_88_, v_f_89_, v_i_90_, v_a_91_, v_a_92_);
lean_dec(v_n_88_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldr___redArg(lean_object* v_n_94_, lean_object* v_f_95_, lean_object* v_init_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Fin_foldr_loop___redArg(v_f_95_, v_n_94_, v_init_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldr(lean_object* v_00_u03b1_98_, lean_object* v_n_99_, lean_object* v_f_100_, lean_object* v_init_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Fin_foldr_loop___redArg(v_f_100_, v_n_99_, v_init_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg___lam__0___boxed(lean_object* v_i_103_, lean_object* v_inst_104_, lean_object* v_n_105_, lean_object* v_f_106_, lean_object* v_x_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg___lam__0(v_i_103_, v_inst_104_, v_n_105_, v_f_106_, v_x_107_);
lean_dec(v_i_103_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg(lean_object* v_inst_109_, lean_object* v_n_110_, lean_object* v_f_111_, lean_object* v_x_112_, lean_object* v_i_113_){
_start:
{
lean_object* v_toApplicative_114_; lean_object* v_toBind_115_; lean_object* v_toPure_116_; uint8_t v___x_117_; 
v_toApplicative_114_ = lean_ctor_get(v_inst_109_, 0);
v_toBind_115_ = lean_ctor_get(v_inst_109_, 1);
lean_inc(v_toBind_115_);
v_toPure_116_ = lean_ctor_get(v_toApplicative_114_, 1);
v___x_117_ = lean_nat_dec_lt(v_i_113_, v_n_110_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; 
lean_inc(v_toPure_116_);
lean_dec(v_toBind_115_);
lean_dec(v_i_113_);
lean_dec(v_f_111_);
lean_dec(v_n_110_);
lean_dec_ref(v_inst_109_);
v___x_118_ = lean_apply_2(v_toPure_116_, lean_box(0), v_x_112_);
return v___x_118_;
}
else
{
lean_object* v___f_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
lean_inc(v_f_111_);
lean_inc(v_i_113_);
v___f_119_ = lean_alloc_closure((void*)(l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_119_, 0, v_i_113_);
lean_closure_set(v___f_119_, 1, v_inst_109_);
lean_closure_set(v___f_119_, 2, v_n_110_);
lean_closure_set(v___f_119_, 3, v_f_111_);
v___x_120_ = lean_apply_2(v_f_111_, v_x_112_, v_i_113_);
v___x_121_ = lean_apply_4(v_toBind_115_, lean_box(0), lean_box(0), v___x_120_, v___f_119_);
return v___x_121_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg___lam__0(lean_object* v_i_122_, lean_object* v_inst_123_, lean_object* v_n_124_, lean_object* v_f_125_, lean_object* v_x_126_){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_127_ = lean_unsigned_to_nat(1u);
v___x_128_ = lean_nat_add(v_i_122_, v___x_127_);
v___x_129_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg(v_inst_123_, v_n_124_, v_f_125_, v_x_126_, v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop(lean_object* v_m_130_, lean_object* v_00_u03b1_131_, lean_object* v_inst_132_, lean_object* v_n_133_, lean_object* v_f_134_, lean_object* v_x_135_, lean_object* v_i_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg(v_inst_132_, v_n_133_, v_f_134_, v_x_135_, v_i_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldlM___redArg(lean_object* v_inst_138_, lean_object* v_n_139_, lean_object* v_f_140_, lean_object* v_init_141_){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_unsigned_to_nat(0u);
v___x_143_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg(v_inst_138_, v_n_139_, v_f_140_, v_init_141_, v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldlM(lean_object* v_m_144_, lean_object* v_00_u03b1_145_, lean_object* v_inst_146_, lean_object* v_n_147_, lean_object* v_f_148_, lean_object* v_init_149_){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_unsigned_to_nat(0u);
v___x_151_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg(v_inst_146_, v_n_147_, v_f_148_, v_init_149_, v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___redArg___boxed(lean_object* v_inst_152_, lean_object* v_f_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___redArg(v_inst_152_, v_f_153_, v_a_154_, v_a_155_);
lean_dec(v_a_154_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___redArg(lean_object* v_inst_157_, lean_object* v_f_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v_toApplicative_161_; lean_object* v_toBind_162_; lean_object* v_toPure_163_; lean_object* v_zero_164_; uint8_t v_isZero_165_; 
v_toApplicative_161_ = lean_ctor_get(v_inst_157_, 0);
v_toBind_162_ = lean_ctor_get(v_inst_157_, 1);
lean_inc(v_toBind_162_);
v_toPure_163_ = lean_ctor_get(v_toApplicative_161_, 1);
v_zero_164_ = lean_unsigned_to_nat(0u);
v_isZero_165_ = lean_nat_dec_eq(v_a_159_, v_zero_164_);
if (v_isZero_165_ == 1)
{
lean_object* v___x_166_; 
lean_inc(v_toPure_163_);
lean_dec(v_toBind_162_);
lean_dec(v_f_158_);
lean_dec_ref(v_inst_157_);
v___x_166_ = lean_apply_2(v_toPure_163_, lean_box(0), v_a_160_);
return v___x_166_;
}
else
{
lean_object* v_one_167_; lean_object* v_n_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v_one_167_ = lean_unsigned_to_nat(1u);
v_n_168_ = lean_nat_sub(v_a_159_, v_one_167_);
lean_inc(v_f_158_);
lean_inc(v_n_168_);
v___x_169_ = lean_apply_2(v_f_158_, v_n_168_, v_a_160_);
v___x_170_ = lean_alloc_closure((void*)(l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___redArg___boxed), 4, 3);
lean_closure_set(v___x_170_, 0, v_inst_157_);
lean_closure_set(v___x_170_, 1, v_f_158_);
lean_closure_set(v___x_170_, 2, v_n_168_);
v___x_171_ = lean_apply_4(v_toBind_162_, lean_box(0), lean_box(0), v___x_169_, v___x_170_);
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop(lean_object* v_m_172_, lean_object* v_00_u03b1_173_, lean_object* v_inst_174_, lean_object* v_n_175_, lean_object* v_f_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___redArg(v_inst_174_, v_f_176_, v_a_177_, v_a_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___boxed(lean_object* v_m_180_, lean_object* v_00_u03b1_181_, lean_object* v_inst_182_, lean_object* v_n_183_, lean_object* v_f_184_, lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop(v_m_180_, v_00_u03b1_181_, v_inst_182_, v_n_183_, v_f_184_, v_a_185_, v_a_186_);
lean_dec(v_a_185_);
lean_dec(v_n_183_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop_match__1_splitter___redArg(lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v_h__1_190_, lean_object* v_h__2_191_){
_start:
{
lean_object* v_zero_192_; uint8_t v_isZero_193_; 
v_zero_192_ = lean_unsigned_to_nat(0u);
v_isZero_193_ = lean_nat_dec_eq(v_x_188_, v_zero_192_);
if (v_isZero_193_ == 1)
{
lean_object* v___x_194_; 
lean_dec(v_h__2_191_);
v___x_194_ = lean_apply_2(v_h__1_190_, lean_box(0), v_x_189_);
return v___x_194_;
}
else
{
lean_object* v_one_195_; lean_object* v_n_196_; lean_object* v___x_197_; 
lean_dec(v_h__1_190_);
v_one_195_ = lean_unsigned_to_nat(1u);
v_n_196_ = lean_nat_sub(v_x_188_, v_one_195_);
v___x_197_ = lean_apply_3(v_h__2_191_, v_n_196_, lean_box(0), v_x_189_);
return v___x_197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop_match__1_splitter___redArg___boxed(lean_object* v_x_198_, lean_object* v_x_199_, lean_object* v_h__1_200_, lean_object* v_h__2_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop_match__1_splitter___redArg(v_x_198_, v_x_199_, v_h__1_200_, v_h__2_201_);
lean_dec(v_x_198_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop_match__1_splitter(lean_object* v_00_u03b1_203_, lean_object* v_n_204_, lean_object* v_motive_205_, lean_object* v_x_206_, lean_object* v_x_207_, lean_object* v_h__1_208_, lean_object* v_h__2_209_){
_start:
{
lean_object* v_zero_210_; uint8_t v_isZero_211_; 
v_zero_210_ = lean_unsigned_to_nat(0u);
v_isZero_211_ = lean_nat_dec_eq(v_x_206_, v_zero_210_);
if (v_isZero_211_ == 1)
{
lean_object* v___x_212_; 
lean_dec(v_h__2_209_);
v___x_212_ = lean_apply_2(v_h__1_208_, lean_box(0), v_x_207_);
return v___x_212_;
}
else
{
lean_object* v_one_213_; lean_object* v_n_214_; lean_object* v___x_215_; 
lean_dec(v_h__1_208_);
v_one_213_ = lean_unsigned_to_nat(1u);
v_n_214_ = lean_nat_sub(v_x_206_, v_one_213_);
v___x_215_ = lean_apply_3(v_h__2_209_, v_n_214_, lean_box(0), v_x_207_);
return v___x_215_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop_match__1_splitter___boxed(lean_object* v_00_u03b1_216_, lean_object* v_n_217_, lean_object* v_motive_218_, lean_object* v_x_219_, lean_object* v_x_220_, lean_object* v_h__1_221_, lean_object* v_h__2_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop_match__1_splitter(v_00_u03b1_216_, v_n_217_, v_motive_218_, v_x_219_, v_x_220_, v_h__1_221_, v_h__2_222_);
lean_dec(v_x_219_);
lean_dec(v_n_217_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldrM___redArg(lean_object* v_inst_224_, lean_object* v_n_225_, lean_object* v_f_226_, lean_object* v_init_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___redArg(v_inst_224_, v_f_226_, v_n_225_, v_init_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldrM___redArg___boxed(lean_object* v_inst_229_, lean_object* v_n_230_, lean_object* v_f_231_, lean_object* v_init_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Fin_foldrM___redArg(v_inst_229_, v_n_230_, v_f_231_, v_init_232_);
lean_dec(v_n_230_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldrM(lean_object* v_m_234_, lean_object* v_00_u03b1_235_, lean_object* v_inst_236_, lean_object* v_n_237_, lean_object* v_f_238_, lean_object* v_init_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___redArg(v_inst_236_, v_f_238_, v_n_237_, v_init_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldrM___boxed(lean_object* v_m_241_, lean_object* v_00_u03b1_242_, lean_object* v_inst_243_, lean_object* v_n_244_, lean_object* v_f_245_, lean_object* v_init_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Fin_foldrM(v_m_241_, v_00_u03b1_242_, v_inst_243_, v_n_244_, v_f_245_, v_init_246_);
lean_dec(v_n_244_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldl_match__1_splitter___redArg(lean_object* v_x_248_, lean_object* v_x_249_, lean_object* v_x_250_, lean_object* v_h__1_251_, lean_object* v_h__2_252_){
_start:
{
lean_object* v_zero_253_; uint8_t v_isZero_254_; 
v_zero_253_ = lean_unsigned_to_nat(0u);
v_isZero_254_ = lean_nat_dec_eq(v_x_248_, v_zero_253_);
if (v_isZero_254_ == 1)
{
lean_object* v___x_255_; 
lean_dec(v_h__2_252_);
v___x_255_ = lean_apply_2(v_h__1_251_, v_x_249_, v_x_250_);
return v___x_255_;
}
else
{
lean_object* v_one_256_; lean_object* v_n_257_; lean_object* v___x_258_; 
lean_dec(v_h__1_251_);
v_one_256_ = lean_unsigned_to_nat(1u);
v_n_257_ = lean_nat_sub(v_x_248_, v_one_256_);
v___x_258_ = lean_apply_3(v_h__2_252_, v_n_257_, v_x_249_, v_x_250_);
return v___x_258_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldl_match__1_splitter___redArg___boxed(lean_object* v_x_259_, lean_object* v_x_260_, lean_object* v_x_261_, lean_object* v_h__1_262_, lean_object* v_h__2_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l___private_Init_Data_Fin_Fold_0__Fin_foldl_match__1_splitter___redArg(v_x_259_, v_x_260_, v_x_261_, v_h__1_262_, v_h__2_263_);
lean_dec(v_x_259_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldl_match__1_splitter(lean_object* v_00_u03b1_265_, lean_object* v_motive_266_, lean_object* v_x_267_, lean_object* v_x_268_, lean_object* v_x_269_, lean_object* v_h__1_270_, lean_object* v_h__2_271_){
_start:
{
lean_object* v_zero_272_; uint8_t v_isZero_273_; 
v_zero_272_ = lean_unsigned_to_nat(0u);
v_isZero_273_ = lean_nat_dec_eq(v_x_267_, v_zero_272_);
if (v_isZero_273_ == 1)
{
lean_object* v___x_274_; 
lean_dec(v_h__2_271_);
v___x_274_ = lean_apply_2(v_h__1_270_, v_x_268_, v_x_269_);
return v___x_274_;
}
else
{
lean_object* v_one_275_; lean_object* v_n_276_; lean_object* v___x_277_; 
lean_dec(v_h__1_270_);
v_one_275_ = lean_unsigned_to_nat(1u);
v_n_276_ = lean_nat_sub(v_x_267_, v_one_275_);
v___x_277_ = lean_apply_3(v_h__2_271_, v_n_276_, v_x_268_, v_x_269_);
return v___x_277_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldl_match__1_splitter___boxed(lean_object* v_00_u03b1_278_, lean_object* v_motive_279_, lean_object* v_x_280_, lean_object* v_x_281_, lean_object* v_x_282_, lean_object* v_h__1_283_, lean_object* v_h__2_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l___private_Init_Data_Fin_Fold_0__Fin_foldl_match__1_splitter(v_00_u03b1_278_, v_motive_279_, v_x_280_, v_x_281_, v_x_282_, v_h__1_283_, v_h__2_284_);
lean_dec(v_x_280_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter___redArg(lean_object* v_x_286_, lean_object* v_x_287_, lean_object* v_h__1_288_, lean_object* v_h__2_289_){
_start:
{
lean_object* v_zero_290_; uint8_t v_isZero_291_; 
v_zero_290_ = lean_unsigned_to_nat(0u);
v_isZero_291_ = lean_nat_dec_eq(v_x_286_, v_zero_290_);
if (v_isZero_291_ == 1)
{
lean_object* v___x_292_; 
lean_dec(v_h__2_289_);
v___x_292_ = lean_apply_2(v_h__1_288_, lean_box(0), v_x_287_);
return v___x_292_;
}
else
{
lean_object* v_one_293_; lean_object* v_n_294_; lean_object* v___x_295_; 
lean_dec(v_h__1_288_);
v_one_293_ = lean_unsigned_to_nat(1u);
v_n_294_ = lean_nat_sub(v_x_286_, v_one_293_);
v___x_295_ = lean_apply_3(v_h__2_289_, v_n_294_, lean_box(0), v_x_287_);
return v___x_295_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter___redArg___boxed(lean_object* v_x_296_, lean_object* v_x_297_, lean_object* v_h__1_298_, lean_object* v_h__2_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter___redArg(v_x_296_, v_x_297_, v_h__1_298_, v_h__2_299_);
lean_dec(v_x_296_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter(lean_object* v_00_u03b1_301_, lean_object* v_n_302_, lean_object* v_motive_303_, lean_object* v_x_304_, lean_object* v_x_305_, lean_object* v_x_306_, lean_object* v_h__1_307_, lean_object* v_h__2_308_){
_start:
{
lean_object* v_zero_309_; uint8_t v_isZero_310_; 
v_zero_309_ = lean_unsigned_to_nat(0u);
v_isZero_310_ = lean_nat_dec_eq(v_x_304_, v_zero_309_);
if (v_isZero_310_ == 1)
{
lean_object* v___x_311_; 
lean_dec(v_h__2_308_);
v___x_311_ = lean_apply_2(v_h__1_307_, lean_box(0), v_x_306_);
return v___x_311_;
}
else
{
lean_object* v_one_312_; lean_object* v_n_313_; lean_object* v___x_314_; 
lean_dec(v_h__1_307_);
v_one_312_ = lean_unsigned_to_nat(1u);
v_n_313_ = lean_nat_sub(v_x_304_, v_one_312_);
v___x_314_ = lean_apply_3(v_h__2_308_, v_n_313_, lean_box(0), v_x_306_);
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter___boxed(lean_object* v_00_u03b1_315_, lean_object* v_n_316_, lean_object* v_motive_317_, lean_object* v_x_318_, lean_object* v_x_319_, lean_object* v_x_320_, lean_object* v_h__1_321_, lean_object* v_h__2_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter(v_00_u03b1_315_, v_n_316_, v_motive_317_, v_x_318_, v_x_319_, v_x_320_, v_h__1_321_, v_h__2_322_);
lean_dec(v_x_318_);
lean_dec(v_n_316_);
return v_res_323_;
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

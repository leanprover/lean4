// Lean compiler output
// Module: Std.Data.Iterators.Combinators.Monadic.StepSize
// Imports: public import Init.Data.Iterators.Consumers.Monadic.Access public import Init.Data.Iterators.Consumers.Monadic.Collect public import Init.Data.Iterators.Consumers.Monadic.Loop
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
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_stepSize___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_stepSize___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_stepSize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_stepSize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIterator___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instFinitenessRelation___redArg();
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instFinitenessRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instFinitenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instFinitenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instProductivenessRelation___redArg();
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instProductivenessRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instProductivenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instProductivenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_stepSize___redArg(lean_object* v_it_1_, lean_object* v_n_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_3_ = lean_unsigned_to_nat(0u);
v___x_4_ = lean_unsigned_to_nat(1u);
v___x_5_ = lean_nat_sub(v_n_2_, v___x_4_);
v___x_6_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6_, 0, v___x_3_);
lean_ctor_set(v___x_6_, 1, v___x_5_);
lean_ctor_set(v___x_6_, 2, v_it_1_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_stepSize___redArg___boxed(lean_object* v_it_7_, lean_object* v_n_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Std_IterM_stepSize___redArg(v_it_7_, v_n_8_);
lean_dec(v_n_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_stepSize(lean_object* v_00_u03b1_10_, lean_object* v_m_11_, lean_object* v_00_u03b2_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_it_16_, lean_object* v_n_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_18_ = lean_unsigned_to_nat(0u);
v___x_19_ = lean_unsigned_to_nat(1u);
v___x_20_ = lean_nat_sub(v_n_17_, v___x_19_);
v___x_21_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_21_, 0, v___x_18_);
lean_ctor_set(v___x_21_, 1, v___x_20_);
lean_ctor_set(v___x_21_, 2, v_it_16_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_stepSize___boxed(lean_object* v_00_u03b1_22_, lean_object* v_m_23_, lean_object* v_00_u03b2_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_it_28_, lean_object* v_n_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Std_IterM_stepSize(v_00_u03b1_22_, v_m_23_, v_00_u03b2_24_, v_inst_25_, v_inst_26_, v_inst_27_, v_it_28_, v_n_29_);
lean_dec(v_n_29_);
lean_dec_ref(v_inst_27_);
lean_dec(v_inst_26_);
lean_dec(v_inst_25_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg___lam__0(lean_object* v_n_31_, lean_object* v_s_32_){
_start:
{
switch(lean_obj_tag(v_s_32_))
{
case 0:
{
lean_object* v_it_33_; lean_object* v_out_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_42_; 
v_it_33_ = lean_ctor_get(v_s_32_, 0);
v_out_34_ = lean_ctor_get(v_s_32_, 1);
v_isSharedCheck_42_ = !lean_is_exclusive(v_s_32_);
if (v_isSharedCheck_42_ == 0)
{
v___x_36_ = v_s_32_;
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_out_34_);
lean_inc(v_it_33_);
lean_dec(v_s_32_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_38_; lean_object* v___x_40_; 
lean_inc(v_n_31_);
v___x_38_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_38_, 0, v_n_31_);
lean_ctor_set(v___x_38_, 1, v_n_31_);
lean_ctor_set(v___x_38_, 2, v_it_33_);
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 0, v___x_38_);
v___x_40_ = v___x_36_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_38_);
lean_ctor_set(v_reuseFailAlloc_41_, 1, v_out_34_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
case 1:
{
lean_object* v_it_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_51_; 
v_it_43_ = lean_ctor_get(v_s_32_, 0);
v_isSharedCheck_51_ = !lean_is_exclusive(v_s_32_);
if (v_isSharedCheck_51_ == 0)
{
v___x_45_ = v_s_32_;
v_isShared_46_ = v_isSharedCheck_51_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_it_43_);
lean_dec(v_s_32_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_51_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_47_; lean_object* v___x_49_; 
lean_inc(v_n_31_);
v___x_47_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_47_, 0, v_n_31_);
lean_ctor_set(v___x_47_, 1, v_n_31_);
lean_ctor_set(v___x_47_, 2, v_it_43_);
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 0, v___x_47_);
v___x_49_ = v___x_45_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v___x_47_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
}
default: 
{
lean_object* v___x_52_; 
lean_dec(v_n_31_);
v___x_52_ = lean_box(2);
return v___x_52_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg___lam__1(lean_object* v_toFunctor_53_, lean_object* v_inst_54_, lean_object* v_it_55_){
_start:
{
lean_object* v_map_56_; lean_object* v_nextIdx_57_; lean_object* v_n_58_; lean_object* v_inner_59_; lean_object* v___f_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v_map_56_ = lean_ctor_get(v_toFunctor_53_, 0);
lean_inc(v_map_56_);
lean_dec_ref(v_toFunctor_53_);
v_nextIdx_57_ = lean_ctor_get(v_it_55_, 0);
lean_inc(v_nextIdx_57_);
v_n_58_ = lean_ctor_get(v_it_55_, 1);
lean_inc(v_n_58_);
v_inner_59_ = lean_ctor_get(v_it_55_, 2);
lean_inc(v_inner_59_);
lean_dec_ref(v_it_55_);
v___f_60_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_60_, 0, v_n_58_);
v___x_61_ = lean_apply_2(v_inst_54_, v_inner_59_, v_nextIdx_57_);
v___x_62_ = lean_apply_4(v_map_56_, lean_box(0), lean_box(0), v___f_60_, v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg(lean_object* v_inst_63_, lean_object* v_inst_64_){
_start:
{
lean_object* v_toApplicative_65_; lean_object* v_toFunctor_66_; lean_object* v___f_67_; 
v_toApplicative_65_ = lean_ctor_get(v_inst_64_, 0);
lean_inc_ref(v_toApplicative_65_);
lean_dec_ref(v_inst_64_);
v_toFunctor_66_ = lean_ctor_get(v_toApplicative_65_, 0);
lean_inc_ref(v_toFunctor_66_);
lean_dec_ref(v_toApplicative_65_);
v___f_67_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg___lam__1), 3, 2);
lean_closure_set(v___f_67_, 0, v_toFunctor_66_);
lean_closure_set(v___f_67_, 1, v_inst_63_);
return v___f_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIterator(lean_object* v_00_u03b1_68_, lean_object* v_m_69_, lean_object* v_00_u03b2_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_inst_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg(v_inst_72_, v_inst_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIterator___boxed(lean_object* v_00_u03b1_75_, lean_object* v_m_76_, lean_object* v_00_u03b2_77_, lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_inst_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Std_Iterators_Types_StepSizeIterator_instIterator(v_00_u03b1_75_, v_m_76_, v_00_u03b2_77_, v_inst_78_, v_inst_79_, v_inst_80_);
lean_dec(v_inst_78_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = lean_box(0);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instFinitenessRelation___redArg___boxed(lean_object* v___dummy_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Std_Iterators_Types_StepSizeIterator_instFinitenessRelation___redArg();
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instFinitenessRelation(lean_object* v_00_u03b1_86_, lean_object* v_m_87_, lean_object* v_00_u03b2_88_, lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_inst_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lean_box(0);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instFinitenessRelation___boxed(lean_object* v_00_u03b1_94_, lean_object* v_m_95_, lean_object* v_00_u03b2_96_, lean_object* v_inst_97_, lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_inst_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Std_Iterators_Types_StepSizeIterator_instFinitenessRelation(v_00_u03b1_94_, v_m_95_, v_00_u03b2_96_, v_inst_97_, v_inst_98_, v_inst_99_, v_inst_100_);
lean_dec_ref(v_inst_99_);
lean_dec(v_inst_98_);
lean_dec(v_inst_97_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instProductivenessRelation___redArg(){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = lean_box(0);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instProductivenessRelation___redArg___boxed(lean_object* v___dummy_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Std_Iterators_Types_StepSizeIterator_instProductivenessRelation___redArg();
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instProductivenessRelation(lean_object* v_00_u03b1_106_, lean_object* v_m_107_, lean_object* v_00_u03b2_108_, lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_inst_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lean_box(0);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instProductivenessRelation___boxed(lean_object* v_00_u03b1_114_, lean_object* v_m_115_, lean_object* v_00_u03b2_116_, lean_object* v_inst_117_, lean_object* v_inst_118_, lean_object* v_inst_119_, lean_object* v_inst_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Std_Iterators_Types_StepSizeIterator_instProductivenessRelation(v_00_u03b1_114_, v_m_115_, v_00_u03b2_116_, v_inst_117_, v_inst_118_, v_inst_119_, v_inst_120_);
lean_dec_ref(v_inst_119_);
lean_dec(v_inst_118_);
lean_dec(v_inst_117_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_122_, lean_object* v_recur_123_, lean_object* v_it_124_, lean_object* v_____do__lift_125_){
_start:
{
if (lean_obj_tag(v_____do__lift_125_) == 0)
{
lean_object* v_a_126_; lean_object* v___x_127_; 
lean_dec_ref(v_it_124_);
lean_dec(v_recur_123_);
v_a_126_ = lean_ctor_get(v_____do__lift_125_, 0);
lean_inc(v_a_126_);
lean_dec_ref_known(v_____do__lift_125_, 1);
v___x_127_ = lean_apply_2(v_toPure_122_, lean_box(0), v_a_126_);
return v___x_127_;
}
else
{
lean_object* v_a_128_; lean_object* v___x_129_; 
lean_dec(v_toPure_122_);
v_a_128_ = lean_ctor_get(v_____do__lift_125_, 0);
lean_inc(v_a_128_);
lean_dec_ref_known(v_____do__lift_125_, 1);
v___x_129_ = lean_apply_4(v_recur_123_, v_it_124_, v_a_128_, lean_box(0), lean_box(0));
return v___x_129_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_130_, lean_object* v_recur_131_, lean_object* v___y_132_, lean_object* v_acc_133_, lean_object* v_toBind_134_, lean_object* v_s_135_){
_start:
{
switch(lean_obj_tag(v_s_135_))
{
case 0:
{
lean_object* v_it_136_; lean_object* v_out_137_; lean_object* v___f_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v_it_136_ = lean_ctor_get(v_s_135_, 0);
lean_inc(v_it_136_);
v_out_137_ = lean_ctor_get(v_s_135_, 1);
lean_inc(v_out_137_);
lean_dec_ref_known(v_s_135_, 2);
v___f_138_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_138_, 0, v_toPure_130_);
lean_closure_set(v___f_138_, 1, v_recur_131_);
lean_closure_set(v___f_138_, 2, v_it_136_);
v___x_139_ = lean_apply_3(v___y_132_, v_out_137_, lean_box(0), v_acc_133_);
v___x_140_ = lean_apply_4(v_toBind_134_, lean_box(0), lean_box(0), v___x_139_, v___f_138_);
return v___x_140_;
}
case 1:
{
lean_object* v_it_141_; lean_object* v___x_142_; 
lean_dec(v_toBind_134_);
lean_dec(v___y_132_);
lean_dec(v_toPure_130_);
v_it_141_ = lean_ctor_get(v_s_135_, 0);
lean_inc(v_it_141_);
lean_dec_ref_known(v_s_135_, 1);
v___x_142_ = lean_apply_4(v_recur_131_, v_it_141_, v_acc_133_, lean_box(0), lean_box(0));
return v___x_142_;
}
default: 
{
lean_object* v___x_143_; 
lean_dec(v_toBind_134_);
lean_dec(v___y_132_);
lean_dec(v_recur_131_);
v___x_143_ = lean_apply_2(v_toPure_130_, lean_box(0), v_acc_133_);
return v___x_143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__3(lean_object* v_inst_144_, lean_object* v_toPure_145_, lean_object* v___y_146_, lean_object* v_toBind_147_, lean_object* v_inst_148_, lean_object* v_lift_149_, lean_object* v_it_150_, lean_object* v_acc_151_, lean_object* v_hP_152_, lean_object* v_recur_153_){
_start:
{
lean_object* v_toApplicative_154_; lean_object* v_toFunctor_155_; lean_object* v_map_156_; lean_object* v_nextIdx_157_; lean_object* v_n_158_; lean_object* v_inner_159_; lean_object* v___f_160_; lean_object* v___f_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v_toApplicative_154_ = lean_ctor_get(v_inst_144_, 0);
lean_inc_ref(v_toApplicative_154_);
lean_dec_ref(v_inst_144_);
v_toFunctor_155_ = lean_ctor_get(v_toApplicative_154_, 0);
lean_inc_ref(v_toFunctor_155_);
lean_dec_ref(v_toApplicative_154_);
v_map_156_ = lean_ctor_get(v_toFunctor_155_, 0);
lean_inc(v_map_156_);
lean_dec_ref(v_toFunctor_155_);
v_nextIdx_157_ = lean_ctor_get(v_it_150_, 0);
lean_inc(v_nextIdx_157_);
v_n_158_ = lean_ctor_get(v_it_150_, 1);
lean_inc(v_n_158_);
v_inner_159_ = lean_ctor_get(v_it_150_, 2);
lean_inc(v_inner_159_);
lean_dec_ref(v_it_150_);
v___f_160_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_160_, 0, v_toPure_145_);
lean_closure_set(v___f_160_, 1, v_recur_153_);
lean_closure_set(v___f_160_, 2, v___y_146_);
lean_closure_set(v___f_160_, 3, v_acc_151_);
lean_closure_set(v___f_160_, 4, v_toBind_147_);
v___f_161_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_161_, 0, v_n_158_);
v___x_162_ = lean_apply_2(v_inst_148_, v_inner_159_, v_nextIdx_157_);
v___x_163_ = lean_apply_4(v_map_156_, lean_box(0), lean_box(0), v___f_161_, v___x_162_);
v___x_164_ = lean_apply_4(v_lift_149_, lean_box(0), lean_box(0), v___f_160_, v___x_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__2(lean_object* v_inst_165_, lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_lift_168_, lean_object* v_00_u03b3_169_, lean_object* v_Pl_170_, lean_object* v_it_171_, lean_object* v_init_172_, lean_object* v___y_173_){
_start:
{
lean_object* v_toApplicative_174_; lean_object* v_toBind_175_; lean_object* v_toPure_176_; lean_object* v___f_177_; lean_object* v___x_178_; 
v_toApplicative_174_ = lean_ctor_get(v_inst_165_, 0);
lean_inc_ref(v_toApplicative_174_);
v_toBind_175_ = lean_ctor_get(v_inst_165_, 1);
lean_inc(v_toBind_175_);
lean_dec_ref(v_inst_165_);
v_toPure_176_ = lean_ctor_get(v_toApplicative_174_, 1);
lean_inc(v_toPure_176_);
lean_dec_ref(v_toApplicative_174_);
v___f_177_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__3), 10, 6);
lean_closure_set(v___f_177_, 0, v_inst_166_);
lean_closure_set(v___f_177_, 1, v_toPure_176_);
lean_closure_set(v___f_177_, 2, v___y_173_);
lean_closure_set(v___f_177_, 3, v_toBind_175_);
lean_closure_set(v___f_177_, 4, v_inst_167_);
lean_closure_set(v___f_177_, 5, v_lift_168_);
v___x_178_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_177_, v_it_171_, v_init_172_, lean_box(0));
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg(lean_object* v_inst_179_, lean_object* v_inst_180_, lean_object* v_inst_181_){
_start:
{
lean_object* v___f_182_; 
v___f_182_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__2), 9, 3);
lean_closure_set(v___f_182_, 0, v_inst_181_);
lean_closure_set(v___f_182_, 1, v_inst_180_);
lean_closure_set(v___f_182_, 2, v_inst_179_);
return v___f_182_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop(lean_object* v_00_u03b1_183_, lean_object* v_00_u03b2_184_, lean_object* v_m_185_, lean_object* v_n_186_, lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_inst_189_, lean_object* v_inst_190_){
_start:
{
lean_object* v___f_191_; 
v___f_191_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__2), 9, 3);
lean_closure_set(v___f_191_, 0, v_inst_190_);
lean_closure_set(v___f_191_, 1, v_inst_189_);
lean_closure_set(v___f_191_, 2, v_inst_188_);
return v___f_191_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___boxed(lean_object* v_00_u03b1_192_, lean_object* v_00_u03b2_193_, lean_object* v_m_194_, lean_object* v_n_195_, lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_inst_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop(v_00_u03b1_192_, v_00_u03b2_193_, v_m_194_, v_n_195_, v_inst_196_, v_inst_197_, v_inst_198_, v_inst_199_);
lean_dec(v_inst_196_);
return v_res_200_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Access(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Access(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(builtin);
}
#ifdef __cplusplus
}
#endif

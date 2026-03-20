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
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instFinitenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instFinitenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instFinitenessRelation(lean_object* v_00_u03b1_82_, lean_object* v_m_83_, lean_object* v_00_u03b2_84_, lean_object* v_inst_85_, lean_object* v_inst_86_, lean_object* v_inst_87_, lean_object* v_inst_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_box(0);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instFinitenessRelation___boxed(lean_object* v_00_u03b1_90_, lean_object* v_m_91_, lean_object* v_00_u03b2_92_, lean_object* v_inst_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_inst_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Std_Iterators_Types_StepSizeIterator_instFinitenessRelation(v_00_u03b1_90_, v_m_91_, v_00_u03b2_92_, v_inst_93_, v_inst_94_, v_inst_95_, v_inst_96_);
lean_dec_ref(v_inst_95_);
lean_dec(v_inst_94_);
lean_dec(v_inst_93_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instProductivenessRelation(lean_object* v_00_u03b1_98_, lean_object* v_m_99_, lean_object* v_00_u03b2_100_, lean_object* v_inst_101_, lean_object* v_inst_102_, lean_object* v_inst_103_, lean_object* v_inst_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = lean_box(0);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instProductivenessRelation___boxed(lean_object* v_00_u03b1_106_, lean_object* v_m_107_, lean_object* v_00_u03b2_108_, lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_inst_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Std_Iterators_Types_StepSizeIterator_instProductivenessRelation(v_00_u03b1_106_, v_m_107_, v_00_u03b2_108_, v_inst_109_, v_inst_110_, v_inst_111_, v_inst_112_);
lean_dec_ref(v_inst_111_);
lean_dec(v_inst_110_);
lean_dec(v_inst_109_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_114_, lean_object* v_recur_115_, lean_object* v_it_116_, lean_object* v_____do__lift_117_){
_start:
{
if (lean_obj_tag(v_____do__lift_117_) == 0)
{
lean_object* v_a_118_; lean_object* v___x_119_; 
lean_dec_ref(v_it_116_);
lean_dec(v_recur_115_);
v_a_118_ = lean_ctor_get(v_____do__lift_117_, 0);
lean_inc(v_a_118_);
lean_dec_ref(v_____do__lift_117_);
v___x_119_ = lean_apply_2(v_toPure_114_, lean_box(0), v_a_118_);
return v___x_119_;
}
else
{
lean_object* v_a_120_; lean_object* v___x_121_; 
lean_dec(v_toPure_114_);
v_a_120_ = lean_ctor_get(v_____do__lift_117_, 0);
lean_inc(v_a_120_);
lean_dec_ref(v_____do__lift_117_);
v___x_121_ = lean_apply_4(v_recur_115_, v_it_116_, v_a_120_, lean_box(0), lean_box(0));
return v___x_121_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_122_, lean_object* v_recur_123_, lean_object* v___y_124_, lean_object* v_acc_125_, lean_object* v_toBind_126_, lean_object* v_s_127_){
_start:
{
switch(lean_obj_tag(v_s_127_))
{
case 0:
{
lean_object* v_it_128_; lean_object* v_out_129_; lean_object* v___f_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v_it_128_ = lean_ctor_get(v_s_127_, 0);
lean_inc(v_it_128_);
v_out_129_ = lean_ctor_get(v_s_127_, 1);
lean_inc(v_out_129_);
lean_dec_ref(v_s_127_);
v___f_130_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_130_, 0, v_toPure_122_);
lean_closure_set(v___f_130_, 1, v_recur_123_);
lean_closure_set(v___f_130_, 2, v_it_128_);
v___x_131_ = lean_apply_3(v___y_124_, v_out_129_, lean_box(0), v_acc_125_);
v___x_132_ = lean_apply_4(v_toBind_126_, lean_box(0), lean_box(0), v___x_131_, v___f_130_);
return v___x_132_;
}
case 1:
{
lean_object* v_it_133_; lean_object* v___x_134_; 
lean_dec(v_toBind_126_);
lean_dec(v___y_124_);
lean_dec(v_toPure_122_);
v_it_133_ = lean_ctor_get(v_s_127_, 0);
lean_inc(v_it_133_);
lean_dec_ref(v_s_127_);
v___x_134_ = lean_apply_4(v_recur_123_, v_it_133_, v_acc_125_, lean_box(0), lean_box(0));
return v___x_134_;
}
default: 
{
lean_object* v___x_135_; 
lean_dec(v_toBind_126_);
lean_dec(v___y_124_);
lean_dec(v_recur_123_);
v___x_135_ = lean_apply_2(v_toPure_122_, lean_box(0), v_acc_125_);
return v___x_135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__3(lean_object* v_inst_136_, lean_object* v_toPure_137_, lean_object* v___y_138_, lean_object* v_toBind_139_, lean_object* v_inst_140_, lean_object* v_lift_141_, lean_object* v_it_142_, lean_object* v_acc_143_, lean_object* v_hP_144_, lean_object* v_recur_145_){
_start:
{
lean_object* v_toApplicative_146_; lean_object* v_toFunctor_147_; lean_object* v_map_148_; lean_object* v_nextIdx_149_; lean_object* v_n_150_; lean_object* v_inner_151_; lean_object* v___f_152_; lean_object* v___f_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v_toApplicative_146_ = lean_ctor_get(v_inst_136_, 0);
lean_inc_ref(v_toApplicative_146_);
lean_dec_ref(v_inst_136_);
v_toFunctor_147_ = lean_ctor_get(v_toApplicative_146_, 0);
lean_inc_ref(v_toFunctor_147_);
lean_dec_ref(v_toApplicative_146_);
v_map_148_ = lean_ctor_get(v_toFunctor_147_, 0);
lean_inc(v_map_148_);
lean_dec_ref(v_toFunctor_147_);
v_nextIdx_149_ = lean_ctor_get(v_it_142_, 0);
lean_inc(v_nextIdx_149_);
v_n_150_ = lean_ctor_get(v_it_142_, 1);
lean_inc(v_n_150_);
v_inner_151_ = lean_ctor_get(v_it_142_, 2);
lean_inc(v_inner_151_);
lean_dec_ref(v_it_142_);
v___f_152_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_152_, 0, v_toPure_137_);
lean_closure_set(v___f_152_, 1, v_recur_145_);
lean_closure_set(v___f_152_, 2, v___y_138_);
lean_closure_set(v___f_152_, 3, v_acc_143_);
lean_closure_set(v___f_152_, 4, v_toBind_139_);
v___f_153_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_153_, 0, v_n_150_);
v___x_154_ = lean_apply_2(v_inst_140_, v_inner_151_, v_nextIdx_149_);
v___x_155_ = lean_apply_4(v_map_148_, lean_box(0), lean_box(0), v___f_153_, v___x_154_);
v___x_156_ = lean_apply_4(v_lift_141_, lean_box(0), lean_box(0), v___f_152_, v___x_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__2(lean_object* v_inst_157_, lean_object* v_inst_158_, lean_object* v_inst_159_, lean_object* v_lift_160_, lean_object* v_00_u03b3_161_, lean_object* v_Pl_162_, lean_object* v_it_163_, lean_object* v_init_164_, lean_object* v___y_165_){
_start:
{
lean_object* v_toApplicative_166_; lean_object* v_toBind_167_; lean_object* v_toPure_168_; lean_object* v___f_169_; lean_object* v___x_170_; 
v_toApplicative_166_ = lean_ctor_get(v_inst_157_, 0);
lean_inc_ref(v_toApplicative_166_);
v_toBind_167_ = lean_ctor_get(v_inst_157_, 1);
lean_inc(v_toBind_167_);
lean_dec_ref(v_inst_157_);
v_toPure_168_ = lean_ctor_get(v_toApplicative_166_, 1);
lean_inc(v_toPure_168_);
lean_dec_ref(v_toApplicative_166_);
v___f_169_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__3), 10, 6);
lean_closure_set(v___f_169_, 0, v_inst_158_);
lean_closure_set(v___f_169_, 1, v_toPure_168_);
lean_closure_set(v___f_169_, 2, v___y_165_);
lean_closure_set(v___f_169_, 3, v_toBind_167_);
lean_closure_set(v___f_169_, 4, v_inst_159_);
lean_closure_set(v___f_169_, 5, v_lift_160_);
v___x_170_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_169_, v_it_163_, v_init_164_, lean_box(0));
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg(lean_object* v_inst_171_, lean_object* v_inst_172_, lean_object* v_inst_173_){
_start:
{
lean_object* v___f_174_; 
v___f_174_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__2), 9, 3);
lean_closure_set(v___f_174_, 0, v_inst_173_);
lean_closure_set(v___f_174_, 1, v_inst_172_);
lean_closure_set(v___f_174_, 2, v_inst_171_);
return v___f_174_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop(lean_object* v_00_u03b1_175_, lean_object* v_00_u03b2_176_, lean_object* v_m_177_, lean_object* v_n_178_, lean_object* v_inst_179_, lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_inst_182_){
_start:
{
lean_object* v___f_183_; 
v___f_183_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__2), 9, 3);
lean_closure_set(v___f_183_, 0, v_inst_182_);
lean_closure_set(v___f_183_, 1, v_inst_181_);
lean_closure_set(v___f_183_, 2, v_inst_180_);
return v___f_183_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___boxed(lean_object* v_00_u03b1_184_, lean_object* v_00_u03b2_185_, lean_object* v_m_186_, lean_object* v_n_187_, lean_object* v_inst_188_, lean_object* v_inst_189_, lean_object* v_inst_190_, lean_object* v_inst_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop(v_00_u03b1_184_, v_00_u03b2_185_, v_m_186_, v_n_187_, v_inst_188_, v_inst_189_, v_inst_190_, v_inst_191_);
lean_dec(v_inst_188_);
return v_res_192_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Access(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

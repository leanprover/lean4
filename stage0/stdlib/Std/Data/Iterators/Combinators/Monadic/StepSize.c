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
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_StepSize_0__Std_IterStep_successor_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_StepSize_0__Std_IterStep_successor_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_StepSize_0__Std_IterStep_successor_match__1_splitter___redArg(lean_object* v_x_82_, lean_object* v_h__1_83_, lean_object* v_h__2_84_, lean_object* v_h__3_85_){
_start:
{
switch(lean_obj_tag(v_x_82_))
{
case 0:
{
lean_object* v_it_86_; lean_object* v_out_87_; lean_object* v___x_88_; 
lean_dec(v_h__3_85_);
lean_dec(v_h__2_84_);
v_it_86_ = lean_ctor_get(v_x_82_, 0);
lean_inc(v_it_86_);
v_out_87_ = lean_ctor_get(v_x_82_, 1);
lean_inc(v_out_87_);
lean_dec_ref_known(v_x_82_, 2);
v___x_88_ = lean_apply_2(v_h__1_83_, v_it_86_, v_out_87_);
return v___x_88_;
}
case 1:
{
lean_object* v_it_89_; lean_object* v___x_90_; 
lean_dec(v_h__3_85_);
lean_dec(v_h__1_83_);
v_it_89_ = lean_ctor_get(v_x_82_, 0);
lean_inc(v_it_89_);
lean_dec_ref_known(v_x_82_, 1);
v___x_90_ = lean_apply_1(v_h__2_84_, v_it_89_);
return v___x_90_;
}
default: 
{
lean_object* v___x_91_; lean_object* v___x_92_; 
lean_dec(v_h__2_84_);
lean_dec(v_h__1_83_);
v___x_91_ = lean_box(0);
v___x_92_ = lean_apply_1(v_h__3_85_, v___x_91_);
return v___x_92_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_StepSize_0__Std_IterStep_successor_match__1_splitter(lean_object* v_00_u03b1_93_, lean_object* v_00_u03b2_94_, lean_object* v_motive_95_, lean_object* v_x_96_, lean_object* v_h__1_97_, lean_object* v_h__2_98_, lean_object* v_h__3_99_){
_start:
{
switch(lean_obj_tag(v_x_96_))
{
case 0:
{
lean_object* v_it_100_; lean_object* v_out_101_; lean_object* v___x_102_; 
lean_dec(v_h__3_99_);
lean_dec(v_h__2_98_);
v_it_100_ = lean_ctor_get(v_x_96_, 0);
lean_inc(v_it_100_);
v_out_101_ = lean_ctor_get(v_x_96_, 1);
lean_inc(v_out_101_);
lean_dec_ref_known(v_x_96_, 2);
v___x_102_ = lean_apply_2(v_h__1_97_, v_it_100_, v_out_101_);
return v___x_102_;
}
case 1:
{
lean_object* v_it_103_; lean_object* v___x_104_; 
lean_dec(v_h__3_99_);
lean_dec(v_h__1_97_);
v_it_103_ = lean_ctor_get(v_x_96_, 0);
lean_inc(v_it_103_);
lean_dec_ref_known(v_x_96_, 1);
v___x_104_ = lean_apply_1(v_h__2_98_, v_it_103_);
return v___x_104_;
}
default: 
{
lean_object* v___x_105_; lean_object* v___x_106_; 
lean_dec(v_h__2_98_);
lean_dec(v_h__1_97_);
v___x_105_ = lean_box(0);
v___x_106_ = lean_apply_1(v_h__3_99_, v___x_105_);
return v___x_106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = lean_box(0);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instFinitenessRelation___redArg___boxed(lean_object* v___dummy_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Std_Iterators_Types_StepSizeIterator_instFinitenessRelation___redArg();
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instFinitenessRelation(lean_object* v_00_u03b1_111_, lean_object* v_m_112_, lean_object* v_00_u03b2_113_, lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_inst_116_, lean_object* v_inst_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_box(0);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instFinitenessRelation___boxed(lean_object* v_00_u03b1_119_, lean_object* v_m_120_, lean_object* v_00_u03b2_121_, lean_object* v_inst_122_, lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_inst_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Std_Iterators_Types_StepSizeIterator_instFinitenessRelation(v_00_u03b1_119_, v_m_120_, v_00_u03b2_121_, v_inst_122_, v_inst_123_, v_inst_124_, v_inst_125_);
lean_dec_ref(v_inst_124_);
lean_dec(v_inst_123_);
lean_dec(v_inst_122_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instProductivenessRelation___redArg(){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = lean_box(0);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instProductivenessRelation___redArg___boxed(lean_object* v___dummy_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Std_Iterators_Types_StepSizeIterator_instProductivenessRelation___redArg();
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instProductivenessRelation(lean_object* v_00_u03b1_131_, lean_object* v_m_132_, lean_object* v_00_u03b2_133_, lean_object* v_inst_134_, lean_object* v_inst_135_, lean_object* v_inst_136_, lean_object* v_inst_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = lean_box(0);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instProductivenessRelation___boxed(lean_object* v_00_u03b1_139_, lean_object* v_m_140_, lean_object* v_00_u03b2_141_, lean_object* v_inst_142_, lean_object* v_inst_143_, lean_object* v_inst_144_, lean_object* v_inst_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Std_Iterators_Types_StepSizeIterator_instProductivenessRelation(v_00_u03b1_139_, v_m_140_, v_00_u03b2_141_, v_inst_142_, v_inst_143_, v_inst_144_, v_inst_145_);
lean_dec_ref(v_inst_144_);
lean_dec(v_inst_143_);
lean_dec(v_inst_142_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_147_, lean_object* v_recur_148_, lean_object* v_it_149_, lean_object* v_____do__lift_150_){
_start:
{
if (lean_obj_tag(v_____do__lift_150_) == 0)
{
lean_object* v_a_151_; lean_object* v___x_152_; 
lean_dec_ref(v_it_149_);
lean_dec(v_recur_148_);
v_a_151_ = lean_ctor_get(v_____do__lift_150_, 0);
lean_inc(v_a_151_);
lean_dec_ref_known(v_____do__lift_150_, 1);
v___x_152_ = lean_apply_2(v_toPure_147_, lean_box(0), v_a_151_);
return v___x_152_;
}
else
{
lean_object* v_a_153_; lean_object* v___x_154_; 
lean_dec(v_toPure_147_);
v_a_153_ = lean_ctor_get(v_____do__lift_150_, 0);
lean_inc(v_a_153_);
lean_dec_ref_known(v_____do__lift_150_, 1);
v___x_154_ = lean_apply_4(v_recur_148_, v_it_149_, v_a_153_, lean_box(0), lean_box(0));
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_155_, lean_object* v_recur_156_, lean_object* v___y_157_, lean_object* v_acc_158_, lean_object* v_toBind_159_, lean_object* v_s_160_){
_start:
{
switch(lean_obj_tag(v_s_160_))
{
case 0:
{
lean_object* v_it_161_; lean_object* v_out_162_; lean_object* v___f_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v_it_161_ = lean_ctor_get(v_s_160_, 0);
lean_inc(v_it_161_);
v_out_162_ = lean_ctor_get(v_s_160_, 1);
lean_inc(v_out_162_);
lean_dec_ref_known(v_s_160_, 2);
v___f_163_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_163_, 0, v_toPure_155_);
lean_closure_set(v___f_163_, 1, v_recur_156_);
lean_closure_set(v___f_163_, 2, v_it_161_);
v___x_164_ = lean_apply_3(v___y_157_, v_out_162_, lean_box(0), v_acc_158_);
v___x_165_ = lean_apply_4(v_toBind_159_, lean_box(0), lean_box(0), v___x_164_, v___f_163_);
return v___x_165_;
}
case 1:
{
lean_object* v_it_166_; lean_object* v___x_167_; 
lean_dec(v_toBind_159_);
lean_dec(v___y_157_);
lean_dec(v_toPure_155_);
v_it_166_ = lean_ctor_get(v_s_160_, 0);
lean_inc(v_it_166_);
lean_dec_ref_known(v_s_160_, 1);
v___x_167_ = lean_apply_4(v_recur_156_, v_it_166_, v_acc_158_, lean_box(0), lean_box(0));
return v___x_167_;
}
default: 
{
lean_object* v___x_168_; 
lean_dec(v_toBind_159_);
lean_dec(v___y_157_);
lean_dec(v_recur_156_);
v___x_168_ = lean_apply_2(v_toPure_155_, lean_box(0), v_acc_158_);
return v___x_168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__3(lean_object* v_inst_169_, lean_object* v_toPure_170_, lean_object* v___y_171_, lean_object* v_toBind_172_, lean_object* v_inst_173_, lean_object* v_lift_174_, lean_object* v_it_175_, lean_object* v_acc_176_, lean_object* v_hP_177_, lean_object* v_recur_178_){
_start:
{
lean_object* v_toApplicative_179_; lean_object* v_toFunctor_180_; lean_object* v_map_181_; lean_object* v_nextIdx_182_; lean_object* v_n_183_; lean_object* v_inner_184_; lean_object* v___f_185_; lean_object* v___f_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v_toApplicative_179_ = lean_ctor_get(v_inst_169_, 0);
lean_inc_ref(v_toApplicative_179_);
lean_dec_ref(v_inst_169_);
v_toFunctor_180_ = lean_ctor_get(v_toApplicative_179_, 0);
lean_inc_ref(v_toFunctor_180_);
lean_dec_ref(v_toApplicative_179_);
v_map_181_ = lean_ctor_get(v_toFunctor_180_, 0);
lean_inc(v_map_181_);
lean_dec_ref(v_toFunctor_180_);
v_nextIdx_182_ = lean_ctor_get(v_it_175_, 0);
lean_inc(v_nextIdx_182_);
v_n_183_ = lean_ctor_get(v_it_175_, 1);
lean_inc(v_n_183_);
v_inner_184_ = lean_ctor_get(v_it_175_, 2);
lean_inc(v_inner_184_);
lean_dec_ref(v_it_175_);
v___f_185_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_185_, 0, v_toPure_170_);
lean_closure_set(v___f_185_, 1, v_recur_178_);
lean_closure_set(v___f_185_, 2, v___y_171_);
lean_closure_set(v___f_185_, 3, v_acc_176_);
lean_closure_set(v___f_185_, 4, v_toBind_172_);
v___f_186_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_186_, 0, v_n_183_);
v___x_187_ = lean_apply_2(v_inst_173_, v_inner_184_, v_nextIdx_182_);
v___x_188_ = lean_apply_4(v_map_181_, lean_box(0), lean_box(0), v___f_186_, v___x_187_);
v___x_189_ = lean_apply_4(v_lift_174_, lean_box(0), lean_box(0), v___f_185_, v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__2(lean_object* v_inst_190_, lean_object* v_inst_191_, lean_object* v_inst_192_, lean_object* v_lift_193_, lean_object* v_00_u03b3_194_, lean_object* v_Pl_195_, lean_object* v_it_196_, lean_object* v_init_197_, lean_object* v___y_198_){
_start:
{
lean_object* v_toApplicative_199_; lean_object* v_toBind_200_; lean_object* v_toPure_201_; lean_object* v___f_202_; lean_object* v___x_203_; 
v_toApplicative_199_ = lean_ctor_get(v_inst_190_, 0);
lean_inc_ref(v_toApplicative_199_);
v_toBind_200_ = lean_ctor_get(v_inst_190_, 1);
lean_inc(v_toBind_200_);
lean_dec_ref(v_inst_190_);
v_toPure_201_ = lean_ctor_get(v_toApplicative_199_, 1);
lean_inc(v_toPure_201_);
lean_dec_ref(v_toApplicative_199_);
v___f_202_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__3), 10, 6);
lean_closure_set(v___f_202_, 0, v_inst_191_);
lean_closure_set(v___f_202_, 1, v_toPure_201_);
lean_closure_set(v___f_202_, 2, v___y_198_);
lean_closure_set(v___f_202_, 3, v_toBind_200_);
lean_closure_set(v___f_202_, 4, v_inst_192_);
lean_closure_set(v___f_202_, 5, v_lift_193_);
v___x_203_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_202_, v_it_196_, v_init_197_, lean_box(0));
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg(lean_object* v_inst_204_, lean_object* v_inst_205_, lean_object* v_inst_206_){
_start:
{
lean_object* v___f_207_; 
v___f_207_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__2), 9, 3);
lean_closure_set(v___f_207_, 0, v_inst_206_);
lean_closure_set(v___f_207_, 1, v_inst_205_);
lean_closure_set(v___f_207_, 2, v_inst_204_);
return v___f_207_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop(lean_object* v_00_u03b1_208_, lean_object* v_00_u03b2_209_, lean_object* v_m_210_, lean_object* v_n_211_, lean_object* v_inst_212_, lean_object* v_inst_213_, lean_object* v_inst_214_, lean_object* v_inst_215_){
_start:
{
lean_object* v___f_216_; 
v___f_216_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__2), 9, 3);
lean_closure_set(v___f_216_, 0, v_inst_215_);
lean_closure_set(v___f_216_, 1, v_inst_214_);
lean_closure_set(v___f_216_, 2, v_inst_213_);
return v___f_216_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___boxed(lean_object* v_00_u03b1_217_, lean_object* v_00_u03b2_218_, lean_object* v_m_219_, lean_object* v_n_220_, lean_object* v_inst_221_, lean_object* v_inst_222_, lean_object* v_inst_223_, lean_object* v_inst_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop(v_00_u03b1_217_, v_00_u03b2_218_, v_m_219_, v_n_220_, v_inst_221_, v_inst_222_, v_inst_223_, v_inst_224_);
lean_dec(v_inst_221_);
return v_res_225_;
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

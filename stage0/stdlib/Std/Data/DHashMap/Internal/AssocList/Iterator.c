// Lean compiler output
// Module: Std.Data.DHashMap.Internal.AssocList.Iterator
// Imports: import Init.Data.Nat.Lemmas public import Init.Data.Iterators.Consumers public import Std.Data.DHashMap.Internal.AssocList.Basic
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Iterator_0__Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Iterator_0__Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Iterator_0__Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Iterator_0__Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Iterator_0__Std_DHashMap_Internal_AssocList_AssocListIterator_finitenessRelation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_iter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_iter___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_iter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_iter___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma___lam__0(lean_object* v_it_1_){
_start:
{
if (lean_obj_tag(v_it_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(2);
return v___x_2_;
}
else
{
lean_object* v_key_3_; lean_object* v_value_4_; lean_object* v_tail_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v_key_3_ = lean_ctor_get(v_it_1_, 0);
v_value_4_ = lean_ctor_get(v_it_1_, 1);
v_tail_5_ = lean_ctor_get(v_it_1_, 2);
lean_inc(v_value_4_);
lean_inc(v_key_3_);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v_key_3_);
lean_ctor_set(v___x_6_, 1, v_value_4_);
lean_inc(v_tail_5_);
v___x_7_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7_, 0, v_tail_5_);
lean_ctor_set(v___x_7_, 1, v___x_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma___lam__0___boxed(lean_object* v_it_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma___lam__0(v_it_8_);
lean_dec(v_it_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma(lean_object* v_00_u03b1_11_, lean_object* v_00_u03b2_12_){
_start:
{
lean_object* v___f_13_; 
v___f_13_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma___closed__0));
return v___f_13_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Iterator_0__Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma_match__3_splitter___redArg(lean_object* v_it_14_, lean_object* v_h__1_15_, lean_object* v_h__2_16_){
_start:
{
if (lean_obj_tag(v_it_14_) == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; 
lean_dec(v_h__2_16_);
v___x_17_ = lean_box(0);
v___x_18_ = lean_apply_1(v_h__1_15_, v___x_17_);
return v___x_18_;
}
else
{
lean_object* v_key_19_; lean_object* v_value_20_; lean_object* v_tail_21_; lean_object* v___x_22_; 
lean_dec(v_h__1_15_);
v_key_19_ = lean_ctor_get(v_it_14_, 0);
lean_inc(v_key_19_);
v_value_20_ = lean_ctor_get(v_it_14_, 1);
lean_inc(v_value_20_);
v_tail_21_ = lean_ctor_get(v_it_14_, 2);
lean_inc(v_tail_21_);
lean_dec_ref(v_it_14_);
v___x_22_ = lean_apply_3(v_h__2_16_, v_key_19_, v_value_20_, v_tail_21_);
return v___x_22_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Iterator_0__Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma_match__3_splitter(lean_object* v_00_u03b1_23_, lean_object* v_00_u03b2_24_, lean_object* v_motive_25_, lean_object* v_it_26_, lean_object* v_h__1_27_, lean_object* v_h__2_28_){
_start:
{
if (lean_obj_tag(v_it_26_) == 0)
{
lean_object* v___x_29_; lean_object* v___x_30_; 
lean_dec(v_h__2_28_);
v___x_29_ = lean_box(0);
v___x_30_ = lean_apply_1(v_h__1_27_, v___x_29_);
return v___x_30_;
}
else
{
lean_object* v_key_31_; lean_object* v_value_32_; lean_object* v_tail_33_; lean_object* v___x_34_; 
lean_dec(v_h__1_27_);
v_key_31_ = lean_ctor_get(v_it_26_, 0);
lean_inc(v_key_31_);
v_value_32_ = lean_ctor_get(v_it_26_, 1);
lean_inc(v_value_32_);
v_tail_33_ = lean_ctor_get(v_it_26_, 2);
lean_inc(v_tail_33_);
lean_dec_ref(v_it_26_);
v___x_34_ = lean_apply_3(v_h__2_28_, v_key_31_, v_value_32_, v_tail_33_);
return v___x_34_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Iterator_0__Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma_match__1_splitter___redArg(lean_object* v_x_35_, lean_object* v_h__1_36_, lean_object* v_h__2_37_, lean_object* v_h__3_38_){
_start:
{
switch(lean_obj_tag(v_x_35_))
{
case 0:
{
lean_object* v_it_39_; lean_object* v_out_40_; lean_object* v___x_41_; 
lean_dec(v_h__3_38_);
lean_dec(v_h__2_37_);
v_it_39_ = lean_ctor_get(v_x_35_, 0);
lean_inc(v_it_39_);
v_out_40_ = lean_ctor_get(v_x_35_, 1);
lean_inc(v_out_40_);
lean_dec_ref(v_x_35_);
v___x_41_ = lean_apply_2(v_h__1_36_, v_it_39_, v_out_40_);
return v___x_41_;
}
case 1:
{
lean_object* v_it_42_; lean_object* v___x_43_; 
lean_dec(v_h__3_38_);
lean_dec(v_h__1_36_);
v_it_42_ = lean_ctor_get(v_x_35_, 0);
lean_inc(v_it_42_);
lean_dec_ref(v_x_35_);
v___x_43_ = lean_apply_1(v_h__2_37_, v_it_42_);
return v___x_43_;
}
default: 
{
lean_object* v___x_44_; lean_object* v___x_45_; 
lean_dec(v_h__2_37_);
lean_dec(v_h__1_36_);
v___x_44_ = lean_box(0);
v___x_45_ = lean_apply_1(v_h__3_38_, v___x_44_);
return v___x_45_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Iterator_0__Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma_match__1_splitter(lean_object* v_00_u03b1_46_, lean_object* v_00_u03b2_47_, lean_object* v_motive_48_, lean_object* v_x_49_, lean_object* v_h__1_50_, lean_object* v_h__2_51_, lean_object* v_h__3_52_){
_start:
{
switch(lean_obj_tag(v_x_49_))
{
case 0:
{
lean_object* v_it_53_; lean_object* v_out_54_; lean_object* v___x_55_; 
lean_dec(v_h__3_52_);
lean_dec(v_h__2_51_);
v_it_53_ = lean_ctor_get(v_x_49_, 0);
lean_inc(v_it_53_);
v_out_54_ = lean_ctor_get(v_x_49_, 1);
lean_inc(v_out_54_);
lean_dec_ref(v_x_49_);
v___x_55_ = lean_apply_2(v_h__1_50_, v_it_53_, v_out_54_);
return v___x_55_;
}
case 1:
{
lean_object* v_it_56_; lean_object* v___x_57_; 
lean_dec(v_h__3_52_);
lean_dec(v_h__1_50_);
v_it_56_ = lean_ctor_get(v_x_49_, 0);
lean_inc(v_it_56_);
lean_dec_ref(v_x_49_);
v___x_57_ = lean_apply_1(v_h__2_51_, v_it_56_);
return v___x_57_;
}
default: 
{
lean_object* v___x_58_; lean_object* v___x_59_; 
lean_dec(v_h__2_51_);
lean_dec(v_h__1_50_);
v___x_58_ = lean_box(0);
v___x_59_ = lean_apply_1(v_h__3_52_, v___x_58_);
return v___x_59_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Iterator_0__Std_DHashMap_Internal_AssocList_AssocListIterator_finitenessRelation(lean_object* v_00_u03b1_60_, lean_object* v_00_u03b2_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = lean_box(0);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__0(lean_object* v_toPure_63_, lean_object* v_recur_64_, lean_object* v_it_65_, lean_object* v_____do__lift_66_){
_start:
{
if (lean_obj_tag(v_____do__lift_66_) == 0)
{
lean_object* v_a_67_; lean_object* v___x_68_; 
lean_dec(v_it_65_);
lean_dec(v_recur_64_);
v_a_67_ = lean_ctor_get(v_____do__lift_66_, 0);
lean_inc(v_a_67_);
lean_dec_ref(v_____do__lift_66_);
v___x_68_ = lean_apply_2(v_toPure_63_, lean_box(0), v_a_67_);
return v___x_68_;
}
else
{
lean_object* v_a_69_; lean_object* v___x_70_; 
lean_dec(v_toPure_63_);
v_a_69_ = lean_ctor_get(v_____do__lift_66_, 0);
lean_inc(v_a_69_);
lean_dec_ref(v_____do__lift_66_);
v___x_70_ = lean_apply_4(v_recur_64_, v_it_65_, v_a_69_, lean_box(0), lean_box(0));
return v___x_70_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__1(lean_object* v_toPure_71_, lean_object* v_recur_72_, lean_object* v___y_73_, lean_object* v_acc_74_, lean_object* v_toBind_75_, lean_object* v_s_76_){
_start:
{
switch(lean_obj_tag(v_s_76_))
{
case 0:
{
lean_object* v_it_77_; lean_object* v_out_78_; lean_object* v___f_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v_it_77_ = lean_ctor_get(v_s_76_, 0);
lean_inc(v_it_77_);
v_out_78_ = lean_ctor_get(v_s_76_, 1);
lean_inc(v_out_78_);
lean_dec_ref(v_s_76_);
v___f_79_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_79_, 0, v_toPure_71_);
lean_closure_set(v___f_79_, 1, v_recur_72_);
lean_closure_set(v___f_79_, 2, v_it_77_);
v___x_80_ = lean_apply_3(v___y_73_, v_out_78_, lean_box(0), v_acc_74_);
v___x_81_ = lean_apply_4(v_toBind_75_, lean_box(0), lean_box(0), v___x_80_, v___f_79_);
return v___x_81_;
}
case 1:
{
lean_object* v_it_82_; lean_object* v___x_83_; 
lean_dec(v_toBind_75_);
lean_dec(v___y_73_);
lean_dec(v_toPure_71_);
v_it_82_ = lean_ctor_get(v_s_76_, 0);
lean_inc(v_it_82_);
lean_dec_ref(v_s_76_);
v___x_83_ = lean_apply_4(v_recur_72_, v_it_82_, v_acc_74_, lean_box(0), lean_box(0));
return v___x_83_;
}
default: 
{
lean_object* v___x_84_; 
lean_dec(v_toBind_75_);
lean_dec(v___y_73_);
lean_dec(v_recur_72_);
v___x_84_ = lean_apply_2(v_toPure_71_, lean_box(0), v_acc_74_);
return v___x_84_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__2(lean_object* v_toPure_85_, lean_object* v___y_86_, lean_object* v_toBind_87_, lean_object* v_lift_88_, lean_object* v_it_89_, lean_object* v_acc_90_, lean_object* v_hP_91_, lean_object* v_recur_92_){
_start:
{
lean_object* v___f_93_; 
v___f_93_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_93_, 0, v_toPure_85_);
lean_closure_set(v___f_93_, 1, v_recur_92_);
lean_closure_set(v___f_93_, 2, v___y_86_);
lean_closure_set(v___f_93_, 3, v_acc_90_);
lean_closure_set(v___f_93_, 4, v_toBind_87_);
if (lean_obj_tag(v_it_89_) == 0)
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_box(2);
v___x_95_ = lean_apply_4(v_lift_88_, lean_box(0), lean_box(0), v___f_93_, v___x_94_);
return v___x_95_;
}
else
{
lean_object* v_key_96_; lean_object* v_value_97_; lean_object* v_tail_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v_key_96_ = lean_ctor_get(v_it_89_, 0);
v_value_97_ = lean_ctor_get(v_it_89_, 1);
v_tail_98_ = lean_ctor_get(v_it_89_, 2);
lean_inc(v_value_97_);
lean_inc(v_key_96_);
v___x_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_99_, 0, v_key_96_);
lean_ctor_set(v___x_99_, 1, v_value_97_);
lean_inc(v_tail_98_);
v___x_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_100_, 0, v_tail_98_);
lean_ctor_set(v___x_100_, 1, v___x_99_);
v___x_101_ = lean_apply_4(v_lift_88_, lean_box(0), lean_box(0), v___f_93_, v___x_100_);
return v___x_101_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__2___boxed(lean_object* v_toPure_102_, lean_object* v___y_103_, lean_object* v_toBind_104_, lean_object* v_lift_105_, lean_object* v_it_106_, lean_object* v_acc_107_, lean_object* v_hP_108_, lean_object* v_recur_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__2(v_toPure_102_, v___y_103_, v_toBind_104_, v_lift_105_, v_it_106_, v_acc_107_, v_hP_108_, v_recur_109_);
lean_dec(v_it_106_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__3(lean_object* v_inst_111_, lean_object* v_lift_112_, lean_object* v_00_u03b3_113_, lean_object* v_Pl_114_, lean_object* v_it_115_, lean_object* v_init_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_toApplicative_118_; lean_object* v_toBind_119_; lean_object* v_toPure_120_; lean_object* v___f_121_; lean_object* v___x_122_; 
v_toApplicative_118_ = lean_ctor_get(v_inst_111_, 0);
lean_inc_ref(v_toApplicative_118_);
v_toBind_119_ = lean_ctor_get(v_inst_111_, 1);
lean_inc(v_toBind_119_);
lean_dec_ref(v_inst_111_);
v_toPure_120_ = lean_ctor_get(v_toApplicative_118_, 1);
lean_inc(v_toPure_120_);
lean_dec_ref(v_toApplicative_118_);
v___f_121_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__2___boxed), 8, 4);
lean_closure_set(v___f_121_, 0, v_toPure_120_);
lean_closure_set(v___f_121_, 1, v___y_117_);
lean_closure_set(v___f_121_, 2, v_toBind_119_);
lean_closure_set(v___f_121_, 3, v_lift_112_);
v___x_122_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_121_, v_it_115_, v_init_116_, lean_box(0));
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg(lean_object* v_inst_123_){
_start:
{
lean_object* v___f_124_; 
v___f_124_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__3), 7, 1);
lean_closure_set(v___f_124_, 0, v_inst_123_);
return v___f_124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad(lean_object* v_00_u03b1_125_, lean_object* v_00_u03b2_126_, lean_object* v_m_127_, lean_object* v_inst_128_){
_start:
{
lean_object* v___f_129_; 
v___f_129_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__3), 7, 1);
lean_closure_set(v___f_129_, 0, v_inst_128_);
return v___f_129_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_iter___redArg(lean_object* v_l_130_){
_start:
{
lean_inc(v_l_130_);
return v_l_130_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_iter___redArg___boxed(lean_object* v_l_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Std_DHashMap_Internal_AssocList_iter___redArg(v_l_131_);
lean_dec(v_l_131_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_iter(lean_object* v_00_u03b1_133_, lean_object* v_00_u03b2_134_, lean_object* v_l_135_){
_start:
{
lean_inc(v_l_135_);
return v_l_135_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_iter___boxed(lean_object* v_00_u03b1_136_, lean_object* v_00_u03b2_137_, lean_object* v_l_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Std_DHashMap_Internal_AssocList_iter(v_00_u03b1_136_, v_00_u03b2_137_, v_l_138_);
lean_dec(v_l_138_);
return v_res_139_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DHashMap_Internal_AssocList_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Internal_AssocList_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DHashMap_Internal_AssocList_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DHashMap_Internal_AssocList_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DHashMap_Internal_AssocList_Iterator(builtin);
}
#ifdef __cplusplus
}
#endif

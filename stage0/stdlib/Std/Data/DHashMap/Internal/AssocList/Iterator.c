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
lean_object* v___x_29_; 
v___x_29_ = l___private_Std_Data_DHashMap_Internal_AssocList_Iterator_0__Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma_match__3_splitter___redArg(v_it_26_, v_h__1_27_, v_h__2_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Iterator_0__Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma_match__1_splitter___redArg(lean_object* v_x_30_, lean_object* v_h__1_31_, lean_object* v_h__2_32_, lean_object* v_h__3_33_){
_start:
{
switch(lean_obj_tag(v_x_30_))
{
case 0:
{
lean_object* v_it_34_; lean_object* v_out_35_; lean_object* v___x_36_; 
lean_dec(v_h__3_33_);
lean_dec(v_h__2_32_);
v_it_34_ = lean_ctor_get(v_x_30_, 0);
lean_inc(v_it_34_);
v_out_35_ = lean_ctor_get(v_x_30_, 1);
lean_inc(v_out_35_);
lean_dec_ref(v_x_30_);
v___x_36_ = lean_apply_2(v_h__1_31_, v_it_34_, v_out_35_);
return v___x_36_;
}
case 1:
{
lean_object* v_it_37_; lean_object* v___x_38_; 
lean_dec(v_h__3_33_);
lean_dec(v_h__1_31_);
v_it_37_ = lean_ctor_get(v_x_30_, 0);
lean_inc(v_it_37_);
lean_dec_ref(v_x_30_);
v___x_38_ = lean_apply_1(v_h__2_32_, v_it_37_);
return v___x_38_;
}
default: 
{
lean_object* v___x_39_; lean_object* v___x_40_; 
lean_dec(v_h__2_32_);
lean_dec(v_h__1_31_);
v___x_39_ = lean_box(0);
v___x_40_ = lean_apply_1(v_h__3_33_, v___x_39_);
return v___x_40_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Iterator_0__Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma_match__1_splitter(lean_object* v_00_u03b1_41_, lean_object* v_00_u03b2_42_, lean_object* v_motive_43_, lean_object* v_x_44_, lean_object* v_h__1_45_, lean_object* v_h__2_46_, lean_object* v_h__3_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l___private_Std_Data_DHashMap_Internal_AssocList_Iterator_0__Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma_match__1_splitter___redArg(v_x_44_, v_h__1_45_, v_h__2_46_, v_h__3_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Iterator_0__Std_DHashMap_Internal_AssocList_AssocListIterator_finitenessRelation(lean_object* v_00_u03b1_49_, lean_object* v_00_u03b2_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lean_box(0);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__0(lean_object* v_toPure_52_, lean_object* v_recur_53_, lean_object* v_it_54_, lean_object* v_____do__lift_55_){
_start:
{
if (lean_obj_tag(v_____do__lift_55_) == 0)
{
lean_object* v_a_56_; lean_object* v___x_57_; 
lean_dec(v_it_54_);
lean_dec(v_recur_53_);
v_a_56_ = lean_ctor_get(v_____do__lift_55_, 0);
lean_inc(v_a_56_);
lean_dec_ref(v_____do__lift_55_);
v___x_57_ = lean_apply_2(v_toPure_52_, lean_box(0), v_a_56_);
return v___x_57_;
}
else
{
lean_object* v_a_58_; lean_object* v___x_59_; 
lean_dec(v_toPure_52_);
v_a_58_ = lean_ctor_get(v_____do__lift_55_, 0);
lean_inc(v_a_58_);
lean_dec_ref(v_____do__lift_55_);
v___x_59_ = lean_apply_4(v_recur_53_, v_it_54_, v_a_58_, lean_box(0), lean_box(0));
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__1(lean_object* v_toPure_60_, lean_object* v_recur_61_, lean_object* v___y_62_, lean_object* v_acc_63_, lean_object* v_toBind_64_, lean_object* v_s_65_){
_start:
{
switch(lean_obj_tag(v_s_65_))
{
case 0:
{
lean_object* v_it_66_; lean_object* v_out_67_; lean_object* v___f_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v_it_66_ = lean_ctor_get(v_s_65_, 0);
lean_inc(v_it_66_);
v_out_67_ = lean_ctor_get(v_s_65_, 1);
lean_inc(v_out_67_);
lean_dec_ref(v_s_65_);
v___f_68_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_68_, 0, v_toPure_60_);
lean_closure_set(v___f_68_, 1, v_recur_61_);
lean_closure_set(v___f_68_, 2, v_it_66_);
v___x_69_ = lean_apply_3(v___y_62_, v_out_67_, lean_box(0), v_acc_63_);
v___x_70_ = lean_apply_4(v_toBind_64_, lean_box(0), lean_box(0), v___x_69_, v___f_68_);
return v___x_70_;
}
case 1:
{
lean_object* v_it_71_; lean_object* v___x_72_; 
lean_dec(v_toBind_64_);
lean_dec(v___y_62_);
lean_dec(v_toPure_60_);
v_it_71_ = lean_ctor_get(v_s_65_, 0);
lean_inc(v_it_71_);
lean_dec_ref(v_s_65_);
v___x_72_ = lean_apply_4(v_recur_61_, v_it_71_, v_acc_63_, lean_box(0), lean_box(0));
return v___x_72_;
}
default: 
{
lean_object* v___x_73_; 
lean_dec(v_toBind_64_);
lean_dec(v___y_62_);
lean_dec(v_recur_61_);
v___x_73_ = lean_apply_2(v_toPure_60_, lean_box(0), v_acc_63_);
return v___x_73_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__2(lean_object* v_toPure_74_, lean_object* v___y_75_, lean_object* v_toBind_76_, lean_object* v_lift_77_, lean_object* v_it_78_, lean_object* v_acc_79_, lean_object* v_hP_80_, lean_object* v_recur_81_){
_start:
{
lean_object* v___f_82_; 
v___f_82_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_82_, 0, v_toPure_74_);
lean_closure_set(v___f_82_, 1, v_recur_81_);
lean_closure_set(v___f_82_, 2, v___y_75_);
lean_closure_set(v___f_82_, 3, v_acc_79_);
lean_closure_set(v___f_82_, 4, v_toBind_76_);
if (lean_obj_tag(v_it_78_) == 0)
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_box(2);
v___x_84_ = lean_apply_4(v_lift_77_, lean_box(0), lean_box(0), v___f_82_, v___x_83_);
return v___x_84_;
}
else
{
lean_object* v_key_85_; lean_object* v_value_86_; lean_object* v_tail_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v_key_85_ = lean_ctor_get(v_it_78_, 0);
v_value_86_ = lean_ctor_get(v_it_78_, 1);
v_tail_87_ = lean_ctor_get(v_it_78_, 2);
lean_inc(v_value_86_);
lean_inc(v_key_85_);
v___x_88_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_88_, 0, v_key_85_);
lean_ctor_set(v___x_88_, 1, v_value_86_);
lean_inc(v_tail_87_);
v___x_89_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_89_, 0, v_tail_87_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = lean_apply_4(v_lift_77_, lean_box(0), lean_box(0), v___f_82_, v___x_89_);
return v___x_90_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__2___boxed(lean_object* v_toPure_91_, lean_object* v___y_92_, lean_object* v_toBind_93_, lean_object* v_lift_94_, lean_object* v_it_95_, lean_object* v_acc_96_, lean_object* v_hP_97_, lean_object* v_recur_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__2(v_toPure_91_, v___y_92_, v_toBind_93_, v_lift_94_, v_it_95_, v_acc_96_, v_hP_97_, v_recur_98_);
lean_dec(v_it_95_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__3(lean_object* v_inst_100_, lean_object* v_lift_101_, lean_object* v_00_u03b3_102_, lean_object* v_Pl_103_, lean_object* v_it_104_, lean_object* v_init_105_, lean_object* v___y_106_){
_start:
{
lean_object* v_toApplicative_107_; lean_object* v_toBind_108_; lean_object* v_toPure_109_; lean_object* v___f_110_; lean_object* v___x_111_; 
v_toApplicative_107_ = lean_ctor_get(v_inst_100_, 0);
lean_inc_ref(v_toApplicative_107_);
v_toBind_108_ = lean_ctor_get(v_inst_100_, 1);
lean_inc(v_toBind_108_);
lean_dec_ref(v_inst_100_);
v_toPure_109_ = lean_ctor_get(v_toApplicative_107_, 1);
lean_inc(v_toPure_109_);
lean_dec_ref(v_toApplicative_107_);
v___f_110_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__2___boxed), 8, 4);
lean_closure_set(v___f_110_, 0, v_toPure_109_);
lean_closure_set(v___f_110_, 1, v___y_106_);
lean_closure_set(v___f_110_, 2, v_toBind_108_);
lean_closure_set(v___f_110_, 3, v_lift_101_);
v___x_111_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_110_, v_it_104_, v_init_105_, lean_box(0));
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg(lean_object* v_inst_112_){
_start:
{
lean_object* v___f_113_; 
v___f_113_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__3), 7, 1);
lean_closure_set(v___f_113_, 0, v_inst_112_);
return v___f_113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad(lean_object* v_00_u03b1_114_, lean_object* v_00_u03b2_115_, lean_object* v_m_116_, lean_object* v_inst_117_){
_start:
{
lean_object* v___f_118_; 
v___f_118_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__3), 7, 1);
lean_closure_set(v___f_118_, 0, v_inst_117_);
return v___f_118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_iter___redArg(lean_object* v_l_119_){
_start:
{
lean_inc(v_l_119_);
return v_l_119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_iter___redArg___boxed(lean_object* v_l_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Std_DHashMap_Internal_AssocList_iter___redArg(v_l_120_);
lean_dec(v_l_120_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_iter(lean_object* v_00_u03b1_122_, lean_object* v_00_u03b2_123_, lean_object* v_l_124_){
_start:
{
lean_inc(v_l_124_);
return v_l_124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_iter___boxed(lean_object* v_00_u03b1_125_, lean_object* v_00_u03b2_126_, lean_object* v_l_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Std_DHashMap_Internal_AssocList_iter(v_00_u03b1_125_, v_00_u03b2_126_, v_l_127_);
lean_dec(v_l_127_);
return v_res_128_;
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

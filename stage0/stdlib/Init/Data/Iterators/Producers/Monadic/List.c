// Lean compiler output
// Module: Init.Data.Iterators.Producers.Monadic.List
// Imports: public import Init.Data.Iterators.Consumers import Init.Data.Nat.Lemmas
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
LEAN_EXPORT lean_object* l_List_iterM___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_iterM___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_iterM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_iterM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ListIterator_instIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ListIterator_instIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ListIterator_instIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instFinitenessRelation(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instFinitenessRelation___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ListIterator_instIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_iterM___redArg(lean_object* v_l_1_){
_start:
{
lean_inc(v_l_1_);
return v_l_1_;
}
}
LEAN_EXPORT lean_object* l_List_iterM___redArg___boxed(lean_object* v_l_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l_List_iterM___redArg(v_l_2_);
lean_dec(v_l_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l_List_iterM(lean_object* v_00_u03b1_4_, lean_object* v_l_5_, lean_object* v_m_6_, lean_object* v_inst_7_){
_start:
{
lean_inc(v_l_5_);
return v_l_5_;
}
}
LEAN_EXPORT lean_object* l_List_iterM___boxed(lean_object* v_00_u03b1_8_, lean_object* v_l_9_, lean_object* v_m_10_, lean_object* v_inst_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_List_iterM(v_00_u03b1_8_, v_l_9_, v_m_10_, v_inst_11_);
lean_dec(v_inst_11_);
lean_dec(v_l_9_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ListIterator_instIterator___redArg___lam__0(lean_object* v_inst_13_, lean_object* v_it_14_){
_start:
{
if (lean_obj_tag(v_it_14_) == 0)
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_box(2);
v___x_16_ = lean_apply_2(v_inst_13_, lean_box(0), v___x_15_);
return v___x_16_;
}
else
{
lean_object* v_head_17_; lean_object* v_tail_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_26_; 
v_head_17_ = lean_ctor_get(v_it_14_, 0);
v_tail_18_ = lean_ctor_get(v_it_14_, 1);
v_isSharedCheck_26_ = !lean_is_exclusive(v_it_14_);
if (v_isSharedCheck_26_ == 0)
{
v___x_20_ = v_it_14_;
v_isShared_21_ = v_isSharedCheck_26_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_tail_18_);
lean_inc(v_head_17_);
lean_dec(v_it_14_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_26_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_23_; 
if (v_isShared_21_ == 0)
{
lean_ctor_set_tag(v___x_20_, 0);
lean_ctor_set(v___x_20_, 1, v_head_17_);
lean_ctor_set(v___x_20_, 0, v_tail_18_);
v___x_23_ = v___x_20_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v_tail_18_);
lean_ctor_set(v_reuseFailAlloc_25_, 1, v_head_17_);
v___x_23_ = v_reuseFailAlloc_25_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
lean_object* v___x_24_; 
v___x_24_ = lean_apply_2(v_inst_13_, lean_box(0), v___x_23_);
return v___x_24_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ListIterator_instIterator___redArg(lean_object* v_inst_27_){
_start:
{
lean_object* v___f_28_; 
v___f_28_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ListIterator_instIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_28_, 0, v_inst_27_);
return v___f_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ListIterator_instIterator(lean_object* v_m_29_, lean_object* v_00_u03b1_30_, lean_object* v_inst_31_){
_start:
{
lean_object* v___f_32_; 
v___f_32_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ListIterator_instIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_32_, 0, v_inst_31_);
return v___f_32_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__3_splitter___redArg(lean_object* v_it_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_){
_start:
{
if (lean_obj_tag(v_it_33_) == 0)
{
lean_object* v___x_36_; lean_object* v___x_37_; 
lean_dec(v_h__2_35_);
v___x_36_ = lean_box(0);
v___x_37_ = lean_apply_1(v_h__1_34_, v___x_36_);
return v___x_37_;
}
else
{
lean_object* v_head_38_; lean_object* v_tail_39_; lean_object* v___x_40_; 
lean_dec(v_h__1_34_);
v_head_38_ = lean_ctor_get(v_it_33_, 0);
lean_inc(v_head_38_);
v_tail_39_ = lean_ctor_get(v_it_33_, 1);
lean_inc(v_tail_39_);
lean_dec_ref(v_it_33_);
v___x_40_ = lean_apply_2(v_h__2_35_, v_head_38_, v_tail_39_);
return v___x_40_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__3_splitter(lean_object* v_m_41_, lean_object* v_00_u03b1_42_, lean_object* v_motive_43_, lean_object* v_it_44_, lean_object* v_h__1_45_, lean_object* v_h__2_46_){
_start:
{
if (lean_obj_tag(v_it_44_) == 0)
{
lean_object* v___x_47_; lean_object* v___x_48_; 
lean_dec(v_h__2_46_);
v___x_47_ = lean_box(0);
v___x_48_ = lean_apply_1(v_h__1_45_, v___x_47_);
return v___x_48_;
}
else
{
lean_object* v_head_49_; lean_object* v_tail_50_; lean_object* v___x_51_; 
lean_dec(v_h__1_45_);
v_head_49_ = lean_ctor_get(v_it_44_, 0);
lean_inc(v_head_49_);
v_tail_50_ = lean_ctor_get(v_it_44_, 1);
lean_inc(v_tail_50_);
lean_dec_ref(v_it_44_);
v___x_51_ = lean_apply_2(v_h__2_46_, v_head_49_, v_tail_50_);
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__1_splitter___redArg(lean_object* v_x_52_, lean_object* v_h__1_53_, lean_object* v_h__2_54_, lean_object* v_h__3_55_){
_start:
{
switch(lean_obj_tag(v_x_52_))
{
case 0:
{
lean_object* v_it_56_; lean_object* v_out_57_; lean_object* v___x_58_; 
lean_dec(v_h__3_55_);
lean_dec(v_h__2_54_);
v_it_56_ = lean_ctor_get(v_x_52_, 0);
lean_inc(v_it_56_);
v_out_57_ = lean_ctor_get(v_x_52_, 1);
lean_inc(v_out_57_);
lean_dec_ref(v_x_52_);
v___x_58_ = lean_apply_2(v_h__1_53_, v_it_56_, v_out_57_);
return v___x_58_;
}
case 1:
{
lean_object* v_it_59_; lean_object* v___x_60_; 
lean_dec(v_h__3_55_);
lean_dec(v_h__1_53_);
v_it_59_ = lean_ctor_get(v_x_52_, 0);
lean_inc(v_it_59_);
lean_dec_ref(v_x_52_);
v___x_60_ = lean_apply_1(v_h__2_54_, v_it_59_);
return v___x_60_;
}
default: 
{
lean_object* v___x_61_; lean_object* v___x_62_; 
lean_dec(v_h__2_54_);
lean_dec(v_h__1_53_);
v___x_61_ = lean_box(0);
v___x_62_ = lean_apply_1(v_h__3_55_, v___x_61_);
return v___x_62_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__1_splitter(lean_object* v_m_63_, lean_object* v_00_u03b1_64_, lean_object* v_motive_65_, lean_object* v_x_66_, lean_object* v_h__1_67_, lean_object* v_h__2_68_, lean_object* v_h__3_69_){
_start:
{
switch(lean_obj_tag(v_x_66_))
{
case 0:
{
lean_object* v_it_70_; lean_object* v_out_71_; lean_object* v___x_72_; 
lean_dec(v_h__3_69_);
lean_dec(v_h__2_68_);
v_it_70_ = lean_ctor_get(v_x_66_, 0);
lean_inc(v_it_70_);
v_out_71_ = lean_ctor_get(v_x_66_, 1);
lean_inc(v_out_71_);
lean_dec_ref(v_x_66_);
v___x_72_ = lean_apply_2(v_h__1_67_, v_it_70_, v_out_71_);
return v___x_72_;
}
case 1:
{
lean_object* v_it_73_; lean_object* v___x_74_; 
lean_dec(v_h__3_69_);
lean_dec(v_h__1_67_);
v_it_73_ = lean_ctor_get(v_x_66_, 0);
lean_inc(v_it_73_);
lean_dec_ref(v_x_66_);
v___x_74_ = lean_apply_1(v_h__2_68_, v_it_73_);
return v___x_74_;
}
default: 
{
lean_object* v___x_75_; lean_object* v___x_76_; 
lean_dec(v_h__2_68_);
lean_dec(v_h__1_67_);
v___x_75_ = lean_box(0);
v___x_76_ = lean_apply_1(v_h__3_69_, v___x_75_);
return v___x_76_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instFinitenessRelation(lean_object* v_00_u03b1_77_, lean_object* v_m_78_, lean_object* v_inst_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_box(0);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instFinitenessRelation___boxed(lean_object* v_00_u03b1_81_, lean_object* v_m_82_, lean_object* v_inst_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instFinitenessRelation(v_00_u03b1_81_, v_m_82_, v_inst_83_);
lean_dec(v_inst_83_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_85_, lean_object* v_recur_86_, lean_object* v_it_87_, lean_object* v_____do__lift_88_){
_start:
{
if (lean_obj_tag(v_____do__lift_88_) == 0)
{
lean_object* v_a_89_; lean_object* v___x_90_; 
lean_dec(v_it_87_);
lean_dec(v_recur_86_);
v_a_89_ = lean_ctor_get(v_____do__lift_88_, 0);
lean_inc(v_a_89_);
lean_dec_ref(v_____do__lift_88_);
v___x_90_ = lean_apply_2(v_toPure_85_, lean_box(0), v_a_89_);
return v___x_90_;
}
else
{
lean_object* v_a_91_; lean_object* v___x_92_; 
lean_dec(v_toPure_85_);
v_a_91_ = lean_ctor_get(v_____do__lift_88_, 0);
lean_inc(v_a_91_);
lean_dec_ref(v_____do__lift_88_);
v___x_92_ = lean_apply_4(v_recur_86_, v_it_87_, v_a_91_, lean_box(0), lean_box(0));
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_93_, lean_object* v_recur_94_, lean_object* v___y_95_, lean_object* v_acc_96_, lean_object* v_toBind_97_, lean_object* v_s_98_){
_start:
{
switch(lean_obj_tag(v_s_98_))
{
case 0:
{
lean_object* v_it_99_; lean_object* v_out_100_; lean_object* v___f_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v_it_99_ = lean_ctor_get(v_s_98_, 0);
lean_inc(v_it_99_);
v_out_100_ = lean_ctor_get(v_s_98_, 1);
lean_inc(v_out_100_);
lean_dec_ref(v_s_98_);
v___f_101_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_101_, 0, v_toPure_93_);
lean_closure_set(v___f_101_, 1, v_recur_94_);
lean_closure_set(v___f_101_, 2, v_it_99_);
v___x_102_ = lean_apply_3(v___y_95_, v_out_100_, lean_box(0), v_acc_96_);
v___x_103_ = lean_apply_4(v_toBind_97_, lean_box(0), lean_box(0), v___x_102_, v___f_101_);
return v___x_103_;
}
case 1:
{
lean_object* v_it_104_; lean_object* v___x_105_; 
lean_dec(v_toBind_97_);
lean_dec(v___y_95_);
lean_dec(v_toPure_93_);
v_it_104_ = lean_ctor_get(v_s_98_, 0);
lean_inc(v_it_104_);
lean_dec_ref(v_s_98_);
v___x_105_ = lean_apply_4(v_recur_94_, v_it_104_, v_acc_96_, lean_box(0), lean_box(0));
return v___x_105_;
}
default: 
{
lean_object* v___x_106_; 
lean_dec(v_toBind_97_);
lean_dec(v___y_95_);
lean_dec(v_recur_94_);
v___x_106_ = lean_apply_2(v_toPure_93_, lean_box(0), v_acc_96_);
return v___x_106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_107_, lean_object* v___y_108_, lean_object* v_toBind_109_, lean_object* v_toPure_110_, lean_object* v_lift_111_, lean_object* v_it_112_, lean_object* v_acc_113_, lean_object* v_hP_114_, lean_object* v_recur_115_){
_start:
{
lean_object* v___f_116_; 
v___f_116_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_116_, 0, v_toPure_107_);
lean_closure_set(v___f_116_, 1, v_recur_115_);
lean_closure_set(v___f_116_, 2, v___y_108_);
lean_closure_set(v___f_116_, 3, v_acc_113_);
lean_closure_set(v___f_116_, 4, v_toBind_109_);
if (lean_obj_tag(v_it_112_) == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_117_ = lean_box(2);
v___x_118_ = lean_apply_2(v_toPure_110_, lean_box(0), v___x_117_);
v___x_119_ = lean_apply_4(v_lift_111_, lean_box(0), lean_box(0), v___f_116_, v___x_118_);
return v___x_119_;
}
else
{
lean_object* v_head_120_; lean_object* v_tail_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_130_; 
v_head_120_ = lean_ctor_get(v_it_112_, 0);
v_tail_121_ = lean_ctor_get(v_it_112_, 1);
v_isSharedCheck_130_ = !lean_is_exclusive(v_it_112_);
if (v_isSharedCheck_130_ == 0)
{
v___x_123_ = v_it_112_;
v_isShared_124_ = v_isSharedCheck_130_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_tail_121_);
lean_inc(v_head_120_);
lean_dec(v_it_112_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_130_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
if (v_isShared_124_ == 0)
{
lean_ctor_set_tag(v___x_123_, 0);
lean_ctor_set(v___x_123_, 1, v_head_120_);
lean_ctor_set(v___x_123_, 0, v_tail_121_);
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_tail_121_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_head_120_);
v___x_126_ = v_reuseFailAlloc_129_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_apply_2(v_toPure_110_, lean_box(0), v___x_126_);
v___x_128_ = lean_apply_4(v_lift_111_, lean_box(0), lean_box(0), v___f_116_, v___x_127_);
return v___x_128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__3(lean_object* v_inst_131_, lean_object* v_toPure_132_, lean_object* v_lift_133_, lean_object* v_00_u03b3_134_, lean_object* v_Pl_135_, lean_object* v_it_136_, lean_object* v_init_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_toApplicative_139_; lean_object* v_toBind_140_; lean_object* v_toPure_141_; lean_object* v___f_142_; lean_object* v___x_143_; 
v_toApplicative_139_ = lean_ctor_get(v_inst_131_, 0);
lean_inc_ref(v_toApplicative_139_);
v_toBind_140_ = lean_ctor_get(v_inst_131_, 1);
lean_inc(v_toBind_140_);
lean_dec_ref(v_inst_131_);
v_toPure_141_ = lean_ctor_get(v_toApplicative_139_, 1);
lean_inc(v_toPure_141_);
lean_dec_ref(v_toApplicative_139_);
v___f_142_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__2), 9, 5);
lean_closure_set(v___f_142_, 0, v_toPure_141_);
lean_closure_set(v___f_142_, 1, v___y_138_);
lean_closure_set(v___f_142_, 2, v_toBind_140_);
lean_closure_set(v___f_142_, 3, v_toPure_132_);
lean_closure_set(v___f_142_, 4, v_lift_133_);
v___x_143_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_142_, v_it_136_, v_init_137_, lean_box(0));
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg(lean_object* v_inst_144_, lean_object* v_inst_145_){
_start:
{
lean_object* v_toApplicative_146_; lean_object* v_toPure_147_; lean_object* v___f_148_; 
v_toApplicative_146_ = lean_ctor_get(v_inst_144_, 0);
lean_inc_ref(v_toApplicative_146_);
lean_dec_ref(v_inst_144_);
v_toPure_147_ = lean_ctor_get(v_toApplicative_146_, 1);
lean_inc(v_toPure_147_);
lean_dec_ref(v_toApplicative_146_);
v___f_148_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_148_, 0, v_inst_145_);
lean_closure_set(v___f_148_, 1, v_toPure_147_);
return v___f_148_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ListIterator_instIteratorLoop(lean_object* v_m_149_, lean_object* v_00_u03b1_150_, lean_object* v_inst_151_, lean_object* v_n_152_, lean_object* v_inst_153_){
_start:
{
lean_object* v_toApplicative_154_; lean_object* v_toPure_155_; lean_object* v___f_156_; 
v_toApplicative_154_ = lean_ctor_get(v_inst_151_, 0);
lean_inc_ref(v_toApplicative_154_);
lean_dec_ref(v_inst_151_);
v_toPure_155_ = lean_ctor_get(v_toApplicative_154_, 1);
lean_inc(v_toPure_155_);
lean_dec_ref(v_toApplicative_154_);
v___f_156_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_156_, 0, v_inst_153_);
lean_closure_set(v___f_156_, 1, v_toPure_155_);
return v___f_156_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Producers_Monadic_List(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Consumers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Producers_Monadic_List(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Consumers(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Producers_Monadic_List(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Consumers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Producers_Monadic_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Producers_Monadic_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Producers_Monadic_List(builtin);
}
#ifdef __cplusplus
}
#endif

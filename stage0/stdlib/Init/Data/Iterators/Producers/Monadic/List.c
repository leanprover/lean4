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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instFinitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instFinitenessRelation___redArg___boxed(lean_object*);
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
lean_dec_ref_known(v_it_33_, 2);
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
lean_dec_ref_known(v_it_44_, 2);
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
lean_dec_ref_known(v_x_52_, 2);
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
lean_dec_ref_known(v_x_52_, 1);
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
lean_dec_ref_known(v_x_66_, 2);
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
lean_dec_ref_known(v_x_66_, 1);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_box(0);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instFinitenessRelation___redArg___boxed(lean_object* v___dummy_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instFinitenessRelation___redArg();
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instFinitenessRelation(lean_object* v_00_u03b1_81_, lean_object* v_m_82_, lean_object* v_inst_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lean_box(0);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instFinitenessRelation___boxed(lean_object* v_00_u03b1_85_, lean_object* v_m_86_, lean_object* v_inst_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instFinitenessRelation(v_00_u03b1_85_, v_m_86_, v_inst_87_);
lean_dec(v_inst_87_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_89_, lean_object* v_recur_90_, lean_object* v_it_91_, lean_object* v_____do__lift_92_){
_start:
{
if (lean_obj_tag(v_____do__lift_92_) == 0)
{
lean_object* v_a_93_; lean_object* v___x_94_; 
lean_dec(v_it_91_);
lean_dec(v_recur_90_);
v_a_93_ = lean_ctor_get(v_____do__lift_92_, 0);
lean_inc(v_a_93_);
lean_dec_ref_known(v_____do__lift_92_, 1);
v___x_94_ = lean_apply_2(v_toPure_89_, lean_box(0), v_a_93_);
return v___x_94_;
}
else
{
lean_object* v_a_95_; lean_object* v___x_96_; 
lean_dec(v_toPure_89_);
v_a_95_ = lean_ctor_get(v_____do__lift_92_, 0);
lean_inc(v_a_95_);
lean_dec_ref_known(v_____do__lift_92_, 1);
v___x_96_ = lean_apply_4(v_recur_90_, v_it_91_, v_a_95_, lean_box(0), lean_box(0));
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_97_, lean_object* v_recur_98_, lean_object* v___y_99_, lean_object* v_acc_100_, lean_object* v_toBind_101_, lean_object* v_s_102_){
_start:
{
switch(lean_obj_tag(v_s_102_))
{
case 0:
{
lean_object* v_it_103_; lean_object* v_out_104_; lean_object* v___f_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v_it_103_ = lean_ctor_get(v_s_102_, 0);
lean_inc(v_it_103_);
v_out_104_ = lean_ctor_get(v_s_102_, 1);
lean_inc(v_out_104_);
lean_dec_ref_known(v_s_102_, 2);
v___f_105_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_105_, 0, v_toPure_97_);
lean_closure_set(v___f_105_, 1, v_recur_98_);
lean_closure_set(v___f_105_, 2, v_it_103_);
v___x_106_ = lean_apply_3(v___y_99_, v_out_104_, lean_box(0), v_acc_100_);
v___x_107_ = lean_apply_4(v_toBind_101_, lean_box(0), lean_box(0), v___x_106_, v___f_105_);
return v___x_107_;
}
case 1:
{
lean_object* v_it_108_; lean_object* v___x_109_; 
lean_dec(v_toBind_101_);
lean_dec(v___y_99_);
lean_dec(v_toPure_97_);
v_it_108_ = lean_ctor_get(v_s_102_, 0);
lean_inc(v_it_108_);
lean_dec_ref_known(v_s_102_, 1);
v___x_109_ = lean_apply_4(v_recur_98_, v_it_108_, v_acc_100_, lean_box(0), lean_box(0));
return v___x_109_;
}
default: 
{
lean_object* v___x_110_; 
lean_dec(v_toBind_101_);
lean_dec(v___y_99_);
lean_dec(v_recur_98_);
v___x_110_ = lean_apply_2(v_toPure_97_, lean_box(0), v_acc_100_);
return v___x_110_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_111_, lean_object* v___y_112_, lean_object* v_toBind_113_, lean_object* v_toPure_114_, lean_object* v_lift_115_, lean_object* v_it_116_, lean_object* v_acc_117_, lean_object* v_hP_118_, lean_object* v_recur_119_){
_start:
{
lean_object* v___f_120_; 
v___f_120_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_120_, 0, v_toPure_111_);
lean_closure_set(v___f_120_, 1, v_recur_119_);
lean_closure_set(v___f_120_, 2, v___y_112_);
lean_closure_set(v___f_120_, 3, v_acc_117_);
lean_closure_set(v___f_120_, 4, v_toBind_113_);
if (lean_obj_tag(v_it_116_) == 0)
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_121_ = lean_box(2);
v___x_122_ = lean_apply_2(v_toPure_114_, lean_box(0), v___x_121_);
v___x_123_ = lean_apply_4(v_lift_115_, lean_box(0), lean_box(0), v___f_120_, v___x_122_);
return v___x_123_;
}
else
{
lean_object* v_head_124_; lean_object* v_tail_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_134_; 
v_head_124_ = lean_ctor_get(v_it_116_, 0);
v_tail_125_ = lean_ctor_get(v_it_116_, 1);
v_isSharedCheck_134_ = !lean_is_exclusive(v_it_116_);
if (v_isSharedCheck_134_ == 0)
{
v___x_127_ = v_it_116_;
v_isShared_128_ = v_isSharedCheck_134_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_tail_125_);
lean_inc(v_head_124_);
lean_dec(v_it_116_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_134_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_130_; 
if (v_isShared_128_ == 0)
{
lean_ctor_set_tag(v___x_127_, 0);
lean_ctor_set(v___x_127_, 1, v_head_124_);
lean_ctor_set(v___x_127_, 0, v_tail_125_);
v___x_130_ = v___x_127_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_tail_125_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v_head_124_);
v___x_130_ = v_reuseFailAlloc_133_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_apply_2(v_toPure_114_, lean_box(0), v___x_130_);
v___x_132_ = lean_apply_4(v_lift_115_, lean_box(0), lean_box(0), v___f_120_, v___x_131_);
return v___x_132_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__3(lean_object* v_inst_135_, lean_object* v_toPure_136_, lean_object* v_lift_137_, lean_object* v_00_u03b3_138_, lean_object* v_Pl_139_, lean_object* v_it_140_, lean_object* v_init_141_, lean_object* v___y_142_){
_start:
{
lean_object* v_toApplicative_143_; lean_object* v_toBind_144_; lean_object* v_toPure_145_; lean_object* v___f_146_; lean_object* v___x_147_; 
v_toApplicative_143_ = lean_ctor_get(v_inst_135_, 0);
lean_inc_ref(v_toApplicative_143_);
v_toBind_144_ = lean_ctor_get(v_inst_135_, 1);
lean_inc(v_toBind_144_);
lean_dec_ref(v_inst_135_);
v_toPure_145_ = lean_ctor_get(v_toApplicative_143_, 1);
lean_inc(v_toPure_145_);
lean_dec_ref(v_toApplicative_143_);
v___f_146_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__2), 9, 5);
lean_closure_set(v___f_146_, 0, v_toPure_145_);
lean_closure_set(v___f_146_, 1, v___y_142_);
lean_closure_set(v___f_146_, 2, v_toBind_144_);
lean_closure_set(v___f_146_, 3, v_toPure_136_);
lean_closure_set(v___f_146_, 4, v_lift_137_);
v___x_147_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_146_, v_it_140_, v_init_141_, lean_box(0));
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg(lean_object* v_inst_148_, lean_object* v_inst_149_){
_start:
{
lean_object* v_toApplicative_150_; lean_object* v_toPure_151_; lean_object* v___f_152_; 
v_toApplicative_150_ = lean_ctor_get(v_inst_148_, 0);
lean_inc_ref(v_toApplicative_150_);
lean_dec_ref(v_inst_148_);
v_toPure_151_ = lean_ctor_get(v_toApplicative_150_, 1);
lean_inc(v_toPure_151_);
lean_dec_ref(v_toApplicative_150_);
v___f_152_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_152_, 0, v_inst_149_);
lean_closure_set(v___f_152_, 1, v_toPure_151_);
return v___f_152_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ListIterator_instIteratorLoop(lean_object* v_m_153_, lean_object* v_00_u03b1_154_, lean_object* v_inst_155_, lean_object* v_n_156_, lean_object* v_inst_157_){
_start:
{
lean_object* v_toApplicative_158_; lean_object* v_toPure_159_; lean_object* v___f_160_; 
v_toApplicative_158_ = lean_ctor_get(v_inst_155_, 0);
lean_inc_ref(v_toApplicative_158_);
lean_dec_ref(v_inst_155_);
v_toPure_159_ = lean_ctor_get(v_toApplicative_158_, 1);
lean_inc(v_toPure_159_);
lean_dec_ref(v_toApplicative_158_);
v___f_160_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_160_, 0, v_inst_157_);
lean_closure_set(v___f_160_, 1, v_toPure_159_);
return v___f_160_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Producers_Monadic_List(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

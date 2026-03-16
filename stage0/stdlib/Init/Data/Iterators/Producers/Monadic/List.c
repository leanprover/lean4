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
lean_object* v___x_47_; 
v___x_47_ = l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__3_splitter___redArg(v_it_44_, v_h__1_45_, v_h__2_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__1_splitter___redArg(lean_object* v_x_48_, lean_object* v_h__1_49_, lean_object* v_h__2_50_, lean_object* v_h__3_51_){
_start:
{
switch(lean_obj_tag(v_x_48_))
{
case 0:
{
lean_object* v_it_52_; lean_object* v_out_53_; lean_object* v___x_54_; 
lean_dec(v_h__3_51_);
lean_dec(v_h__2_50_);
v_it_52_ = lean_ctor_get(v_x_48_, 0);
lean_inc(v_it_52_);
v_out_53_ = lean_ctor_get(v_x_48_, 1);
lean_inc(v_out_53_);
lean_dec_ref(v_x_48_);
v___x_54_ = lean_apply_2(v_h__1_49_, v_it_52_, v_out_53_);
return v___x_54_;
}
case 1:
{
lean_object* v_it_55_; lean_object* v___x_56_; 
lean_dec(v_h__3_51_);
lean_dec(v_h__1_49_);
v_it_55_ = lean_ctor_get(v_x_48_, 0);
lean_inc(v_it_55_);
lean_dec_ref(v_x_48_);
v___x_56_ = lean_apply_1(v_h__2_50_, v_it_55_);
return v___x_56_;
}
default: 
{
lean_object* v___x_57_; lean_object* v___x_58_; 
lean_dec(v_h__2_50_);
lean_dec(v_h__1_49_);
v___x_57_ = lean_box(0);
v___x_58_ = lean_apply_1(v_h__3_51_, v___x_57_);
return v___x_58_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__1_splitter(lean_object* v_m_59_, lean_object* v_00_u03b1_60_, lean_object* v_motive_61_, lean_object* v_x_62_, lean_object* v_h__1_63_, lean_object* v_h__2_64_, lean_object* v_h__3_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__1_splitter___redArg(v_x_62_, v_h__1_63_, v_h__2_64_, v_h__3_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instFinitenessRelation(lean_object* v_00_u03b1_67_, lean_object* v_m_68_, lean_object* v_inst_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lean_box(0);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instFinitenessRelation___boxed(lean_object* v_00_u03b1_71_, lean_object* v_m_72_, lean_object* v_inst_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instFinitenessRelation(v_00_u03b1_71_, v_m_72_, v_inst_73_);
lean_dec(v_inst_73_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_75_, lean_object* v_recur_76_, lean_object* v_it_77_, lean_object* v_____do__lift_78_){
_start:
{
if (lean_obj_tag(v_____do__lift_78_) == 0)
{
lean_object* v_a_79_; lean_object* v___x_80_; 
lean_dec(v_it_77_);
lean_dec(v_recur_76_);
v_a_79_ = lean_ctor_get(v_____do__lift_78_, 0);
lean_inc(v_a_79_);
lean_dec_ref(v_____do__lift_78_);
v___x_80_ = lean_apply_2(v_toPure_75_, lean_box(0), v_a_79_);
return v___x_80_;
}
else
{
lean_object* v_a_81_; lean_object* v___x_82_; 
lean_dec(v_toPure_75_);
v_a_81_ = lean_ctor_get(v_____do__lift_78_, 0);
lean_inc(v_a_81_);
lean_dec_ref(v_____do__lift_78_);
v___x_82_ = lean_apply_4(v_recur_76_, v_it_77_, v_a_81_, lean_box(0), lean_box(0));
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_83_, lean_object* v_recur_84_, lean_object* v___y_85_, lean_object* v_acc_86_, lean_object* v_toBind_87_, lean_object* v_s_88_){
_start:
{
switch(lean_obj_tag(v_s_88_))
{
case 0:
{
lean_object* v_it_89_; lean_object* v_out_90_; lean_object* v___f_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v_it_89_ = lean_ctor_get(v_s_88_, 0);
lean_inc(v_it_89_);
v_out_90_ = lean_ctor_get(v_s_88_, 1);
lean_inc(v_out_90_);
lean_dec_ref(v_s_88_);
v___f_91_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_91_, 0, v_toPure_83_);
lean_closure_set(v___f_91_, 1, v_recur_84_);
lean_closure_set(v___f_91_, 2, v_it_89_);
v___x_92_ = lean_apply_3(v___y_85_, v_out_90_, lean_box(0), v_acc_86_);
v___x_93_ = lean_apply_4(v_toBind_87_, lean_box(0), lean_box(0), v___x_92_, v___f_91_);
return v___x_93_;
}
case 1:
{
lean_object* v_it_94_; lean_object* v___x_95_; 
lean_dec(v_toBind_87_);
lean_dec(v___y_85_);
lean_dec(v_toPure_83_);
v_it_94_ = lean_ctor_get(v_s_88_, 0);
lean_inc(v_it_94_);
lean_dec_ref(v_s_88_);
v___x_95_ = lean_apply_4(v_recur_84_, v_it_94_, v_acc_86_, lean_box(0), lean_box(0));
return v___x_95_;
}
default: 
{
lean_object* v___x_96_; 
lean_dec(v_toBind_87_);
lean_dec(v___y_85_);
lean_dec(v_recur_84_);
v___x_96_ = lean_apply_2(v_toPure_83_, lean_box(0), v_acc_86_);
return v___x_96_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_97_, lean_object* v___y_98_, lean_object* v_toBind_99_, lean_object* v_toPure_100_, lean_object* v_lift_101_, lean_object* v_it_102_, lean_object* v_acc_103_, lean_object* v_hP_104_, lean_object* v_recur_105_){
_start:
{
lean_object* v___f_106_; 
v___f_106_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_106_, 0, v_toPure_97_);
lean_closure_set(v___f_106_, 1, v_recur_105_);
lean_closure_set(v___f_106_, 2, v___y_98_);
lean_closure_set(v___f_106_, 3, v_acc_103_);
lean_closure_set(v___f_106_, 4, v_toBind_99_);
if (lean_obj_tag(v_it_102_) == 0)
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_107_ = lean_box(2);
v___x_108_ = lean_apply_2(v_toPure_100_, lean_box(0), v___x_107_);
v___x_109_ = lean_apply_4(v_lift_101_, lean_box(0), lean_box(0), v___f_106_, v___x_108_);
return v___x_109_;
}
else
{
lean_object* v_head_110_; lean_object* v_tail_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_120_; 
v_head_110_ = lean_ctor_get(v_it_102_, 0);
v_tail_111_ = lean_ctor_get(v_it_102_, 1);
v_isSharedCheck_120_ = !lean_is_exclusive(v_it_102_);
if (v_isSharedCheck_120_ == 0)
{
v___x_113_ = v_it_102_;
v_isShared_114_ = v_isSharedCheck_120_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_tail_111_);
lean_inc(v_head_110_);
lean_dec(v_it_102_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_120_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_116_; 
if (v_isShared_114_ == 0)
{
lean_ctor_set_tag(v___x_113_, 0);
lean_ctor_set(v___x_113_, 1, v_head_110_);
lean_ctor_set(v___x_113_, 0, v_tail_111_);
v___x_116_ = v___x_113_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_tail_111_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v_head_110_);
v___x_116_ = v_reuseFailAlloc_119_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lean_apply_2(v_toPure_100_, lean_box(0), v___x_116_);
v___x_118_ = lean_apply_4(v_lift_101_, lean_box(0), lean_box(0), v___f_106_, v___x_117_);
return v___x_118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__3(lean_object* v_inst_121_, lean_object* v_toPure_122_, lean_object* v_lift_123_, lean_object* v_00_u03b3_124_, lean_object* v_Pl_125_, lean_object* v_it_126_, lean_object* v_init_127_, lean_object* v___y_128_){
_start:
{
lean_object* v_toApplicative_129_; lean_object* v_toBind_130_; lean_object* v_toPure_131_; lean_object* v___f_132_; lean_object* v___x_133_; 
v_toApplicative_129_ = lean_ctor_get(v_inst_121_, 0);
lean_inc_ref(v_toApplicative_129_);
v_toBind_130_ = lean_ctor_get(v_inst_121_, 1);
lean_inc(v_toBind_130_);
lean_dec_ref(v_inst_121_);
v_toPure_131_ = lean_ctor_get(v_toApplicative_129_, 1);
lean_inc(v_toPure_131_);
lean_dec_ref(v_toApplicative_129_);
v___f_132_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__2), 9, 5);
lean_closure_set(v___f_132_, 0, v_toPure_131_);
lean_closure_set(v___f_132_, 1, v___y_128_);
lean_closure_set(v___f_132_, 2, v_toBind_130_);
lean_closure_set(v___f_132_, 3, v_toPure_122_);
lean_closure_set(v___f_132_, 4, v_lift_123_);
v___x_133_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_132_, v_it_126_, v_init_127_, lean_box(0));
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg(lean_object* v_inst_134_, lean_object* v_inst_135_){
_start:
{
lean_object* v_toApplicative_136_; lean_object* v_toPure_137_; lean_object* v___f_138_; 
v_toApplicative_136_ = lean_ctor_get(v_inst_134_, 0);
lean_inc_ref(v_toApplicative_136_);
lean_dec_ref(v_inst_134_);
v_toPure_137_ = lean_ctor_get(v_toApplicative_136_, 1);
lean_inc(v_toPure_137_);
lean_dec_ref(v_toApplicative_136_);
v___f_138_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_138_, 0, v_inst_135_);
lean_closure_set(v___f_138_, 1, v_toPure_137_);
return v___f_138_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ListIterator_instIteratorLoop(lean_object* v_m_139_, lean_object* v_00_u03b1_140_, lean_object* v_inst_141_, lean_object* v_n_142_, lean_object* v_inst_143_){
_start:
{
lean_object* v_toApplicative_144_; lean_object* v_toPure_145_; lean_object* v___f_146_; 
v_toApplicative_144_ = lean_ctor_get(v_inst_141_, 0);
lean_inc_ref(v_toApplicative_144_);
lean_dec_ref(v_inst_141_);
v_toPure_145_ = lean_ctor_get(v_toApplicative_144_, 1);
lean_inc(v_toPure_145_);
lean_dec_ref(v_toApplicative_144_);
v___f_146_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_146_, 0, v_inst_143_);
lean_closure_set(v___f_146_, 1, v_toPure_145_);
return v___f_146_;
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

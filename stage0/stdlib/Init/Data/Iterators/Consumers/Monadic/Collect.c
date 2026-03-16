// Lean compiler output
// Module: Init.Data.Iterators.Consumers.Monadic.Collect
// Imports: public import Init.Data.Iterators.Consumers.Monadic.Partial public import Init.Data.Iterators.Consumers.Monadic.Total public import Init.WFExtrinsicFix public import Init.Ext
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
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toArray_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toArray_go___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toArray_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toArray_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_IterM_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_IterM_toArray___redArg___closed__0 = (const lean_object*)&l_Std_IterM_toArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_IterM_toArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_toArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_toArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_toArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_toArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toListRev_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toListRev_go___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toListRev_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toListRev_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toListRev___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toListRev(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_toListRev___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_toListRev(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_toListRev___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_toListRev(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toList___redArg___lam__0(lean_object*);
static const lean_closure_object l_Std_IterM_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_IterM_toList___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_IterM_toList___redArg___closed__0 = (const lean_object*)&l_Std_IterM_toList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_IterM_toList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_toList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_toList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_toList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_toList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toArray_go___redArg___lam__0(lean_object* v_acc_1_, lean_object* v_recur_2_, lean_object* v_toPure_3_, lean_object* v_____do__lift_4_){
_start:
{
switch(lean_obj_tag(v_____do__lift_4_))
{
case 0:
{
lean_object* v_it_5_; lean_object* v_out_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
lean_dec(v_toPure_3_);
v_it_5_ = lean_ctor_get(v_____do__lift_4_, 0);
lean_inc(v_it_5_);
v_out_6_ = lean_ctor_get(v_____do__lift_4_, 1);
lean_inc(v_out_6_);
lean_dec_ref(v_____do__lift_4_);
v___x_7_ = lean_array_push(v_acc_1_, v_out_6_);
v___x_8_ = lean_apply_3(v_recur_2_, v_it_5_, v___x_7_, lean_box(0));
return v___x_8_;
}
case 1:
{
lean_object* v_it_9_; lean_object* v___x_10_; 
lean_dec(v_toPure_3_);
v_it_9_ = lean_ctor_get(v_____do__lift_4_, 0);
lean_inc(v_it_9_);
lean_dec_ref(v_____do__lift_4_);
v___x_10_ = lean_apply_3(v_recur_2_, v_it_9_, v_acc_1_, lean_box(0));
return v___x_10_;
}
default: 
{
lean_object* v___x_11_; 
lean_dec(v_recur_2_);
v___x_11_ = lean_apply_2(v_toPure_3_, lean_box(0), v_acc_1_);
return v___x_11_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toArray_go___redArg___lam__1(lean_object* v_toPure_12_, lean_object* v_inst_13_, lean_object* v_toBind_14_, lean_object* v_it_15_, lean_object* v_acc_16_, lean_object* v_recur_17_){
_start:
{
lean_object* v___f_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___f_18_ = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__0), 4, 3);
lean_closure_set(v___f_18_, 0, v_acc_16_);
lean_closure_set(v___f_18_, 1, v_recur_17_);
lean_closure_set(v___f_18_, 2, v_toPure_12_);
v___x_19_ = lean_apply_1(v_inst_13_, v_it_15_);
v___x_20_ = lean_apply_4(v_toBind_14_, lean_box(0), lean_box(0), v___x_19_, v___f_18_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toArray_go___redArg(lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_it_23_, lean_object* v_acc_24_){
_start:
{
lean_object* v_toApplicative_25_; lean_object* v_toBind_26_; lean_object* v_toPure_27_; lean_object* v___f_28_; lean_object* v___x_29_; 
v_toApplicative_25_ = lean_ctor_get(v_inst_21_, 0);
lean_inc_ref(v_toApplicative_25_);
v_toBind_26_ = lean_ctor_get(v_inst_21_, 1);
lean_inc(v_toBind_26_);
lean_dec_ref(v_inst_21_);
v_toPure_27_ = lean_ctor_get(v_toApplicative_25_, 1);
lean_inc(v_toPure_27_);
lean_dec_ref(v_toApplicative_25_);
v___f_28_ = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_28_, 0, v_toPure_27_);
lean_closure_set(v___f_28_, 1, v_inst_22_);
lean_closure_set(v___f_28_, 2, v_toBind_26_);
v___x_29_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_28_, v_it_23_, v_acc_24_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toArray_go(lean_object* v_00_u03b1_30_, lean_object* v_00_u03b2_31_, lean_object* v_m_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_it_35_, lean_object* v_acc_36_){
_start:
{
lean_object* v_toApplicative_37_; lean_object* v_toBind_38_; lean_object* v_toPure_39_; lean_object* v___f_40_; lean_object* v___x_41_; 
v_toApplicative_37_ = lean_ctor_get(v_inst_33_, 0);
lean_inc_ref(v_toApplicative_37_);
v_toBind_38_ = lean_ctor_get(v_inst_33_, 1);
lean_inc(v_toBind_38_);
lean_dec_ref(v_inst_33_);
v_toPure_39_ = lean_ctor_get(v_toApplicative_37_, 1);
lean_inc(v_toPure_39_);
lean_dec_ref(v_toApplicative_37_);
v___f_40_ = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_40_, 0, v_toPure_39_);
lean_closure_set(v___f_40_, 1, v_inst_34_);
lean_closure_set(v___f_40_, 2, v_toBind_38_);
v___x_41_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_40_, v_it_35_, v_acc_36_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toArray___redArg(lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_it_46_){
_start:
{
lean_object* v_toApplicative_47_; lean_object* v_toBind_48_; lean_object* v_toPure_49_; lean_object* v___x_50_; lean_object* v___f_51_; lean_object* v___x_52_; 
v_toApplicative_47_ = lean_ctor_get(v_inst_44_, 0);
lean_inc_ref(v_toApplicative_47_);
v_toBind_48_ = lean_ctor_get(v_inst_44_, 1);
lean_inc(v_toBind_48_);
lean_dec_ref(v_inst_44_);
v_toPure_49_ = lean_ctor_get(v_toApplicative_47_, 1);
lean_inc(v_toPure_49_);
lean_dec_ref(v_toApplicative_47_);
v___x_50_ = ((lean_object*)(l_Std_IterM_toArray___redArg___closed__0));
v___f_51_ = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_51_, 0, v_toPure_49_);
lean_closure_set(v___f_51_, 1, v_inst_45_);
lean_closure_set(v___f_51_, 2, v_toBind_48_);
v___x_52_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_51_, v_it_46_, v___x_50_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toArray(lean_object* v_00_u03b1_53_, lean_object* v_00_u03b2_54_, lean_object* v_m_55_, lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_it_58_){
_start:
{
lean_object* v_toApplicative_59_; lean_object* v_toBind_60_; lean_object* v_toPure_61_; lean_object* v___x_62_; lean_object* v___f_63_; lean_object* v___x_64_; 
v_toApplicative_59_ = lean_ctor_get(v_inst_56_, 0);
lean_inc_ref(v_toApplicative_59_);
v_toBind_60_ = lean_ctor_get(v_inst_56_, 1);
lean_inc(v_toBind_60_);
lean_dec_ref(v_inst_56_);
v_toPure_61_ = lean_ctor_get(v_toApplicative_59_, 1);
lean_inc(v_toPure_61_);
lean_dec_ref(v_toApplicative_59_);
v___x_62_ = ((lean_object*)(l_Std_IterM_toArray___redArg___closed__0));
v___f_63_ = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_63_, 0, v_toPure_61_);
lean_closure_set(v___f_63_, 1, v_inst_57_);
lean_closure_set(v___f_63_, 2, v_toBind_60_);
v___x_64_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_63_, v_it_58_, v___x_62_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_toArray___redArg(lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_it_67_){
_start:
{
lean_object* v_toApplicative_68_; lean_object* v_toBind_69_; lean_object* v_toPure_70_; lean_object* v___x_71_; lean_object* v___f_72_; lean_object* v___x_73_; 
v_toApplicative_68_ = lean_ctor_get(v_inst_65_, 0);
lean_inc_ref(v_toApplicative_68_);
v_toBind_69_ = lean_ctor_get(v_inst_65_, 1);
lean_inc(v_toBind_69_);
lean_dec_ref(v_inst_65_);
v_toPure_70_ = lean_ctor_get(v_toApplicative_68_, 1);
lean_inc(v_toPure_70_);
lean_dec_ref(v_toApplicative_68_);
v___x_71_ = ((lean_object*)(l_Std_IterM_toArray___redArg___closed__0));
v___f_72_ = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_72_, 0, v_toPure_70_);
lean_closure_set(v___f_72_, 1, v_inst_66_);
lean_closure_set(v___f_72_, 2, v_toBind_69_);
v___x_73_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_72_, v_it_67_, v___x_71_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_toArray(lean_object* v_00_u03b1_74_, lean_object* v_m_75_, lean_object* v_00_u03b2_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_it_79_){
_start:
{
lean_object* v_toApplicative_80_; lean_object* v_toBind_81_; lean_object* v_toPure_82_; lean_object* v___x_83_; lean_object* v___f_84_; lean_object* v___x_85_; 
v_toApplicative_80_ = lean_ctor_get(v_inst_77_, 0);
lean_inc_ref(v_toApplicative_80_);
v_toBind_81_ = lean_ctor_get(v_inst_77_, 1);
lean_inc(v_toBind_81_);
lean_dec_ref(v_inst_77_);
v_toPure_82_ = lean_ctor_get(v_toApplicative_80_, 1);
lean_inc(v_toPure_82_);
lean_dec_ref(v_toApplicative_80_);
v___x_83_ = ((lean_object*)(l_Std_IterM_toArray___redArg___closed__0));
v___f_84_ = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_84_, 0, v_toPure_82_);
lean_closure_set(v___f_84_, 1, v_inst_78_);
lean_closure_set(v___f_84_, 2, v_toBind_81_);
v___x_85_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_84_, v_it_79_, v___x_83_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toArray___redArg(lean_object* v_inst_86_, lean_object* v_inst_87_, lean_object* v_it_88_){
_start:
{
lean_object* v_toApplicative_89_; lean_object* v_toBind_90_; lean_object* v_toPure_91_; lean_object* v___x_92_; lean_object* v___f_93_; lean_object* v___x_94_; 
v_toApplicative_89_ = lean_ctor_get(v_inst_86_, 0);
lean_inc_ref(v_toApplicative_89_);
v_toBind_90_ = lean_ctor_get(v_inst_86_, 1);
lean_inc(v_toBind_90_);
lean_dec_ref(v_inst_86_);
v_toPure_91_ = lean_ctor_get(v_toApplicative_89_, 1);
lean_inc(v_toPure_91_);
lean_dec_ref(v_toApplicative_89_);
v___x_92_ = ((lean_object*)(l_Std_IterM_toArray___redArg___closed__0));
v___f_93_ = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_93_, 0, v_toPure_91_);
lean_closure_set(v___f_93_, 1, v_inst_87_);
lean_closure_set(v___f_93_, 2, v_toBind_90_);
v___x_94_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_93_, v_it_88_, v___x_92_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toArray(lean_object* v_00_u03b1_95_, lean_object* v_m_96_, lean_object* v_00_u03b2_97_, lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_it_101_){
_start:
{
lean_object* v_toApplicative_102_; lean_object* v_toBind_103_; lean_object* v_toPure_104_; lean_object* v___x_105_; lean_object* v___f_106_; lean_object* v___x_107_; 
v_toApplicative_102_ = lean_ctor_get(v_inst_98_, 0);
lean_inc_ref(v_toApplicative_102_);
v_toBind_103_ = lean_ctor_get(v_inst_98_, 1);
lean_inc(v_toBind_103_);
lean_dec_ref(v_inst_98_);
v_toPure_104_ = lean_ctor_get(v_toApplicative_102_, 1);
lean_inc(v_toPure_104_);
lean_dec_ref(v_toApplicative_102_);
v___x_105_ = ((lean_object*)(l_Std_IterM_toArray___redArg___closed__0));
v___f_106_ = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_106_, 0, v_toPure_104_);
lean_closure_set(v___f_106_, 1, v_inst_99_);
lean_closure_set(v___f_106_, 2, v_toBind_103_);
v___x_107_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_106_, v_it_101_, v___x_105_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toListRev_go___redArg___lam__0(lean_object* v_acc_108_, lean_object* v_recur_109_, lean_object* v_toPure_110_, lean_object* v_____do__lift_111_){
_start:
{
switch(lean_obj_tag(v_____do__lift_111_))
{
case 0:
{
lean_object* v_it_112_; lean_object* v_out_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_121_; 
lean_dec(v_toPure_110_);
v_it_112_ = lean_ctor_get(v_____do__lift_111_, 0);
v_out_113_ = lean_ctor_get(v_____do__lift_111_, 1);
v_isSharedCheck_121_ = !lean_is_exclusive(v_____do__lift_111_);
if (v_isSharedCheck_121_ == 0)
{
v___x_115_ = v_____do__lift_111_;
v_isShared_116_ = v_isSharedCheck_121_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_out_113_);
lean_inc(v_it_112_);
lean_dec(v_____do__lift_111_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_121_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_118_; 
if (v_isShared_116_ == 0)
{
lean_ctor_set_tag(v___x_115_, 1);
lean_ctor_set(v___x_115_, 1, v_acc_108_);
lean_ctor_set(v___x_115_, 0, v_out_113_);
v___x_118_ = v___x_115_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_out_113_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v_acc_108_);
v___x_118_ = v_reuseFailAlloc_120_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
lean_object* v___x_119_; 
v___x_119_ = lean_apply_3(v_recur_109_, v_it_112_, v___x_118_, lean_box(0));
return v___x_119_;
}
}
}
case 1:
{
lean_object* v_it_122_; lean_object* v___x_123_; 
lean_dec(v_toPure_110_);
v_it_122_ = lean_ctor_get(v_____do__lift_111_, 0);
lean_inc(v_it_122_);
lean_dec_ref(v_____do__lift_111_);
v___x_123_ = lean_apply_3(v_recur_109_, v_it_122_, v_acc_108_, lean_box(0));
return v___x_123_;
}
default: 
{
lean_object* v___x_124_; 
lean_dec(v_recur_109_);
v___x_124_ = lean_apply_2(v_toPure_110_, lean_box(0), v_acc_108_);
return v___x_124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toListRev_go___redArg___lam__1(lean_object* v_toPure_125_, lean_object* v_inst_126_, lean_object* v_toBind_127_, lean_object* v_it_128_, lean_object* v_acc_129_, lean_object* v_recur_130_){
_start:
{
lean_object* v___f_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___f_131_ = lean_alloc_closure((void*)(l_Std_IterM_toListRev_go___redArg___lam__0), 4, 3);
lean_closure_set(v___f_131_, 0, v_acc_129_);
lean_closure_set(v___f_131_, 1, v_recur_130_);
lean_closure_set(v___f_131_, 2, v_toPure_125_);
v___x_132_ = lean_apply_1(v_inst_126_, v_it_128_);
v___x_133_ = lean_apply_4(v_toBind_127_, lean_box(0), lean_box(0), v___x_132_, v___f_131_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toListRev_go___redArg(lean_object* v_inst_134_, lean_object* v_inst_135_, lean_object* v_it_136_, lean_object* v_acc_137_){
_start:
{
lean_object* v_toApplicative_138_; lean_object* v_toBind_139_; lean_object* v_toPure_140_; lean_object* v___f_141_; lean_object* v___x_142_; 
v_toApplicative_138_ = lean_ctor_get(v_inst_134_, 0);
lean_inc_ref(v_toApplicative_138_);
v_toBind_139_ = lean_ctor_get(v_inst_134_, 1);
lean_inc(v_toBind_139_);
lean_dec_ref(v_inst_134_);
v_toPure_140_ = lean_ctor_get(v_toApplicative_138_, 1);
lean_inc(v_toPure_140_);
lean_dec_ref(v_toApplicative_138_);
v___f_141_ = lean_alloc_closure((void*)(l_Std_IterM_toListRev_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_141_, 0, v_toPure_140_);
lean_closure_set(v___f_141_, 1, v_inst_135_);
lean_closure_set(v___f_141_, 2, v_toBind_139_);
v___x_142_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_141_, v_it_136_, v_acc_137_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toListRev_go(lean_object* v_00_u03b1_143_, lean_object* v_m_144_, lean_object* v_inst_145_, lean_object* v_00_u03b2_146_, lean_object* v_inst_147_, lean_object* v_it_148_, lean_object* v_acc_149_){
_start:
{
lean_object* v_toApplicative_150_; lean_object* v_toBind_151_; lean_object* v_toPure_152_; lean_object* v___f_153_; lean_object* v___x_154_; 
v_toApplicative_150_ = lean_ctor_get(v_inst_145_, 0);
lean_inc_ref(v_toApplicative_150_);
v_toBind_151_ = lean_ctor_get(v_inst_145_, 1);
lean_inc(v_toBind_151_);
lean_dec_ref(v_inst_145_);
v_toPure_152_ = lean_ctor_get(v_toApplicative_150_, 1);
lean_inc(v_toPure_152_);
lean_dec_ref(v_toApplicative_150_);
v___f_153_ = lean_alloc_closure((void*)(l_Std_IterM_toListRev_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_153_, 0, v_toPure_152_);
lean_closure_set(v___f_153_, 1, v_inst_147_);
lean_closure_set(v___f_153_, 2, v_toBind_151_);
v___x_154_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_153_, v_it_148_, v_acc_149_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toListRev___redArg(lean_object* v_inst_155_, lean_object* v_inst_156_, lean_object* v_it_157_){
_start:
{
lean_object* v_toApplicative_158_; lean_object* v_toBind_159_; lean_object* v_toPure_160_; lean_object* v___x_161_; lean_object* v___f_162_; lean_object* v___x_163_; 
v_toApplicative_158_ = lean_ctor_get(v_inst_155_, 0);
lean_inc_ref(v_toApplicative_158_);
v_toBind_159_ = lean_ctor_get(v_inst_155_, 1);
lean_inc(v_toBind_159_);
lean_dec_ref(v_inst_155_);
v_toPure_160_ = lean_ctor_get(v_toApplicative_158_, 1);
lean_inc(v_toPure_160_);
lean_dec_ref(v_toApplicative_158_);
v___x_161_ = lean_box(0);
v___f_162_ = lean_alloc_closure((void*)(l_Std_IterM_toListRev_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_162_, 0, v_toPure_160_);
lean_closure_set(v___f_162_, 1, v_inst_156_);
lean_closure_set(v___f_162_, 2, v_toBind_159_);
v___x_163_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_162_, v_it_157_, v___x_161_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toListRev(lean_object* v_00_u03b1_164_, lean_object* v_m_165_, lean_object* v_inst_166_, lean_object* v_00_u03b2_167_, lean_object* v_inst_168_, lean_object* v_it_169_){
_start:
{
lean_object* v_toApplicative_170_; lean_object* v_toBind_171_; lean_object* v_toPure_172_; lean_object* v___x_173_; lean_object* v___f_174_; lean_object* v___x_175_; 
v_toApplicative_170_ = lean_ctor_get(v_inst_166_, 0);
lean_inc_ref(v_toApplicative_170_);
v_toBind_171_ = lean_ctor_get(v_inst_166_, 1);
lean_inc(v_toBind_171_);
lean_dec_ref(v_inst_166_);
v_toPure_172_ = lean_ctor_get(v_toApplicative_170_, 1);
lean_inc(v_toPure_172_);
lean_dec_ref(v_toApplicative_170_);
v___x_173_ = lean_box(0);
v___f_174_ = lean_alloc_closure((void*)(l_Std_IterM_toListRev_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_174_, 0, v_toPure_172_);
lean_closure_set(v___f_174_, 1, v_inst_168_);
lean_closure_set(v___f_174_, 2, v_toBind_171_);
v___x_175_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_174_, v_it_169_, v___x_173_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_toListRev___redArg(lean_object* v_inst_176_, lean_object* v_inst_177_, lean_object* v_it_178_){
_start:
{
lean_object* v_toApplicative_179_; lean_object* v_toBind_180_; lean_object* v_toPure_181_; lean_object* v___x_182_; lean_object* v___f_183_; lean_object* v___x_184_; 
v_toApplicative_179_ = lean_ctor_get(v_inst_176_, 0);
lean_inc_ref(v_toApplicative_179_);
v_toBind_180_ = lean_ctor_get(v_inst_176_, 1);
lean_inc(v_toBind_180_);
lean_dec_ref(v_inst_176_);
v_toPure_181_ = lean_ctor_get(v_toApplicative_179_, 1);
lean_inc(v_toPure_181_);
lean_dec_ref(v_toApplicative_179_);
v___x_182_ = lean_box(0);
v___f_183_ = lean_alloc_closure((void*)(l_Std_IterM_toListRev_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_183_, 0, v_toPure_181_);
lean_closure_set(v___f_183_, 1, v_inst_177_);
lean_closure_set(v___f_183_, 2, v_toBind_180_);
v___x_184_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_183_, v_it_178_, v___x_182_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_toListRev(lean_object* v_00_u03b1_185_, lean_object* v_m_186_, lean_object* v_inst_187_, lean_object* v_00_u03b2_188_, lean_object* v_inst_189_, lean_object* v_it_190_){
_start:
{
lean_object* v_toApplicative_191_; lean_object* v_toBind_192_; lean_object* v_toPure_193_; lean_object* v___x_194_; lean_object* v___f_195_; lean_object* v___x_196_; 
v_toApplicative_191_ = lean_ctor_get(v_inst_187_, 0);
lean_inc_ref(v_toApplicative_191_);
v_toBind_192_ = lean_ctor_get(v_inst_187_, 1);
lean_inc(v_toBind_192_);
lean_dec_ref(v_inst_187_);
v_toPure_193_ = lean_ctor_get(v_toApplicative_191_, 1);
lean_inc(v_toPure_193_);
lean_dec_ref(v_toApplicative_191_);
v___x_194_ = lean_box(0);
v___f_195_ = lean_alloc_closure((void*)(l_Std_IterM_toListRev_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_195_, 0, v_toPure_193_);
lean_closure_set(v___f_195_, 1, v_inst_189_);
lean_closure_set(v___f_195_, 2, v_toBind_192_);
v___x_196_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_195_, v_it_190_, v___x_194_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toListRev___redArg(lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_it_199_){
_start:
{
lean_object* v_toApplicative_200_; lean_object* v_toBind_201_; lean_object* v_toPure_202_; lean_object* v___x_203_; lean_object* v___f_204_; lean_object* v___x_205_; 
v_toApplicative_200_ = lean_ctor_get(v_inst_197_, 0);
lean_inc_ref(v_toApplicative_200_);
v_toBind_201_ = lean_ctor_get(v_inst_197_, 1);
lean_inc(v_toBind_201_);
lean_dec_ref(v_inst_197_);
v_toPure_202_ = lean_ctor_get(v_toApplicative_200_, 1);
lean_inc(v_toPure_202_);
lean_dec_ref(v_toApplicative_200_);
v___x_203_ = lean_box(0);
v___f_204_ = lean_alloc_closure((void*)(l_Std_IterM_toListRev_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_204_, 0, v_toPure_202_);
lean_closure_set(v___f_204_, 1, v_inst_198_);
lean_closure_set(v___f_204_, 2, v_toBind_201_);
v___x_205_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_204_, v_it_199_, v___x_203_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toListRev(lean_object* v_00_u03b1_206_, lean_object* v_m_207_, lean_object* v_00_u03b2_208_, lean_object* v_inst_209_, lean_object* v_inst_210_, lean_object* v_inst_211_, lean_object* v_it_212_){
_start:
{
lean_object* v_toApplicative_213_; lean_object* v_toBind_214_; lean_object* v_toPure_215_; lean_object* v___x_216_; lean_object* v___f_217_; lean_object* v___x_218_; 
v_toApplicative_213_ = lean_ctor_get(v_inst_209_, 0);
lean_inc_ref(v_toApplicative_213_);
v_toBind_214_ = lean_ctor_get(v_inst_209_, 1);
lean_inc(v_toBind_214_);
lean_dec_ref(v_inst_209_);
v_toPure_215_ = lean_ctor_get(v_toApplicative_213_, 1);
lean_inc(v_toPure_215_);
lean_dec_ref(v_toApplicative_213_);
v___x_216_ = lean_box(0);
v___f_217_ = lean_alloc_closure((void*)(l_Std_IterM_toListRev_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_217_, 0, v_toPure_215_);
lean_closure_set(v___f_217_, 1, v_inst_210_);
lean_closure_set(v___f_217_, 2, v_toBind_214_);
v___x_218_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_217_, v_it_212_, v___x_216_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toList___redArg___lam__0(lean_object* v_self_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = lean_array_to_list(v_self_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toList___redArg(lean_object* v_inst_222_, lean_object* v_inst_223_, lean_object* v_it_224_){
_start:
{
lean_object* v_toApplicative_225_; lean_object* v_toFunctor_226_; lean_object* v_toBind_227_; lean_object* v_toPure_228_; lean_object* v_map_229_; lean_object* v___f_230_; lean_object* v___f_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v_toApplicative_225_ = lean_ctor_get(v_inst_222_, 0);
lean_inc_ref(v_toApplicative_225_);
v_toFunctor_226_ = lean_ctor_get(v_toApplicative_225_, 0);
lean_inc_ref(v_toFunctor_226_);
v_toBind_227_ = lean_ctor_get(v_inst_222_, 1);
lean_inc(v_toBind_227_);
lean_dec_ref(v_inst_222_);
v_toPure_228_ = lean_ctor_get(v_toApplicative_225_, 1);
lean_inc(v_toPure_228_);
lean_dec_ref(v_toApplicative_225_);
v_map_229_ = lean_ctor_get(v_toFunctor_226_, 0);
lean_inc(v_map_229_);
lean_dec_ref(v_toFunctor_226_);
v___f_230_ = ((lean_object*)(l_Std_IterM_toList___redArg___closed__0));
v___f_231_ = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_231_, 0, v_toPure_228_);
lean_closure_set(v___f_231_, 1, v_inst_223_);
lean_closure_set(v___f_231_, 2, v_toBind_227_);
v___x_232_ = ((lean_object*)(l_Std_IterM_toArray___redArg___closed__0));
v___x_233_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_231_, v_it_224_, v___x_232_);
v___x_234_ = lean_apply_4(v_map_229_, lean_box(0), lean_box(0), v___f_230_, v___x_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toList(lean_object* v_00_u03b1_235_, lean_object* v_m_236_, lean_object* v_inst_237_, lean_object* v_00_u03b2_238_, lean_object* v_inst_239_, lean_object* v_it_240_){
_start:
{
lean_object* v_toApplicative_241_; lean_object* v_toFunctor_242_; lean_object* v_toBind_243_; lean_object* v_toPure_244_; lean_object* v_map_245_; lean_object* v___f_246_; lean_object* v___f_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v_toApplicative_241_ = lean_ctor_get(v_inst_237_, 0);
lean_inc_ref(v_toApplicative_241_);
v_toFunctor_242_ = lean_ctor_get(v_toApplicative_241_, 0);
lean_inc_ref(v_toFunctor_242_);
v_toBind_243_ = lean_ctor_get(v_inst_237_, 1);
lean_inc(v_toBind_243_);
lean_dec_ref(v_inst_237_);
v_toPure_244_ = lean_ctor_get(v_toApplicative_241_, 1);
lean_inc(v_toPure_244_);
lean_dec_ref(v_toApplicative_241_);
v_map_245_ = lean_ctor_get(v_toFunctor_242_, 0);
lean_inc(v_map_245_);
lean_dec_ref(v_toFunctor_242_);
v___f_246_ = ((lean_object*)(l_Std_IterM_toList___redArg___closed__0));
v___f_247_ = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_247_, 0, v_toPure_244_);
lean_closure_set(v___f_247_, 1, v_inst_239_);
lean_closure_set(v___f_247_, 2, v_toBind_243_);
v___x_248_ = ((lean_object*)(l_Std_IterM_toArray___redArg___closed__0));
v___x_249_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_247_, v_it_240_, v___x_248_);
v___x_250_ = lean_apply_4(v_map_245_, lean_box(0), lean_box(0), v___f_246_, v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_toList___redArg(lean_object* v_inst_251_, lean_object* v_inst_252_, lean_object* v_it_253_){
_start:
{
lean_object* v_toApplicative_254_; lean_object* v_toFunctor_255_; lean_object* v_toBind_256_; lean_object* v_toPure_257_; lean_object* v_map_258_; lean_object* v___f_259_; lean_object* v___f_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v_toApplicative_254_ = lean_ctor_get(v_inst_251_, 0);
lean_inc_ref(v_toApplicative_254_);
v_toFunctor_255_ = lean_ctor_get(v_toApplicative_254_, 0);
lean_inc_ref(v_toFunctor_255_);
v_toBind_256_ = lean_ctor_get(v_inst_251_, 1);
lean_inc(v_toBind_256_);
lean_dec_ref(v_inst_251_);
v_toPure_257_ = lean_ctor_get(v_toApplicative_254_, 1);
lean_inc(v_toPure_257_);
lean_dec_ref(v_toApplicative_254_);
v_map_258_ = lean_ctor_get(v_toFunctor_255_, 0);
lean_inc(v_map_258_);
lean_dec_ref(v_toFunctor_255_);
v___f_259_ = ((lean_object*)(l_Std_IterM_toList___redArg___closed__0));
v___f_260_ = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_260_, 0, v_toPure_257_);
lean_closure_set(v___f_260_, 1, v_inst_252_);
lean_closure_set(v___f_260_, 2, v_toBind_256_);
v___x_261_ = ((lean_object*)(l_Std_IterM_toArray___redArg___closed__0));
v___x_262_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_260_, v_it_253_, v___x_261_);
v___x_263_ = lean_apply_4(v_map_258_, lean_box(0), lean_box(0), v___f_259_, v___x_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_toList(lean_object* v_00_u03b1_264_, lean_object* v_m_265_, lean_object* v_inst_266_, lean_object* v_00_u03b2_267_, lean_object* v_inst_268_, lean_object* v_it_269_){
_start:
{
lean_object* v_toApplicative_270_; lean_object* v_toFunctor_271_; lean_object* v_toBind_272_; lean_object* v_toPure_273_; lean_object* v_map_274_; lean_object* v___f_275_; lean_object* v___f_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v_toApplicative_270_ = lean_ctor_get(v_inst_266_, 0);
lean_inc_ref(v_toApplicative_270_);
v_toFunctor_271_ = lean_ctor_get(v_toApplicative_270_, 0);
lean_inc_ref(v_toFunctor_271_);
v_toBind_272_ = lean_ctor_get(v_inst_266_, 1);
lean_inc(v_toBind_272_);
lean_dec_ref(v_inst_266_);
v_toPure_273_ = lean_ctor_get(v_toApplicative_270_, 1);
lean_inc(v_toPure_273_);
lean_dec_ref(v_toApplicative_270_);
v_map_274_ = lean_ctor_get(v_toFunctor_271_, 0);
lean_inc(v_map_274_);
lean_dec_ref(v_toFunctor_271_);
v___f_275_ = ((lean_object*)(l_Std_IterM_toList___redArg___closed__0));
v___f_276_ = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_276_, 0, v_toPure_273_);
lean_closure_set(v___f_276_, 1, v_inst_268_);
lean_closure_set(v___f_276_, 2, v_toBind_272_);
v___x_277_ = ((lean_object*)(l_Std_IterM_toArray___redArg___closed__0));
v___x_278_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_276_, v_it_269_, v___x_277_);
v___x_279_ = lean_apply_4(v_map_274_, lean_box(0), lean_box(0), v___f_275_, v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toList___redArg(lean_object* v_inst_280_, lean_object* v_inst_281_, lean_object* v_it_282_){
_start:
{
lean_object* v_toApplicative_283_; lean_object* v_toFunctor_284_; lean_object* v_toBind_285_; lean_object* v_toPure_286_; lean_object* v_map_287_; lean_object* v___f_288_; lean_object* v___f_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v_toApplicative_283_ = lean_ctor_get(v_inst_280_, 0);
lean_inc_ref(v_toApplicative_283_);
v_toFunctor_284_ = lean_ctor_get(v_toApplicative_283_, 0);
lean_inc_ref(v_toFunctor_284_);
v_toBind_285_ = lean_ctor_get(v_inst_280_, 1);
lean_inc(v_toBind_285_);
lean_dec_ref(v_inst_280_);
v_toPure_286_ = lean_ctor_get(v_toApplicative_283_, 1);
lean_inc(v_toPure_286_);
lean_dec_ref(v_toApplicative_283_);
v_map_287_ = lean_ctor_get(v_toFunctor_284_, 0);
lean_inc(v_map_287_);
lean_dec_ref(v_toFunctor_284_);
v___f_288_ = ((lean_object*)(l_Std_IterM_toList___redArg___closed__0));
v___f_289_ = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_289_, 0, v_toPure_286_);
lean_closure_set(v___f_289_, 1, v_inst_281_);
lean_closure_set(v___f_289_, 2, v_toBind_285_);
v___x_290_ = ((lean_object*)(l_Std_IterM_toArray___redArg___closed__0));
v___x_291_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_289_, v_it_282_, v___x_290_);
v___x_292_ = lean_apply_4(v_map_287_, lean_box(0), lean_box(0), v___f_288_, v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toList(lean_object* v_00_u03b1_293_, lean_object* v_m_294_, lean_object* v_00_u03b2_295_, lean_object* v_inst_296_, lean_object* v_inst_297_, lean_object* v_inst_298_, lean_object* v_it_299_){
_start:
{
lean_object* v_toApplicative_300_; lean_object* v_toFunctor_301_; lean_object* v_toBind_302_; lean_object* v_toPure_303_; lean_object* v_map_304_; lean_object* v___f_305_; lean_object* v___f_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v_toApplicative_300_ = lean_ctor_get(v_inst_296_, 0);
lean_inc_ref(v_toApplicative_300_);
v_toFunctor_301_ = lean_ctor_get(v_toApplicative_300_, 0);
lean_inc_ref(v_toFunctor_301_);
v_toBind_302_ = lean_ctor_get(v_inst_296_, 1);
lean_inc(v_toBind_302_);
lean_dec_ref(v_inst_296_);
v_toPure_303_ = lean_ctor_get(v_toApplicative_300_, 1);
lean_inc(v_toPure_303_);
lean_dec_ref(v_toApplicative_300_);
v_map_304_ = lean_ctor_get(v_toFunctor_301_, 0);
lean_inc(v_map_304_);
lean_dec_ref(v_toFunctor_301_);
v___f_305_ = ((lean_object*)(l_Std_IterM_toList___redArg___closed__0));
v___f_306_ = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_306_, 0, v_toPure_303_);
lean_closure_set(v___f_306_, 1, v_inst_297_);
lean_closure_set(v___f_306_, 2, v_toBind_302_);
v___x_307_ = ((lean_object*)(l_Std_IterM_toArray___redArg___closed__0));
v___x_308_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_306_, v_it_299_, v___x_307_);
v___x_309_ = lean_apply_4(v_map_304_, lean_box(0), lean_box(0), v___f_305_, v___x_308_);
return v___x_309_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Partial(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Total(uint8_t builtin);
lean_object* runtime_initialize_Init_WFExtrinsicFix(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Partial(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Total(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFExtrinsicFix(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Partial(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Total(uint8_t builtin);
lean_object* initialize_Init_WFExtrinsicFix(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Consumers_Monadic_Partial(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Total(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFExtrinsicFix(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
}
#ifdef __cplusplus
}
#endif

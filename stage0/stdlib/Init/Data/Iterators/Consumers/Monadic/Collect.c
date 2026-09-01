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
LEAN_EXPORT lean_object* l_Std_IterM_Total_toArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_toArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toListRev_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toListRev_go___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toListRev_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toListRev_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toListRev___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toListRev(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_toListRev___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_toListRev(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toList___redArg___lam__0(lean_object*);
static const lean_closure_object l_Std_IterM_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_IterM_toList___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_IterM_toList___redArg___closed__0 = (const lean_object*)&l_Std_IterM_toList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_IterM_toList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v_____do__lift_4_, 2);
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
lean_dec_ref_known(v_____do__lift_4_, 1);
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
LEAN_EXPORT lean_object* l_Std_IterM_Total_toArray___redArg(lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_it_67_){
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
LEAN_EXPORT lean_object* l_Std_IterM_Total_toArray(lean_object* v_00_u03b1_74_, lean_object* v_m_75_, lean_object* v_00_u03b2_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_it_80_){
_start:
{
lean_object* v_toApplicative_81_; lean_object* v_toBind_82_; lean_object* v_toPure_83_; lean_object* v___x_84_; lean_object* v___f_85_; lean_object* v___x_86_; 
v_toApplicative_81_ = lean_ctor_get(v_inst_77_, 0);
lean_inc_ref(v_toApplicative_81_);
v_toBind_82_ = lean_ctor_get(v_inst_77_, 1);
lean_inc(v_toBind_82_);
lean_dec_ref(v_inst_77_);
v_toPure_83_ = lean_ctor_get(v_toApplicative_81_, 1);
lean_inc(v_toPure_83_);
lean_dec_ref(v_toApplicative_81_);
v___x_84_ = ((lean_object*)(l_Std_IterM_toArray___redArg___closed__0));
v___f_85_ = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_85_, 0, v_toPure_83_);
lean_closure_set(v___f_85_, 1, v_inst_78_);
lean_closure_set(v___f_85_, 2, v_toBind_82_);
v___x_86_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_85_, v_it_80_, v___x_84_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toListRev_go___redArg___lam__0(lean_object* v_acc_87_, lean_object* v_recur_88_, lean_object* v_toPure_89_, lean_object* v_____do__lift_90_){
_start:
{
switch(lean_obj_tag(v_____do__lift_90_))
{
case 0:
{
lean_object* v_it_91_; lean_object* v_out_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_100_; 
lean_dec(v_toPure_89_);
v_it_91_ = lean_ctor_get(v_____do__lift_90_, 0);
v_out_92_ = lean_ctor_get(v_____do__lift_90_, 1);
v_isSharedCheck_100_ = !lean_is_exclusive(v_____do__lift_90_);
if (v_isSharedCheck_100_ == 0)
{
v___x_94_ = v_____do__lift_90_;
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_out_92_);
lean_inc(v_it_91_);
lean_dec(v_____do__lift_90_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
lean_ctor_set_tag(v___x_94_, 1);
lean_ctor_set(v___x_94_, 1, v_acc_87_);
lean_ctor_set(v___x_94_, 0, v_out_92_);
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_out_92_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v_acc_87_);
v___x_97_ = v_reuseFailAlloc_99_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
lean_object* v___x_98_; 
v___x_98_ = lean_apply_3(v_recur_88_, v_it_91_, v___x_97_, lean_box(0));
return v___x_98_;
}
}
}
case 1:
{
lean_object* v_it_101_; lean_object* v___x_102_; 
lean_dec(v_toPure_89_);
v_it_101_ = lean_ctor_get(v_____do__lift_90_, 0);
lean_inc(v_it_101_);
lean_dec_ref_known(v_____do__lift_90_, 1);
v___x_102_ = lean_apply_3(v_recur_88_, v_it_101_, v_acc_87_, lean_box(0));
return v___x_102_;
}
default: 
{
lean_object* v___x_103_; 
lean_dec(v_recur_88_);
v___x_103_ = lean_apply_2(v_toPure_89_, lean_box(0), v_acc_87_);
return v___x_103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toListRev_go___redArg___lam__1(lean_object* v_toPure_104_, lean_object* v_inst_105_, lean_object* v_toBind_106_, lean_object* v_it_107_, lean_object* v_acc_108_, lean_object* v_recur_109_){
_start:
{
lean_object* v___f_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___f_110_ = lean_alloc_closure((void*)(l_Std_IterM_toListRev_go___redArg___lam__0), 4, 3);
lean_closure_set(v___f_110_, 0, v_acc_108_);
lean_closure_set(v___f_110_, 1, v_recur_109_);
lean_closure_set(v___f_110_, 2, v_toPure_104_);
v___x_111_ = lean_apply_1(v_inst_105_, v_it_107_);
v___x_112_ = lean_apply_4(v_toBind_106_, lean_box(0), lean_box(0), v___x_111_, v___f_110_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toListRev_go___redArg(lean_object* v_inst_113_, lean_object* v_inst_114_, lean_object* v_it_115_, lean_object* v_acc_116_){
_start:
{
lean_object* v_toApplicative_117_; lean_object* v_toBind_118_; lean_object* v_toPure_119_; lean_object* v___f_120_; lean_object* v___x_121_; 
v_toApplicative_117_ = lean_ctor_get(v_inst_113_, 0);
lean_inc_ref(v_toApplicative_117_);
v_toBind_118_ = lean_ctor_get(v_inst_113_, 1);
lean_inc(v_toBind_118_);
lean_dec_ref(v_inst_113_);
v_toPure_119_ = lean_ctor_get(v_toApplicative_117_, 1);
lean_inc(v_toPure_119_);
lean_dec_ref(v_toApplicative_117_);
v___f_120_ = lean_alloc_closure((void*)(l_Std_IterM_toListRev_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_120_, 0, v_toPure_119_);
lean_closure_set(v___f_120_, 1, v_inst_114_);
lean_closure_set(v___f_120_, 2, v_toBind_118_);
v___x_121_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_120_, v_it_115_, v_acc_116_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toListRev_go(lean_object* v_00_u03b1_122_, lean_object* v_m_123_, lean_object* v_inst_124_, lean_object* v_00_u03b2_125_, lean_object* v_inst_126_, lean_object* v_it_127_, lean_object* v_acc_128_){
_start:
{
lean_object* v_toApplicative_129_; lean_object* v_toBind_130_; lean_object* v_toPure_131_; lean_object* v___f_132_; lean_object* v___x_133_; 
v_toApplicative_129_ = lean_ctor_get(v_inst_124_, 0);
lean_inc_ref(v_toApplicative_129_);
v_toBind_130_ = lean_ctor_get(v_inst_124_, 1);
lean_inc(v_toBind_130_);
lean_dec_ref(v_inst_124_);
v_toPure_131_ = lean_ctor_get(v_toApplicative_129_, 1);
lean_inc(v_toPure_131_);
lean_dec_ref(v_toApplicative_129_);
v___f_132_ = lean_alloc_closure((void*)(l_Std_IterM_toListRev_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_132_, 0, v_toPure_131_);
lean_closure_set(v___f_132_, 1, v_inst_126_);
lean_closure_set(v___f_132_, 2, v_toBind_130_);
v___x_133_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_132_, v_it_127_, v_acc_128_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toListRev___redArg(lean_object* v_inst_134_, lean_object* v_inst_135_, lean_object* v_it_136_){
_start:
{
lean_object* v_toApplicative_137_; lean_object* v_toBind_138_; lean_object* v_toPure_139_; lean_object* v___x_140_; lean_object* v___f_141_; lean_object* v___x_142_; 
v_toApplicative_137_ = lean_ctor_get(v_inst_134_, 0);
lean_inc_ref(v_toApplicative_137_);
v_toBind_138_ = lean_ctor_get(v_inst_134_, 1);
lean_inc(v_toBind_138_);
lean_dec_ref(v_inst_134_);
v_toPure_139_ = lean_ctor_get(v_toApplicative_137_, 1);
lean_inc(v_toPure_139_);
lean_dec_ref(v_toApplicative_137_);
v___x_140_ = lean_box(0);
v___f_141_ = lean_alloc_closure((void*)(l_Std_IterM_toListRev_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_141_, 0, v_toPure_139_);
lean_closure_set(v___f_141_, 1, v_inst_135_);
lean_closure_set(v___f_141_, 2, v_toBind_138_);
v___x_142_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_141_, v_it_136_, v___x_140_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toListRev(lean_object* v_00_u03b1_143_, lean_object* v_m_144_, lean_object* v_inst_145_, lean_object* v_00_u03b2_146_, lean_object* v_inst_147_, lean_object* v_it_148_){
_start:
{
lean_object* v_toApplicative_149_; lean_object* v_toBind_150_; lean_object* v_toPure_151_; lean_object* v___x_152_; lean_object* v___f_153_; lean_object* v___x_154_; 
v_toApplicative_149_ = lean_ctor_get(v_inst_145_, 0);
lean_inc_ref(v_toApplicative_149_);
v_toBind_150_ = lean_ctor_get(v_inst_145_, 1);
lean_inc(v_toBind_150_);
lean_dec_ref(v_inst_145_);
v_toPure_151_ = lean_ctor_get(v_toApplicative_149_, 1);
lean_inc(v_toPure_151_);
lean_dec_ref(v_toApplicative_149_);
v___x_152_ = lean_box(0);
v___f_153_ = lean_alloc_closure((void*)(l_Std_IterM_toListRev_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_153_, 0, v_toPure_151_);
lean_closure_set(v___f_153_, 1, v_inst_147_);
lean_closure_set(v___f_153_, 2, v_toBind_150_);
v___x_154_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_153_, v_it_148_, v___x_152_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toListRev___redArg(lean_object* v_inst_155_, lean_object* v_inst_156_, lean_object* v_it_157_){
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
LEAN_EXPORT lean_object* l_Std_IterM_Total_toListRev(lean_object* v_00_u03b1_164_, lean_object* v_m_165_, lean_object* v_00_u03b2_166_, lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_inst_169_, lean_object* v_it_170_){
_start:
{
lean_object* v_toApplicative_171_; lean_object* v_toBind_172_; lean_object* v_toPure_173_; lean_object* v___x_174_; lean_object* v___f_175_; lean_object* v___x_176_; 
v_toApplicative_171_ = lean_ctor_get(v_inst_167_, 0);
lean_inc_ref(v_toApplicative_171_);
v_toBind_172_ = lean_ctor_get(v_inst_167_, 1);
lean_inc(v_toBind_172_);
lean_dec_ref(v_inst_167_);
v_toPure_173_ = lean_ctor_get(v_toApplicative_171_, 1);
lean_inc(v_toPure_173_);
lean_dec_ref(v_toApplicative_171_);
v___x_174_ = lean_box(0);
v___f_175_ = lean_alloc_closure((void*)(l_Std_IterM_toListRev_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_175_, 0, v_toPure_173_);
lean_closure_set(v___f_175_, 1, v_inst_168_);
lean_closure_set(v___f_175_, 2, v_toBind_172_);
v___x_176_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_175_, v_it_170_, v___x_174_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toList___redArg___lam__0(lean_object* v_self_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = lean_array_to_list(v_self_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toList___redArg(lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_it_182_){
_start:
{
lean_object* v_toApplicative_183_; lean_object* v_toFunctor_184_; lean_object* v_toBind_185_; lean_object* v_toPure_186_; lean_object* v_map_187_; lean_object* v___f_188_; lean_object* v___f_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v_toApplicative_183_ = lean_ctor_get(v_inst_180_, 0);
lean_inc_ref(v_toApplicative_183_);
v_toFunctor_184_ = lean_ctor_get(v_toApplicative_183_, 0);
lean_inc_ref(v_toFunctor_184_);
v_toBind_185_ = lean_ctor_get(v_inst_180_, 1);
lean_inc(v_toBind_185_);
lean_dec_ref(v_inst_180_);
v_toPure_186_ = lean_ctor_get(v_toApplicative_183_, 1);
lean_inc(v_toPure_186_);
lean_dec_ref(v_toApplicative_183_);
v_map_187_ = lean_ctor_get(v_toFunctor_184_, 0);
lean_inc(v_map_187_);
lean_dec_ref(v_toFunctor_184_);
v___f_188_ = ((lean_object*)(l_Std_IterM_toList___redArg___closed__0));
v___f_189_ = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_189_, 0, v_toPure_186_);
lean_closure_set(v___f_189_, 1, v_inst_181_);
lean_closure_set(v___f_189_, 2, v_toBind_185_);
v___x_190_ = ((lean_object*)(l_Std_IterM_toArray___redArg___closed__0));
v___x_191_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_189_, v_it_182_, v___x_190_);
v___x_192_ = lean_apply_4(v_map_187_, lean_box(0), lean_box(0), v___f_188_, v___x_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toList(lean_object* v_00_u03b1_193_, lean_object* v_m_194_, lean_object* v_inst_195_, lean_object* v_00_u03b2_196_, lean_object* v_inst_197_, lean_object* v_it_198_){
_start:
{
lean_object* v_toApplicative_199_; lean_object* v_toFunctor_200_; lean_object* v_toBind_201_; lean_object* v_toPure_202_; lean_object* v_map_203_; lean_object* v___f_204_; lean_object* v___f_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v_toApplicative_199_ = lean_ctor_get(v_inst_195_, 0);
lean_inc_ref(v_toApplicative_199_);
v_toFunctor_200_ = lean_ctor_get(v_toApplicative_199_, 0);
lean_inc_ref(v_toFunctor_200_);
v_toBind_201_ = lean_ctor_get(v_inst_195_, 1);
lean_inc(v_toBind_201_);
lean_dec_ref(v_inst_195_);
v_toPure_202_ = lean_ctor_get(v_toApplicative_199_, 1);
lean_inc(v_toPure_202_);
lean_dec_ref(v_toApplicative_199_);
v_map_203_ = lean_ctor_get(v_toFunctor_200_, 0);
lean_inc(v_map_203_);
lean_dec_ref(v_toFunctor_200_);
v___f_204_ = ((lean_object*)(l_Std_IterM_toList___redArg___closed__0));
v___f_205_ = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_205_, 0, v_toPure_202_);
lean_closure_set(v___f_205_, 1, v_inst_197_);
lean_closure_set(v___f_205_, 2, v_toBind_201_);
v___x_206_ = ((lean_object*)(l_Std_IterM_toArray___redArg___closed__0));
v___x_207_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_205_, v_it_198_, v___x_206_);
v___x_208_ = lean_apply_4(v_map_203_, lean_box(0), lean_box(0), v___f_204_, v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toList___redArg(lean_object* v_inst_209_, lean_object* v_inst_210_, lean_object* v_it_211_){
_start:
{
lean_object* v_toApplicative_212_; lean_object* v_toFunctor_213_; lean_object* v_toBind_214_; lean_object* v_toPure_215_; lean_object* v_map_216_; lean_object* v___f_217_; lean_object* v___f_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_toApplicative_212_ = lean_ctor_get(v_inst_209_, 0);
lean_inc_ref(v_toApplicative_212_);
v_toFunctor_213_ = lean_ctor_get(v_toApplicative_212_, 0);
lean_inc_ref(v_toFunctor_213_);
v_toBind_214_ = lean_ctor_get(v_inst_209_, 1);
lean_inc(v_toBind_214_);
lean_dec_ref(v_inst_209_);
v_toPure_215_ = lean_ctor_get(v_toApplicative_212_, 1);
lean_inc(v_toPure_215_);
lean_dec_ref(v_toApplicative_212_);
v_map_216_ = lean_ctor_get(v_toFunctor_213_, 0);
lean_inc(v_map_216_);
lean_dec_ref(v_toFunctor_213_);
v___f_217_ = ((lean_object*)(l_Std_IterM_toList___redArg___closed__0));
v___f_218_ = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_218_, 0, v_toPure_215_);
lean_closure_set(v___f_218_, 1, v_inst_210_);
lean_closure_set(v___f_218_, 2, v_toBind_214_);
v___x_219_ = ((lean_object*)(l_Std_IterM_toArray___redArg___closed__0));
v___x_220_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_218_, v_it_211_, v___x_219_);
v___x_221_ = lean_apply_4(v_map_216_, lean_box(0), lean_box(0), v___f_217_, v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toList(lean_object* v_00_u03b1_222_, lean_object* v_m_223_, lean_object* v_00_u03b2_224_, lean_object* v_inst_225_, lean_object* v_inst_226_, lean_object* v_inst_227_, lean_object* v_it_228_){
_start:
{
lean_object* v_toApplicative_229_; lean_object* v_toFunctor_230_; lean_object* v_toBind_231_; lean_object* v_toPure_232_; lean_object* v_map_233_; lean_object* v___f_234_; lean_object* v___f_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v_toApplicative_229_ = lean_ctor_get(v_inst_225_, 0);
lean_inc_ref(v_toApplicative_229_);
v_toFunctor_230_ = lean_ctor_get(v_toApplicative_229_, 0);
lean_inc_ref(v_toFunctor_230_);
v_toBind_231_ = lean_ctor_get(v_inst_225_, 1);
lean_inc(v_toBind_231_);
lean_dec_ref(v_inst_225_);
v_toPure_232_ = lean_ctor_get(v_toApplicative_229_, 1);
lean_inc(v_toPure_232_);
lean_dec_ref(v_toApplicative_229_);
v_map_233_ = lean_ctor_get(v_toFunctor_230_, 0);
lean_inc(v_map_233_);
lean_dec_ref(v_toFunctor_230_);
v___f_234_ = ((lean_object*)(l_Std_IterM_toList___redArg___closed__0));
v___f_235_ = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(v___f_235_, 0, v_toPure_232_);
lean_closure_set(v___f_235_, 1, v_inst_226_);
lean_closure_set(v___f_235_, 2, v_toBind_231_);
v___x_236_ = ((lean_object*)(l_Std_IterM_toArray___redArg___closed__0));
v___x_237_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_235_, v_it_228_, v___x_236_);
v___x_238_ = lean_apply_4(v_map_233_, lean_box(0), lean_box(0), v___f_234_, v___x_237_);
return v___x_238_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Partial(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Total(uint8_t builtin);
lean_object* runtime_initialize_Init_WFExtrinsicFix(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

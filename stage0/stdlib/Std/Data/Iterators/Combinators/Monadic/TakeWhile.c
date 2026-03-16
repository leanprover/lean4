// Lean compiler output
// Module: Std.Data.Iterators.Combinators.Monadic.TakeWhile
// Imports: public import Init.Data.Nat.Lemmas public import Init.Data.Iterators.Consumers.Monadic.Collect public import Init.Data.Iterators.Consumers.Monadic.Loop public import Init.Data.Iterators.PostconditionMonad
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
LEAN_EXPORT lean_object* l_Std_IterM_takeWhileWithPostcondition___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_takeWhileWithPostcondition___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_takeWhileWithPostcondition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_takeWhileWithPostcondition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_takeWhileM___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_takeWhileM___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_takeWhileM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_takeWhileM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_takeWhile___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_takeWhile___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_takeWhile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_takeWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIterator___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instFinitenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instFinitenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instProductivenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instProductivenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIteratorLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_takeWhileWithPostcondition___redArg(lean_object* v_it_1_){
_start:
{
lean_inc(v_it_1_);
return v_it_1_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_takeWhileWithPostcondition___redArg___boxed(lean_object* v_it_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l_Std_IterM_takeWhileWithPostcondition___redArg(v_it_2_);
lean_dec(v_it_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_takeWhileWithPostcondition(lean_object* v_00_u03b1_4_, lean_object* v_m_5_, lean_object* v_00_u03b2_6_, lean_object* v_P_7_, lean_object* v_it_8_){
_start:
{
lean_inc(v_it_8_);
return v_it_8_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_takeWhileWithPostcondition___boxed(lean_object* v_00_u03b1_9_, lean_object* v_m_10_, lean_object* v_00_u03b2_11_, lean_object* v_P_12_, lean_object* v_it_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_IterM_takeWhileWithPostcondition(v_00_u03b1_9_, v_m_10_, v_00_u03b2_11_, v_P_12_, v_it_13_);
lean_dec(v_it_13_);
lean_dec(v_P_12_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_takeWhileM___redArg(lean_object* v_it_15_){
_start:
{
lean_inc(v_it_15_);
return v_it_15_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_takeWhileM___redArg___boxed(lean_object* v_it_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Std_IterM_takeWhileM___redArg(v_it_16_);
lean_dec(v_it_16_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_takeWhileM(lean_object* v_00_u03b1_18_, lean_object* v_m_19_, lean_object* v_00_u03b2_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_P_23_, lean_object* v_it_24_){
_start:
{
lean_inc(v_it_24_);
return v_it_24_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_takeWhileM___boxed(lean_object* v_00_u03b1_25_, lean_object* v_m_26_, lean_object* v_00_u03b2_27_, lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_P_30_, lean_object* v_it_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Std_IterM_takeWhileM(v_00_u03b1_25_, v_m_26_, v_00_u03b2_27_, v_inst_28_, v_inst_29_, v_P_30_, v_it_31_);
lean_dec(v_it_31_);
lean_dec(v_P_30_);
lean_dec(v_inst_29_);
lean_dec_ref(v_inst_28_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_takeWhile___redArg(lean_object* v_it_33_){
_start:
{
lean_inc(v_it_33_);
return v_it_33_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_takeWhile___redArg___boxed(lean_object* v_it_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Std_IterM_takeWhile___redArg(v_it_34_);
lean_dec(v_it_34_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_takeWhile(lean_object* v_00_u03b1_36_, lean_object* v_m_37_, lean_object* v_00_u03b2_38_, lean_object* v_inst_39_, lean_object* v_P_40_, lean_object* v_it_41_){
_start:
{
lean_inc(v_it_41_);
return v_it_41_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_takeWhile___boxed(lean_object* v_00_u03b1_42_, lean_object* v_m_43_, lean_object* v_00_u03b2_44_, lean_object* v_inst_45_, lean_object* v_P_46_, lean_object* v_it_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Std_IterM_takeWhile(v_00_u03b1_42_, v_m_43_, v_00_u03b2_44_, v_inst_45_, v_P_46_, v_it_47_);
lean_dec(v_it_47_);
lean_dec_ref(v_P_46_);
lean_dec_ref(v_inst_45_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__0(lean_object* v_toPure_49_, lean_object* v_it_50_, lean_object* v_out_51_, uint8_t v_____do__lift_52_){
_start:
{
if (v_____do__lift_52_ == 0)
{
lean_object* v___x_53_; lean_object* v___x_54_; 
lean_dec(v_out_51_);
lean_dec(v_it_50_);
v___x_53_ = lean_box(2);
v___x_54_ = lean_apply_2(v_toPure_49_, lean_box(0), v___x_53_);
return v___x_54_;
}
else
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_55_, 0, v_it_50_);
lean_ctor_set(v___x_55_, 1, v_out_51_);
v___x_56_ = lean_apply_2(v_toPure_49_, lean_box(0), v___x_55_);
return v___x_56_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__0___boxed(lean_object* v_toPure_57_, lean_object* v_it_58_, lean_object* v_out_59_, lean_object* v_____do__lift_60_){
_start:
{
uint8_t v_____do__lift_267__boxed_61_; lean_object* v_res_62_; 
v_____do__lift_267__boxed_61_ = lean_unbox(v_____do__lift_60_);
v_res_62_ = l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__0(v_toPure_57_, v_it_58_, v_out_59_, v_____do__lift_267__boxed_61_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__1(lean_object* v_toPure_63_, lean_object* v_P_64_, lean_object* v_toBind_65_, lean_object* v_____do__lift_66_){
_start:
{
switch(lean_obj_tag(v_____do__lift_66_))
{
case 0:
{
lean_object* v_it_67_; lean_object* v_out_68_; lean_object* v___f_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v_it_67_ = lean_ctor_get(v_____do__lift_66_, 0);
lean_inc(v_it_67_);
v_out_68_ = lean_ctor_get(v_____do__lift_66_, 1);
lean_inc(v_out_68_);
lean_dec_ref(v_____do__lift_66_);
lean_inc(v_out_68_);
v___f_69_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_69_, 0, v_toPure_63_);
lean_closure_set(v___f_69_, 1, v_it_67_);
lean_closure_set(v___f_69_, 2, v_out_68_);
v___x_70_ = lean_apply_1(v_P_64_, v_out_68_);
v___x_71_ = lean_apply_4(v_toBind_65_, lean_box(0), lean_box(0), v___x_70_, v___f_69_);
return v___x_71_;
}
case 1:
{
lean_object* v_it_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_80_; 
lean_dec(v_toBind_65_);
lean_dec(v_P_64_);
v_it_72_ = lean_ctor_get(v_____do__lift_66_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v_____do__lift_66_);
if (v_isSharedCheck_80_ == 0)
{
v___x_74_ = v_____do__lift_66_;
v_isShared_75_ = v_isSharedCheck_80_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_it_72_);
lean_dec(v_____do__lift_66_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_80_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_77_; 
if (v_isShared_75_ == 0)
{
v___x_77_ = v___x_74_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_it_72_);
v___x_77_ = v_reuseFailAlloc_79_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
lean_object* v___x_78_; 
v___x_78_ = lean_apply_2(v_toPure_63_, lean_box(0), v___x_77_);
return v___x_78_;
}
}
}
default: 
{
lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec(v_toBind_65_);
lean_dec(v_P_64_);
v___x_81_ = lean_box(2);
v___x_82_ = lean_apply_2(v_toPure_63_, lean_box(0), v___x_81_);
return v___x_82_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__2(lean_object* v_inst_83_, lean_object* v_toBind_84_, lean_object* v___f_85_, lean_object* v_it_86_){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_apply_1(v_inst_83_, v_it_86_);
v___x_88_ = lean_apply_4(v_toBind_84_, lean_box(0), lean_box(0), v___x_87_, v___f_85_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIterator___redArg(lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_P_91_){
_start:
{
lean_object* v_toApplicative_92_; lean_object* v_toBind_93_; lean_object* v_toPure_94_; lean_object* v___f_95_; lean_object* v___f_96_; 
v_toApplicative_92_ = lean_ctor_get(v_inst_89_, 0);
lean_inc_ref(v_toApplicative_92_);
v_toBind_93_ = lean_ctor_get(v_inst_89_, 1);
lean_inc(v_toBind_93_);
lean_dec_ref(v_inst_89_);
v_toPure_94_ = lean_ctor_get(v_toApplicative_92_, 1);
lean_inc(v_toPure_94_);
lean_dec_ref(v_toApplicative_92_);
lean_inc(v_toBind_93_);
v___f_95_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__1), 4, 3);
lean_closure_set(v___f_95_, 0, v_toPure_94_);
lean_closure_set(v___f_95_, 1, v_P_91_);
lean_closure_set(v___f_95_, 2, v_toBind_93_);
v___f_96_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__2), 4, 3);
lean_closure_set(v___f_96_, 0, v_inst_90_);
lean_closure_set(v___f_96_, 1, v_toBind_93_);
lean_closure_set(v___f_96_, 2, v___f_95_);
return v___f_96_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIterator(lean_object* v_00_u03b1_97_, lean_object* v_m_98_, lean_object* v_00_u03b2_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_P_102_){
_start:
{
lean_object* v_toApplicative_103_; lean_object* v_toBind_104_; lean_object* v_toPure_105_; lean_object* v___f_106_; lean_object* v___f_107_; 
v_toApplicative_103_ = lean_ctor_get(v_inst_100_, 0);
lean_inc_ref(v_toApplicative_103_);
v_toBind_104_ = lean_ctor_get(v_inst_100_, 1);
lean_inc(v_toBind_104_);
lean_dec_ref(v_inst_100_);
v_toPure_105_ = lean_ctor_get(v_toApplicative_103_, 1);
lean_inc(v_toPure_105_);
lean_dec_ref(v_toApplicative_103_);
lean_inc(v_toBind_104_);
v___f_106_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__1), 4, 3);
lean_closure_set(v___f_106_, 0, v_toPure_105_);
lean_closure_set(v___f_106_, 1, v_P_102_);
lean_closure_set(v___f_106_, 2, v_toBind_104_);
v___f_107_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__2), 4, 3);
lean_closure_set(v___f_107_, 0, v_inst_101_);
lean_closure_set(v___f_107_, 1, v_toBind_104_);
lean_closure_set(v___f_107_, 2, v___f_106_);
return v___f_107_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instFinitenessRelation(lean_object* v_00_u03b1_108_, lean_object* v_m_109_, lean_object* v_00_u03b2_110_, lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_inst_113_, lean_object* v_P_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lean_box(0);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instFinitenessRelation___boxed(lean_object* v_00_u03b1_116_, lean_object* v_m_117_, lean_object* v_00_u03b2_118_, lean_object* v_inst_119_, lean_object* v_inst_120_, lean_object* v_inst_121_, lean_object* v_P_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instFinitenessRelation(v_00_u03b1_116_, v_m_117_, v_00_u03b2_118_, v_inst_119_, v_inst_120_, v_inst_121_, v_P_122_);
lean_dec(v_P_122_);
lean_dec(v_inst_120_);
lean_dec_ref(v_inst_119_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instProductivenessRelation(lean_object* v_00_u03b1_124_, lean_object* v_m_125_, lean_object* v_00_u03b2_126_, lean_object* v_inst_127_, lean_object* v_inst_128_, lean_object* v_inst_129_, lean_object* v_P_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = lean_box(0);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instProductivenessRelation___boxed(lean_object* v_00_u03b1_132_, lean_object* v_m_133_, lean_object* v_00_u03b2_134_, lean_object* v_inst_135_, lean_object* v_inst_136_, lean_object* v_inst_137_, lean_object* v_P_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instProductivenessRelation(v_00_u03b1_132_, v_m_133_, v_00_u03b2_134_, v_inst_135_, v_inst_136_, v_inst_137_, v_P_138_);
lean_dec(v_P_138_);
lean_dec(v_inst_136_);
lean_dec_ref(v_inst_135_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_140_, lean_object* v_recur_141_, lean_object* v_it_142_, lean_object* v_____do__lift_143_){
_start:
{
if (lean_obj_tag(v_____do__lift_143_) == 0)
{
lean_object* v_a_144_; lean_object* v___x_145_; 
lean_dec(v_it_142_);
lean_dec(v_recur_141_);
v_a_144_ = lean_ctor_get(v_____do__lift_143_, 0);
lean_inc(v_a_144_);
lean_dec_ref(v_____do__lift_143_);
v___x_145_ = lean_apply_2(v_toPure_140_, lean_box(0), v_a_144_);
return v___x_145_;
}
else
{
lean_object* v_a_146_; lean_object* v___x_147_; 
lean_dec(v_toPure_140_);
v_a_146_ = lean_ctor_get(v_____do__lift_143_, 0);
lean_inc(v_a_146_);
lean_dec_ref(v_____do__lift_143_);
v___x_147_ = lean_apply_4(v_recur_141_, v_it_142_, v_a_146_, lean_box(0), lean_box(0));
return v___x_147_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_148_, lean_object* v_recur_149_, lean_object* v___y_150_, lean_object* v_acc_151_, lean_object* v_toBind_152_, lean_object* v_s_153_){
_start:
{
switch(lean_obj_tag(v_s_153_))
{
case 0:
{
lean_object* v_it_154_; lean_object* v_out_155_; lean_object* v___f_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v_it_154_ = lean_ctor_get(v_s_153_, 0);
lean_inc(v_it_154_);
v_out_155_ = lean_ctor_get(v_s_153_, 1);
lean_inc(v_out_155_);
lean_dec_ref(v_s_153_);
v___f_156_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_156_, 0, v_toPure_148_);
lean_closure_set(v___f_156_, 1, v_recur_149_);
lean_closure_set(v___f_156_, 2, v_it_154_);
v___x_157_ = lean_apply_3(v___y_150_, v_out_155_, lean_box(0), v_acc_151_);
v___x_158_ = lean_apply_4(v_toBind_152_, lean_box(0), lean_box(0), v___x_157_, v___f_156_);
return v___x_158_;
}
case 1:
{
lean_object* v_it_159_; lean_object* v___x_160_; 
lean_dec(v_toBind_152_);
lean_dec(v___y_150_);
lean_dec(v_toPure_148_);
v_it_159_ = lean_ctor_get(v_s_153_, 0);
lean_inc(v_it_159_);
lean_dec_ref(v_s_153_);
v___x_160_ = lean_apply_4(v_recur_149_, v_it_159_, v_acc_151_, lean_box(0), lean_box(0));
return v___x_160_;
}
default: 
{
lean_object* v___x_161_; 
lean_dec(v_toBind_152_);
lean_dec(v___y_150_);
lean_dec(v_recur_149_);
v___x_161_ = lean_apply_2(v_toPure_148_, lean_box(0), v_acc_151_);
return v___x_161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__4(lean_object* v_inst_162_, lean_object* v_toPure_163_, lean_object* v___y_164_, lean_object* v_toBind_165_, lean_object* v_P_166_, lean_object* v_inst_167_, lean_object* v_lift_168_, lean_object* v_it_169_, lean_object* v_acc_170_, lean_object* v_hP_171_, lean_object* v_recur_172_){
_start:
{
lean_object* v_toApplicative_173_; lean_object* v_toBind_174_; lean_object* v_toPure_175_; lean_object* v___f_176_; lean_object* v___f_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_toApplicative_173_ = lean_ctor_get(v_inst_162_, 0);
lean_inc_ref(v_toApplicative_173_);
v_toBind_174_ = lean_ctor_get(v_inst_162_, 1);
lean_inc(v_toBind_174_);
lean_dec_ref(v_inst_162_);
v_toPure_175_ = lean_ctor_get(v_toApplicative_173_, 1);
lean_inc(v_toPure_175_);
lean_dec_ref(v_toApplicative_173_);
v___f_176_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_176_, 0, v_toPure_163_);
lean_closure_set(v___f_176_, 1, v_recur_172_);
lean_closure_set(v___f_176_, 2, v___y_164_);
lean_closure_set(v___f_176_, 3, v_acc_170_);
lean_closure_set(v___f_176_, 4, v_toBind_165_);
lean_inc(v_toBind_174_);
v___f_177_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__1), 4, 3);
lean_closure_set(v___f_177_, 0, v_toPure_175_);
lean_closure_set(v___f_177_, 1, v_P_166_);
lean_closure_set(v___f_177_, 2, v_toBind_174_);
v___x_178_ = lean_apply_1(v_inst_167_, v_it_169_);
v___x_179_ = lean_apply_4(v_toBind_174_, lean_box(0), lean_box(0), v___x_178_, v___f_177_);
v___x_180_ = lean_apply_4(v_lift_168_, lean_box(0), lean_box(0), v___f_176_, v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__2(lean_object* v_inst_181_, lean_object* v_inst_182_, lean_object* v_P_183_, lean_object* v_inst_184_, lean_object* v_lift_185_, lean_object* v_00_u03b3_186_, lean_object* v_Pl_187_, lean_object* v_it_188_, lean_object* v_init_189_, lean_object* v___y_190_){
_start:
{
lean_object* v_toApplicative_191_; lean_object* v_toBind_192_; lean_object* v_toPure_193_; lean_object* v___f_194_; lean_object* v___x_195_; 
v_toApplicative_191_ = lean_ctor_get(v_inst_181_, 0);
lean_inc_ref(v_toApplicative_191_);
v_toBind_192_ = lean_ctor_get(v_inst_181_, 1);
lean_inc(v_toBind_192_);
lean_dec_ref(v_inst_181_);
v_toPure_193_ = lean_ctor_get(v_toApplicative_191_, 1);
lean_inc(v_toPure_193_);
lean_dec_ref(v_toApplicative_191_);
v___f_194_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__4), 11, 7);
lean_closure_set(v___f_194_, 0, v_inst_182_);
lean_closure_set(v___f_194_, 1, v_toPure_193_);
lean_closure_set(v___f_194_, 2, v___y_190_);
lean_closure_set(v___f_194_, 3, v_toBind_192_);
lean_closure_set(v___f_194_, 4, v_P_183_);
lean_closure_set(v___f_194_, 5, v_inst_184_);
lean_closure_set(v___f_194_, 6, v_lift_185_);
v___x_195_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_194_, v_it_188_, v_init_189_, lean_box(0));
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg(lean_object* v_P_196_, lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_inst_199_){
_start:
{
lean_object* v___f_200_; 
v___f_200_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__2), 10, 4);
lean_closure_set(v___f_200_, 0, v_inst_198_);
lean_closure_set(v___f_200_, 1, v_inst_197_);
lean_closure_set(v___f_200_, 2, v_P_196_);
lean_closure_set(v___f_200_, 3, v_inst_199_);
return v___f_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIteratorLoop(lean_object* v_00_u03b1_201_, lean_object* v_m_202_, lean_object* v_00_u03b2_203_, lean_object* v_n_204_, lean_object* v_P_205_, lean_object* v_inst_206_, lean_object* v_inst_207_, lean_object* v_inst_208_, lean_object* v_inst_209_){
_start:
{
lean_object* v___f_210_; 
v___f_210_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__2), 10, 4);
lean_closure_set(v___f_210_, 0, v_inst_207_);
lean_closure_set(v___f_210_, 1, v_inst_206_);
lean_closure_set(v___f_210_, 2, v_P_205_);
lean_closure_set(v___f_210_, 3, v_inst_208_);
return v___f_210_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIteratorLoop___boxed(lean_object* v_00_u03b1_211_, lean_object* v_m_212_, lean_object* v_00_u03b2_213_, lean_object* v_n_214_, lean_object* v_P_215_, lean_object* v_inst_216_, lean_object* v_inst_217_, lean_object* v_inst_218_, lean_object* v_inst_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Std_Iterators_Types_TakeWhile_instIteratorLoop(v_00_u03b1_211_, v_m_212_, v_00_u03b2_213_, v_n_214_, v_P_215_, v_inst_216_, v_inst_217_, v_inst_218_, v_inst_219_);
lean_dec(v_inst_219_);
return v_res_220_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_PostconditionMonad(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_PostconditionMonad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_PostconditionMonad(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_PostconditionMonad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(builtin);
}
#ifdef __cplusplus
}
#endif

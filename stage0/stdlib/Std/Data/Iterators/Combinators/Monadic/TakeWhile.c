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
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instFinitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instFinitenessRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instFinitenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instFinitenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instProductivenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instProductivenessRelation___redArg___boxed(lean_object*);
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
uint8_t v_____do__lift_189__boxed_61_; lean_object* v_res_62_; 
v_____do__lift_189__boxed_61_ = lean_unbox(v_____do__lift_60_);
v_res_62_ = l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__0(v_toPure_57_, v_it_58_, v_out_59_, v_____do__lift_189__boxed_61_);
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
lean_inc_n(v_out_68_, 2);
lean_dec_ref_known(v_____do__lift_66_, 2);
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
lean_inc_n(v_toBind_93_, 2);
lean_dec_ref(v_inst_89_);
v_toPure_94_ = lean_ctor_get(v_toApplicative_92_, 1);
lean_inc(v_toPure_94_);
lean_dec_ref(v_toApplicative_92_);
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
lean_inc_n(v_toBind_104_, 2);
lean_dec_ref(v_inst_100_);
v_toPure_105_ = lean_ctor_get(v_toApplicative_103_, 1);
lean_inc(v_toPure_105_);
lean_dec_ref(v_toApplicative_103_);
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
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lean_box(0);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instFinitenessRelation___redArg___boxed(lean_object* v___dummy_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instFinitenessRelation___redArg();
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instFinitenessRelation(lean_object* v_00_u03b1_112_, lean_object* v_m_113_, lean_object* v_00_u03b2_114_, lean_object* v_inst_115_, lean_object* v_inst_116_, lean_object* v_inst_117_, lean_object* v_P_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = lean_box(0);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instFinitenessRelation___boxed(lean_object* v_00_u03b1_120_, lean_object* v_m_121_, lean_object* v_00_u03b2_122_, lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_inst_125_, lean_object* v_P_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instFinitenessRelation(v_00_u03b1_120_, v_m_121_, v_00_u03b2_122_, v_inst_123_, v_inst_124_, v_inst_125_, v_P_126_);
lean_dec(v_P_126_);
lean_dec(v_inst_124_);
lean_dec_ref(v_inst_123_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instProductivenessRelation___redArg(){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lean_box(0);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instProductivenessRelation___redArg___boxed(lean_object* v___dummy_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instProductivenessRelation___redArg();
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instProductivenessRelation(lean_object* v_00_u03b1_132_, lean_object* v_m_133_, lean_object* v_00_u03b2_134_, lean_object* v_inst_135_, lean_object* v_inst_136_, lean_object* v_inst_137_, lean_object* v_P_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = lean_box(0);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instProductivenessRelation___boxed(lean_object* v_00_u03b1_140_, lean_object* v_m_141_, lean_object* v_00_u03b2_142_, lean_object* v_inst_143_, lean_object* v_inst_144_, lean_object* v_inst_145_, lean_object* v_P_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instProductivenessRelation(v_00_u03b1_140_, v_m_141_, v_00_u03b2_142_, v_inst_143_, v_inst_144_, v_inst_145_, v_P_146_);
lean_dec(v_P_146_);
lean_dec(v_inst_144_);
lean_dec_ref(v_inst_143_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_148_, lean_object* v_recur_149_, lean_object* v_it_150_, lean_object* v_____do__lift_151_){
_start:
{
if (lean_obj_tag(v_____do__lift_151_) == 0)
{
lean_object* v_a_152_; lean_object* v___x_153_; 
lean_dec(v_it_150_);
lean_dec(v_recur_149_);
v_a_152_ = lean_ctor_get(v_____do__lift_151_, 0);
lean_inc(v_a_152_);
lean_dec_ref_known(v_____do__lift_151_, 1);
v___x_153_ = lean_apply_2(v_toPure_148_, lean_box(0), v_a_152_);
return v___x_153_;
}
else
{
lean_object* v_a_154_; lean_object* v___x_155_; 
lean_dec(v_toPure_148_);
v_a_154_ = lean_ctor_get(v_____do__lift_151_, 0);
lean_inc(v_a_154_);
lean_dec_ref_known(v_____do__lift_151_, 1);
v___x_155_ = lean_apply_4(v_recur_149_, v_it_150_, v_a_154_, lean_box(0), lean_box(0));
return v___x_155_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_156_, lean_object* v_recur_157_, lean_object* v___y_158_, lean_object* v_acc_159_, lean_object* v_toBind_160_, lean_object* v_s_161_){
_start:
{
switch(lean_obj_tag(v_s_161_))
{
case 0:
{
lean_object* v_it_162_; lean_object* v_out_163_; lean_object* v___f_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v_it_162_ = lean_ctor_get(v_s_161_, 0);
lean_inc(v_it_162_);
v_out_163_ = lean_ctor_get(v_s_161_, 1);
lean_inc(v_out_163_);
lean_dec_ref_known(v_s_161_, 2);
v___f_164_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_164_, 0, v_toPure_156_);
lean_closure_set(v___f_164_, 1, v_recur_157_);
lean_closure_set(v___f_164_, 2, v_it_162_);
v___x_165_ = lean_apply_3(v___y_158_, v_out_163_, lean_box(0), v_acc_159_);
v___x_166_ = lean_apply_4(v_toBind_160_, lean_box(0), lean_box(0), v___x_165_, v___f_164_);
return v___x_166_;
}
case 1:
{
lean_object* v_it_167_; lean_object* v___x_168_; 
lean_dec(v_toBind_160_);
lean_dec(v___y_158_);
lean_dec(v_toPure_156_);
v_it_167_ = lean_ctor_get(v_s_161_, 0);
lean_inc(v_it_167_);
lean_dec_ref_known(v_s_161_, 1);
v___x_168_ = lean_apply_4(v_recur_157_, v_it_167_, v_acc_159_, lean_box(0), lean_box(0));
return v___x_168_;
}
default: 
{
lean_object* v___x_169_; 
lean_dec(v_toBind_160_);
lean_dec(v___y_158_);
lean_dec(v_recur_157_);
v___x_169_ = lean_apply_2(v_toPure_156_, lean_box(0), v_acc_159_);
return v___x_169_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__4(lean_object* v_inst_170_, lean_object* v_toPure_171_, lean_object* v___y_172_, lean_object* v_toBind_173_, lean_object* v_P_174_, lean_object* v_inst_175_, lean_object* v_lift_176_, lean_object* v_it_177_, lean_object* v_acc_178_, lean_object* v_hP_179_, lean_object* v_recur_180_){
_start:
{
lean_object* v_toApplicative_181_; lean_object* v_toBind_182_; lean_object* v_toPure_183_; lean_object* v___f_184_; lean_object* v___f_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v_toApplicative_181_ = lean_ctor_get(v_inst_170_, 0);
lean_inc_ref(v_toApplicative_181_);
v_toBind_182_ = lean_ctor_get(v_inst_170_, 1);
lean_inc_n(v_toBind_182_, 2);
lean_dec_ref(v_inst_170_);
v_toPure_183_ = lean_ctor_get(v_toApplicative_181_, 1);
lean_inc(v_toPure_183_);
lean_dec_ref(v_toApplicative_181_);
v___f_184_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_184_, 0, v_toPure_171_);
lean_closure_set(v___f_184_, 1, v_recur_180_);
lean_closure_set(v___f_184_, 2, v___y_172_);
lean_closure_set(v___f_184_, 3, v_acc_178_);
lean_closure_set(v___f_184_, 4, v_toBind_173_);
v___f_185_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__1), 4, 3);
lean_closure_set(v___f_185_, 0, v_toPure_183_);
lean_closure_set(v___f_185_, 1, v_P_174_);
lean_closure_set(v___f_185_, 2, v_toBind_182_);
v___x_186_ = lean_apply_1(v_inst_175_, v_it_177_);
v___x_187_ = lean_apply_4(v_toBind_182_, lean_box(0), lean_box(0), v___x_186_, v___f_185_);
v___x_188_ = lean_apply_4(v_lift_176_, lean_box(0), lean_box(0), v___f_184_, v___x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__2(lean_object* v_inst_189_, lean_object* v_inst_190_, lean_object* v_P_191_, lean_object* v_inst_192_, lean_object* v_lift_193_, lean_object* v_00_u03b3_194_, lean_object* v_Pl_195_, lean_object* v_it_196_, lean_object* v_init_197_, lean_object* v___y_198_){
_start:
{
lean_object* v_toApplicative_199_; lean_object* v_toBind_200_; lean_object* v_toPure_201_; lean_object* v___f_202_; lean_object* v___x_203_; 
v_toApplicative_199_ = lean_ctor_get(v_inst_189_, 0);
lean_inc_ref(v_toApplicative_199_);
v_toBind_200_ = lean_ctor_get(v_inst_189_, 1);
lean_inc(v_toBind_200_);
lean_dec_ref(v_inst_189_);
v_toPure_201_ = lean_ctor_get(v_toApplicative_199_, 1);
lean_inc(v_toPure_201_);
lean_dec_ref(v_toApplicative_199_);
v___f_202_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__4), 11, 7);
lean_closure_set(v___f_202_, 0, v_inst_190_);
lean_closure_set(v___f_202_, 1, v_toPure_201_);
lean_closure_set(v___f_202_, 2, v___y_198_);
lean_closure_set(v___f_202_, 3, v_toBind_200_);
lean_closure_set(v___f_202_, 4, v_P_191_);
lean_closure_set(v___f_202_, 5, v_inst_192_);
lean_closure_set(v___f_202_, 6, v_lift_193_);
v___x_203_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_202_, v_it_196_, v_init_197_, lean_box(0));
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg(lean_object* v_P_204_, lean_object* v_inst_205_, lean_object* v_inst_206_, lean_object* v_inst_207_){
_start:
{
lean_object* v___f_208_; 
v___f_208_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__2), 10, 4);
lean_closure_set(v___f_208_, 0, v_inst_206_);
lean_closure_set(v___f_208_, 1, v_inst_205_);
lean_closure_set(v___f_208_, 2, v_P_204_);
lean_closure_set(v___f_208_, 3, v_inst_207_);
return v___f_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIteratorLoop(lean_object* v_00_u03b1_209_, lean_object* v_m_210_, lean_object* v_00_u03b2_211_, lean_object* v_n_212_, lean_object* v_P_213_, lean_object* v_inst_214_, lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_inst_217_){
_start:
{
lean_object* v___f_218_; 
v___f_218_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__2), 10, 4);
lean_closure_set(v___f_218_, 0, v_inst_215_);
lean_closure_set(v___f_218_, 1, v_inst_214_);
lean_closure_set(v___f_218_, 2, v_P_213_);
lean_closure_set(v___f_218_, 3, v_inst_216_);
return v___f_218_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIteratorLoop___boxed(lean_object* v_00_u03b1_219_, lean_object* v_m_220_, lean_object* v_00_u03b2_221_, lean_object* v_n_222_, lean_object* v_P_223_, lean_object* v_inst_224_, lean_object* v_inst_225_, lean_object* v_inst_226_, lean_object* v_inst_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Std_Iterators_Types_TakeWhile_instIteratorLoop(v_00_u03b1_219_, v_m_220_, v_00_u03b2_221_, v_n_222_, v_P_223_, v_inst_224_, v_inst_225_, v_inst_226_, v_inst_227_);
lean_dec(v_inst_227_);
return v_res_228_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_PostconditionMonad(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

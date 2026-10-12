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
lean_object* l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__0(lean_object* v_toPure_49_, lean_object* v_it_50_, lean_object* v_out_51_, uint8_t v_____do__lift_52_){
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
LEAN_EXPORT void l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_49_ = stack[0].m_obj;
lean_object* v_it_50_ = stack[1].m_obj;
lean_object* v_out_51_ = stack[2].m_obj;
uint8_t v_____do__lift_52_ = stack[3].m_num;
lean_object* v_res_57_;
v_res_57_ = l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__0(v_toPure_49_, v_it_50_, v_out_51_, v_____do__lift_52_);
stack->m_obj
 = v_res_57_;
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__0___boxed(lean_object* v_toPure_58_, lean_object* v_it_59_, lean_object* v_out_60_, lean_object* v_____do__lift_61_){
_start:
{
uint8_t v_____do__lift_189__boxed_62_; lean_object* v_res_63_; 
v_____do__lift_189__boxed_62_ = lean_unbox(v_____do__lift_61_);
v_res_63_ = l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__0(v_toPure_58_, v_it_59_, v_out_60_, v_____do__lift_189__boxed_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__1(lean_object* v_toPure_64_, lean_object* v_P_65_, lean_object* v_toBind_66_, lean_object* v_____do__lift_67_){
_start:
{
switch(lean_obj_tag(v_____do__lift_67_))
{
case 0:
{
lean_object* v_it_68_; lean_object* v_out_69_; lean_object* v___f_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v_it_68_ = lean_ctor_get(v_____do__lift_67_, 0);
lean_inc(v_it_68_);
v_out_69_ = lean_ctor_get(v_____do__lift_67_, 1);
lean_inc_n(v_out_69_, 2);
lean_dec_ref_known(v_____do__lift_67_, 2);
v___f_70_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_70_, 0, v_toPure_64_);
lean_closure_set(v___f_70_, 1, v_it_68_);
lean_closure_set(v___f_70_, 2, v_out_69_);
v___x_71_ = lean_apply_1(v_P_65_, v_out_69_);
v___x_72_ = lean_apply_4(v_toBind_66_, lean_box(0), lean_box(0), v___x_71_, v___f_70_);
return v___x_72_;
}
case 1:
{
lean_object* v_it_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_81_; 
lean_dec(v_toBind_66_);
lean_dec(v_P_65_);
v_it_73_ = lean_ctor_get(v_____do__lift_67_, 0);
v_isSharedCheck_81_ = !lean_is_exclusive(v_____do__lift_67_);
if (v_isSharedCheck_81_ == 0)
{
v___x_75_ = v_____do__lift_67_;
v_isShared_76_ = v_isSharedCheck_81_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_it_73_);
lean_dec(v_____do__lift_67_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_81_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_78_; 
if (v_isShared_76_ == 0)
{
v___x_78_ = v___x_75_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v_it_73_);
v___x_78_ = v_reuseFailAlloc_80_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
lean_object* v___x_79_; 
v___x_79_ = lean_apply_2(v_toPure_64_, lean_box(0), v___x_78_);
return v___x_79_;
}
}
}
default: 
{
lean_object* v___x_82_; lean_object* v___x_83_; 
lean_dec(v_toBind_66_);
lean_dec(v_P_65_);
v___x_82_ = lean_box(2);
v___x_83_ = lean_apply_2(v_toPure_64_, lean_box(0), v___x_82_);
return v___x_83_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__2(lean_object* v_inst_84_, lean_object* v_toBind_85_, lean_object* v___f_86_, lean_object* v_it_87_){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_apply_1(v_inst_84_, v_it_87_);
v___x_89_ = lean_apply_4(v_toBind_85_, lean_box(0), lean_box(0), v___x_88_, v___f_86_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIterator___redArg(lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_P_92_){
_start:
{
lean_object* v_toApplicative_93_; lean_object* v_toBind_94_; lean_object* v_toPure_95_; lean_object* v___f_96_; lean_object* v___f_97_; 
v_toApplicative_93_ = lean_ctor_get(v_inst_90_, 0);
lean_inc_ref(v_toApplicative_93_);
v_toBind_94_ = lean_ctor_get(v_inst_90_, 1);
lean_inc_n(v_toBind_94_, 2);
lean_dec_ref(v_inst_90_);
v_toPure_95_ = lean_ctor_get(v_toApplicative_93_, 1);
lean_inc(v_toPure_95_);
lean_dec_ref(v_toApplicative_93_);
v___f_96_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__1), 4, 3);
lean_closure_set(v___f_96_, 0, v_toPure_95_);
lean_closure_set(v___f_96_, 1, v_P_92_);
lean_closure_set(v___f_96_, 2, v_toBind_94_);
v___f_97_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__2), 4, 3);
lean_closure_set(v___f_97_, 0, v_inst_91_);
lean_closure_set(v___f_97_, 1, v_toBind_94_);
lean_closure_set(v___f_97_, 2, v___f_96_);
return v___f_97_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIterator(lean_object* v_00_u03b1_98_, lean_object* v_m_99_, lean_object* v_00_u03b2_100_, lean_object* v_inst_101_, lean_object* v_inst_102_, lean_object* v_P_103_){
_start:
{
lean_object* v_toApplicative_104_; lean_object* v_toBind_105_; lean_object* v_toPure_106_; lean_object* v___f_107_; lean_object* v___f_108_; 
v_toApplicative_104_ = lean_ctor_get(v_inst_101_, 0);
lean_inc_ref(v_toApplicative_104_);
v_toBind_105_ = lean_ctor_get(v_inst_101_, 1);
lean_inc_n(v_toBind_105_, 2);
lean_dec_ref(v_inst_101_);
v_toPure_106_ = lean_ctor_get(v_toApplicative_104_, 1);
lean_inc(v_toPure_106_);
lean_dec_ref(v_toApplicative_104_);
v___f_107_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__1), 4, 3);
lean_closure_set(v___f_107_, 0, v_toPure_106_);
lean_closure_set(v___f_107_, 1, v_P_103_);
lean_closure_set(v___f_107_, 2, v_toBind_105_);
v___f_108_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__2), 4, 3);
lean_closure_set(v___f_108_, 0, v_inst_102_);
lean_closure_set(v___f_108_, 1, v_toBind_105_);
lean_closure_set(v___f_108_, 2, v___f_107_);
return v___f_108_;
}
}
lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_box(0);
return v___x_110_;
}
}
LEAN_EXPORT void l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instFinitenessRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_111_;
v_res_111_ = l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instFinitenessRelation___redArg();
stack->m_obj
 = v_res_111_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instFinitenessRelation___redArg___boxed(lean_object* v___dummy_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instFinitenessRelation___redArg();
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instFinitenessRelation(lean_object* v_00_u03b1_114_, lean_object* v_m_115_, lean_object* v_00_u03b2_116_, lean_object* v_inst_117_, lean_object* v_inst_118_, lean_object* v_inst_119_, lean_object* v_P_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = lean_box(0);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instFinitenessRelation___boxed(lean_object* v_00_u03b1_122_, lean_object* v_m_123_, lean_object* v_00_u03b2_124_, lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_P_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instFinitenessRelation(v_00_u03b1_122_, v_m_123_, v_00_u03b2_124_, v_inst_125_, v_inst_126_, v_inst_127_, v_P_128_);
lean_dec(v_P_128_);
lean_dec(v_inst_126_);
lean_dec_ref(v_inst_125_);
return v_res_129_;
}
}
lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instProductivenessRelation___redArg(){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = lean_box(0);
return v___x_131_;
}
}
LEAN_EXPORT void l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instProductivenessRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_132_;
v_res_132_ = l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instProductivenessRelation___redArg();
stack->m_obj
 = v_res_132_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instProductivenessRelation___redArg___boxed(lean_object* v___dummy_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instProductivenessRelation___redArg();
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instProductivenessRelation(lean_object* v_00_u03b1_135_, lean_object* v_m_136_, lean_object* v_00_u03b2_137_, lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_inst_140_, lean_object* v_P_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = lean_box(0);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instProductivenessRelation___boxed(lean_object* v_00_u03b1_143_, lean_object* v_m_144_, lean_object* v_00_u03b2_145_, lean_object* v_inst_146_, lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_P_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instProductivenessRelation(v_00_u03b1_143_, v_m_144_, v_00_u03b2_145_, v_inst_146_, v_inst_147_, v_inst_148_, v_P_149_);
lean_dec(v_P_149_);
lean_dec(v_inst_147_);
lean_dec_ref(v_inst_146_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_151_, lean_object* v_recur_152_, lean_object* v_it_153_, lean_object* v_____do__lift_154_){
_start:
{
if (lean_obj_tag(v_____do__lift_154_) == 0)
{
lean_object* v_a_155_; lean_object* v___x_156_; 
lean_dec(v_it_153_);
lean_dec(v_recur_152_);
v_a_155_ = lean_ctor_get(v_____do__lift_154_, 0);
lean_inc(v_a_155_);
lean_dec_ref_known(v_____do__lift_154_, 1);
v___x_156_ = lean_apply_2(v_toPure_151_, lean_box(0), v_a_155_);
return v___x_156_;
}
else
{
lean_object* v_a_157_; lean_object* v___x_158_; 
lean_dec(v_toPure_151_);
v_a_157_ = lean_ctor_get(v_____do__lift_154_, 0);
lean_inc(v_a_157_);
lean_dec_ref_known(v_____do__lift_154_, 1);
v___x_158_ = lean_apply_4(v_recur_152_, v_it_153_, v_a_157_, lean_box(0), lean_box(0));
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_159_, lean_object* v_recur_160_, lean_object* v___y_161_, lean_object* v_acc_162_, lean_object* v_toBind_163_, lean_object* v_s_164_){
_start:
{
switch(lean_obj_tag(v_s_164_))
{
case 0:
{
lean_object* v_it_165_; lean_object* v_out_166_; lean_object* v___f_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v_it_165_ = lean_ctor_get(v_s_164_, 0);
lean_inc(v_it_165_);
v_out_166_ = lean_ctor_get(v_s_164_, 1);
lean_inc(v_out_166_);
lean_dec_ref_known(v_s_164_, 2);
v___f_167_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_167_, 0, v_toPure_159_);
lean_closure_set(v___f_167_, 1, v_recur_160_);
lean_closure_set(v___f_167_, 2, v_it_165_);
v___x_168_ = lean_apply_3(v___y_161_, v_out_166_, lean_box(0), v_acc_162_);
v___x_169_ = lean_apply_4(v_toBind_163_, lean_box(0), lean_box(0), v___x_168_, v___f_167_);
return v___x_169_;
}
case 1:
{
lean_object* v_it_170_; lean_object* v___x_171_; 
lean_dec(v_toBind_163_);
lean_dec(v___y_161_);
lean_dec(v_toPure_159_);
v_it_170_ = lean_ctor_get(v_s_164_, 0);
lean_inc(v_it_170_);
lean_dec_ref_known(v_s_164_, 1);
v___x_171_ = lean_apply_4(v_recur_160_, v_it_170_, v_acc_162_, lean_box(0), lean_box(0));
return v___x_171_;
}
default: 
{
lean_object* v___x_172_; 
lean_dec(v_toBind_163_);
lean_dec(v___y_161_);
lean_dec(v_recur_160_);
v___x_172_ = lean_apply_2(v_toPure_159_, lean_box(0), v_acc_162_);
return v___x_172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__4(lean_object* v_inst_173_, lean_object* v_toPure_174_, lean_object* v___y_175_, lean_object* v_toBind_176_, lean_object* v_P_177_, lean_object* v_inst_178_, lean_object* v_lift_179_, lean_object* v_it_180_, lean_object* v_acc_181_, lean_object* v_hP_182_, lean_object* v_recur_183_){
_start:
{
lean_object* v_toApplicative_184_; lean_object* v_toBind_185_; lean_object* v_toPure_186_; lean_object* v___f_187_; lean_object* v___f_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v_toApplicative_184_ = lean_ctor_get(v_inst_173_, 0);
lean_inc_ref(v_toApplicative_184_);
v_toBind_185_ = lean_ctor_get(v_inst_173_, 1);
lean_inc_n(v_toBind_185_, 2);
lean_dec_ref(v_inst_173_);
v_toPure_186_ = lean_ctor_get(v_toApplicative_184_, 1);
lean_inc(v_toPure_186_);
lean_dec_ref(v_toApplicative_184_);
v___f_187_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_187_, 0, v_toPure_174_);
lean_closure_set(v___f_187_, 1, v_recur_183_);
lean_closure_set(v___f_187_, 2, v___y_175_);
lean_closure_set(v___f_187_, 3, v_acc_181_);
lean_closure_set(v___f_187_, 4, v_toBind_176_);
v___f_188_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__1), 4, 3);
lean_closure_set(v___f_188_, 0, v_toPure_186_);
lean_closure_set(v___f_188_, 1, v_P_177_);
lean_closure_set(v___f_188_, 2, v_toBind_185_);
v___x_189_ = lean_apply_1(v_inst_178_, v_it_180_);
v___x_190_ = lean_apply_4(v_toBind_185_, lean_box(0), lean_box(0), v___x_189_, v___f_188_);
v___x_191_ = lean_apply_4(v_lift_179_, lean_box(0), lean_box(0), v___f_187_, v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__2(lean_object* v_inst_192_, lean_object* v_inst_193_, lean_object* v_P_194_, lean_object* v_inst_195_, lean_object* v_lift_196_, lean_object* v_00_u03b3_197_, lean_object* v_Pl_198_, lean_object* v_it_199_, lean_object* v_init_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_toApplicative_202_; lean_object* v_toBind_203_; lean_object* v_toPure_204_; lean_object* v___f_205_; lean_object* v___x_206_; 
v_toApplicative_202_ = lean_ctor_get(v_inst_192_, 0);
lean_inc_ref(v_toApplicative_202_);
v_toBind_203_ = lean_ctor_get(v_inst_192_, 1);
lean_inc(v_toBind_203_);
lean_dec_ref(v_inst_192_);
v_toPure_204_ = lean_ctor_get(v_toApplicative_202_, 1);
lean_inc(v_toPure_204_);
lean_dec_ref(v_toApplicative_202_);
v___f_205_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__4), 11, 7);
lean_closure_set(v___f_205_, 0, v_inst_193_);
lean_closure_set(v___f_205_, 1, v_toPure_204_);
lean_closure_set(v___f_205_, 2, v___y_201_);
lean_closure_set(v___f_205_, 3, v_toBind_203_);
lean_closure_set(v___f_205_, 4, v_P_194_);
lean_closure_set(v___f_205_, 5, v_inst_195_);
lean_closure_set(v___f_205_, 6, v_lift_196_);
v___x_206_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_205_, v_it_199_, v_init_200_, lean_box(0));
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg(lean_object* v_P_207_, lean_object* v_inst_208_, lean_object* v_inst_209_, lean_object* v_inst_210_){
_start:
{
lean_object* v___f_211_; 
v___f_211_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__2), 10, 4);
lean_closure_set(v___f_211_, 0, v_inst_209_);
lean_closure_set(v___f_211_, 1, v_inst_208_);
lean_closure_set(v___f_211_, 2, v_P_207_);
lean_closure_set(v___f_211_, 3, v_inst_210_);
return v___f_211_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIteratorLoop(lean_object* v_00_u03b1_212_, lean_object* v_m_213_, lean_object* v_00_u03b2_214_, lean_object* v_n_215_, lean_object* v_P_216_, lean_object* v_inst_217_, lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_inst_220_){
_start:
{
lean_object* v___f_221_; 
v___f_221_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__2), 10, 4);
lean_closure_set(v___f_221_, 0, v_inst_218_);
lean_closure_set(v___f_221_, 1, v_inst_217_);
lean_closure_set(v___f_221_, 2, v_P_216_);
lean_closure_set(v___f_221_, 3, v_inst_219_);
return v___f_221_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_TakeWhile_instIteratorLoop___boxed(lean_object* v_00_u03b1_222_, lean_object* v_m_223_, lean_object* v_00_u03b2_224_, lean_object* v_n_225_, lean_object* v_P_226_, lean_object* v_inst_227_, lean_object* v_inst_228_, lean_object* v_inst_229_, lean_object* v_inst_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Std_Iterators_Types_TakeWhile_instIteratorLoop(v_00_u03b1_222_, v_m_223_, v_00_u03b2_224_, v_n_225_, v_P_226_, v_inst_227_, v_inst_228_, v_inst_229_, v_inst_230_);
lean_dec(v_inst_230_);
return v_res_231_;
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

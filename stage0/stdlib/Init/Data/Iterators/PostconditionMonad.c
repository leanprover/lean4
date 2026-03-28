// Lean compiler output
// Module: Init.Data.Iterators.PostconditionMonad
// Imports: public import Init.Control.Lawful.Basic public import Init.Control.Lawful.MonadLift.Basic public import Init.Ext public import Init.NotationExtra import Init.Data.Subtype.Basic import Init.PropLemmas
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
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_lift___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_lift___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Iterators_PostconditionT_lift___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Iterators_PostconditionT_lift___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Iterators_PostconditionT_lift___redArg___closed__0 = (const lean_object*)&l_Std_Iterators_PostconditionT_lift___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_lift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_lift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_attachLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_attachLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_pure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_pure(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftWithProperty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftWithProperty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftWithProperty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftWithProperty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_map___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_map___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_bind___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_bind___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_bind___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Iterators_PostconditionT_bind___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Iterators_PostconditionT_bind___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Iterators_PostconditionT_bind___redArg___closed__0 = (const lean_object*)&l_Std_Iterators_PostconditionT_bind___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_bind___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_pbind___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_pbind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftMap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_run___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_run___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Iterators_PostconditionT_run___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Iterators_PostconditionT_run___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Iterators_PostconditionT_run___redArg___closed__0 = (const lean_object*)&l_Std_Iterators_PostconditionT_run___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instFunctorPostconditionT___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instFunctorPostconditionT___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instFunctorPostconditionT___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instFunctorPostconditionT___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instFunctorPostconditionT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadLiftPostconditionT___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadLiftPostconditionT___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadLiftPostconditionT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_lift___redArg___lam__0(lean_object* v_x_1_){
_start:
{
lean_inc(v_x_1_);
return v_x_1_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_lift___redArg___lam__0___boxed(lean_object* v_x_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l_Std_Iterators_PostconditionT_lift___redArg___lam__0(v_x_2_);
lean_dec(v_x_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_lift___redArg(lean_object* v_inst_5_, lean_object* v_x_6_){
_start:
{
lean_object* v_map_7_; lean_object* v___f_8_; lean_object* v___x_9_; 
v_map_7_ = lean_ctor_get(v_inst_5_, 0);
lean_inc(v_map_7_);
lean_dec_ref(v_inst_5_);
v___f_8_ = ((lean_object*)(l_Std_Iterators_PostconditionT_lift___redArg___closed__0));
v___x_9_ = lean_apply_4(v_map_7_, lean_box(0), lean_box(0), v___f_8_, v_x_6_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_lift(lean_object* v_00_u03b1_10_, lean_object* v_m_11_, lean_object* v_inst_12_, lean_object* v_x_13_){
_start:
{
lean_object* v_map_14_; lean_object* v___f_15_; lean_object* v___x_16_; 
v_map_14_ = lean_ctor_get(v_inst_12_, 0);
lean_inc(v_map_14_);
lean_dec_ref(v_inst_12_);
v___f_15_ = ((lean_object*)(l_Std_Iterators_PostconditionT_lift___redArg___closed__0));
v___x_16_ = lean_apply_4(v_map_14_, lean_box(0), lean_box(0), v___f_15_, v_x_13_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_attachLift___redArg(lean_object* v_inst_17_, lean_object* v_x_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lean_apply_2(v_inst_17_, lean_box(0), v_x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_attachLift(lean_object* v_00_u03b1_20_, lean_object* v_m_21_, lean_object* v_inst_22_, lean_object* v_x_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lean_apply_2(v_inst_22_, lean_box(0), v_x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_pure___redArg(lean_object* v_inst_25_, lean_object* v_a_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_apply_2(v_inst_25_, lean_box(0), v_a_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_pure(lean_object* v_m_28_, lean_object* v_inst_29_, lean_object* v_00_u03b1_30_, lean_object* v_a_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lean_apply_2(v_inst_29_, lean_box(0), v_a_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftWithProperty___redArg(lean_object* v_x_33_){
_start:
{
lean_inc(v_x_33_);
return v_x_33_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftWithProperty___redArg___boxed(lean_object* v_x_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Std_Iterators_PostconditionT_liftWithProperty___redArg(v_x_34_);
lean_dec(v_x_34_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftWithProperty(lean_object* v_00_u03b1_36_, lean_object* v_m_37_, lean_object* v_P_38_, lean_object* v_x_39_){
_start:
{
lean_inc(v_x_39_);
return v_x_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftWithProperty___boxed(lean_object* v_00_u03b1_40_, lean_object* v_m_41_, lean_object* v_P_42_, lean_object* v_x_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Std_Iterators_PostconditionT_liftWithProperty(v_00_u03b1_40_, v_m_41_, v_P_42_, v_x_43_);
lean_dec(v_x_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_map___redArg___lam__0(lean_object* v_f_45_, lean_object* v_a_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lean_apply_1(v_f_45_, v_a_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_map___redArg(lean_object* v_inst_48_, lean_object* v_f_49_, lean_object* v_x_50_){
_start:
{
lean_object* v_map_51_; lean_object* v___f_52_; lean_object* v___x_53_; 
v_map_51_ = lean_ctor_get(v_inst_48_, 0);
lean_inc(v_map_51_);
lean_dec_ref(v_inst_48_);
v___f_52_ = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_52_, 0, v_f_49_);
v___x_53_ = lean_apply_4(v_map_51_, lean_box(0), lean_box(0), v___f_52_, v_x_50_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_map(lean_object* v_m_54_, lean_object* v_inst_55_, lean_object* v_00_u03b1_56_, lean_object* v_00_u03b2_57_, lean_object* v_f_58_, lean_object* v_x_59_){
_start:
{
lean_object* v_map_60_; lean_object* v___f_61_; lean_object* v___x_62_; 
v_map_60_ = lean_ctor_get(v_inst_55_, 0);
lean_inc(v_map_60_);
lean_dec_ref(v_inst_55_);
v___f_61_ = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_61_, 0, v_f_58_);
v___x_62_ = lean_apply_4(v_map_60_, lean_box(0), lean_box(0), v___f_61_, v_x_59_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_bind___redArg___lam__0(lean_object* v_b_63_){
_start:
{
lean_inc(v_b_63_);
return v_b_63_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_bind___redArg___lam__0___boxed(lean_object* v_b_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Std_Iterators_PostconditionT_bind___redArg___lam__0(v_b_64_);
lean_dec(v_b_64_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_bind___redArg___lam__1(lean_object* v_toFunctor_66_, lean_object* v_f_67_, lean_object* v___f_68_, lean_object* v_a_69_){
_start:
{
lean_object* v_map_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v_map_70_ = lean_ctor_get(v_toFunctor_66_, 0);
lean_inc(v_map_70_);
lean_dec_ref(v_toFunctor_66_);
v___x_71_ = lean_apply_1(v_f_67_, v_a_69_);
v___x_72_ = lean_apply_4(v_map_70_, lean_box(0), lean_box(0), v___f_68_, v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_bind___redArg(lean_object* v_inst_74_, lean_object* v_x_75_, lean_object* v_f_76_){
_start:
{
lean_object* v_toApplicative_77_; lean_object* v_toBind_78_; lean_object* v_toFunctor_79_; lean_object* v___f_80_; lean_object* v___f_81_; lean_object* v___x_82_; 
v_toApplicative_77_ = lean_ctor_get(v_inst_74_, 0);
lean_inc_ref(v_toApplicative_77_);
v_toBind_78_ = lean_ctor_get(v_inst_74_, 1);
lean_inc(v_toBind_78_);
lean_dec_ref(v_inst_74_);
v_toFunctor_79_ = lean_ctor_get(v_toApplicative_77_, 0);
lean_inc_ref(v_toFunctor_79_);
lean_dec_ref(v_toApplicative_77_);
v___f_80_ = ((lean_object*)(l_Std_Iterators_PostconditionT_bind___redArg___closed__0));
v___f_81_ = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_bind___redArg___lam__1), 4, 3);
lean_closure_set(v___f_81_, 0, v_toFunctor_79_);
lean_closure_set(v___f_81_, 1, v_f_76_);
lean_closure_set(v___f_81_, 2, v___f_80_);
v___x_82_ = lean_apply_4(v_toBind_78_, lean_box(0), lean_box(0), v_x_75_, v___f_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_bind(lean_object* v_m_83_, lean_object* v_inst_84_, lean_object* v_00_u03b1_85_, lean_object* v_00_u03b2_86_, lean_object* v_x_87_, lean_object* v_f_88_){
_start:
{
lean_object* v_toApplicative_89_; lean_object* v_toBind_90_; lean_object* v_toFunctor_91_; lean_object* v___f_92_; lean_object* v___f_93_; lean_object* v___x_94_; 
v_toApplicative_89_ = lean_ctor_get(v_inst_84_, 0);
lean_inc_ref(v_toApplicative_89_);
v_toBind_90_ = lean_ctor_get(v_inst_84_, 1);
lean_inc(v_toBind_90_);
lean_dec_ref(v_inst_84_);
v_toFunctor_91_ = lean_ctor_get(v_toApplicative_89_, 0);
lean_inc_ref(v_toFunctor_91_);
lean_dec_ref(v_toApplicative_89_);
v___f_92_ = ((lean_object*)(l_Std_Iterators_PostconditionT_bind___redArg___closed__0));
v___f_93_ = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_bind___redArg___lam__1), 4, 3);
lean_closure_set(v___f_93_, 0, v_toFunctor_91_);
lean_closure_set(v___f_93_, 1, v_f_88_);
lean_closure_set(v___f_93_, 2, v___f_92_);
v___x_94_ = lean_apply_4(v_toBind_90_, lean_box(0), lean_box(0), v_x_87_, v___f_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_pbind___redArg(lean_object* v_inst_95_, lean_object* v_x_96_, lean_object* v_f_97_){
_start:
{
lean_object* v_toApplicative_98_; lean_object* v_toBind_99_; lean_object* v_toFunctor_100_; lean_object* v___f_101_; lean_object* v___f_102_; lean_object* v___x_103_; 
v_toApplicative_98_ = lean_ctor_get(v_inst_95_, 0);
lean_inc_ref(v_toApplicative_98_);
v_toBind_99_ = lean_ctor_get(v_inst_95_, 1);
lean_inc(v_toBind_99_);
lean_dec_ref(v_inst_95_);
v_toFunctor_100_ = lean_ctor_get(v_toApplicative_98_, 0);
lean_inc_ref(v_toFunctor_100_);
lean_dec_ref(v_toApplicative_98_);
v___f_101_ = ((lean_object*)(l_Std_Iterators_PostconditionT_bind___redArg___closed__0));
v___f_102_ = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_bind___redArg___lam__1), 4, 3);
lean_closure_set(v___f_102_, 0, v_toFunctor_100_);
lean_closure_set(v___f_102_, 1, v_f_97_);
lean_closure_set(v___f_102_, 2, v___f_101_);
v___x_103_ = lean_apply_4(v_toBind_99_, lean_box(0), lean_box(0), v_x_96_, v___f_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_pbind(lean_object* v_m_104_, lean_object* v_inst_105_, lean_object* v_00_u03b1_106_, lean_object* v_00_u03b2_107_, lean_object* v_x_108_, lean_object* v_f_109_){
_start:
{
lean_object* v_toApplicative_110_; lean_object* v_toBind_111_; lean_object* v_toFunctor_112_; lean_object* v___f_113_; lean_object* v___f_114_; lean_object* v___x_115_; 
v_toApplicative_110_ = lean_ctor_get(v_inst_105_, 0);
lean_inc_ref(v_toApplicative_110_);
v_toBind_111_ = lean_ctor_get(v_inst_105_, 1);
lean_inc(v_toBind_111_);
lean_dec_ref(v_inst_105_);
v_toFunctor_112_ = lean_ctor_get(v_toApplicative_110_, 0);
lean_inc_ref(v_toFunctor_112_);
lean_dec_ref(v_toApplicative_110_);
v___f_113_ = ((lean_object*)(l_Std_Iterators_PostconditionT_bind___redArg___closed__0));
v___f_114_ = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_bind___redArg___lam__1), 4, 3);
lean_closure_set(v___f_114_, 0, v_toFunctor_112_);
lean_closure_set(v___f_114_, 1, v_f_109_);
lean_closure_set(v___f_114_, 2, v___f_113_);
v___x_115_ = lean_apply_4(v_toBind_111_, lean_box(0), lean_box(0), v_x_108_, v___f_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftMap___redArg(lean_object* v_inst_116_, lean_object* v_f_117_, lean_object* v_x_118_){
_start:
{
lean_object* v_toApplicative_119_; lean_object* v_toFunctor_120_; lean_object* v_map_121_; lean_object* v___f_122_; lean_object* v___x_123_; 
v_toApplicative_119_ = lean_ctor_get(v_inst_116_, 0);
lean_inc_ref(v_toApplicative_119_);
lean_dec_ref(v_inst_116_);
v_toFunctor_120_ = lean_ctor_get(v_toApplicative_119_, 0);
lean_inc_ref(v_toFunctor_120_);
lean_dec_ref(v_toApplicative_119_);
v_map_121_ = lean_ctor_get(v_toFunctor_120_, 0);
lean_inc(v_map_121_);
lean_dec_ref(v_toFunctor_120_);
v___f_122_ = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_122_, 0, v_f_117_);
v___x_123_ = lean_apply_4(v_map_121_, lean_box(0), lean_box(0), v___f_122_, v_x_118_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftMap(lean_object* v_m_124_, lean_object* v_inst_125_, lean_object* v_00_u03b1_126_, lean_object* v_00_u03b2_127_, lean_object* v_f_128_, lean_object* v_x_129_){
_start:
{
lean_object* v_toApplicative_130_; lean_object* v_toFunctor_131_; lean_object* v_map_132_; lean_object* v___f_133_; lean_object* v___x_134_; 
v_toApplicative_130_ = lean_ctor_get(v_inst_125_, 0);
lean_inc_ref(v_toApplicative_130_);
lean_dec_ref(v_inst_125_);
v_toFunctor_131_ = lean_ctor_get(v_toApplicative_130_, 0);
lean_inc_ref(v_toFunctor_131_);
lean_dec_ref(v_toApplicative_130_);
v_map_132_ = lean_ctor_get(v_toFunctor_131_, 0);
lean_inc(v_map_132_);
lean_dec_ref(v_toFunctor_131_);
v___f_133_ = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_133_, 0, v_f_128_);
v___x_134_ = lean_apply_4(v_map_132_, lean_box(0), lean_box(0), v___f_133_, v_x_129_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_run___redArg___lam__0(lean_object* v_a_135_){
_start:
{
lean_inc(v_a_135_);
return v_a_135_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_run___redArg___lam__0___boxed(lean_object* v_a_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Std_Iterators_PostconditionT_run___redArg___lam__0(v_a_136_);
lean_dec(v_a_136_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_run___redArg(lean_object* v_inst_139_, lean_object* v_x_140_){
_start:
{
lean_object* v_toApplicative_141_; lean_object* v_toFunctor_142_; lean_object* v_map_143_; lean_object* v___f_144_; lean_object* v___x_145_; 
v_toApplicative_141_ = lean_ctor_get(v_inst_139_, 0);
lean_inc_ref(v_toApplicative_141_);
lean_dec_ref(v_inst_139_);
v_toFunctor_142_ = lean_ctor_get(v_toApplicative_141_, 0);
lean_inc_ref(v_toFunctor_142_);
lean_dec_ref(v_toApplicative_141_);
v_map_143_ = lean_ctor_get(v_toFunctor_142_, 0);
lean_inc(v_map_143_);
lean_dec_ref(v_toFunctor_142_);
v___f_144_ = ((lean_object*)(l_Std_Iterators_PostconditionT_run___redArg___closed__0));
v___x_145_ = lean_apply_4(v_map_143_, lean_box(0), lean_box(0), v___f_144_, v_x_140_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_run(lean_object* v_m_146_, lean_object* v_inst_147_, lean_object* v_00_u03b1_148_, lean_object* v_x_149_){
_start:
{
lean_object* v_toApplicative_150_; lean_object* v_toFunctor_151_; lean_object* v_map_152_; lean_object* v___f_153_; lean_object* v___x_154_; 
v_toApplicative_150_ = lean_ctor_get(v_inst_147_, 0);
lean_inc_ref(v_toApplicative_150_);
lean_dec_ref(v_inst_147_);
v_toFunctor_151_ = lean_ctor_get(v_toApplicative_150_, 0);
lean_inc_ref(v_toFunctor_151_);
lean_dec_ref(v_toApplicative_150_);
v_map_152_ = lean_ctor_get(v_toFunctor_151_, 0);
lean_inc(v_map_152_);
lean_dec_ref(v_toFunctor_151_);
v___f_153_ = ((lean_object*)(l_Std_Iterators_PostconditionT_run___redArg___closed__0));
v___x_154_ = lean_apply_4(v_map_152_, lean_box(0), lean_box(0), v___f_153_, v_x_149_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instFunctorPostconditionT___redArg___lam__0(lean_object* v___y_155_, lean_object* v_a_156_){
_start:
{
lean_inc(v___y_155_);
return v___y_155_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instFunctorPostconditionT___redArg___lam__0___boxed(lean_object* v___y_157_, lean_object* v_a_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Std_Iterators_instFunctorPostconditionT___redArg___lam__0(v___y_157_, v_a_158_);
lean_dec(v_a_158_);
lean_dec(v___y_157_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instFunctorPostconditionT___redArg___lam__1(lean_object* v_inst_160_, lean_object* v_00_u03b1_161_, lean_object* v_00_u03b2_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
lean_object* v_map_165_; lean_object* v___f_166_; lean_object* v___x_167_; 
v_map_165_ = lean_ctor_get(v_inst_160_, 0);
lean_inc(v_map_165_);
lean_dec_ref(v_inst_160_);
v___f_166_ = lean_alloc_closure((void*)(l_Std_Iterators_instFunctorPostconditionT___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_166_, 0, v___y_163_);
v___x_167_ = lean_apply_4(v_map_165_, lean_box(0), lean_box(0), v___f_166_, v___y_164_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instFunctorPostconditionT___redArg(lean_object* v_inst_168_){
_start:
{
lean_object* v___f_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
lean_inc_ref(v_inst_168_);
v___f_169_ = lean_alloc_closure((void*)(l_Std_Iterators_instFunctorPostconditionT___redArg___lam__1), 5, 1);
lean_closure_set(v___f_169_, 0, v_inst_168_);
v___x_170_ = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_map), 6, 2);
lean_closure_set(v___x_170_, 0, lean_box(0));
lean_closure_set(v___x_170_, 1, v_inst_168_);
v___x_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___f_169_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instFunctorPostconditionT(lean_object* v_m_172_, lean_object* v_inst_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_Std_Iterators_instFunctorPostconditionT___redArg(v_inst_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__4(lean_object* v_toFunctor_175_, lean_object* v_y_176_, lean_object* v___f_177_, lean_object* v_a_178_){
_start:
{
lean_object* v_map_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_map_179_ = lean_ctor_get(v_toFunctor_175_, 0);
lean_inc(v_map_179_);
lean_dec_ref(v_toFunctor_175_);
v___x_180_ = lean_box(0);
v___x_181_ = lean_apply_1(v_y_176_, v___x_180_);
v___x_182_ = lean_apply_4(v_map_179_, lean_box(0), lean_box(0), v___f_177_, v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__4___boxed(lean_object* v_toFunctor_183_, lean_object* v_y_184_, lean_object* v___f_185_, lean_object* v_a_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Std_Iterators_instMonadPostconditionT___redArg___lam__4(v_toFunctor_183_, v_y_184_, v___f_185_, v_a_186_);
lean_dec(v_a_186_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__0(lean_object* v_toFunctor_188_, lean_object* v___f_189_, lean_object* v_toBind_190_, lean_object* v_00_u03b1_191_, lean_object* v_00_u03b2_192_, lean_object* v_x_193_, lean_object* v_y_194_){
_start:
{
lean_object* v___f_195_; lean_object* v___x_196_; 
v___f_195_ = lean_alloc_closure((void*)(l_Std_Iterators_instMonadPostconditionT___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_195_, 0, v_toFunctor_188_);
lean_closure_set(v___f_195_, 1, v_y_194_);
lean_closure_set(v___f_195_, 2, v___f_189_);
v___x_196_ = lean_apply_4(v_toBind_190_, lean_box(0), lean_box(0), v_x_193_, v___f_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__1(lean_object* v_toPure_197_, lean_object* v_a_198_, lean_object* v_map_199_, lean_object* v___f_200_, lean_object* v_a_201_){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = lean_apply_2(v_toPure_197_, lean_box(0), v_a_198_);
v___x_203_ = lean_apply_4(v_map_199_, lean_box(0), lean_box(0), v___f_200_, v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__1___boxed(lean_object* v_toPure_204_, lean_object* v_a_205_, lean_object* v_map_206_, lean_object* v___f_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Std_Iterators_instMonadPostconditionT___redArg___lam__1(v_toPure_204_, v_a_205_, v_map_206_, v___f_207_, v_a_208_);
lean_dec(v_a_208_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__2(lean_object* v_toFunctor_210_, lean_object* v_toPure_211_, lean_object* v___f_212_, lean_object* v_y_213_, lean_object* v_toBind_214_, lean_object* v___f_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_map_217_; lean_object* v___f_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v_map_217_ = lean_ctor_get(v_toFunctor_210_, 0);
lean_inc_n(v_map_217_, 2);
lean_dec_ref(v_toFunctor_210_);
v___f_218_ = lean_alloc_closure((void*)(l_Std_Iterators_instMonadPostconditionT___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_218_, 0, v_toPure_211_);
lean_closure_set(v___f_218_, 1, v_a_216_);
lean_closure_set(v___f_218_, 2, v_map_217_);
lean_closure_set(v___f_218_, 3, v___f_212_);
v___x_219_ = lean_box(0);
v___x_220_ = lean_apply_1(v_y_213_, v___x_219_);
v___x_221_ = lean_apply_4(v_toBind_214_, lean_box(0), lean_box(0), v___x_220_, v___f_218_);
v___x_222_ = lean_apply_4(v_map_217_, lean_box(0), lean_box(0), v___f_215_, v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__3(lean_object* v_toFunctor_223_, lean_object* v_toPure_224_, lean_object* v___f_225_, lean_object* v_toBind_226_, lean_object* v___f_227_, lean_object* v_00_u03b1_228_, lean_object* v_00_u03b2_229_, lean_object* v_x_230_, lean_object* v_y_231_){
_start:
{
lean_object* v___f_232_; lean_object* v___x_233_; 
lean_inc(v_toBind_226_);
v___f_232_ = lean_alloc_closure((void*)(l_Std_Iterators_instMonadPostconditionT___redArg___lam__2), 7, 6);
lean_closure_set(v___f_232_, 0, v_toFunctor_223_);
lean_closure_set(v___f_232_, 1, v_toPure_224_);
lean_closure_set(v___f_232_, 2, v___f_225_);
lean_closure_set(v___f_232_, 3, v_y_231_);
lean_closure_set(v___f_232_, 4, v_toBind_226_);
lean_closure_set(v___f_232_, 5, v___f_227_);
v___x_233_ = lean_apply_4(v_toBind_226_, lean_box(0), lean_box(0), v_x_230_, v___f_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__5(lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = lean_apply_1(v_a_234_, v_a_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__6(lean_object* v_toFunctor_237_, lean_object* v_x_238_, lean_object* v___f_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_map_241_; lean_object* v___f_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v_map_241_ = lean_ctor_get(v_toFunctor_237_, 0);
lean_inc_n(v_map_241_, 2);
lean_dec_ref(v_toFunctor_237_);
v___f_242_ = lean_alloc_closure((void*)(l_Std_Iterators_instMonadPostconditionT___redArg___lam__5), 2, 1);
lean_closure_set(v___f_242_, 0, v_a_240_);
v___x_243_ = lean_box(0);
v___x_244_ = lean_apply_1(v_x_238_, v___x_243_);
v___x_245_ = lean_apply_4(v_map_241_, lean_box(0), lean_box(0), v___f_242_, v___x_244_);
v___x_246_ = lean_apply_4(v_map_241_, lean_box(0), lean_box(0), v___f_239_, v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__7(lean_object* v_toFunctor_247_, lean_object* v___f_248_, lean_object* v_toBind_249_, lean_object* v_00_u03b1_250_, lean_object* v_00_u03b2_251_, lean_object* v_f_252_, lean_object* v_x_253_){
_start:
{
lean_object* v___f_254_; lean_object* v___x_255_; 
v___f_254_ = lean_alloc_closure((void*)(l_Std_Iterators_instMonadPostconditionT___redArg___lam__6), 4, 3);
lean_closure_set(v___f_254_, 0, v_toFunctor_247_);
lean_closure_set(v___f_254_, 1, v_x_253_);
lean_closure_set(v___f_254_, 2, v___f_248_);
v___x_255_ = lean_apply_4(v_toBind_249_, lean_box(0), lean_box(0), v_f_252_, v___f_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg(lean_object* v_inst_256_){
_start:
{
lean_object* v_toApplicative_257_; lean_object* v_toBind_258_; lean_object* v_toFunctor_259_; lean_object* v_toPure_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_275_; 
v_toApplicative_257_ = lean_ctor_get(v_inst_256_, 0);
lean_inc_ref(v_toApplicative_257_);
v_toBind_258_ = lean_ctor_get(v_inst_256_, 1);
v_toFunctor_259_ = lean_ctor_get(v_toApplicative_257_, 0);
v_toPure_260_ = lean_ctor_get(v_toApplicative_257_, 1);
v_isSharedCheck_275_ = !lean_is_exclusive(v_toApplicative_257_);
if (v_isSharedCheck_275_ == 0)
{
lean_object* v_unused_276_; lean_object* v_unused_277_; lean_object* v_unused_278_; 
v_unused_276_ = lean_ctor_get(v_toApplicative_257_, 4);
lean_dec(v_unused_276_);
v_unused_277_ = lean_ctor_get(v_toApplicative_257_, 3);
lean_dec(v_unused_277_);
v_unused_278_ = lean_ctor_get(v_toApplicative_257_, 2);
lean_dec(v_unused_278_);
v___x_262_ = v_toApplicative_257_;
v_isShared_263_ = v_isSharedCheck_275_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_toPure_260_);
lean_inc(v_toFunctor_259_);
lean_dec(v_toApplicative_257_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_275_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___f_264_; lean_object* v___f_265_; lean_object* v___f_266_; lean_object* v___f_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_271_; 
v___f_264_ = ((lean_object*)(l_Std_Iterators_PostconditionT_bind___redArg___closed__0));
lean_inc_n(v_toBind_258_, 3);
lean_inc_ref_n(v_toFunctor_259_, 3);
v___f_265_ = lean_alloc_closure((void*)(l_Std_Iterators_instMonadPostconditionT___redArg___lam__0), 7, 3);
lean_closure_set(v___f_265_, 0, v_toFunctor_259_);
lean_closure_set(v___f_265_, 1, v___f_264_);
lean_closure_set(v___f_265_, 2, v_toBind_258_);
lean_inc(v_toPure_260_);
v___f_266_ = lean_alloc_closure((void*)(l_Std_Iterators_instMonadPostconditionT___redArg___lam__3), 9, 5);
lean_closure_set(v___f_266_, 0, v_toFunctor_259_);
lean_closure_set(v___f_266_, 1, v_toPure_260_);
lean_closure_set(v___f_266_, 2, v___f_264_);
lean_closure_set(v___f_266_, 3, v_toBind_258_);
lean_closure_set(v___f_266_, 4, v___f_264_);
v___f_267_ = lean_alloc_closure((void*)(l_Std_Iterators_instMonadPostconditionT___redArg___lam__7), 7, 3);
lean_closure_set(v___f_267_, 0, v_toFunctor_259_);
lean_closure_set(v___f_267_, 1, v___f_264_);
lean_closure_set(v___f_267_, 2, v_toBind_258_);
v___x_268_ = l_Std_Iterators_instFunctorPostconditionT___redArg(v_toFunctor_259_);
v___x_269_ = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_pure), 4, 2);
lean_closure_set(v___x_269_, 0, lean_box(0));
lean_closure_set(v___x_269_, 1, v_toPure_260_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 4, v___f_265_);
lean_ctor_set(v___x_262_, 3, v___f_266_);
lean_ctor_set(v___x_262_, 2, v___f_267_);
lean_ctor_set(v___x_262_, 1, v___x_269_);
lean_ctor_set(v___x_262_, 0, v___x_268_);
v___x_271_ = v___x_262_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_268_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v___x_269_);
lean_ctor_set(v_reuseFailAlloc_274_, 2, v___f_267_);
lean_ctor_set(v_reuseFailAlloc_274_, 3, v___f_266_);
lean_ctor_set(v_reuseFailAlloc_274_, 4, v___f_265_);
v___x_271_ = v_reuseFailAlloc_274_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_bind), 6, 2);
lean_closure_set(v___x_272_, 0, lean_box(0));
lean_closure_set(v___x_272_, 1, v_inst_256_);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_271_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
return v___x_273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT(lean_object* v_m_279_, lean_object* v_inst_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l_Std_Iterators_instMonadPostconditionT___redArg(v_inst_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadLiftPostconditionT___redArg___lam__0(lean_object* v_inst_282_, lean_object* v_00_u03b1_283_, lean_object* v_x_284_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = lean_apply_2(v_inst_282_, lean_box(0), v_x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadLiftPostconditionT___redArg(lean_object* v_inst_286_){
_start:
{
lean_object* v___f_287_; 
v___f_287_ = lean_alloc_closure((void*)(l_Std_Iterators_instMonadLiftPostconditionT___redArg___lam__0), 3, 1);
lean_closure_set(v___f_287_, 0, v_inst_286_);
return v___f_287_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadLiftPostconditionT(lean_object* v_m_288_, lean_object* v_n_289_, lean_object* v_inst_290_){
_start:
{
lean_object* v___f_291_; 
v___f_291_ = lean_alloc_closure((void*)(l_Std_Iterators_instMonadLiftPostconditionT___redArg___lam__0), 3, 1);
lean_closure_set(v___f_291_, 0, v_inst_290_);
return v___f_291_;
}
}
lean_object* runtime_initialize_Init_Control_Lawful_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Lawful_MonadLift_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Subtype_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_PostconditionMonad(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Control_Lawful_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Lawful_MonadLift_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Subtype_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_PostconditionMonad(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Control_Lawful_Basic(uint8_t builtin);
lean_object* initialize_Init_Control_Lawful_MonadLift_Basic(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Init_NotationExtra(uint8_t builtin);
lean_object* initialize_Init_Data_Subtype_Basic(uint8_t builtin);
lean_object* initialize_Init_PropLemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_PostconditionMonad(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Lawful_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Lawful_MonadLift_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Subtype_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_PostconditionMonad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_PostconditionMonad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_PostconditionMonad(builtin);
}
#ifdef __cplusplus
}
#endif

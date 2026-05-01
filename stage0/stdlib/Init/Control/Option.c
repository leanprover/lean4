// Lean compiler output
// Module: Init.Control.Option
// Imports: public import Init.Data.Option.Basic public import Init.Control.MonadAttach
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
lean_object* l_Option_isSome___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instToBoolOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_isSome___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instToBoolOption___closed__0 = (const lean_object*)&l_instToBoolOption___closed__0_value;
LEAN_EXPORT lean_object* l_instToBoolOption(lean_object*);
LEAN_EXPORT lean_object* l_OptionT_run___redArg(lean_object*);
LEAN_EXPORT lean_object* l_OptionT_run___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_OptionT_run(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_run___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_mk___redArg(lean_object*);
LEAN_EXPORT lean_object* l_OptionT_mk___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_OptionT_mk(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_mk___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_bind___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_bind___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_pure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_pure(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instInhabitedOfPure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instInhabitedOfPure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_orElse___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_orElse___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_orElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_fail___redArg(lean_object*);
LEAN_EXPORT lean_object* l_OptionT_fail(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instAlternative___redArg(lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instAlternative(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_lift___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_lift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_lift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonadLift___redArg(lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonadLift(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_OptionT_instMonadFunctor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_OptionT_instMonadFunctor___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_OptionT_instMonadFunctor___closed__0 = (const lean_object*)&l_OptionT_instMonadFunctor___closed__0_value;
LEAN_EXPORT lean_object* l_OptionT_instMonadFunctor(lean_object*);
LEAN_EXPORT lean_object* l_OptionT_tryCatch___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_tryCatch___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_tryCatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOfPUnit___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOfPUnit___redArg(lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOfPUnit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOf___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOf___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOf___redArg(lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonadAttach___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonadAttach___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_OptionT_instMonadAttach___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_OptionT_instMonadAttach___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_OptionT_instMonadAttach___redArg___closed__0 = (const lean_object*)&l_OptionT_instMonadAttach___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_OptionT_instMonadAttach___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonadAttach(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instMonadControlOptionTOfMonad___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadControlOptionTOfMonad___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadControlOptionTOfMonad___redArg___closed__0 = (const lean_object*)&l_instMonadControlOptionTOfMonad___redArg___closed__0_value;
static const lean_closure_object l_instMonadControlOptionTOfMonad___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadControlOptionTOfMonad___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadControlOptionTOfMonad___redArg___closed__1 = (const lean_object*)&l_instMonadControlOptionTOfMonad___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToBoolOption(lean_object* v_00_u03b1_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = ((lean_object*)(l_instToBoolOption___closed__0));
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_OptionT_run___redArg(lean_object* v_x_4_){
_start:
{
lean_inc(v_x_4_);
return v_x_4_;
}
}
LEAN_EXPORT lean_object* l_OptionT_run___redArg___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_OptionT_run___redArg(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_OptionT_run(lean_object* v_m_7_, lean_object* v_00_u03b1_8_, lean_object* v_x_9_){
_start:
{
lean_inc(v_x_9_);
return v_x_9_;
}
}
LEAN_EXPORT lean_object* l_OptionT_run___boxed(lean_object* v_m_10_, lean_object* v_00_u03b1_11_, lean_object* v_x_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_OptionT_run(v_m_10_, v_00_u03b1_11_, v_x_12_);
lean_dec(v_x_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_OptionT_mk___redArg(lean_object* v_x_14_){
_start:
{
lean_inc(v_x_14_);
return v_x_14_;
}
}
LEAN_EXPORT lean_object* l_OptionT_mk___redArg___boxed(lean_object* v_x_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_OptionT_mk___redArg(v_x_15_);
lean_dec(v_x_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_OptionT_mk(lean_object* v_m_17_, lean_object* v_00_u03b1_18_, lean_object* v_x_19_){
_start:
{
lean_inc(v_x_19_);
return v_x_19_;
}
}
LEAN_EXPORT lean_object* l_OptionT_mk___boxed(lean_object* v_m_20_, lean_object* v_00_u03b1_21_, lean_object* v_x_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_OptionT_mk(v_m_20_, v_00_u03b1_21_, v_x_22_);
lean_dec(v_x_22_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_OptionT_bind___redArg___lam__0(lean_object* v_toPure_24_, lean_object* v_f_25_, lean_object* v_____do__lift_26_){
_start:
{
if (lean_obj_tag(v_____do__lift_26_) == 0)
{
lean_object* v___x_27_; lean_object* v___x_28_; 
lean_dec(v_f_25_);
v___x_27_ = lean_box(0);
v___x_28_ = lean_apply_2(v_toPure_24_, lean_box(0), v___x_27_);
return v___x_28_;
}
else
{
lean_object* v_val_29_; lean_object* v___x_30_; 
lean_dec(v_toPure_24_);
v_val_29_ = lean_ctor_get(v_____do__lift_26_, 0);
lean_inc(v_val_29_);
lean_dec_ref(v_____do__lift_26_);
v___x_30_ = lean_apply_1(v_f_25_, v_val_29_);
return v___x_30_;
}
}
}
LEAN_EXPORT lean_object* l_OptionT_bind___redArg(lean_object* v_inst_31_, lean_object* v_x_32_, lean_object* v_f_33_){
_start:
{
lean_object* v_toApplicative_34_; lean_object* v_toBind_35_; lean_object* v_toPure_36_; lean_object* v___f_37_; lean_object* v___x_38_; 
v_toApplicative_34_ = lean_ctor_get(v_inst_31_, 0);
lean_inc_ref(v_toApplicative_34_);
v_toBind_35_ = lean_ctor_get(v_inst_31_, 1);
lean_inc(v_toBind_35_);
lean_dec_ref(v_inst_31_);
v_toPure_36_ = lean_ctor_get(v_toApplicative_34_, 1);
lean_inc(v_toPure_36_);
lean_dec_ref(v_toApplicative_34_);
v___f_37_ = lean_alloc_closure((void*)(l_OptionT_bind___redArg___lam__0), 3, 2);
lean_closure_set(v___f_37_, 0, v_toPure_36_);
lean_closure_set(v___f_37_, 1, v_f_33_);
v___x_38_ = lean_apply_4(v_toBind_35_, lean_box(0), lean_box(0), v_x_32_, v___f_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_OptionT_bind(lean_object* v_m_39_, lean_object* v_inst_40_, lean_object* v_00_u03b1_41_, lean_object* v_00_u03b2_42_, lean_object* v_x_43_, lean_object* v_f_44_){
_start:
{
lean_object* v_toApplicative_45_; lean_object* v_toBind_46_; lean_object* v_toPure_47_; lean_object* v___f_48_; lean_object* v___x_49_; 
v_toApplicative_45_ = lean_ctor_get(v_inst_40_, 0);
lean_inc_ref(v_toApplicative_45_);
v_toBind_46_ = lean_ctor_get(v_inst_40_, 1);
lean_inc(v_toBind_46_);
lean_dec_ref(v_inst_40_);
v_toPure_47_ = lean_ctor_get(v_toApplicative_45_, 1);
lean_inc(v_toPure_47_);
lean_dec_ref(v_toApplicative_45_);
v___f_48_ = lean_alloc_closure((void*)(l_OptionT_bind___redArg___lam__0), 3, 2);
lean_closure_set(v___f_48_, 0, v_toPure_47_);
lean_closure_set(v___f_48_, 1, v_f_44_);
v___x_49_ = lean_apply_4(v_toBind_46_, lean_box(0), lean_box(0), v_x_43_, v___f_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_OptionT_pure___redArg(lean_object* v_inst_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_toApplicative_52_; lean_object* v_toPure_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v_toApplicative_52_ = lean_ctor_get(v_inst_50_, 0);
lean_inc_ref(v_toApplicative_52_);
lean_dec_ref(v_inst_50_);
v_toPure_53_ = lean_ctor_get(v_toApplicative_52_, 1);
lean_inc(v_toPure_53_);
lean_dec_ref(v_toApplicative_52_);
v___x_54_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_54_, 0, v_a_51_);
v___x_55_ = lean_apply_2(v_toPure_53_, lean_box(0), v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_OptionT_pure(lean_object* v_m_56_, lean_object* v_inst_57_, lean_object* v_00_u03b1_58_, lean_object* v_a_59_){
_start:
{
lean_object* v_toApplicative_60_; lean_object* v_toPure_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v_toApplicative_60_ = lean_ctor_get(v_inst_57_, 0);
lean_inc_ref(v_toApplicative_60_);
lean_dec_ref(v_inst_57_);
v_toPure_61_ = lean_ctor_get(v_toApplicative_60_, 1);
lean_inc(v_toPure_61_);
lean_dec_ref(v_toApplicative_60_);
v___x_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_62_, 0, v_a_59_);
v___x_63_ = lean_apply_2(v_toPure_61_, lean_box(0), v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__0(lean_object* v_toPure_64_, lean_object* v_f_65_, lean_object* v_____do__lift_66_){
_start:
{
if (lean_obj_tag(v_____do__lift_66_) == 0)
{
lean_object* v___x_67_; lean_object* v___x_68_; 
lean_dec(v_f_65_);
v___x_67_ = lean_box(0);
v___x_68_ = lean_apply_2(v_toPure_64_, lean_box(0), v___x_67_);
return v___x_68_;
}
else
{
lean_object* v_val_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_78_; 
v_val_69_ = lean_ctor_get(v_____do__lift_66_, 0);
v_isSharedCheck_78_ = !lean_is_exclusive(v_____do__lift_66_);
if (v_isSharedCheck_78_ == 0)
{
v___x_71_ = v_____do__lift_66_;
v_isShared_72_ = v_isSharedCheck_78_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_val_69_);
lean_dec(v_____do__lift_66_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_78_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_73_; lean_object* v___x_75_; 
v___x_73_ = lean_apply_1(v_f_65_, v_val_69_);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 0, v___x_73_);
v___x_75_ = v___x_71_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v___x_73_);
v___x_75_ = v_reuseFailAlloc_77_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
lean_object* v___x_76_; 
v___x_76_ = lean_apply_2(v_toPure_64_, lean_box(0), v___x_75_);
return v___x_76_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__1(lean_object* v_inst_79_, lean_object* v_00_u03b1_80_, lean_object* v_00_u03b2_81_, lean_object* v_f_82_, lean_object* v_x_83_){
_start:
{
lean_object* v_toApplicative_84_; lean_object* v_toBind_85_; lean_object* v_toPure_86_; lean_object* v___f_87_; lean_object* v___x_88_; 
v_toApplicative_84_ = lean_ctor_get(v_inst_79_, 0);
lean_inc_ref(v_toApplicative_84_);
v_toBind_85_ = lean_ctor_get(v_inst_79_, 1);
lean_inc(v_toBind_85_);
lean_dec_ref(v_inst_79_);
v_toPure_86_ = lean_ctor_get(v_toApplicative_84_, 1);
lean_inc(v_toPure_86_);
lean_dec_ref(v_toApplicative_84_);
v___f_87_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__0), 3, 2);
lean_closure_set(v___f_87_, 0, v_toPure_86_);
lean_closure_set(v___f_87_, 1, v_f_82_);
v___x_88_ = lean_apply_4(v_toBind_85_, lean_box(0), lean_box(0), v_x_83_, v___f_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__2(lean_object* v_toPure_89_, lean_object* v___y_90_, lean_object* v_____do__lift_91_){
_start:
{
if (lean_obj_tag(v_____do__lift_91_) == 0)
{
lean_object* v___x_92_; lean_object* v___x_93_; 
lean_dec(v___y_90_);
v___x_92_ = lean_box(0);
v___x_93_ = lean_apply_2(v_toPure_89_, lean_box(0), v___x_92_);
return v___x_93_;
}
else
{
lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_101_; 
v_isSharedCheck_101_ = !lean_is_exclusive(v_____do__lift_91_);
if (v_isSharedCheck_101_ == 0)
{
lean_object* v_unused_102_; 
v_unused_102_ = lean_ctor_get(v_____do__lift_91_, 0);
lean_dec(v_unused_102_);
v___x_95_ = v_____do__lift_91_;
v_isShared_96_ = v_isSharedCheck_101_;
goto v_resetjp_94_;
}
else
{
lean_dec(v_____do__lift_91_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_101_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 0, v___y_90_);
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___y_90_);
v___x_98_ = v_reuseFailAlloc_100_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
lean_object* v___x_99_; 
v___x_99_ = lean_apply_2(v_toPure_89_, lean_box(0), v___x_98_);
return v___x_99_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__3(lean_object* v_inst_103_, lean_object* v_00_u03b1_104_, lean_object* v_00_u03b2_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_toApplicative_108_; lean_object* v_toBind_109_; lean_object* v_toPure_110_; lean_object* v___f_111_; lean_object* v___x_112_; 
v_toApplicative_108_ = lean_ctor_get(v_inst_103_, 0);
lean_inc_ref(v_toApplicative_108_);
v_toBind_109_ = lean_ctor_get(v_inst_103_, 1);
lean_inc(v_toBind_109_);
lean_dec_ref(v_inst_103_);
v_toPure_110_ = lean_ctor_get(v_toApplicative_108_, 1);
lean_inc(v_toPure_110_);
lean_dec_ref(v_toApplicative_108_);
v___f_111_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__2), 3, 2);
lean_closure_set(v___f_111_, 0, v_toPure_110_);
lean_closure_set(v___f_111_, 1, v___y_106_);
v___x_112_ = lean_apply_4(v_toBind_109_, lean_box(0), lean_box(0), v___y_107_, v___f_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__4(lean_object* v_toPure_113_, lean_object* v_val_114_, lean_object* v_____do__lift_115_){
_start:
{
if (lean_obj_tag(v_____do__lift_115_) == 0)
{
lean_object* v___x_116_; lean_object* v___x_117_; 
lean_dec(v_val_114_);
v___x_116_ = lean_box(0);
v___x_117_ = lean_apply_2(v_toPure_113_, lean_box(0), v___x_116_);
return v___x_117_;
}
else
{
lean_object* v_val_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_127_; 
v_val_118_ = lean_ctor_get(v_____do__lift_115_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v_____do__lift_115_);
if (v_isSharedCheck_127_ == 0)
{
v___x_120_ = v_____do__lift_115_;
v_isShared_121_ = v_isSharedCheck_127_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_val_118_);
lean_dec(v_____do__lift_115_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_127_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_122_ = lean_apply_1(v_val_114_, v_val_118_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 0, v___x_122_);
v___x_124_ = v___x_120_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_122_);
v___x_124_ = v_reuseFailAlloc_126_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
lean_object* v___x_125_; 
v___x_125_ = lean_apply_2(v_toPure_113_, lean_box(0), v___x_124_);
return v___x_125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__5(lean_object* v_toPure_128_, lean_object* v_x_129_, lean_object* v_toBind_130_, lean_object* v_____do__lift_131_){
_start:
{
if (lean_obj_tag(v_____do__lift_131_) == 0)
{
lean_object* v___x_132_; lean_object* v___x_133_; 
lean_dec(v_toBind_130_);
lean_dec(v_x_129_);
v___x_132_ = lean_box(0);
v___x_133_ = lean_apply_2(v_toPure_128_, lean_box(0), v___x_132_);
return v___x_133_;
}
else
{
lean_object* v_val_134_; lean_object* v___f_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_val_134_ = lean_ctor_get(v_____do__lift_131_, 0);
lean_inc(v_val_134_);
lean_dec_ref(v_____do__lift_131_);
v___f_135_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__4), 3, 2);
lean_closure_set(v___f_135_, 0, v_toPure_128_);
lean_closure_set(v___f_135_, 1, v_val_134_);
v___x_136_ = lean_box(0);
v___x_137_ = lean_apply_1(v_x_129_, v___x_136_);
v___x_138_ = lean_apply_4(v_toBind_130_, lean_box(0), lean_box(0), v___x_137_, v___f_135_);
return v___x_138_;
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__6(lean_object* v_inst_139_, lean_object* v_00_u03b1_140_, lean_object* v_00_u03b2_141_, lean_object* v_f_142_, lean_object* v_x_143_){
_start:
{
lean_object* v_toApplicative_144_; lean_object* v_toBind_145_; lean_object* v_toPure_146_; lean_object* v___f_147_; lean_object* v___x_148_; 
v_toApplicative_144_ = lean_ctor_get(v_inst_139_, 0);
lean_inc_ref(v_toApplicative_144_);
v_toBind_145_ = lean_ctor_get(v_inst_139_, 1);
lean_inc_n(v_toBind_145_, 2);
lean_dec_ref(v_inst_139_);
v_toPure_146_ = lean_ctor_get(v_toApplicative_144_, 1);
lean_inc(v_toPure_146_);
lean_dec_ref(v_toApplicative_144_);
v___f_147_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__5), 4, 3);
lean_closure_set(v___f_147_, 0, v_toPure_146_);
lean_closure_set(v___f_147_, 1, v_x_143_);
lean_closure_set(v___f_147_, 2, v_toBind_145_);
v___x_148_ = lean_apply_4(v_toBind_145_, lean_box(0), lean_box(0), v_f_142_, v___f_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__7(lean_object* v_toPure_149_, lean_object* v_____do__lift_150_, lean_object* v_____do__lift_151_){
_start:
{
if (lean_obj_tag(v_____do__lift_151_) == 0)
{
lean_object* v___x_152_; lean_object* v___x_153_; 
lean_dec(v_____do__lift_150_);
v___x_152_ = lean_box(0);
v___x_153_ = lean_apply_2(v_toPure_149_, lean_box(0), v___x_152_);
return v___x_153_;
}
else
{
lean_object* v___x_154_; 
v___x_154_ = lean_apply_2(v_toPure_149_, lean_box(0), v_____do__lift_150_);
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__7___boxed(lean_object* v_toPure_155_, lean_object* v_____do__lift_156_, lean_object* v_____do__lift_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_OptionT_instMonad___redArg___lam__7(v_toPure_155_, v_____do__lift_156_, v_____do__lift_157_);
lean_dec(v_____do__lift_157_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__8(lean_object* v_toPure_159_, lean_object* v_y_160_, lean_object* v_toBind_161_, lean_object* v_____do__lift_162_){
_start:
{
if (lean_obj_tag(v_____do__lift_162_) == 0)
{
lean_object* v___x_163_; 
lean_dec(v_toBind_161_);
lean_dec(v_y_160_);
v___x_163_ = lean_apply_2(v_toPure_159_, lean_box(0), v_____do__lift_162_);
return v___x_163_;
}
else
{
lean_object* v___f_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___f_164_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_164_, 0, v_toPure_159_);
lean_closure_set(v___f_164_, 1, v_____do__lift_162_);
v___x_165_ = lean_box(0);
v___x_166_ = lean_apply_1(v_y_160_, v___x_165_);
v___x_167_ = lean_apply_4(v_toBind_161_, lean_box(0), lean_box(0), v___x_166_, v___f_164_);
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__9(lean_object* v_inst_168_, lean_object* v_00_u03b1_169_, lean_object* v_00_u03b2_170_, lean_object* v_x_171_, lean_object* v_y_172_){
_start:
{
lean_object* v_toApplicative_173_; lean_object* v_toBind_174_; lean_object* v_toPure_175_; lean_object* v___f_176_; lean_object* v___x_177_; 
v_toApplicative_173_ = lean_ctor_get(v_inst_168_, 0);
lean_inc_ref(v_toApplicative_173_);
v_toBind_174_ = lean_ctor_get(v_inst_168_, 1);
lean_inc_n(v_toBind_174_, 2);
lean_dec_ref(v_inst_168_);
v_toPure_175_ = lean_ctor_get(v_toApplicative_173_, 1);
lean_inc(v_toPure_175_);
lean_dec_ref(v_toApplicative_173_);
v___f_176_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__8), 4, 3);
lean_closure_set(v___f_176_, 0, v_toPure_175_);
lean_closure_set(v___f_176_, 1, v_y_172_);
lean_closure_set(v___f_176_, 2, v_toBind_174_);
v___x_177_ = lean_apply_4(v_toBind_174_, lean_box(0), lean_box(0), v_x_171_, v___f_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__10(lean_object* v_toPure_178_, lean_object* v_y_179_, lean_object* v_____do__lift_180_){
_start:
{
if (lean_obj_tag(v_____do__lift_180_) == 0)
{
lean_object* v___x_181_; lean_object* v___x_182_; 
lean_dec(v_y_179_);
v___x_181_ = lean_box(0);
v___x_182_ = lean_apply_2(v_toPure_178_, lean_box(0), v___x_181_);
return v___x_182_;
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec(v_toPure_178_);
v___x_183_ = lean_box(0);
v___x_184_ = lean_apply_1(v_y_179_, v___x_183_);
return v___x_184_;
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__10___boxed(lean_object* v_toPure_185_, lean_object* v_y_186_, lean_object* v_____do__lift_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_OptionT_instMonad___redArg___lam__10(v_toPure_185_, v_y_186_, v_____do__lift_187_);
lean_dec(v_____do__lift_187_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__11(lean_object* v_inst_189_, lean_object* v_00_u03b1_190_, lean_object* v_00_u03b2_191_, lean_object* v_x_192_, lean_object* v_y_193_){
_start:
{
lean_object* v_toApplicative_194_; lean_object* v_toBind_195_; lean_object* v_toPure_196_; lean_object* v___f_197_; lean_object* v___x_198_; 
v_toApplicative_194_ = lean_ctor_get(v_inst_189_, 0);
lean_inc_ref(v_toApplicative_194_);
v_toBind_195_ = lean_ctor_get(v_inst_189_, 1);
lean_inc(v_toBind_195_);
lean_dec_ref(v_inst_189_);
v_toPure_196_ = lean_ctor_get(v_toApplicative_194_, 1);
lean_inc(v_toPure_196_);
lean_dec_ref(v_toApplicative_194_);
v___f_197_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__10___boxed), 3, 2);
lean_closure_set(v___f_197_, 0, v_toPure_196_);
lean_closure_set(v___f_197_, 1, v_y_193_);
v___x_198_ = lean_apply_4(v_toBind_195_, lean_box(0), lean_box(0), v_x_192_, v___f_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg(lean_object* v_inst_199_){
_start:
{
lean_object* v___f_200_; lean_object* v___f_201_; lean_object* v___f_202_; lean_object* v___f_203_; lean_object* v___f_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
lean_inc_ref_n(v_inst_199_, 6);
v___f_200_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_200_, 0, v_inst_199_);
v___f_201_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_201_, 0, v_inst_199_);
v___f_202_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_202_, 0, v_inst_199_);
v___f_203_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_203_, 0, v_inst_199_);
v___f_204_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_204_, 0, v_inst_199_);
v___x_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_205_, 0, v___f_200_);
lean_ctor_set(v___x_205_, 1, v___f_201_);
v___x_206_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_206_, 0, lean_box(0));
lean_closure_set(v___x_206_, 1, v_inst_199_);
v___x_207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_207_, 0, v___x_205_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
lean_ctor_set(v___x_207_, 2, v___f_202_);
lean_ctor_set(v___x_207_, 3, v___f_203_);
lean_ctor_set(v___x_207_, 4, v___f_204_);
v___x_208_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_208_, 0, lean_box(0));
lean_closure_set(v___x_208_, 1, v_inst_199_);
v___x_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_207_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad(lean_object* v_m_210_, lean_object* v_inst_211_){
_start:
{
lean_object* v___f_212_; lean_object* v___f_213_; lean_object* v___f_214_; lean_object* v___f_215_; lean_object* v___f_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
lean_inc_ref_n(v_inst_211_, 6);
v___f_212_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_212_, 0, v_inst_211_);
v___f_213_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_213_, 0, v_inst_211_);
v___f_214_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_214_, 0, v_inst_211_);
v___f_215_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_215_, 0, v_inst_211_);
v___f_216_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_216_, 0, v_inst_211_);
v___x_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_217_, 0, v___f_212_);
lean_ctor_set(v___x_217_, 1, v___f_213_);
v___x_218_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_218_, 0, lean_box(0));
lean_closure_set(v___x_218_, 1, v_inst_211_);
v___x_219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_219_, 0, v___x_217_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
lean_ctor_set(v___x_219_, 2, v___f_214_);
lean_ctor_set(v___x_219_, 3, v___f_215_);
lean_ctor_set(v___x_219_, 4, v___f_216_);
v___x_220_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_220_, 0, lean_box(0));
lean_closure_set(v___x_220_, 1, v_inst_211_);
v___x_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_219_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instInhabitedOfPure___redArg(lean_object* v_inst_222_){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = lean_box(0);
v___x_224_ = lean_apply_2(v_inst_222_, lean_box(0), v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instInhabitedOfPure(lean_object* v_00_u03b1_225_, lean_object* v_m_226_, lean_object* v_inst_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_OptionT_instInhabitedOfPure___redArg(v_inst_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_OptionT_orElse___redArg___lam__0(lean_object* v_y_229_, lean_object* v_toPure_230_, lean_object* v_____do__lift_231_){
_start:
{
if (lean_obj_tag(v_____do__lift_231_) == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; 
lean_dec(v_toPure_230_);
v___x_232_ = lean_box(0);
v___x_233_ = lean_apply_1(v_y_229_, v___x_232_);
return v___x_233_;
}
else
{
lean_object* v___x_234_; 
lean_dec(v_y_229_);
v___x_234_ = lean_apply_2(v_toPure_230_, lean_box(0), v_____do__lift_231_);
return v___x_234_;
}
}
}
LEAN_EXPORT lean_object* l_OptionT_orElse___redArg(lean_object* v_inst_235_, lean_object* v_x_236_, lean_object* v_y_237_){
_start:
{
lean_object* v_toApplicative_238_; lean_object* v_toBind_239_; lean_object* v_toPure_240_; lean_object* v___f_241_; lean_object* v___x_242_; 
v_toApplicative_238_ = lean_ctor_get(v_inst_235_, 0);
lean_inc_ref(v_toApplicative_238_);
v_toBind_239_ = lean_ctor_get(v_inst_235_, 1);
lean_inc(v_toBind_239_);
lean_dec_ref(v_inst_235_);
v_toPure_240_ = lean_ctor_get(v_toApplicative_238_, 1);
lean_inc(v_toPure_240_);
lean_dec_ref(v_toApplicative_238_);
v___f_241_ = lean_alloc_closure((void*)(l_OptionT_orElse___redArg___lam__0), 3, 2);
lean_closure_set(v___f_241_, 0, v_y_237_);
lean_closure_set(v___f_241_, 1, v_toPure_240_);
v___x_242_ = lean_apply_4(v_toBind_239_, lean_box(0), lean_box(0), v_x_236_, v___f_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_OptionT_orElse(lean_object* v_m_243_, lean_object* v_inst_244_, lean_object* v_00_u03b1_245_, lean_object* v_x_246_, lean_object* v_y_247_){
_start:
{
lean_object* v_toApplicative_248_; lean_object* v_toBind_249_; lean_object* v_toPure_250_; lean_object* v___f_251_; lean_object* v___x_252_; 
v_toApplicative_248_ = lean_ctor_get(v_inst_244_, 0);
lean_inc_ref(v_toApplicative_248_);
v_toBind_249_ = lean_ctor_get(v_inst_244_, 1);
lean_inc(v_toBind_249_);
lean_dec_ref(v_inst_244_);
v_toPure_250_ = lean_ctor_get(v_toApplicative_248_, 1);
lean_inc(v_toPure_250_);
lean_dec_ref(v_toApplicative_248_);
v___f_251_ = lean_alloc_closure((void*)(l_OptionT_orElse___redArg___lam__0), 3, 2);
lean_closure_set(v___f_251_, 0, v_y_247_);
lean_closure_set(v___f_251_, 1, v_toPure_250_);
v___x_252_ = lean_apply_4(v_toBind_249_, lean_box(0), lean_box(0), v_x_246_, v___f_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_OptionT_fail___redArg(lean_object* v_inst_253_){
_start:
{
lean_object* v_toApplicative_254_; lean_object* v_toPure_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v_toApplicative_254_ = lean_ctor_get(v_inst_253_, 0);
lean_inc_ref(v_toApplicative_254_);
lean_dec_ref(v_inst_253_);
v_toPure_255_ = lean_ctor_get(v_toApplicative_254_, 1);
lean_inc(v_toPure_255_);
lean_dec_ref(v_toApplicative_254_);
v___x_256_ = lean_box(0);
v___x_257_ = lean_apply_2(v_toPure_255_, lean_box(0), v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_OptionT_fail(lean_object* v_m_258_, lean_object* v_inst_259_, lean_object* v_00_u03b1_260_){
_start:
{
lean_object* v_toApplicative_261_; lean_object* v_toPure_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v_toApplicative_261_ = lean_ctor_get(v_inst_259_, 0);
lean_inc_ref(v_toApplicative_261_);
lean_dec_ref(v_inst_259_);
v_toPure_262_ = lean_ctor_get(v_toApplicative_261_, 1);
lean_inc(v_toPure_262_);
lean_dec_ref(v_toApplicative_261_);
v___x_263_ = lean_box(0);
v___x_264_ = lean_apply_2(v_toPure_262_, lean_box(0), v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instAlternative___redArg(lean_object* v_inst_265_){
_start:
{
lean_object* v___f_266_; lean_object* v___f_267_; lean_object* v___f_268_; lean_object* v___f_269_; lean_object* v___f_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
lean_inc_ref_n(v_inst_265_, 7);
v___f_266_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_266_, 0, v_inst_265_);
v___f_267_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_267_, 0, v_inst_265_);
v___f_268_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_268_, 0, v_inst_265_);
v___f_269_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_269_, 0, v_inst_265_);
v___f_270_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_270_, 0, v_inst_265_);
v___x_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_271_, 0, v___f_266_);
lean_ctor_set(v___x_271_, 1, v___f_267_);
v___x_272_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_272_, 0, lean_box(0));
lean_closure_set(v___x_272_, 1, v_inst_265_);
v___x_273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_273_, 0, v___x_271_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
lean_ctor_set(v___x_273_, 2, v___f_268_);
lean_ctor_set(v___x_273_, 3, v___f_269_);
lean_ctor_set(v___x_273_, 4, v___f_270_);
v___x_274_ = lean_alloc_closure((void*)(l_OptionT_fail), 3, 2);
lean_closure_set(v___x_274_, 0, lean_box(0));
lean_closure_set(v___x_274_, 1, v_inst_265_);
v___x_275_ = lean_alloc_closure((void*)(l_OptionT_orElse), 5, 2);
lean_closure_set(v___x_275_, 0, lean_box(0));
lean_closure_set(v___x_275_, 1, v_inst_265_);
v___x_276_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_276_, 0, v___x_273_);
lean_ctor_set(v___x_276_, 1, v___x_274_);
lean_ctor_set(v___x_276_, 2, v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instAlternative(lean_object* v_m_277_, lean_object* v_inst_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_OptionT_instAlternative___redArg(v_inst_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_OptionT_lift___redArg___lam__0(lean_object* v_toPure_280_, lean_object* v_____do__lift_281_){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_282_, 0, v_____do__lift_281_);
v___x_283_ = lean_apply_2(v_toPure_280_, lean_box(0), v___x_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_OptionT_lift___redArg(lean_object* v_inst_284_, lean_object* v_x_285_){
_start:
{
lean_object* v_toApplicative_286_; lean_object* v_toBind_287_; lean_object* v_toPure_288_; lean_object* v___f_289_; lean_object* v___x_290_; 
v_toApplicative_286_ = lean_ctor_get(v_inst_284_, 0);
lean_inc_ref(v_toApplicative_286_);
v_toBind_287_ = lean_ctor_get(v_inst_284_, 1);
lean_inc(v_toBind_287_);
lean_dec_ref(v_inst_284_);
v_toPure_288_ = lean_ctor_get(v_toApplicative_286_, 1);
lean_inc(v_toPure_288_);
lean_dec_ref(v_toApplicative_286_);
v___f_289_ = lean_alloc_closure((void*)(l_OptionT_lift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_289_, 0, v_toPure_288_);
v___x_290_ = lean_apply_4(v_toBind_287_, lean_box(0), lean_box(0), v_x_285_, v___f_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_OptionT_lift(lean_object* v_m_291_, lean_object* v_inst_292_, lean_object* v_00_u03b1_293_, lean_object* v_x_294_){
_start:
{
lean_object* v_toApplicative_295_; lean_object* v_toBind_296_; lean_object* v_toPure_297_; lean_object* v___f_298_; lean_object* v___x_299_; 
v_toApplicative_295_ = lean_ctor_get(v_inst_292_, 0);
lean_inc_ref(v_toApplicative_295_);
v_toBind_296_ = lean_ctor_get(v_inst_292_, 1);
lean_inc(v_toBind_296_);
lean_dec_ref(v_inst_292_);
v_toPure_297_ = lean_ctor_get(v_toApplicative_295_, 1);
lean_inc(v_toPure_297_);
lean_dec_ref(v_toApplicative_295_);
v___f_298_ = lean_alloc_closure((void*)(l_OptionT_lift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_298_, 0, v_toPure_297_);
v___x_299_ = lean_apply_4(v_toBind_296_, lean_box(0), lean_box(0), v_x_294_, v___f_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadLift___redArg(lean_object* v_inst_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(v___x_301_, 0, lean_box(0));
lean_closure_set(v___x_301_, 1, v_inst_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadLift(lean_object* v_m_302_, lean_object* v_inst_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(v___x_304_, 0, lean_box(0));
lean_closure_set(v___x_304_, 1, v_inst_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadFunctor___lam__0(lean_object* v_00_u03b1_305_, lean_object* v_f_306_, lean_object* v_x_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = lean_apply_2(v_f_306_, lean_box(0), v_x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadFunctor(lean_object* v_m_310_){
_start:
{
lean_object* v___f_311_; 
v___f_311_ = ((lean_object*)(l_OptionT_instMonadFunctor___closed__0));
return v___f_311_;
}
}
LEAN_EXPORT lean_object* l_OptionT_tryCatch___redArg___lam__0(lean_object* v_handle_312_, lean_object* v_toPure_313_, lean_object* v_____x_314_){
_start:
{
if (lean_obj_tag(v_____x_314_) == 0)
{
lean_object* v___x_315_; lean_object* v___x_316_; 
lean_dec(v_toPure_313_);
v___x_315_ = lean_box(0);
v___x_316_ = lean_apply_1(v_handle_312_, v___x_315_);
return v___x_316_;
}
else
{
lean_object* v___x_317_; 
lean_dec(v_handle_312_);
v___x_317_ = lean_apply_2(v_toPure_313_, lean_box(0), v_____x_314_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l_OptionT_tryCatch___redArg(lean_object* v_inst_318_, lean_object* v_x_319_, lean_object* v_handle_320_){
_start:
{
lean_object* v_toApplicative_321_; lean_object* v_toBind_322_; lean_object* v_toPure_323_; lean_object* v___f_324_; lean_object* v___x_325_; 
v_toApplicative_321_ = lean_ctor_get(v_inst_318_, 0);
lean_inc_ref(v_toApplicative_321_);
v_toBind_322_ = lean_ctor_get(v_inst_318_, 1);
lean_inc(v_toBind_322_);
lean_dec_ref(v_inst_318_);
v_toPure_323_ = lean_ctor_get(v_toApplicative_321_, 1);
lean_inc(v_toPure_323_);
lean_dec_ref(v_toApplicative_321_);
v___f_324_ = lean_alloc_closure((void*)(l_OptionT_tryCatch___redArg___lam__0), 3, 2);
lean_closure_set(v___f_324_, 0, v_handle_320_);
lean_closure_set(v___f_324_, 1, v_toPure_323_);
v___x_325_ = lean_apply_4(v_toBind_322_, lean_box(0), lean_box(0), v_x_319_, v___f_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_OptionT_tryCatch(lean_object* v_m_326_, lean_object* v_inst_327_, lean_object* v_00_u03b1_328_, lean_object* v_x_329_, lean_object* v_handle_330_){
_start:
{
lean_object* v_toApplicative_331_; lean_object* v_toBind_332_; lean_object* v_toPure_333_; lean_object* v___f_334_; lean_object* v___x_335_; 
v_toApplicative_331_ = lean_ctor_get(v_inst_327_, 0);
lean_inc_ref(v_toApplicative_331_);
v_toBind_332_ = lean_ctor_get(v_inst_327_, 1);
lean_inc(v_toBind_332_);
lean_dec_ref(v_inst_327_);
v_toPure_333_ = lean_ctor_get(v_toApplicative_331_, 1);
lean_inc(v_toPure_333_);
lean_dec_ref(v_toApplicative_331_);
v___f_334_ = lean_alloc_closure((void*)(l_OptionT_tryCatch___redArg___lam__0), 3, 2);
lean_closure_set(v___f_334_, 0, v_handle_330_);
lean_closure_set(v___f_334_, 1, v_toPure_333_);
v___x_335_ = lean_apply_4(v_toBind_332_, lean_box(0), lean_box(0), v_x_329_, v___f_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOfPUnit___redArg___lam__0(lean_object* v_inst_336_, lean_object* v_00_u03b1_337_, lean_object* v_x_338_){
_start:
{
lean_object* v_toApplicative_339_; lean_object* v_toPure_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v_toApplicative_339_ = lean_ctor_get(v_inst_336_, 0);
lean_inc_ref(v_toApplicative_339_);
lean_dec_ref(v_inst_336_);
v_toPure_340_ = lean_ctor_get(v_toApplicative_339_, 1);
lean_inc(v_toPure_340_);
lean_dec_ref(v_toApplicative_339_);
v___x_341_ = lean_box(0);
v___x_342_ = lean_apply_2(v_toPure_340_, lean_box(0), v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOfPUnit___redArg(lean_object* v_inst_343_){
_start:
{
lean_object* v___f_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
lean_inc_ref(v_inst_343_);
v___f_344_ = lean_alloc_closure((void*)(l_OptionT_instMonadExceptOfPUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_344_, 0, v_inst_343_);
v___x_345_ = lean_alloc_closure((void*)(l_OptionT_tryCatch), 5, 2);
lean_closure_set(v___x_345_, 0, lean_box(0));
lean_closure_set(v___x_345_, 1, v_inst_343_);
v___x_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_346_, 0, v___f_344_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOfPUnit(lean_object* v_m_347_, lean_object* v_inst_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_OptionT_instMonadExceptOfPUnit___redArg(v_inst_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOf___redArg___lam__0(lean_object* v_inst_350_, lean_object* v_00_u03b1_351_, lean_object* v_e_352_){
_start:
{
lean_object* v_throw_353_; lean_object* v___x_354_; 
v_throw_353_ = lean_ctor_get(v_inst_350_, 0);
lean_inc(v_throw_353_);
lean_dec_ref(v_inst_350_);
v___x_354_ = lean_apply_2(v_throw_353_, lean_box(0), v_e_352_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOf___redArg___lam__1(lean_object* v_inst_355_, lean_object* v_00_u03b1_356_, lean_object* v_x_357_, lean_object* v_handle_358_){
_start:
{
lean_object* v_tryCatch_359_; lean_object* v___x_360_; 
v_tryCatch_359_ = lean_ctor_get(v_inst_355_, 1);
lean_inc(v_tryCatch_359_);
lean_dec_ref(v_inst_355_);
v___x_360_ = lean_apply_3(v_tryCatch_359_, lean_box(0), v_x_357_, v_handle_358_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOf___redArg(lean_object* v_inst_361_){
_start:
{
lean_object* v___f_362_; lean_object* v___f_363_; lean_object* v___x_364_; 
lean_inc_ref(v_inst_361_);
v___f_362_ = lean_alloc_closure((void*)(l_OptionT_instMonadExceptOf___redArg___lam__0), 3, 1);
lean_closure_set(v___f_362_, 0, v_inst_361_);
v___f_363_ = lean_alloc_closure((void*)(l_OptionT_instMonadExceptOf___redArg___lam__1), 4, 1);
lean_closure_set(v___f_363_, 0, v_inst_361_);
v___x_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_364_, 0, v___f_362_);
lean_ctor_set(v___x_364_, 1, v___f_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOf(lean_object* v_m_365_, lean_object* v_00_u03b5_366_, lean_object* v_inst_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_OptionT_instMonadExceptOf___redArg(v_inst_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadAttach___redArg___lam__0(lean_object* v_x_369_){
_start:
{
if (lean_obj_tag(v_x_369_) == 0)
{
lean_object* v___x_370_; 
v___x_370_ = lean_box(0);
return v___x_370_;
}
else
{
lean_object* v_val_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
v_val_371_ = lean_ctor_get(v_x_369_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v_x_369_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v_x_369_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_val_371_);
lean_dec(v_x_369_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_val_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadAttach___redArg___lam__1(lean_object* v_toFunctor_379_, lean_object* v_inst_380_, lean_object* v___f_381_, lean_object* v_00_u03b1_382_, lean_object* v_x_383_){
_start:
{
lean_object* v_map_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v_map_384_ = lean_ctor_get(v_toFunctor_379_, 0);
lean_inc(v_map_384_);
lean_dec_ref(v_toFunctor_379_);
v___x_385_ = lean_apply_2(v_inst_380_, lean_box(0), v_x_383_);
v___x_386_ = lean_apply_4(v_map_384_, lean_box(0), lean_box(0), v___f_381_, v___x_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadAttach___redArg(lean_object* v_inst_388_, lean_object* v_inst_389_){
_start:
{
lean_object* v_toApplicative_390_; lean_object* v_toFunctor_391_; lean_object* v___f_392_; lean_object* v___f_393_; 
v_toApplicative_390_ = lean_ctor_get(v_inst_388_, 0);
lean_inc_ref(v_toApplicative_390_);
lean_dec_ref(v_inst_388_);
v_toFunctor_391_ = lean_ctor_get(v_toApplicative_390_, 0);
lean_inc_ref(v_toFunctor_391_);
lean_dec_ref(v_toApplicative_390_);
v___f_392_ = ((lean_object*)(l_OptionT_instMonadAttach___redArg___closed__0));
v___f_393_ = lean_alloc_closure((void*)(l_OptionT_instMonadAttach___redArg___lam__1), 5, 3);
lean_closure_set(v___f_393_, 0, v_toFunctor_391_);
lean_closure_set(v___f_393_, 1, v_inst_389_);
lean_closure_set(v___f_393_, 2, v___f_392_);
return v___f_393_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadAttach(lean_object* v_m_394_, lean_object* v_inst_395_, lean_object* v_inst_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_OptionT_instMonadAttach___redArg(v_inst_395_, v_inst_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg___lam__0(lean_object* v_00_u03b2_398_, lean_object* v_x_399_){
_start:
{
lean_inc(v_x_399_);
return v_x_399_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg___lam__0___boxed(lean_object* v_00_u03b2_400_, lean_object* v_x_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_instMonadControlOptionTOfMonad___redArg___lam__0(v_00_u03b2_400_, v_x_401_);
lean_dec(v_x_401_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg___lam__2(lean_object* v_inst_403_, lean_object* v___f_404_, lean_object* v_00_u03b1_405_, lean_object* v_f_406_){
_start:
{
lean_object* v_toApplicative_407_; lean_object* v_toBind_408_; lean_object* v_toPure_409_; lean_object* v___x_410_; lean_object* v___f_411_; lean_object* v___x_412_; 
v_toApplicative_407_ = lean_ctor_get(v_inst_403_, 0);
lean_inc_ref(v_toApplicative_407_);
v_toBind_408_ = lean_ctor_get(v_inst_403_, 1);
lean_inc(v_toBind_408_);
lean_dec_ref(v_inst_403_);
v_toPure_409_ = lean_ctor_get(v_toApplicative_407_, 1);
lean_inc(v_toPure_409_);
lean_dec_ref(v_toApplicative_407_);
v___x_410_ = lean_apply_1(v_f_406_, v___f_404_);
v___f_411_ = lean_alloc_closure((void*)(l_OptionT_lift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_411_, 0, v_toPure_409_);
v___x_412_ = lean_apply_4(v_toBind_408_, lean_box(0), lean_box(0), v___x_410_, v___f_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg___lam__1(lean_object* v_00_u03b1_413_, lean_object* v_x_414_){
_start:
{
lean_inc(v_x_414_);
return v_x_414_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg___lam__1___boxed(lean_object* v_00_u03b1_415_, lean_object* v_x_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_instMonadControlOptionTOfMonad___redArg___lam__1(v_00_u03b1_415_, v_x_416_);
lean_dec(v_x_416_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg(lean_object* v_inst_420_){
_start:
{
lean_object* v___f_421_; lean_object* v___f_422_; lean_object* v___f_423_; lean_object* v___x_424_; 
v___f_421_ = ((lean_object*)(l_instMonadControlOptionTOfMonad___redArg___closed__0));
v___f_422_ = lean_alloc_closure((void*)(l_instMonadControlOptionTOfMonad___redArg___lam__2), 4, 2);
lean_closure_set(v___f_422_, 0, v_inst_420_);
lean_closure_set(v___f_422_, 1, v___f_421_);
v___f_423_ = ((lean_object*)(l_instMonadControlOptionTOfMonad___redArg___closed__1));
v___x_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_424_, 0, v___f_422_);
lean_ctor_set(v___x_424_, 1, v___f_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad(lean_object* v_m_425_, lean_object* v_inst_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_instMonadControlOptionTOfMonad___redArg(v_inst_426_);
return v___x_427_;
}
}
lean_object* runtime_initialize_Init_Data_Option_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_MonadAttach(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Control_Option(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Option_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_MonadAttach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Control_Option(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Option_Basic(uint8_t builtin);
lean_object* initialize_Init_Control_MonadAttach(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Control_Option(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Option_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_MonadAttach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Option(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Control_Option(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Control_Option(builtin);
}
#ifdef __cplusplus
}
#endif

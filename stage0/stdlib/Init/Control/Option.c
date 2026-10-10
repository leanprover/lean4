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
static const lean_closure_object l_instToBoolOption___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_isSome___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instToBoolOption___redArg___closed__0 = (const lean_object*)&l_instToBoolOption___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instToBoolOption___redArg();
LEAN_EXPORT lean_object* l_instToBoolOption___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_OptionT_instMonadFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_OptionT_instMonadFunctor___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_OptionT_instMonadFunctor___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_OptionT_instMonadFunctor___redArg___closed__0 = (const lean_object*)&l_OptionT_instMonadFunctor___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_OptionT_instMonadFunctor___redArg();
LEAN_EXPORT lean_object* l_OptionT_instMonadFunctor___redArg___boxed(lean_object*);
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
lean_object* l_instToBoolOption___redArg(){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = ((lean_object*)(l_instToBoolOption___redArg___closed__0));
return v___x_3_;
}
}
LEAN_EXPORT void l_instToBoolOption___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4_;
v_res_4_ = l_instToBoolOption___redArg();
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_instToBoolOption___redArg___boxed(lean_object* v___dummy_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_instToBoolOption___redArg();
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_instToBoolOption(lean_object* v_00_u03b1_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = ((lean_object*)(l_instToBoolOption___redArg___closed__0));
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_OptionT_run___redArg(lean_object* v_x_9_){
_start:
{
lean_inc(v_x_9_);
return v_x_9_;
}
}
LEAN_EXPORT lean_object* l_OptionT_run___redArg___boxed(lean_object* v_x_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_OptionT_run___redArg(v_x_10_);
lean_dec(v_x_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_OptionT_run(lean_object* v_m_12_, lean_object* v_00_u03b1_13_, lean_object* v_x_14_){
_start:
{
lean_inc(v_x_14_);
return v_x_14_;
}
}
LEAN_EXPORT lean_object* l_OptionT_run___boxed(lean_object* v_m_15_, lean_object* v_00_u03b1_16_, lean_object* v_x_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_OptionT_run(v_m_15_, v_00_u03b1_16_, v_x_17_);
lean_dec(v_x_17_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_OptionT_mk___redArg(lean_object* v_x_19_){
_start:
{
lean_inc(v_x_19_);
return v_x_19_;
}
}
LEAN_EXPORT lean_object* l_OptionT_mk___redArg___boxed(lean_object* v_x_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_OptionT_mk___redArg(v_x_20_);
lean_dec(v_x_20_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_OptionT_mk(lean_object* v_m_22_, lean_object* v_00_u03b1_23_, lean_object* v_x_24_){
_start:
{
lean_inc(v_x_24_);
return v_x_24_;
}
}
LEAN_EXPORT lean_object* l_OptionT_mk___boxed(lean_object* v_m_25_, lean_object* v_00_u03b1_26_, lean_object* v_x_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_OptionT_mk(v_m_25_, v_00_u03b1_26_, v_x_27_);
lean_dec(v_x_27_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_OptionT_bind___redArg___lam__0(lean_object* v_toPure_29_, lean_object* v_f_30_, lean_object* v_____do__lift_31_){
_start:
{
if (lean_obj_tag(v_____do__lift_31_) == 0)
{
lean_object* v___x_32_; lean_object* v___x_33_; 
lean_dec(v_f_30_);
v___x_32_ = lean_box(0);
v___x_33_ = lean_apply_2(v_toPure_29_, lean_box(0), v___x_32_);
return v___x_33_;
}
else
{
lean_object* v_val_34_; lean_object* v___x_35_; 
lean_dec(v_toPure_29_);
v_val_34_ = lean_ctor_get(v_____do__lift_31_, 0);
lean_inc(v_val_34_);
lean_dec_ref_known(v_____do__lift_31_, 1);
v___x_35_ = lean_apply_1(v_f_30_, v_val_34_);
return v___x_35_;
}
}
}
LEAN_EXPORT lean_object* l_OptionT_bind___redArg(lean_object* v_inst_36_, lean_object* v_x_37_, lean_object* v_f_38_){
_start:
{
lean_object* v_toApplicative_39_; lean_object* v_toBind_40_; lean_object* v_toPure_41_; lean_object* v___f_42_; lean_object* v___x_43_; 
v_toApplicative_39_ = lean_ctor_get(v_inst_36_, 0);
lean_inc_ref(v_toApplicative_39_);
v_toBind_40_ = lean_ctor_get(v_inst_36_, 1);
lean_inc(v_toBind_40_);
lean_dec_ref(v_inst_36_);
v_toPure_41_ = lean_ctor_get(v_toApplicative_39_, 1);
lean_inc(v_toPure_41_);
lean_dec_ref(v_toApplicative_39_);
v___f_42_ = lean_alloc_closure((void*)(l_OptionT_bind___redArg___lam__0), 3, 2);
lean_closure_set(v___f_42_, 0, v_toPure_41_);
lean_closure_set(v___f_42_, 1, v_f_38_);
v___x_43_ = lean_apply_4(v_toBind_40_, lean_box(0), lean_box(0), v_x_37_, v___f_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_OptionT_bind(lean_object* v_m_44_, lean_object* v_inst_45_, lean_object* v_00_u03b1_46_, lean_object* v_00_u03b2_47_, lean_object* v_x_48_, lean_object* v_f_49_){
_start:
{
lean_object* v_toApplicative_50_; lean_object* v_toBind_51_; lean_object* v_toPure_52_; lean_object* v___f_53_; lean_object* v___x_54_; 
v_toApplicative_50_ = lean_ctor_get(v_inst_45_, 0);
lean_inc_ref(v_toApplicative_50_);
v_toBind_51_ = lean_ctor_get(v_inst_45_, 1);
lean_inc(v_toBind_51_);
lean_dec_ref(v_inst_45_);
v_toPure_52_ = lean_ctor_get(v_toApplicative_50_, 1);
lean_inc(v_toPure_52_);
lean_dec_ref(v_toApplicative_50_);
v___f_53_ = lean_alloc_closure((void*)(l_OptionT_bind___redArg___lam__0), 3, 2);
lean_closure_set(v___f_53_, 0, v_toPure_52_);
lean_closure_set(v___f_53_, 1, v_f_49_);
v___x_54_ = lean_apply_4(v_toBind_51_, lean_box(0), lean_box(0), v_x_48_, v___f_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_OptionT_pure___redArg(lean_object* v_inst_55_, lean_object* v_a_56_){
_start:
{
lean_object* v_toApplicative_57_; lean_object* v_toPure_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v_toApplicative_57_ = lean_ctor_get(v_inst_55_, 0);
lean_inc_ref(v_toApplicative_57_);
lean_dec_ref(v_inst_55_);
v_toPure_58_ = lean_ctor_get(v_toApplicative_57_, 1);
lean_inc(v_toPure_58_);
lean_dec_ref(v_toApplicative_57_);
v___x_59_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_59_, 0, v_a_56_);
v___x_60_ = lean_apply_2(v_toPure_58_, lean_box(0), v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_OptionT_pure(lean_object* v_m_61_, lean_object* v_inst_62_, lean_object* v_00_u03b1_63_, lean_object* v_a_64_){
_start:
{
lean_object* v_toApplicative_65_; lean_object* v_toPure_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v_toApplicative_65_ = lean_ctor_get(v_inst_62_, 0);
lean_inc_ref(v_toApplicative_65_);
lean_dec_ref(v_inst_62_);
v_toPure_66_ = lean_ctor_get(v_toApplicative_65_, 1);
lean_inc(v_toPure_66_);
lean_dec_ref(v_toApplicative_65_);
v___x_67_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_67_, 0, v_a_64_);
v___x_68_ = lean_apply_2(v_toPure_66_, lean_box(0), v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__0(lean_object* v_toPure_69_, lean_object* v_f_70_, lean_object* v_____do__lift_71_){
_start:
{
if (lean_obj_tag(v_____do__lift_71_) == 0)
{
lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec(v_f_70_);
v___x_72_ = lean_box(0);
v___x_73_ = lean_apply_2(v_toPure_69_, lean_box(0), v___x_72_);
return v___x_73_;
}
else
{
lean_object* v_val_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_83_; 
v_val_74_ = lean_ctor_get(v_____do__lift_71_, 0);
v_isSharedCheck_83_ = !lean_is_exclusive(v_____do__lift_71_);
if (v_isSharedCheck_83_ == 0)
{
v___x_76_ = v_____do__lift_71_;
v_isShared_77_ = v_isSharedCheck_83_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_val_74_);
lean_dec(v_____do__lift_71_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_83_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_78_; lean_object* v___x_80_; 
v___x_78_ = lean_apply_1(v_f_70_, v_val_74_);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 0, v___x_78_);
v___x_80_ = v___x_76_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v___x_78_);
v___x_80_ = v_reuseFailAlloc_82_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
lean_object* v___x_81_; 
v___x_81_ = lean_apply_2(v_toPure_69_, lean_box(0), v___x_80_);
return v___x_81_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__1(lean_object* v_inst_84_, lean_object* v_00_u03b1_85_, lean_object* v_00_u03b2_86_, lean_object* v_f_87_, lean_object* v_x_88_){
_start:
{
lean_object* v_toApplicative_89_; lean_object* v_toBind_90_; lean_object* v_toPure_91_; lean_object* v___f_92_; lean_object* v___x_93_; 
v_toApplicative_89_ = lean_ctor_get(v_inst_84_, 0);
lean_inc_ref(v_toApplicative_89_);
v_toBind_90_ = lean_ctor_get(v_inst_84_, 1);
lean_inc(v_toBind_90_);
lean_dec_ref(v_inst_84_);
v_toPure_91_ = lean_ctor_get(v_toApplicative_89_, 1);
lean_inc(v_toPure_91_);
lean_dec_ref(v_toApplicative_89_);
v___f_92_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__0), 3, 2);
lean_closure_set(v___f_92_, 0, v_toPure_91_);
lean_closure_set(v___f_92_, 1, v_f_87_);
v___x_93_ = lean_apply_4(v_toBind_90_, lean_box(0), lean_box(0), v_x_88_, v___f_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__2(lean_object* v_toPure_94_, lean_object* v___y_95_, lean_object* v_____do__lift_96_){
_start:
{
if (lean_obj_tag(v_____do__lift_96_) == 0)
{
lean_object* v___x_97_; lean_object* v___x_98_; 
lean_dec(v___y_95_);
v___x_97_ = lean_box(0);
v___x_98_ = lean_apply_2(v_toPure_94_, lean_box(0), v___x_97_);
return v___x_98_;
}
else
{
lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_106_; 
v_isSharedCheck_106_ = !lean_is_exclusive(v_____do__lift_96_);
if (v_isSharedCheck_106_ == 0)
{
lean_object* v_unused_107_; 
v_unused_107_ = lean_ctor_get(v_____do__lift_96_, 0);
lean_dec(v_unused_107_);
v___x_100_ = v_____do__lift_96_;
v_isShared_101_ = v_isSharedCheck_106_;
goto v_resetjp_99_;
}
else
{
lean_dec(v_____do__lift_96_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_106_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_103_; 
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 0, v___y_95_);
v___x_103_ = v___x_100_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___y_95_);
v___x_103_ = v_reuseFailAlloc_105_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
lean_object* v___x_104_; 
v___x_104_ = lean_apply_2(v_toPure_94_, lean_box(0), v___x_103_);
return v___x_104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__3(lean_object* v_inst_108_, lean_object* v_00_u03b1_109_, lean_object* v_00_u03b2_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v_toApplicative_113_; lean_object* v_toBind_114_; lean_object* v_toPure_115_; lean_object* v___f_116_; lean_object* v___x_117_; 
v_toApplicative_113_ = lean_ctor_get(v_inst_108_, 0);
lean_inc_ref(v_toApplicative_113_);
v_toBind_114_ = lean_ctor_get(v_inst_108_, 1);
lean_inc(v_toBind_114_);
lean_dec_ref(v_inst_108_);
v_toPure_115_ = lean_ctor_get(v_toApplicative_113_, 1);
lean_inc(v_toPure_115_);
lean_dec_ref(v_toApplicative_113_);
v___f_116_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__2), 3, 2);
lean_closure_set(v___f_116_, 0, v_toPure_115_);
lean_closure_set(v___f_116_, 1, v___y_111_);
v___x_117_ = lean_apply_4(v_toBind_114_, lean_box(0), lean_box(0), v___y_112_, v___f_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__4(lean_object* v_toPure_118_, lean_object* v_val_119_, lean_object* v_____do__lift_120_){
_start:
{
if (lean_obj_tag(v_____do__lift_120_) == 0)
{
lean_object* v___x_121_; lean_object* v___x_122_; 
lean_dec(v_val_119_);
v___x_121_ = lean_box(0);
v___x_122_ = lean_apply_2(v_toPure_118_, lean_box(0), v___x_121_);
return v___x_122_;
}
else
{
lean_object* v_val_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_132_; 
v_val_123_ = lean_ctor_get(v_____do__lift_120_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v_____do__lift_120_);
if (v_isSharedCheck_132_ == 0)
{
v___x_125_ = v_____do__lift_120_;
v_isShared_126_ = v_isSharedCheck_132_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_val_123_);
lean_dec(v_____do__lift_120_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_132_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_127_ = lean_apply_1(v_val_119_, v_val_123_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_127_);
v___x_129_ = v___x_125_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_127_);
v___x_129_ = v_reuseFailAlloc_131_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
lean_object* v___x_130_; 
v___x_130_ = lean_apply_2(v_toPure_118_, lean_box(0), v___x_129_);
return v___x_130_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__5(lean_object* v_toPure_133_, lean_object* v_x_134_, lean_object* v_toBind_135_, lean_object* v_____do__lift_136_){
_start:
{
if (lean_obj_tag(v_____do__lift_136_) == 0)
{
lean_object* v___x_137_; lean_object* v___x_138_; 
lean_dec(v_toBind_135_);
lean_dec(v_x_134_);
v___x_137_ = lean_box(0);
v___x_138_ = lean_apply_2(v_toPure_133_, lean_box(0), v___x_137_);
return v___x_138_;
}
else
{
lean_object* v_val_139_; lean_object* v___f_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v_val_139_ = lean_ctor_get(v_____do__lift_136_, 0);
lean_inc(v_val_139_);
lean_dec_ref_known(v_____do__lift_136_, 1);
v___f_140_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__4), 3, 2);
lean_closure_set(v___f_140_, 0, v_toPure_133_);
lean_closure_set(v___f_140_, 1, v_val_139_);
v___x_141_ = lean_box(0);
v___x_142_ = lean_apply_1(v_x_134_, v___x_141_);
v___x_143_ = lean_apply_4(v_toBind_135_, lean_box(0), lean_box(0), v___x_142_, v___f_140_);
return v___x_143_;
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__6(lean_object* v_inst_144_, lean_object* v_00_u03b1_145_, lean_object* v_00_u03b2_146_, lean_object* v_f_147_, lean_object* v_x_148_){
_start:
{
lean_object* v_toApplicative_149_; lean_object* v_toBind_150_; lean_object* v_toPure_151_; lean_object* v___f_152_; lean_object* v___x_153_; 
v_toApplicative_149_ = lean_ctor_get(v_inst_144_, 0);
lean_inc_ref(v_toApplicative_149_);
v_toBind_150_ = lean_ctor_get(v_inst_144_, 1);
lean_inc_n(v_toBind_150_, 2);
lean_dec_ref(v_inst_144_);
v_toPure_151_ = lean_ctor_get(v_toApplicative_149_, 1);
lean_inc(v_toPure_151_);
lean_dec_ref(v_toApplicative_149_);
v___f_152_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__5), 4, 3);
lean_closure_set(v___f_152_, 0, v_toPure_151_);
lean_closure_set(v___f_152_, 1, v_x_148_);
lean_closure_set(v___f_152_, 2, v_toBind_150_);
v___x_153_ = lean_apply_4(v_toBind_150_, lean_box(0), lean_box(0), v_f_147_, v___f_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__7(lean_object* v_toPure_154_, lean_object* v_____do__lift_155_, lean_object* v_____do__lift_156_){
_start:
{
if (lean_obj_tag(v_____do__lift_156_) == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec(v_____do__lift_155_);
v___x_157_ = lean_box(0);
v___x_158_ = lean_apply_2(v_toPure_154_, lean_box(0), v___x_157_);
return v___x_158_;
}
else
{
lean_object* v___x_159_; 
v___x_159_ = lean_apply_2(v_toPure_154_, lean_box(0), v_____do__lift_155_);
return v___x_159_;
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__7___boxed(lean_object* v_toPure_160_, lean_object* v_____do__lift_161_, lean_object* v_____do__lift_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_OptionT_instMonad___redArg___lam__7(v_toPure_160_, v_____do__lift_161_, v_____do__lift_162_);
lean_dec(v_____do__lift_162_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__8(lean_object* v_toPure_164_, lean_object* v_y_165_, lean_object* v_toBind_166_, lean_object* v_____do__lift_167_){
_start:
{
if (lean_obj_tag(v_____do__lift_167_) == 0)
{
lean_object* v___x_168_; 
lean_dec(v_toBind_166_);
lean_dec(v_y_165_);
v___x_168_ = lean_apply_2(v_toPure_164_, lean_box(0), v_____do__lift_167_);
return v___x_168_;
}
else
{
lean_object* v___f_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___f_169_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_169_, 0, v_toPure_164_);
lean_closure_set(v___f_169_, 1, v_____do__lift_167_);
v___x_170_ = lean_box(0);
v___x_171_ = lean_apply_1(v_y_165_, v___x_170_);
v___x_172_ = lean_apply_4(v_toBind_166_, lean_box(0), lean_box(0), v___x_171_, v___f_169_);
return v___x_172_;
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__9(lean_object* v_inst_173_, lean_object* v_00_u03b1_174_, lean_object* v_00_u03b2_175_, lean_object* v_x_176_, lean_object* v_y_177_){
_start:
{
lean_object* v_toApplicative_178_; lean_object* v_toBind_179_; lean_object* v_toPure_180_; lean_object* v___f_181_; lean_object* v___x_182_; 
v_toApplicative_178_ = lean_ctor_get(v_inst_173_, 0);
lean_inc_ref(v_toApplicative_178_);
v_toBind_179_ = lean_ctor_get(v_inst_173_, 1);
lean_inc_n(v_toBind_179_, 2);
lean_dec_ref(v_inst_173_);
v_toPure_180_ = lean_ctor_get(v_toApplicative_178_, 1);
lean_inc(v_toPure_180_);
lean_dec_ref(v_toApplicative_178_);
v___f_181_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__8), 4, 3);
lean_closure_set(v___f_181_, 0, v_toPure_180_);
lean_closure_set(v___f_181_, 1, v_y_177_);
lean_closure_set(v___f_181_, 2, v_toBind_179_);
v___x_182_ = lean_apply_4(v_toBind_179_, lean_box(0), lean_box(0), v_x_176_, v___f_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__10(lean_object* v_toPure_183_, lean_object* v_y_184_, lean_object* v_____do__lift_185_){
_start:
{
if (lean_obj_tag(v_____do__lift_185_) == 0)
{
lean_object* v___x_186_; lean_object* v___x_187_; 
lean_dec(v_y_184_);
v___x_186_ = lean_box(0);
v___x_187_ = lean_apply_2(v_toPure_183_, lean_box(0), v___x_186_);
return v___x_187_;
}
else
{
lean_object* v___x_188_; lean_object* v___x_189_; 
lean_dec(v_toPure_183_);
v___x_188_ = lean_box(0);
v___x_189_ = lean_apply_1(v_y_184_, v___x_188_);
return v___x_189_;
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__10___boxed(lean_object* v_toPure_190_, lean_object* v_y_191_, lean_object* v_____do__lift_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_OptionT_instMonad___redArg___lam__10(v_toPure_190_, v_y_191_, v_____do__lift_192_);
lean_dec(v_____do__lift_192_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__11(lean_object* v_inst_194_, lean_object* v_00_u03b1_195_, lean_object* v_00_u03b2_196_, lean_object* v_x_197_, lean_object* v_y_198_){
_start:
{
lean_object* v_toApplicative_199_; lean_object* v_toBind_200_; lean_object* v_toPure_201_; lean_object* v___f_202_; lean_object* v___x_203_; 
v_toApplicative_199_ = lean_ctor_get(v_inst_194_, 0);
lean_inc_ref(v_toApplicative_199_);
v_toBind_200_ = lean_ctor_get(v_inst_194_, 1);
lean_inc(v_toBind_200_);
lean_dec_ref(v_inst_194_);
v_toPure_201_ = lean_ctor_get(v_toApplicative_199_, 1);
lean_inc(v_toPure_201_);
lean_dec_ref(v_toApplicative_199_);
v___f_202_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__10___boxed), 3, 2);
lean_closure_set(v___f_202_, 0, v_toPure_201_);
lean_closure_set(v___f_202_, 1, v_y_198_);
v___x_203_ = lean_apply_4(v_toBind_200_, lean_box(0), lean_box(0), v_x_197_, v___f_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg(lean_object* v_inst_204_){
_start:
{
lean_object* v___f_205_; lean_object* v___f_206_; lean_object* v___f_207_; lean_object* v___f_208_; lean_object* v___f_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
lean_inc_ref_n(v_inst_204_, 6);
v___f_205_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_205_, 0, v_inst_204_);
v___f_206_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_206_, 0, v_inst_204_);
v___f_207_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_207_, 0, v_inst_204_);
v___f_208_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_208_, 0, v_inst_204_);
v___f_209_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_209_, 0, v_inst_204_);
v___x_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_210_, 0, v___f_205_);
lean_ctor_set(v___x_210_, 1, v___f_206_);
v___x_211_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_211_, 0, lean_box(0));
lean_closure_set(v___x_211_, 1, v_inst_204_);
v___x_212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_212_, 0, v___x_210_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
lean_ctor_set(v___x_212_, 2, v___f_207_);
lean_ctor_set(v___x_212_, 3, v___f_208_);
lean_ctor_set(v___x_212_, 4, v___f_209_);
v___x_213_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_213_, 0, lean_box(0));
lean_closure_set(v___x_213_, 1, v_inst_204_);
v___x_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_212_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad(lean_object* v_m_215_, lean_object* v_inst_216_){
_start:
{
lean_object* v___f_217_; lean_object* v___f_218_; lean_object* v___f_219_; lean_object* v___f_220_; lean_object* v___f_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
lean_inc_ref_n(v_inst_216_, 6);
v___f_217_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_217_, 0, v_inst_216_);
v___f_218_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_218_, 0, v_inst_216_);
v___f_219_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_219_, 0, v_inst_216_);
v___f_220_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_220_, 0, v_inst_216_);
v___f_221_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_221_, 0, v_inst_216_);
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v___f_217_);
lean_ctor_set(v___x_222_, 1, v___f_218_);
v___x_223_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_223_, 0, lean_box(0));
lean_closure_set(v___x_223_, 1, v_inst_216_);
v___x_224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_224_, 0, v___x_222_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
lean_ctor_set(v___x_224_, 2, v___f_219_);
lean_ctor_set(v___x_224_, 3, v___f_220_);
lean_ctor_set(v___x_224_, 4, v___f_221_);
v___x_225_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_225_, 0, lean_box(0));
lean_closure_set(v___x_225_, 1, v_inst_216_);
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_224_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instInhabitedOfPure___redArg(lean_object* v_inst_227_){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_box(0);
v___x_229_ = lean_apply_2(v_inst_227_, lean_box(0), v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instInhabitedOfPure(lean_object* v_00_u03b1_230_, lean_object* v_m_231_, lean_object* v_inst_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_OptionT_instInhabitedOfPure___redArg(v_inst_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_OptionT_orElse___redArg___lam__0(lean_object* v_y_234_, lean_object* v_toPure_235_, lean_object* v_____do__lift_236_){
_start:
{
if (lean_obj_tag(v_____do__lift_236_) == 0)
{
lean_object* v___x_237_; lean_object* v___x_238_; 
lean_dec(v_toPure_235_);
v___x_237_ = lean_box(0);
v___x_238_ = lean_apply_1(v_y_234_, v___x_237_);
return v___x_238_;
}
else
{
lean_object* v___x_239_; 
lean_dec(v_y_234_);
v___x_239_ = lean_apply_2(v_toPure_235_, lean_box(0), v_____do__lift_236_);
return v___x_239_;
}
}
}
LEAN_EXPORT lean_object* l_OptionT_orElse___redArg(lean_object* v_inst_240_, lean_object* v_x_241_, lean_object* v_y_242_){
_start:
{
lean_object* v_toApplicative_243_; lean_object* v_toBind_244_; lean_object* v_toPure_245_; lean_object* v___f_246_; lean_object* v___x_247_; 
v_toApplicative_243_ = lean_ctor_get(v_inst_240_, 0);
lean_inc_ref(v_toApplicative_243_);
v_toBind_244_ = lean_ctor_get(v_inst_240_, 1);
lean_inc(v_toBind_244_);
lean_dec_ref(v_inst_240_);
v_toPure_245_ = lean_ctor_get(v_toApplicative_243_, 1);
lean_inc(v_toPure_245_);
lean_dec_ref(v_toApplicative_243_);
v___f_246_ = lean_alloc_closure((void*)(l_OptionT_orElse___redArg___lam__0), 3, 2);
lean_closure_set(v___f_246_, 0, v_y_242_);
lean_closure_set(v___f_246_, 1, v_toPure_245_);
v___x_247_ = lean_apply_4(v_toBind_244_, lean_box(0), lean_box(0), v_x_241_, v___f_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_OptionT_orElse(lean_object* v_m_248_, lean_object* v_inst_249_, lean_object* v_00_u03b1_250_, lean_object* v_x_251_, lean_object* v_y_252_){
_start:
{
lean_object* v_toApplicative_253_; lean_object* v_toBind_254_; lean_object* v_toPure_255_; lean_object* v___f_256_; lean_object* v___x_257_; 
v_toApplicative_253_ = lean_ctor_get(v_inst_249_, 0);
lean_inc_ref(v_toApplicative_253_);
v_toBind_254_ = lean_ctor_get(v_inst_249_, 1);
lean_inc(v_toBind_254_);
lean_dec_ref(v_inst_249_);
v_toPure_255_ = lean_ctor_get(v_toApplicative_253_, 1);
lean_inc(v_toPure_255_);
lean_dec_ref(v_toApplicative_253_);
v___f_256_ = lean_alloc_closure((void*)(l_OptionT_orElse___redArg___lam__0), 3, 2);
lean_closure_set(v___f_256_, 0, v_y_252_);
lean_closure_set(v___f_256_, 1, v_toPure_255_);
v___x_257_ = lean_apply_4(v_toBind_254_, lean_box(0), lean_box(0), v_x_251_, v___f_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_OptionT_fail___redArg(lean_object* v_inst_258_){
_start:
{
lean_object* v_toApplicative_259_; lean_object* v_toPure_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_toApplicative_259_ = lean_ctor_get(v_inst_258_, 0);
lean_inc_ref(v_toApplicative_259_);
lean_dec_ref(v_inst_258_);
v_toPure_260_ = lean_ctor_get(v_toApplicative_259_, 1);
lean_inc(v_toPure_260_);
lean_dec_ref(v_toApplicative_259_);
v___x_261_ = lean_box(0);
v___x_262_ = lean_apply_2(v_toPure_260_, lean_box(0), v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_OptionT_fail(lean_object* v_m_263_, lean_object* v_inst_264_, lean_object* v_00_u03b1_265_){
_start:
{
lean_object* v_toApplicative_266_; lean_object* v_toPure_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v_toApplicative_266_ = lean_ctor_get(v_inst_264_, 0);
lean_inc_ref(v_toApplicative_266_);
lean_dec_ref(v_inst_264_);
v_toPure_267_ = lean_ctor_get(v_toApplicative_266_, 1);
lean_inc(v_toPure_267_);
lean_dec_ref(v_toApplicative_266_);
v___x_268_ = lean_box(0);
v___x_269_ = lean_apply_2(v_toPure_267_, lean_box(0), v___x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instAlternative___redArg(lean_object* v_inst_270_){
_start:
{
lean_object* v___f_271_; lean_object* v___f_272_; lean_object* v___f_273_; lean_object* v___f_274_; lean_object* v___f_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
lean_inc_ref_n(v_inst_270_, 7);
v___f_271_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_271_, 0, v_inst_270_);
v___f_272_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_272_, 0, v_inst_270_);
v___f_273_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_273_, 0, v_inst_270_);
v___f_274_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_274_, 0, v_inst_270_);
v___f_275_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_275_, 0, v_inst_270_);
v___x_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_276_, 0, v___f_271_);
lean_ctor_set(v___x_276_, 1, v___f_272_);
v___x_277_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_277_, 0, lean_box(0));
lean_closure_set(v___x_277_, 1, v_inst_270_);
v___x_278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_278_, 0, v___x_276_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
lean_ctor_set(v___x_278_, 2, v___f_273_);
lean_ctor_set(v___x_278_, 3, v___f_274_);
lean_ctor_set(v___x_278_, 4, v___f_275_);
v___x_279_ = lean_alloc_closure((void*)(l_OptionT_fail), 3, 2);
lean_closure_set(v___x_279_, 0, lean_box(0));
lean_closure_set(v___x_279_, 1, v_inst_270_);
v___x_280_ = lean_alloc_closure((void*)(l_OptionT_orElse), 5, 2);
lean_closure_set(v___x_280_, 0, lean_box(0));
lean_closure_set(v___x_280_, 1, v_inst_270_);
v___x_281_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_281_, 0, v___x_278_);
lean_ctor_set(v___x_281_, 1, v___x_279_);
lean_ctor_set(v___x_281_, 2, v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instAlternative(lean_object* v_m_282_, lean_object* v_inst_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_OptionT_instAlternative___redArg(v_inst_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_OptionT_lift___redArg___lam__0(lean_object* v_toPure_285_, lean_object* v_____do__lift_286_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_287_, 0, v_____do__lift_286_);
v___x_288_ = lean_apply_2(v_toPure_285_, lean_box(0), v___x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_OptionT_lift___redArg(lean_object* v_inst_289_, lean_object* v_x_290_){
_start:
{
lean_object* v_toApplicative_291_; lean_object* v_toBind_292_; lean_object* v_toPure_293_; lean_object* v___f_294_; lean_object* v___x_295_; 
v_toApplicative_291_ = lean_ctor_get(v_inst_289_, 0);
lean_inc_ref(v_toApplicative_291_);
v_toBind_292_ = lean_ctor_get(v_inst_289_, 1);
lean_inc(v_toBind_292_);
lean_dec_ref(v_inst_289_);
v_toPure_293_ = lean_ctor_get(v_toApplicative_291_, 1);
lean_inc(v_toPure_293_);
lean_dec_ref(v_toApplicative_291_);
v___f_294_ = lean_alloc_closure((void*)(l_OptionT_lift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_294_, 0, v_toPure_293_);
v___x_295_ = lean_apply_4(v_toBind_292_, lean_box(0), lean_box(0), v_x_290_, v___f_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_OptionT_lift(lean_object* v_m_296_, lean_object* v_inst_297_, lean_object* v_00_u03b1_298_, lean_object* v_x_299_){
_start:
{
lean_object* v_toApplicative_300_; lean_object* v_toBind_301_; lean_object* v_toPure_302_; lean_object* v___f_303_; lean_object* v___x_304_; 
v_toApplicative_300_ = lean_ctor_get(v_inst_297_, 0);
lean_inc_ref(v_toApplicative_300_);
v_toBind_301_ = lean_ctor_get(v_inst_297_, 1);
lean_inc(v_toBind_301_);
lean_dec_ref(v_inst_297_);
v_toPure_302_ = lean_ctor_get(v_toApplicative_300_, 1);
lean_inc(v_toPure_302_);
lean_dec_ref(v_toApplicative_300_);
v___f_303_ = lean_alloc_closure((void*)(l_OptionT_lift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_303_, 0, v_toPure_302_);
v___x_304_ = lean_apply_4(v_toBind_301_, lean_box(0), lean_box(0), v_x_299_, v___f_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadLift___redArg(lean_object* v_inst_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(v___x_306_, 0, lean_box(0));
lean_closure_set(v___x_306_, 1, v_inst_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadLift(lean_object* v_m_307_, lean_object* v_inst_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(v___x_309_, 0, lean_box(0));
lean_closure_set(v___x_309_, 1, v_inst_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadFunctor___redArg___lam__0(lean_object* v_00_u03b1_310_, lean_object* v_f_311_, lean_object* v_x_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = lean_apply_2(v_f_311_, lean_box(0), v_x_312_);
return v___x_313_;
}
}
lean_object* l_OptionT_instMonadFunctor___redArg(){
_start:
{
lean_object* v___f_316_; 
v___f_316_ = ((lean_object*)(l_OptionT_instMonadFunctor___redArg___closed__0));
return v___f_316_;
}
}
LEAN_EXPORT void l_OptionT_instMonadFunctor___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_317_;
v_res_317_ = l_OptionT_instMonadFunctor___redArg();
stack->m_obj
 = v_res_317_;
}
LEAN_EXPORT lean_object* l_OptionT_instMonadFunctor___redArg___boxed(lean_object* v___dummy_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_OptionT_instMonadFunctor___redArg();
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadFunctor(lean_object* v_m_320_){
_start:
{
lean_object* v___f_321_; 
v___f_321_ = ((lean_object*)(l_OptionT_instMonadFunctor___redArg___closed__0));
return v___f_321_;
}
}
LEAN_EXPORT lean_object* l_OptionT_tryCatch___redArg___lam__0(lean_object* v_handle_322_, lean_object* v_toPure_323_, lean_object* v_____x_324_){
_start:
{
if (lean_obj_tag(v_____x_324_) == 0)
{
lean_object* v___x_325_; lean_object* v___x_326_; 
lean_dec(v_toPure_323_);
v___x_325_ = lean_box(0);
v___x_326_ = lean_apply_1(v_handle_322_, v___x_325_);
return v___x_326_;
}
else
{
lean_object* v___x_327_; 
lean_dec(v_handle_322_);
v___x_327_ = lean_apply_2(v_toPure_323_, lean_box(0), v_____x_324_);
return v___x_327_;
}
}
}
LEAN_EXPORT lean_object* l_OptionT_tryCatch___redArg(lean_object* v_inst_328_, lean_object* v_x_329_, lean_object* v_handle_330_){
_start:
{
lean_object* v_toApplicative_331_; lean_object* v_toBind_332_; lean_object* v_toPure_333_; lean_object* v___f_334_; lean_object* v___x_335_; 
v_toApplicative_331_ = lean_ctor_get(v_inst_328_, 0);
lean_inc_ref(v_toApplicative_331_);
v_toBind_332_ = lean_ctor_get(v_inst_328_, 1);
lean_inc(v_toBind_332_);
lean_dec_ref(v_inst_328_);
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
LEAN_EXPORT lean_object* l_OptionT_tryCatch(lean_object* v_m_336_, lean_object* v_inst_337_, lean_object* v_00_u03b1_338_, lean_object* v_x_339_, lean_object* v_handle_340_){
_start:
{
lean_object* v_toApplicative_341_; lean_object* v_toBind_342_; lean_object* v_toPure_343_; lean_object* v___f_344_; lean_object* v___x_345_; 
v_toApplicative_341_ = lean_ctor_get(v_inst_337_, 0);
lean_inc_ref(v_toApplicative_341_);
v_toBind_342_ = lean_ctor_get(v_inst_337_, 1);
lean_inc(v_toBind_342_);
lean_dec_ref(v_inst_337_);
v_toPure_343_ = lean_ctor_get(v_toApplicative_341_, 1);
lean_inc(v_toPure_343_);
lean_dec_ref(v_toApplicative_341_);
v___f_344_ = lean_alloc_closure((void*)(l_OptionT_tryCatch___redArg___lam__0), 3, 2);
lean_closure_set(v___f_344_, 0, v_handle_340_);
lean_closure_set(v___f_344_, 1, v_toPure_343_);
v___x_345_ = lean_apply_4(v_toBind_342_, lean_box(0), lean_box(0), v_x_339_, v___f_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOfPUnit___redArg___lam__0(lean_object* v_inst_346_, lean_object* v_00_u03b1_347_, lean_object* v_x_348_){
_start:
{
lean_object* v_toApplicative_349_; lean_object* v_toPure_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_toApplicative_349_ = lean_ctor_get(v_inst_346_, 0);
lean_inc_ref(v_toApplicative_349_);
lean_dec_ref(v_inst_346_);
v_toPure_350_ = lean_ctor_get(v_toApplicative_349_, 1);
lean_inc(v_toPure_350_);
lean_dec_ref(v_toApplicative_349_);
v___x_351_ = lean_box(0);
v___x_352_ = lean_apply_2(v_toPure_350_, lean_box(0), v___x_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOfPUnit___redArg(lean_object* v_inst_353_){
_start:
{
lean_object* v___f_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
lean_inc_ref(v_inst_353_);
v___f_354_ = lean_alloc_closure((void*)(l_OptionT_instMonadExceptOfPUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_354_, 0, v_inst_353_);
v___x_355_ = lean_alloc_closure((void*)(l_OptionT_tryCatch), 5, 2);
lean_closure_set(v___x_355_, 0, lean_box(0));
lean_closure_set(v___x_355_, 1, v_inst_353_);
v___x_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_356_, 0, v___f_354_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOfPUnit(lean_object* v_m_357_, lean_object* v_inst_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_OptionT_instMonadExceptOfPUnit___redArg(v_inst_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOf___redArg___lam__0(lean_object* v_inst_360_, lean_object* v_00_u03b1_361_, lean_object* v_e_362_){
_start:
{
lean_object* v_throw_363_; lean_object* v___x_364_; 
v_throw_363_ = lean_ctor_get(v_inst_360_, 0);
lean_inc(v_throw_363_);
lean_dec_ref(v_inst_360_);
v___x_364_ = lean_apply_2(v_throw_363_, lean_box(0), v_e_362_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOf___redArg___lam__1(lean_object* v_inst_365_, lean_object* v_00_u03b1_366_, lean_object* v_x_367_, lean_object* v_handle_368_){
_start:
{
lean_object* v_tryCatch_369_; lean_object* v___x_370_; 
v_tryCatch_369_ = lean_ctor_get(v_inst_365_, 1);
lean_inc(v_tryCatch_369_);
lean_dec_ref(v_inst_365_);
v___x_370_ = lean_apply_3(v_tryCatch_369_, lean_box(0), v_x_367_, v_handle_368_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOf___redArg(lean_object* v_inst_371_){
_start:
{
lean_object* v___f_372_; lean_object* v___f_373_; lean_object* v___x_374_; 
lean_inc_ref(v_inst_371_);
v___f_372_ = lean_alloc_closure((void*)(l_OptionT_instMonadExceptOf___redArg___lam__0), 3, 1);
lean_closure_set(v___f_372_, 0, v_inst_371_);
v___f_373_ = lean_alloc_closure((void*)(l_OptionT_instMonadExceptOf___redArg___lam__1), 4, 1);
lean_closure_set(v___f_373_, 0, v_inst_371_);
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v___f_372_);
lean_ctor_set(v___x_374_, 1, v___f_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOf(lean_object* v_m_375_, lean_object* v_00_u03b5_376_, lean_object* v_inst_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_OptionT_instMonadExceptOf___redArg(v_inst_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadAttach___redArg___lam__0(lean_object* v_x_379_){
_start:
{
if (lean_obj_tag(v_x_379_) == 0)
{
lean_object* v___x_380_; 
v___x_380_ = lean_box(0);
return v___x_380_;
}
else
{
lean_object* v_val_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
v_val_381_ = lean_ctor_get(v_x_379_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v_x_379_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v_x_379_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_val_381_);
lean_dec(v_x_379_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_val_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadAttach___redArg___lam__1(lean_object* v_toFunctor_389_, lean_object* v_inst_390_, lean_object* v___f_391_, lean_object* v_00_u03b1_392_, lean_object* v_x_393_){
_start:
{
lean_object* v_map_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v_map_394_ = lean_ctor_get(v_toFunctor_389_, 0);
lean_inc(v_map_394_);
lean_dec_ref(v_toFunctor_389_);
v___x_395_ = lean_apply_2(v_inst_390_, lean_box(0), v_x_393_);
v___x_396_ = lean_apply_4(v_map_394_, lean_box(0), lean_box(0), v___f_391_, v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadAttach___redArg(lean_object* v_inst_398_, lean_object* v_inst_399_){
_start:
{
lean_object* v_toApplicative_400_; lean_object* v_toFunctor_401_; lean_object* v___f_402_; lean_object* v___f_403_; 
v_toApplicative_400_ = lean_ctor_get(v_inst_398_, 0);
lean_inc_ref(v_toApplicative_400_);
lean_dec_ref(v_inst_398_);
v_toFunctor_401_ = lean_ctor_get(v_toApplicative_400_, 0);
lean_inc_ref(v_toFunctor_401_);
lean_dec_ref(v_toApplicative_400_);
v___f_402_ = ((lean_object*)(l_OptionT_instMonadAttach___redArg___closed__0));
v___f_403_ = lean_alloc_closure((void*)(l_OptionT_instMonadAttach___redArg___lam__1), 5, 3);
lean_closure_set(v___f_403_, 0, v_toFunctor_401_);
lean_closure_set(v___f_403_, 1, v_inst_399_);
lean_closure_set(v___f_403_, 2, v___f_402_);
return v___f_403_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadAttach(lean_object* v_m_404_, lean_object* v_inst_405_, lean_object* v_inst_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_OptionT_instMonadAttach___redArg(v_inst_405_, v_inst_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg___lam__0(lean_object* v_00_u03b2_408_, lean_object* v_x_409_){
_start:
{
lean_inc(v_x_409_);
return v_x_409_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg___lam__0___boxed(lean_object* v_00_u03b2_410_, lean_object* v_x_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_instMonadControlOptionTOfMonad___redArg___lam__0(v_00_u03b2_410_, v_x_411_);
lean_dec(v_x_411_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg___lam__2(lean_object* v_inst_413_, lean_object* v___f_414_, lean_object* v_00_u03b1_415_, lean_object* v_f_416_){
_start:
{
lean_object* v_toApplicative_417_; lean_object* v_toBind_418_; lean_object* v_toPure_419_; lean_object* v___x_420_; lean_object* v___f_421_; lean_object* v___x_422_; 
v_toApplicative_417_ = lean_ctor_get(v_inst_413_, 0);
lean_inc_ref(v_toApplicative_417_);
v_toBind_418_ = lean_ctor_get(v_inst_413_, 1);
lean_inc(v_toBind_418_);
lean_dec_ref(v_inst_413_);
v_toPure_419_ = lean_ctor_get(v_toApplicative_417_, 1);
lean_inc(v_toPure_419_);
lean_dec_ref(v_toApplicative_417_);
v___x_420_ = lean_apply_1(v_f_416_, v___f_414_);
v___f_421_ = lean_alloc_closure((void*)(l_OptionT_lift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_421_, 0, v_toPure_419_);
v___x_422_ = lean_apply_4(v_toBind_418_, lean_box(0), lean_box(0), v___x_420_, v___f_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg___lam__1(lean_object* v_00_u03b1_423_, lean_object* v_x_424_){
_start:
{
lean_inc(v_x_424_);
return v_x_424_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg___lam__1___boxed(lean_object* v_00_u03b1_425_, lean_object* v_x_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_instMonadControlOptionTOfMonad___redArg___lam__1(v_00_u03b1_425_, v_x_426_);
lean_dec(v_x_426_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg(lean_object* v_inst_430_){
_start:
{
lean_object* v___f_431_; lean_object* v___f_432_; lean_object* v___f_433_; lean_object* v___x_434_; 
v___f_431_ = ((lean_object*)(l_instMonadControlOptionTOfMonad___redArg___closed__0));
v___f_432_ = lean_alloc_closure((void*)(l_instMonadControlOptionTOfMonad___redArg___lam__2), 4, 2);
lean_closure_set(v___f_432_, 0, v_inst_430_);
lean_closure_set(v___f_432_, 1, v___f_431_);
v___f_433_ = ((lean_object*)(l_instMonadControlOptionTOfMonad___redArg___closed__1));
v___x_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_434_, 0, v___f_432_);
lean_ctor_set(v___x_434_, 1, v___f_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad(lean_object* v_m_435_, lean_object* v_inst_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_instMonadControlOptionTOfMonad___redArg(v_inst_436_);
return v___x_437_;
}
}
lean_object* runtime_initialize_Init_Data_Option_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_MonadAttach(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Control_Option(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

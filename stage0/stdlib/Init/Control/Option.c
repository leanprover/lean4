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
LEAN_EXPORT lean_object* l_instToBoolOption___redArg(){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = ((lean_object*)(l_instToBoolOption___redArg___closed__0));
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_instToBoolOption___redArg___boxed(lean_object* v___dummy_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_instToBoolOption___redArg();
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_instToBoolOption(lean_object* v_00_u03b1_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = ((lean_object*)(l_instToBoolOption___redArg___closed__0));
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_OptionT_run___redArg(lean_object* v_x_8_){
_start:
{
lean_inc(v_x_8_);
return v_x_8_;
}
}
LEAN_EXPORT lean_object* l_OptionT_run___redArg___boxed(lean_object* v_x_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_OptionT_run___redArg(v_x_9_);
lean_dec(v_x_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_OptionT_run(lean_object* v_m_11_, lean_object* v_00_u03b1_12_, lean_object* v_x_13_){
_start:
{
lean_inc(v_x_13_);
return v_x_13_;
}
}
LEAN_EXPORT lean_object* l_OptionT_run___boxed(lean_object* v_m_14_, lean_object* v_00_u03b1_15_, lean_object* v_x_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_OptionT_run(v_m_14_, v_00_u03b1_15_, v_x_16_);
lean_dec(v_x_16_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_OptionT_mk___redArg(lean_object* v_x_18_){
_start:
{
lean_inc(v_x_18_);
return v_x_18_;
}
}
LEAN_EXPORT lean_object* l_OptionT_mk___redArg___boxed(lean_object* v_x_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_OptionT_mk___redArg(v_x_19_);
lean_dec(v_x_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_OptionT_mk(lean_object* v_m_21_, lean_object* v_00_u03b1_22_, lean_object* v_x_23_){
_start:
{
lean_inc(v_x_23_);
return v_x_23_;
}
}
LEAN_EXPORT lean_object* l_OptionT_mk___boxed(lean_object* v_m_24_, lean_object* v_00_u03b1_25_, lean_object* v_x_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_OptionT_mk(v_m_24_, v_00_u03b1_25_, v_x_26_);
lean_dec(v_x_26_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_OptionT_bind___redArg___lam__0(lean_object* v_toPure_28_, lean_object* v_f_29_, lean_object* v_____do__lift_30_){
_start:
{
if (lean_obj_tag(v_____do__lift_30_) == 0)
{
lean_object* v___x_31_; lean_object* v___x_32_; 
lean_dec(v_f_29_);
v___x_31_ = lean_box(0);
v___x_32_ = lean_apply_2(v_toPure_28_, lean_box(0), v___x_31_);
return v___x_32_;
}
else
{
lean_object* v_val_33_; lean_object* v___x_34_; 
lean_dec(v_toPure_28_);
v_val_33_ = lean_ctor_get(v_____do__lift_30_, 0);
lean_inc(v_val_33_);
lean_dec_ref_known(v_____do__lift_30_, 1);
v___x_34_ = lean_apply_1(v_f_29_, v_val_33_);
return v___x_34_;
}
}
}
LEAN_EXPORT lean_object* l_OptionT_bind___redArg(lean_object* v_inst_35_, lean_object* v_x_36_, lean_object* v_f_37_){
_start:
{
lean_object* v_toApplicative_38_; lean_object* v_toBind_39_; lean_object* v_toPure_40_; lean_object* v___f_41_; lean_object* v___x_42_; 
v_toApplicative_38_ = lean_ctor_get(v_inst_35_, 0);
lean_inc_ref(v_toApplicative_38_);
v_toBind_39_ = lean_ctor_get(v_inst_35_, 1);
lean_inc(v_toBind_39_);
lean_dec_ref(v_inst_35_);
v_toPure_40_ = lean_ctor_get(v_toApplicative_38_, 1);
lean_inc(v_toPure_40_);
lean_dec_ref(v_toApplicative_38_);
v___f_41_ = lean_alloc_closure((void*)(l_OptionT_bind___redArg___lam__0), 3, 2);
lean_closure_set(v___f_41_, 0, v_toPure_40_);
lean_closure_set(v___f_41_, 1, v_f_37_);
v___x_42_ = lean_apply_4(v_toBind_39_, lean_box(0), lean_box(0), v_x_36_, v___f_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_OptionT_bind(lean_object* v_m_43_, lean_object* v_inst_44_, lean_object* v_00_u03b1_45_, lean_object* v_00_u03b2_46_, lean_object* v_x_47_, lean_object* v_f_48_){
_start:
{
lean_object* v_toApplicative_49_; lean_object* v_toBind_50_; lean_object* v_toPure_51_; lean_object* v___f_52_; lean_object* v___x_53_; 
v_toApplicative_49_ = lean_ctor_get(v_inst_44_, 0);
lean_inc_ref(v_toApplicative_49_);
v_toBind_50_ = lean_ctor_get(v_inst_44_, 1);
lean_inc(v_toBind_50_);
lean_dec_ref(v_inst_44_);
v_toPure_51_ = lean_ctor_get(v_toApplicative_49_, 1);
lean_inc(v_toPure_51_);
lean_dec_ref(v_toApplicative_49_);
v___f_52_ = lean_alloc_closure((void*)(l_OptionT_bind___redArg___lam__0), 3, 2);
lean_closure_set(v___f_52_, 0, v_toPure_51_);
lean_closure_set(v___f_52_, 1, v_f_48_);
v___x_53_ = lean_apply_4(v_toBind_50_, lean_box(0), lean_box(0), v_x_47_, v___f_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_OptionT_pure___redArg(lean_object* v_inst_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_toApplicative_56_; lean_object* v_toPure_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v_toApplicative_56_ = lean_ctor_get(v_inst_54_, 0);
lean_inc_ref(v_toApplicative_56_);
lean_dec_ref(v_inst_54_);
v_toPure_57_ = lean_ctor_get(v_toApplicative_56_, 1);
lean_inc(v_toPure_57_);
lean_dec_ref(v_toApplicative_56_);
v___x_58_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_58_, 0, v_a_55_);
v___x_59_ = lean_apply_2(v_toPure_57_, lean_box(0), v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_OptionT_pure(lean_object* v_m_60_, lean_object* v_inst_61_, lean_object* v_00_u03b1_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_toApplicative_64_; lean_object* v_toPure_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v_toApplicative_64_ = lean_ctor_get(v_inst_61_, 0);
lean_inc_ref(v_toApplicative_64_);
lean_dec_ref(v_inst_61_);
v_toPure_65_ = lean_ctor_get(v_toApplicative_64_, 1);
lean_inc(v_toPure_65_);
lean_dec_ref(v_toApplicative_64_);
v___x_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_66_, 0, v_a_63_);
v___x_67_ = lean_apply_2(v_toPure_65_, lean_box(0), v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__0(lean_object* v_toPure_68_, lean_object* v_f_69_, lean_object* v_____do__lift_70_){
_start:
{
if (lean_obj_tag(v_____do__lift_70_) == 0)
{
lean_object* v___x_71_; lean_object* v___x_72_; 
lean_dec(v_f_69_);
v___x_71_ = lean_box(0);
v___x_72_ = lean_apply_2(v_toPure_68_, lean_box(0), v___x_71_);
return v___x_72_;
}
else
{
lean_object* v_val_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_82_; 
v_val_73_ = lean_ctor_get(v_____do__lift_70_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v_____do__lift_70_);
if (v_isSharedCheck_82_ == 0)
{
v___x_75_ = v_____do__lift_70_;
v_isShared_76_ = v_isSharedCheck_82_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_val_73_);
lean_dec(v_____do__lift_70_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_82_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_77_; lean_object* v___x_79_; 
v___x_77_ = lean_apply_1(v_f_69_, v_val_73_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 0, v___x_77_);
v___x_79_ = v___x_75_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_77_);
v___x_79_ = v_reuseFailAlloc_81_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
lean_object* v___x_80_; 
v___x_80_ = lean_apply_2(v_toPure_68_, lean_box(0), v___x_79_);
return v___x_80_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__1(lean_object* v_inst_83_, lean_object* v_00_u03b1_84_, lean_object* v_00_u03b2_85_, lean_object* v_f_86_, lean_object* v_x_87_){
_start:
{
lean_object* v_toApplicative_88_; lean_object* v_toBind_89_; lean_object* v_toPure_90_; lean_object* v___f_91_; lean_object* v___x_92_; 
v_toApplicative_88_ = lean_ctor_get(v_inst_83_, 0);
lean_inc_ref(v_toApplicative_88_);
v_toBind_89_ = lean_ctor_get(v_inst_83_, 1);
lean_inc(v_toBind_89_);
lean_dec_ref(v_inst_83_);
v_toPure_90_ = lean_ctor_get(v_toApplicative_88_, 1);
lean_inc(v_toPure_90_);
lean_dec_ref(v_toApplicative_88_);
v___f_91_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__0), 3, 2);
lean_closure_set(v___f_91_, 0, v_toPure_90_);
lean_closure_set(v___f_91_, 1, v_f_86_);
v___x_92_ = lean_apply_4(v_toBind_89_, lean_box(0), lean_box(0), v_x_87_, v___f_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__2(lean_object* v_toPure_93_, lean_object* v___y_94_, lean_object* v_____do__lift_95_){
_start:
{
if (lean_obj_tag(v_____do__lift_95_) == 0)
{
lean_object* v___x_96_; lean_object* v___x_97_; 
lean_dec(v___y_94_);
v___x_96_ = lean_box(0);
v___x_97_ = lean_apply_2(v_toPure_93_, lean_box(0), v___x_96_);
return v___x_97_;
}
else
{
lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_105_; 
v_isSharedCheck_105_ = !lean_is_exclusive(v_____do__lift_95_);
if (v_isSharedCheck_105_ == 0)
{
lean_object* v_unused_106_; 
v_unused_106_ = lean_ctor_get(v_____do__lift_95_, 0);
lean_dec(v_unused_106_);
v___x_99_ = v_____do__lift_95_;
v_isShared_100_ = v_isSharedCheck_105_;
goto v_resetjp_98_;
}
else
{
lean_dec(v_____do__lift_95_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_105_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_102_; 
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 0, v___y_94_);
v___x_102_ = v___x_99_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___y_94_);
v___x_102_ = v_reuseFailAlloc_104_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
lean_object* v___x_103_; 
v___x_103_ = lean_apply_2(v_toPure_93_, lean_box(0), v___x_102_);
return v___x_103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__3(lean_object* v_inst_107_, lean_object* v_00_u03b1_108_, lean_object* v_00_u03b2_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v_toApplicative_112_; lean_object* v_toBind_113_; lean_object* v_toPure_114_; lean_object* v___f_115_; lean_object* v___x_116_; 
v_toApplicative_112_ = lean_ctor_get(v_inst_107_, 0);
lean_inc_ref(v_toApplicative_112_);
v_toBind_113_ = lean_ctor_get(v_inst_107_, 1);
lean_inc(v_toBind_113_);
lean_dec_ref(v_inst_107_);
v_toPure_114_ = lean_ctor_get(v_toApplicative_112_, 1);
lean_inc(v_toPure_114_);
lean_dec_ref(v_toApplicative_112_);
v___f_115_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__2), 3, 2);
lean_closure_set(v___f_115_, 0, v_toPure_114_);
lean_closure_set(v___f_115_, 1, v___y_110_);
v___x_116_ = lean_apply_4(v_toBind_113_, lean_box(0), lean_box(0), v___y_111_, v___f_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__4(lean_object* v_toPure_117_, lean_object* v_val_118_, lean_object* v_____do__lift_119_){
_start:
{
if (lean_obj_tag(v_____do__lift_119_) == 0)
{
lean_object* v___x_120_; lean_object* v___x_121_; 
lean_dec(v_val_118_);
v___x_120_ = lean_box(0);
v___x_121_ = lean_apply_2(v_toPure_117_, lean_box(0), v___x_120_);
return v___x_121_;
}
else
{
lean_object* v_val_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_131_; 
v_val_122_ = lean_ctor_get(v_____do__lift_119_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v_____do__lift_119_);
if (v_isSharedCheck_131_ == 0)
{
v___x_124_ = v_____do__lift_119_;
v_isShared_125_ = v_isSharedCheck_131_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_val_122_);
lean_dec(v_____do__lift_119_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_131_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_126_ = lean_apply_1(v_val_118_, v_val_122_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v___x_126_);
v___x_128_ = v___x_124_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_126_);
v___x_128_ = v_reuseFailAlloc_130_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
lean_object* v___x_129_; 
v___x_129_ = lean_apply_2(v_toPure_117_, lean_box(0), v___x_128_);
return v___x_129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__5(lean_object* v_toPure_132_, lean_object* v_x_133_, lean_object* v_toBind_134_, lean_object* v_____do__lift_135_){
_start:
{
if (lean_obj_tag(v_____do__lift_135_) == 0)
{
lean_object* v___x_136_; lean_object* v___x_137_; 
lean_dec(v_toBind_134_);
lean_dec(v_x_133_);
v___x_136_ = lean_box(0);
v___x_137_ = lean_apply_2(v_toPure_132_, lean_box(0), v___x_136_);
return v___x_137_;
}
else
{
lean_object* v_val_138_; lean_object* v___f_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v_val_138_ = lean_ctor_get(v_____do__lift_135_, 0);
lean_inc(v_val_138_);
lean_dec_ref_known(v_____do__lift_135_, 1);
v___f_139_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__4), 3, 2);
lean_closure_set(v___f_139_, 0, v_toPure_132_);
lean_closure_set(v___f_139_, 1, v_val_138_);
v___x_140_ = lean_box(0);
v___x_141_ = lean_apply_1(v_x_133_, v___x_140_);
v___x_142_ = lean_apply_4(v_toBind_134_, lean_box(0), lean_box(0), v___x_141_, v___f_139_);
return v___x_142_;
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__6(lean_object* v_inst_143_, lean_object* v_00_u03b1_144_, lean_object* v_00_u03b2_145_, lean_object* v_f_146_, lean_object* v_x_147_){
_start:
{
lean_object* v_toApplicative_148_; lean_object* v_toBind_149_; lean_object* v_toPure_150_; lean_object* v___f_151_; lean_object* v___x_152_; 
v_toApplicative_148_ = lean_ctor_get(v_inst_143_, 0);
lean_inc_ref(v_toApplicative_148_);
v_toBind_149_ = lean_ctor_get(v_inst_143_, 1);
lean_inc_n(v_toBind_149_, 2);
lean_dec_ref(v_inst_143_);
v_toPure_150_ = lean_ctor_get(v_toApplicative_148_, 1);
lean_inc(v_toPure_150_);
lean_dec_ref(v_toApplicative_148_);
v___f_151_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__5), 4, 3);
lean_closure_set(v___f_151_, 0, v_toPure_150_);
lean_closure_set(v___f_151_, 1, v_x_147_);
lean_closure_set(v___f_151_, 2, v_toBind_149_);
v___x_152_ = lean_apply_4(v_toBind_149_, lean_box(0), lean_box(0), v_f_146_, v___f_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__7(lean_object* v_toPure_153_, lean_object* v_____do__lift_154_, lean_object* v_____do__lift_155_){
_start:
{
if (lean_obj_tag(v_____do__lift_155_) == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; 
lean_dec(v_____do__lift_154_);
v___x_156_ = lean_box(0);
v___x_157_ = lean_apply_2(v_toPure_153_, lean_box(0), v___x_156_);
return v___x_157_;
}
else
{
lean_object* v___x_158_; 
v___x_158_ = lean_apply_2(v_toPure_153_, lean_box(0), v_____do__lift_154_);
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__7___boxed(lean_object* v_toPure_159_, lean_object* v_____do__lift_160_, lean_object* v_____do__lift_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_OptionT_instMonad___redArg___lam__7(v_toPure_159_, v_____do__lift_160_, v_____do__lift_161_);
lean_dec(v_____do__lift_161_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__8(lean_object* v_toPure_163_, lean_object* v_y_164_, lean_object* v_toBind_165_, lean_object* v_____do__lift_166_){
_start:
{
if (lean_obj_tag(v_____do__lift_166_) == 0)
{
lean_object* v___x_167_; 
lean_dec(v_toBind_165_);
lean_dec(v_y_164_);
v___x_167_ = lean_apply_2(v_toPure_163_, lean_box(0), v_____do__lift_166_);
return v___x_167_;
}
else
{
lean_object* v___f_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___f_168_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_168_, 0, v_toPure_163_);
lean_closure_set(v___f_168_, 1, v_____do__lift_166_);
v___x_169_ = lean_box(0);
v___x_170_ = lean_apply_1(v_y_164_, v___x_169_);
v___x_171_ = lean_apply_4(v_toBind_165_, lean_box(0), lean_box(0), v___x_170_, v___f_168_);
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__9(lean_object* v_inst_172_, lean_object* v_00_u03b1_173_, lean_object* v_00_u03b2_174_, lean_object* v_x_175_, lean_object* v_y_176_){
_start:
{
lean_object* v_toApplicative_177_; lean_object* v_toBind_178_; lean_object* v_toPure_179_; lean_object* v___f_180_; lean_object* v___x_181_; 
v_toApplicative_177_ = lean_ctor_get(v_inst_172_, 0);
lean_inc_ref(v_toApplicative_177_);
v_toBind_178_ = lean_ctor_get(v_inst_172_, 1);
lean_inc_n(v_toBind_178_, 2);
lean_dec_ref(v_inst_172_);
v_toPure_179_ = lean_ctor_get(v_toApplicative_177_, 1);
lean_inc(v_toPure_179_);
lean_dec_ref(v_toApplicative_177_);
v___f_180_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__8), 4, 3);
lean_closure_set(v___f_180_, 0, v_toPure_179_);
lean_closure_set(v___f_180_, 1, v_y_176_);
lean_closure_set(v___f_180_, 2, v_toBind_178_);
v___x_181_ = lean_apply_4(v_toBind_178_, lean_box(0), lean_box(0), v_x_175_, v___f_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__10(lean_object* v_toPure_182_, lean_object* v_y_183_, lean_object* v_____do__lift_184_){
_start:
{
if (lean_obj_tag(v_____do__lift_184_) == 0)
{
lean_object* v___x_185_; lean_object* v___x_186_; 
lean_dec(v_y_183_);
v___x_185_ = lean_box(0);
v___x_186_ = lean_apply_2(v_toPure_182_, lean_box(0), v___x_185_);
return v___x_186_;
}
else
{
lean_object* v___x_187_; lean_object* v___x_188_; 
lean_dec(v_toPure_182_);
v___x_187_ = lean_box(0);
v___x_188_ = lean_apply_1(v_y_183_, v___x_187_);
return v___x_188_;
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__10___boxed(lean_object* v_toPure_189_, lean_object* v_y_190_, lean_object* v_____do__lift_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_OptionT_instMonad___redArg___lam__10(v_toPure_189_, v_y_190_, v_____do__lift_191_);
lean_dec(v_____do__lift_191_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__11(lean_object* v_inst_193_, lean_object* v_00_u03b1_194_, lean_object* v_00_u03b2_195_, lean_object* v_x_196_, lean_object* v_y_197_){
_start:
{
lean_object* v_toApplicative_198_; lean_object* v_toBind_199_; lean_object* v_toPure_200_; lean_object* v___f_201_; lean_object* v___x_202_; 
v_toApplicative_198_ = lean_ctor_get(v_inst_193_, 0);
lean_inc_ref(v_toApplicative_198_);
v_toBind_199_ = lean_ctor_get(v_inst_193_, 1);
lean_inc(v_toBind_199_);
lean_dec_ref(v_inst_193_);
v_toPure_200_ = lean_ctor_get(v_toApplicative_198_, 1);
lean_inc(v_toPure_200_);
lean_dec_ref(v_toApplicative_198_);
v___f_201_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__10___boxed), 3, 2);
lean_closure_set(v___f_201_, 0, v_toPure_200_);
lean_closure_set(v___f_201_, 1, v_y_197_);
v___x_202_ = lean_apply_4(v_toBind_199_, lean_box(0), lean_box(0), v_x_196_, v___f_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg(lean_object* v_inst_203_){
_start:
{
lean_object* v___f_204_; lean_object* v___f_205_; lean_object* v___f_206_; lean_object* v___f_207_; lean_object* v___f_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
lean_inc_ref_n(v_inst_203_, 6);
v___f_204_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_204_, 0, v_inst_203_);
v___f_205_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_205_, 0, v_inst_203_);
v___f_206_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_206_, 0, v_inst_203_);
v___f_207_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_207_, 0, v_inst_203_);
v___f_208_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_208_, 0, v_inst_203_);
v___x_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_209_, 0, v___f_204_);
lean_ctor_set(v___x_209_, 1, v___f_205_);
v___x_210_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_210_, 0, lean_box(0));
lean_closure_set(v___x_210_, 1, v_inst_203_);
v___x_211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_211_, 0, v___x_209_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
lean_ctor_set(v___x_211_, 2, v___f_206_);
lean_ctor_set(v___x_211_, 3, v___f_207_);
lean_ctor_set(v___x_211_, 4, v___f_208_);
v___x_212_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_212_, 0, lean_box(0));
lean_closure_set(v___x_212_, 1, v_inst_203_);
v___x_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_211_);
lean_ctor_set(v___x_213_, 1, v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad(lean_object* v_m_214_, lean_object* v_inst_215_){
_start:
{
lean_object* v___f_216_; lean_object* v___f_217_; lean_object* v___f_218_; lean_object* v___f_219_; lean_object* v___f_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
lean_inc_ref_n(v_inst_215_, 6);
v___f_216_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_216_, 0, v_inst_215_);
v___f_217_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_217_, 0, v_inst_215_);
v___f_218_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_218_, 0, v_inst_215_);
v___f_219_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_219_, 0, v_inst_215_);
v___f_220_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_220_, 0, v_inst_215_);
v___x_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_221_, 0, v___f_216_);
lean_ctor_set(v___x_221_, 1, v___f_217_);
v___x_222_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_222_, 0, lean_box(0));
lean_closure_set(v___x_222_, 1, v_inst_215_);
v___x_223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_223_, 0, v___x_221_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
lean_ctor_set(v___x_223_, 2, v___f_218_);
lean_ctor_set(v___x_223_, 3, v___f_219_);
lean_ctor_set(v___x_223_, 4, v___f_220_);
v___x_224_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_224_, 0, lean_box(0));
lean_closure_set(v___x_224_, 1, v_inst_215_);
v___x_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_223_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instInhabitedOfPure___redArg(lean_object* v_inst_226_){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_box(0);
v___x_228_ = lean_apply_2(v_inst_226_, lean_box(0), v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instInhabitedOfPure(lean_object* v_00_u03b1_229_, lean_object* v_m_230_, lean_object* v_inst_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_OptionT_instInhabitedOfPure___redArg(v_inst_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_OptionT_orElse___redArg___lam__0(lean_object* v_y_233_, lean_object* v_toPure_234_, lean_object* v_____do__lift_235_){
_start:
{
if (lean_obj_tag(v_____do__lift_235_) == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; 
lean_dec(v_toPure_234_);
v___x_236_ = lean_box(0);
v___x_237_ = lean_apply_1(v_y_233_, v___x_236_);
return v___x_237_;
}
else
{
lean_object* v___x_238_; 
lean_dec(v_y_233_);
v___x_238_ = lean_apply_2(v_toPure_234_, lean_box(0), v_____do__lift_235_);
return v___x_238_;
}
}
}
LEAN_EXPORT lean_object* l_OptionT_orElse___redArg(lean_object* v_inst_239_, lean_object* v_x_240_, lean_object* v_y_241_){
_start:
{
lean_object* v_toApplicative_242_; lean_object* v_toBind_243_; lean_object* v_toPure_244_; lean_object* v___f_245_; lean_object* v___x_246_; 
v_toApplicative_242_ = lean_ctor_get(v_inst_239_, 0);
lean_inc_ref(v_toApplicative_242_);
v_toBind_243_ = lean_ctor_get(v_inst_239_, 1);
lean_inc(v_toBind_243_);
lean_dec_ref(v_inst_239_);
v_toPure_244_ = lean_ctor_get(v_toApplicative_242_, 1);
lean_inc(v_toPure_244_);
lean_dec_ref(v_toApplicative_242_);
v___f_245_ = lean_alloc_closure((void*)(l_OptionT_orElse___redArg___lam__0), 3, 2);
lean_closure_set(v___f_245_, 0, v_y_241_);
lean_closure_set(v___f_245_, 1, v_toPure_244_);
v___x_246_ = lean_apply_4(v_toBind_243_, lean_box(0), lean_box(0), v_x_240_, v___f_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_OptionT_orElse(lean_object* v_m_247_, lean_object* v_inst_248_, lean_object* v_00_u03b1_249_, lean_object* v_x_250_, lean_object* v_y_251_){
_start:
{
lean_object* v_toApplicative_252_; lean_object* v_toBind_253_; lean_object* v_toPure_254_; lean_object* v___f_255_; lean_object* v___x_256_; 
v_toApplicative_252_ = lean_ctor_get(v_inst_248_, 0);
lean_inc_ref(v_toApplicative_252_);
v_toBind_253_ = lean_ctor_get(v_inst_248_, 1);
lean_inc(v_toBind_253_);
lean_dec_ref(v_inst_248_);
v_toPure_254_ = lean_ctor_get(v_toApplicative_252_, 1);
lean_inc(v_toPure_254_);
lean_dec_ref(v_toApplicative_252_);
v___f_255_ = lean_alloc_closure((void*)(l_OptionT_orElse___redArg___lam__0), 3, 2);
lean_closure_set(v___f_255_, 0, v_y_251_);
lean_closure_set(v___f_255_, 1, v_toPure_254_);
v___x_256_ = lean_apply_4(v_toBind_253_, lean_box(0), lean_box(0), v_x_250_, v___f_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_OptionT_fail___redArg(lean_object* v_inst_257_){
_start:
{
lean_object* v_toApplicative_258_; lean_object* v_toPure_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v_toApplicative_258_ = lean_ctor_get(v_inst_257_, 0);
lean_inc_ref(v_toApplicative_258_);
lean_dec_ref(v_inst_257_);
v_toPure_259_ = lean_ctor_get(v_toApplicative_258_, 1);
lean_inc(v_toPure_259_);
lean_dec_ref(v_toApplicative_258_);
v___x_260_ = lean_box(0);
v___x_261_ = lean_apply_2(v_toPure_259_, lean_box(0), v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_OptionT_fail(lean_object* v_m_262_, lean_object* v_inst_263_, lean_object* v_00_u03b1_264_){
_start:
{
lean_object* v_toApplicative_265_; lean_object* v_toPure_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v_toApplicative_265_ = lean_ctor_get(v_inst_263_, 0);
lean_inc_ref(v_toApplicative_265_);
lean_dec_ref(v_inst_263_);
v_toPure_266_ = lean_ctor_get(v_toApplicative_265_, 1);
lean_inc(v_toPure_266_);
lean_dec_ref(v_toApplicative_265_);
v___x_267_ = lean_box(0);
v___x_268_ = lean_apply_2(v_toPure_266_, lean_box(0), v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instAlternative___redArg(lean_object* v_inst_269_){
_start:
{
lean_object* v___f_270_; lean_object* v___f_271_; lean_object* v___f_272_; lean_object* v___f_273_; lean_object* v___f_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
lean_inc_ref_n(v_inst_269_, 7);
v___f_270_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_270_, 0, v_inst_269_);
v___f_271_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_271_, 0, v_inst_269_);
v___f_272_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_272_, 0, v_inst_269_);
v___f_273_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_273_, 0, v_inst_269_);
v___f_274_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_274_, 0, v_inst_269_);
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v___f_270_);
lean_ctor_set(v___x_275_, 1, v___f_271_);
v___x_276_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_276_, 0, lean_box(0));
lean_closure_set(v___x_276_, 1, v_inst_269_);
v___x_277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_277_, 0, v___x_275_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
lean_ctor_set(v___x_277_, 2, v___f_272_);
lean_ctor_set(v___x_277_, 3, v___f_273_);
lean_ctor_set(v___x_277_, 4, v___f_274_);
v___x_278_ = lean_alloc_closure((void*)(l_OptionT_fail), 3, 2);
lean_closure_set(v___x_278_, 0, lean_box(0));
lean_closure_set(v___x_278_, 1, v_inst_269_);
v___x_279_ = lean_alloc_closure((void*)(l_OptionT_orElse), 5, 2);
lean_closure_set(v___x_279_, 0, lean_box(0));
lean_closure_set(v___x_279_, 1, v_inst_269_);
v___x_280_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_280_, 0, v___x_277_);
lean_ctor_set(v___x_280_, 1, v___x_278_);
lean_ctor_set(v___x_280_, 2, v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instAlternative(lean_object* v_m_281_, lean_object* v_inst_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_OptionT_instAlternative___redArg(v_inst_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_OptionT_lift___redArg___lam__0(lean_object* v_toPure_284_, lean_object* v_____do__lift_285_){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_286_, 0, v_____do__lift_285_);
v___x_287_ = lean_apply_2(v_toPure_284_, lean_box(0), v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_OptionT_lift___redArg(lean_object* v_inst_288_, lean_object* v_x_289_){
_start:
{
lean_object* v_toApplicative_290_; lean_object* v_toBind_291_; lean_object* v_toPure_292_; lean_object* v___f_293_; lean_object* v___x_294_; 
v_toApplicative_290_ = lean_ctor_get(v_inst_288_, 0);
lean_inc_ref(v_toApplicative_290_);
v_toBind_291_ = lean_ctor_get(v_inst_288_, 1);
lean_inc(v_toBind_291_);
lean_dec_ref(v_inst_288_);
v_toPure_292_ = lean_ctor_get(v_toApplicative_290_, 1);
lean_inc(v_toPure_292_);
lean_dec_ref(v_toApplicative_290_);
v___f_293_ = lean_alloc_closure((void*)(l_OptionT_lift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_293_, 0, v_toPure_292_);
v___x_294_ = lean_apply_4(v_toBind_291_, lean_box(0), lean_box(0), v_x_289_, v___f_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_OptionT_lift(lean_object* v_m_295_, lean_object* v_inst_296_, lean_object* v_00_u03b1_297_, lean_object* v_x_298_){
_start:
{
lean_object* v_toApplicative_299_; lean_object* v_toBind_300_; lean_object* v_toPure_301_; lean_object* v___f_302_; lean_object* v___x_303_; 
v_toApplicative_299_ = lean_ctor_get(v_inst_296_, 0);
lean_inc_ref(v_toApplicative_299_);
v_toBind_300_ = lean_ctor_get(v_inst_296_, 1);
lean_inc(v_toBind_300_);
lean_dec_ref(v_inst_296_);
v_toPure_301_ = lean_ctor_get(v_toApplicative_299_, 1);
lean_inc(v_toPure_301_);
lean_dec_ref(v_toApplicative_299_);
v___f_302_ = lean_alloc_closure((void*)(l_OptionT_lift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_302_, 0, v_toPure_301_);
v___x_303_ = lean_apply_4(v_toBind_300_, lean_box(0), lean_box(0), v_x_298_, v___f_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadLift___redArg(lean_object* v_inst_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(v___x_305_, 0, lean_box(0));
lean_closure_set(v___x_305_, 1, v_inst_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadLift(lean_object* v_m_306_, lean_object* v_inst_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(v___x_308_, 0, lean_box(0));
lean_closure_set(v___x_308_, 1, v_inst_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadFunctor___redArg___lam__0(lean_object* v_00_u03b1_309_, lean_object* v_f_310_, lean_object* v_x_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = lean_apply_2(v_f_310_, lean_box(0), v_x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadFunctor___redArg(){
_start:
{
lean_object* v___f_315_; 
v___f_315_ = ((lean_object*)(l_OptionT_instMonadFunctor___redArg___closed__0));
return v___f_315_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadFunctor___redArg___boxed(lean_object* v___dummy_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_OptionT_instMonadFunctor___redArg();
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadFunctor(lean_object* v_m_318_){
_start:
{
lean_object* v___f_319_; 
v___f_319_ = ((lean_object*)(l_OptionT_instMonadFunctor___redArg___closed__0));
return v___f_319_;
}
}
LEAN_EXPORT lean_object* l_OptionT_tryCatch___redArg___lam__0(lean_object* v_handle_320_, lean_object* v_toPure_321_, lean_object* v_____x_322_){
_start:
{
if (lean_obj_tag(v_____x_322_) == 0)
{
lean_object* v___x_323_; lean_object* v___x_324_; 
lean_dec(v_toPure_321_);
v___x_323_ = lean_box(0);
v___x_324_ = lean_apply_1(v_handle_320_, v___x_323_);
return v___x_324_;
}
else
{
lean_object* v___x_325_; 
lean_dec(v_handle_320_);
v___x_325_ = lean_apply_2(v_toPure_321_, lean_box(0), v_____x_322_);
return v___x_325_;
}
}
}
LEAN_EXPORT lean_object* l_OptionT_tryCatch___redArg(lean_object* v_inst_326_, lean_object* v_x_327_, lean_object* v_handle_328_){
_start:
{
lean_object* v_toApplicative_329_; lean_object* v_toBind_330_; lean_object* v_toPure_331_; lean_object* v___f_332_; lean_object* v___x_333_; 
v_toApplicative_329_ = lean_ctor_get(v_inst_326_, 0);
lean_inc_ref(v_toApplicative_329_);
v_toBind_330_ = lean_ctor_get(v_inst_326_, 1);
lean_inc(v_toBind_330_);
lean_dec_ref(v_inst_326_);
v_toPure_331_ = lean_ctor_get(v_toApplicative_329_, 1);
lean_inc(v_toPure_331_);
lean_dec_ref(v_toApplicative_329_);
v___f_332_ = lean_alloc_closure((void*)(l_OptionT_tryCatch___redArg___lam__0), 3, 2);
lean_closure_set(v___f_332_, 0, v_handle_328_);
lean_closure_set(v___f_332_, 1, v_toPure_331_);
v___x_333_ = lean_apply_4(v_toBind_330_, lean_box(0), lean_box(0), v_x_327_, v___f_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_OptionT_tryCatch(lean_object* v_m_334_, lean_object* v_inst_335_, lean_object* v_00_u03b1_336_, lean_object* v_x_337_, lean_object* v_handle_338_){
_start:
{
lean_object* v_toApplicative_339_; lean_object* v_toBind_340_; lean_object* v_toPure_341_; lean_object* v___f_342_; lean_object* v___x_343_; 
v_toApplicative_339_ = lean_ctor_get(v_inst_335_, 0);
lean_inc_ref(v_toApplicative_339_);
v_toBind_340_ = lean_ctor_get(v_inst_335_, 1);
lean_inc(v_toBind_340_);
lean_dec_ref(v_inst_335_);
v_toPure_341_ = lean_ctor_get(v_toApplicative_339_, 1);
lean_inc(v_toPure_341_);
lean_dec_ref(v_toApplicative_339_);
v___f_342_ = lean_alloc_closure((void*)(l_OptionT_tryCatch___redArg___lam__0), 3, 2);
lean_closure_set(v___f_342_, 0, v_handle_338_);
lean_closure_set(v___f_342_, 1, v_toPure_341_);
v___x_343_ = lean_apply_4(v_toBind_340_, lean_box(0), lean_box(0), v_x_337_, v___f_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOfPUnit___redArg___lam__0(lean_object* v_inst_344_, lean_object* v_00_u03b1_345_, lean_object* v_x_346_){
_start:
{
lean_object* v_toApplicative_347_; lean_object* v_toPure_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v_toApplicative_347_ = lean_ctor_get(v_inst_344_, 0);
lean_inc_ref(v_toApplicative_347_);
lean_dec_ref(v_inst_344_);
v_toPure_348_ = lean_ctor_get(v_toApplicative_347_, 1);
lean_inc(v_toPure_348_);
lean_dec_ref(v_toApplicative_347_);
v___x_349_ = lean_box(0);
v___x_350_ = lean_apply_2(v_toPure_348_, lean_box(0), v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOfPUnit___redArg(lean_object* v_inst_351_){
_start:
{
lean_object* v___f_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
lean_inc_ref(v_inst_351_);
v___f_352_ = lean_alloc_closure((void*)(l_OptionT_instMonadExceptOfPUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_352_, 0, v_inst_351_);
v___x_353_ = lean_alloc_closure((void*)(l_OptionT_tryCatch), 5, 2);
lean_closure_set(v___x_353_, 0, lean_box(0));
lean_closure_set(v___x_353_, 1, v_inst_351_);
v___x_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_354_, 0, v___f_352_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOfPUnit(lean_object* v_m_355_, lean_object* v_inst_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_OptionT_instMonadExceptOfPUnit___redArg(v_inst_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOf___redArg___lam__0(lean_object* v_inst_358_, lean_object* v_00_u03b1_359_, lean_object* v_e_360_){
_start:
{
lean_object* v_throw_361_; lean_object* v___x_362_; 
v_throw_361_ = lean_ctor_get(v_inst_358_, 0);
lean_inc(v_throw_361_);
lean_dec_ref(v_inst_358_);
v___x_362_ = lean_apply_2(v_throw_361_, lean_box(0), v_e_360_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOf___redArg___lam__1(lean_object* v_inst_363_, lean_object* v_00_u03b1_364_, lean_object* v_x_365_, lean_object* v_handle_366_){
_start:
{
lean_object* v_tryCatch_367_; lean_object* v___x_368_; 
v_tryCatch_367_ = lean_ctor_get(v_inst_363_, 1);
lean_inc(v_tryCatch_367_);
lean_dec_ref(v_inst_363_);
v___x_368_ = lean_apply_3(v_tryCatch_367_, lean_box(0), v_x_365_, v_handle_366_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOf___redArg(lean_object* v_inst_369_){
_start:
{
lean_object* v___f_370_; lean_object* v___f_371_; lean_object* v___x_372_; 
lean_inc_ref(v_inst_369_);
v___f_370_ = lean_alloc_closure((void*)(l_OptionT_instMonadExceptOf___redArg___lam__0), 3, 1);
lean_closure_set(v___f_370_, 0, v_inst_369_);
v___f_371_ = lean_alloc_closure((void*)(l_OptionT_instMonadExceptOf___redArg___lam__1), 4, 1);
lean_closure_set(v___f_371_, 0, v_inst_369_);
v___x_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_372_, 0, v___f_370_);
lean_ctor_set(v___x_372_, 1, v___f_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOf(lean_object* v_m_373_, lean_object* v_00_u03b5_374_, lean_object* v_inst_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_OptionT_instMonadExceptOf___redArg(v_inst_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadAttach___redArg___lam__0(lean_object* v_x_377_){
_start:
{
if (lean_obj_tag(v_x_377_) == 0)
{
lean_object* v___x_378_; 
v___x_378_ = lean_box(0);
return v___x_378_;
}
else
{
lean_object* v_val_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_386_; 
v_val_379_ = lean_ctor_get(v_x_377_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v_x_377_);
if (v_isSharedCheck_386_ == 0)
{
v___x_381_ = v_x_377_;
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_val_379_);
lean_dec(v_x_377_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_384_; 
if (v_isShared_382_ == 0)
{
v___x_384_ = v___x_381_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_val_379_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadAttach___redArg___lam__1(lean_object* v_toFunctor_387_, lean_object* v_inst_388_, lean_object* v___f_389_, lean_object* v_00_u03b1_390_, lean_object* v_x_391_){
_start:
{
lean_object* v_map_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v_map_392_ = lean_ctor_get(v_toFunctor_387_, 0);
lean_inc(v_map_392_);
lean_dec_ref(v_toFunctor_387_);
v___x_393_ = lean_apply_2(v_inst_388_, lean_box(0), v_x_391_);
v___x_394_ = lean_apply_4(v_map_392_, lean_box(0), lean_box(0), v___f_389_, v___x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadAttach___redArg(lean_object* v_inst_396_, lean_object* v_inst_397_){
_start:
{
lean_object* v_toApplicative_398_; lean_object* v_toFunctor_399_; lean_object* v___f_400_; lean_object* v___f_401_; 
v_toApplicative_398_ = lean_ctor_get(v_inst_396_, 0);
lean_inc_ref(v_toApplicative_398_);
lean_dec_ref(v_inst_396_);
v_toFunctor_399_ = lean_ctor_get(v_toApplicative_398_, 0);
lean_inc_ref(v_toFunctor_399_);
lean_dec_ref(v_toApplicative_398_);
v___f_400_ = ((lean_object*)(l_OptionT_instMonadAttach___redArg___closed__0));
v___f_401_ = lean_alloc_closure((void*)(l_OptionT_instMonadAttach___redArg___lam__1), 5, 3);
lean_closure_set(v___f_401_, 0, v_toFunctor_399_);
lean_closure_set(v___f_401_, 1, v_inst_397_);
lean_closure_set(v___f_401_, 2, v___f_400_);
return v___f_401_;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadAttach(lean_object* v_m_402_, lean_object* v_inst_403_, lean_object* v_inst_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_OptionT_instMonadAttach___redArg(v_inst_403_, v_inst_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg___lam__0(lean_object* v_00_u03b2_406_, lean_object* v_x_407_){
_start:
{
lean_inc(v_x_407_);
return v_x_407_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg___lam__0___boxed(lean_object* v_00_u03b2_408_, lean_object* v_x_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_instMonadControlOptionTOfMonad___redArg___lam__0(v_00_u03b2_408_, v_x_409_);
lean_dec(v_x_409_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg___lam__2(lean_object* v_inst_411_, lean_object* v___f_412_, lean_object* v_00_u03b1_413_, lean_object* v_f_414_){
_start:
{
lean_object* v_toApplicative_415_; lean_object* v_toBind_416_; lean_object* v_toPure_417_; lean_object* v___x_418_; lean_object* v___f_419_; lean_object* v___x_420_; 
v_toApplicative_415_ = lean_ctor_get(v_inst_411_, 0);
lean_inc_ref(v_toApplicative_415_);
v_toBind_416_ = lean_ctor_get(v_inst_411_, 1);
lean_inc(v_toBind_416_);
lean_dec_ref(v_inst_411_);
v_toPure_417_ = lean_ctor_get(v_toApplicative_415_, 1);
lean_inc(v_toPure_417_);
lean_dec_ref(v_toApplicative_415_);
v___x_418_ = lean_apply_1(v_f_414_, v___f_412_);
v___f_419_ = lean_alloc_closure((void*)(l_OptionT_lift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_419_, 0, v_toPure_417_);
v___x_420_ = lean_apply_4(v_toBind_416_, lean_box(0), lean_box(0), v___x_418_, v___f_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg___lam__1(lean_object* v_00_u03b1_421_, lean_object* v_x_422_){
_start:
{
lean_inc(v_x_422_);
return v_x_422_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg___lam__1___boxed(lean_object* v_00_u03b1_423_, lean_object* v_x_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_instMonadControlOptionTOfMonad___redArg___lam__1(v_00_u03b1_423_, v_x_424_);
lean_dec(v_x_424_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg(lean_object* v_inst_428_){
_start:
{
lean_object* v___f_429_; lean_object* v___f_430_; lean_object* v___f_431_; lean_object* v___x_432_; 
v___f_429_ = ((lean_object*)(l_instMonadControlOptionTOfMonad___redArg___closed__0));
v___f_430_ = lean_alloc_closure((void*)(l_instMonadControlOptionTOfMonad___redArg___lam__2), 4, 2);
lean_closure_set(v___f_430_, 0, v_inst_428_);
lean_closure_set(v___f_430_, 1, v___f_429_);
v___f_431_ = ((lean_object*)(l_instMonadControlOptionTOfMonad___redArg___closed__1));
v___x_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_432_, 0, v___f_430_);
lean_ctor_set(v___x_432_, 1, v___f_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad(lean_object* v_m_433_, lean_object* v_inst_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_instMonadControlOptionTOfMonad___redArg(v_inst_434_);
return v___x_435_;
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

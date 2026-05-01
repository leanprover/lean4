// Lean compiler output
// Module: Init.Control.State
// Imports: public import Init.Control.Except
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
LEAN_EXPORT lean_object* l_StateT_mk___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_mk(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_run_x27___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_StateT_run_x27___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_StateT_run_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_run_x27___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_StateT_run_x27___redArg___closed__0 = (const lean_object*)&l_StateT_run_x27___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_StateT_run_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_run_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_pure___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_bind___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_bind___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_map___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_instMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_instMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_instMonad___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_instMonad___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_instMonad___redArg___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_StateT_instMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_orElse___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_orElse___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_orElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_failure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_StateT_failure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_failure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_instAlternative___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_instAlternative(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_get___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_get(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_set___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_set(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_modifyGet___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_modifyGet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_lift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_lift___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_lift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_instMonadLift___redArg(lean_object*);
LEAN_EXPORT lean_object* l_StateT_instMonadLift(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_StateT_instMonadFunctor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_StateT_instMonadFunctor___closed__0 = (const lean_object*)&l_StateT_instMonadFunctor___closed__0_value;
LEAN_EXPORT lean_object* l_StateT_instMonadFunctor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_instMonadExceptOf___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_instMonadExceptOf___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_instMonadExceptOf___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_instMonadExceptOf___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_instMonadExceptOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ForM_forIn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ForM_forIn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ForM_forIn___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ForM_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ForM_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadStateOfStateTOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instMonadStateOfStateTOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_monadControl___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_monadControl___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_monadControl___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_monadControl___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_monadControl___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_monadControl___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_monadControl___redArg___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_monadControl___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_monadControl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_StateT_monadControl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_tryFinally___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_tryFinally___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_tryFinally___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_tryFinally___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_tryFinally(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadAttachStateTOfMonad___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instMonadAttachStateTOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instMonadAttachStateTOfMonad___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadAttachStateTOfMonad___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadAttachStateTOfMonad___redArg___closed__0 = (const lean_object*)&l_instMonadAttachStateTOfMonad___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instMonadAttachStateTOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadAttachStateTOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_mk___redArg(lean_object* v_x_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_1(v_x_1_, v_a_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_StateT_mk(lean_object* v_00_u03c3_4_, lean_object* v_m_5_, lean_object* v_00_u03b1_6_, lean_object* v_x_7_, lean_object* v_a_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_apply_1(v_x_7_, v_a_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_StateT_run___redArg(lean_object* v_x_10_, lean_object* v_s_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_apply_1(v_x_10_, v_s_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_StateT_run(lean_object* v_00_u03c3_13_, lean_object* v_m_14_, lean_object* v_00_u03b1_15_, lean_object* v_x_16_, lean_object* v_s_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_apply_1(v_x_16_, v_s_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_StateT_run_x27___redArg___lam__0(lean_object* v_x_19_){
_start:
{
lean_object* v_fst_20_; 
v_fst_20_ = lean_ctor_get(v_x_19_, 0);
lean_inc(v_fst_20_);
return v_fst_20_;
}
}
LEAN_EXPORT lean_object* l_StateT_run_x27___redArg___lam__0___boxed(lean_object* v_x_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_StateT_run_x27___redArg___lam__0(v_x_21_);
lean_dec_ref(v_x_21_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_StateT_run_x27___redArg(lean_object* v_inst_24_, lean_object* v_x_25_, lean_object* v_s_26_){
_start:
{
lean_object* v_map_27_; lean_object* v___f_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v_map_27_ = lean_ctor_get(v_inst_24_, 0);
lean_inc(v_map_27_);
lean_dec_ref(v_inst_24_);
v___f_28_ = ((lean_object*)(l_StateT_run_x27___redArg___closed__0));
v___x_29_ = lean_apply_1(v_x_25_, v_s_26_);
v___x_30_ = lean_apply_4(v_map_27_, lean_box(0), lean_box(0), v___f_28_, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_StateT_run_x27(lean_object* v_00_u03c3_31_, lean_object* v_m_32_, lean_object* v_inst_33_, lean_object* v_00_u03b1_34_, lean_object* v_x_35_, lean_object* v_s_36_){
_start:
{
lean_object* v_map_37_; lean_object* v___f_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v_map_37_ = lean_ctor_get(v_inst_33_, 0);
lean_inc(v_map_37_);
lean_dec_ref(v_inst_33_);
v___f_38_ = ((lean_object*)(l_StateT_run_x27___redArg___closed__0));
v___x_39_ = lean_apply_1(v_x_35_, v_s_36_);
v___x_40_ = lean_apply_4(v_map_37_, lean_box(0), lean_box(0), v___f_38_, v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_StateT_pure___redArg(lean_object* v_inst_41_, lean_object* v_a_42_, lean_object* v_s_43_){
_start:
{
lean_object* v_toApplicative_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_53_; 
v_toApplicative_44_ = lean_ctor_get(v_inst_41_, 0);
v_isSharedCheck_53_ = !lean_is_exclusive(v_inst_41_);
if (v_isSharedCheck_53_ == 0)
{
lean_object* v_unused_54_; 
v_unused_54_ = lean_ctor_get(v_inst_41_, 1);
lean_dec(v_unused_54_);
v___x_46_ = v_inst_41_;
v_isShared_47_ = v_isSharedCheck_53_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_toApplicative_44_);
lean_dec(v_inst_41_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_53_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v_toPure_48_; lean_object* v___x_50_; 
v_toPure_48_ = lean_ctor_get(v_toApplicative_44_, 1);
lean_inc(v_toPure_48_);
lean_dec_ref(v_toApplicative_44_);
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 1, v_s_43_);
lean_ctor_set(v___x_46_, 0, v_a_42_);
v___x_50_ = v___x_46_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v_a_42_);
lean_ctor_set(v_reuseFailAlloc_52_, 1, v_s_43_);
v___x_50_ = v_reuseFailAlloc_52_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
lean_object* v___x_51_; 
v___x_51_ = lean_apply_2(v_toPure_48_, lean_box(0), v___x_50_);
return v___x_51_;
}
}
}
}
LEAN_EXPORT lean_object* l_StateT_pure(lean_object* v_00_u03c3_55_, lean_object* v_m_56_, lean_object* v_inst_57_, lean_object* v_00_u03b1_58_, lean_object* v_a_59_, lean_object* v_s_60_){
_start:
{
lean_object* v_toApplicative_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_70_; 
v_toApplicative_61_ = lean_ctor_get(v_inst_57_, 0);
v_isSharedCheck_70_ = !lean_is_exclusive(v_inst_57_);
if (v_isSharedCheck_70_ == 0)
{
lean_object* v_unused_71_; 
v_unused_71_ = lean_ctor_get(v_inst_57_, 1);
lean_dec(v_unused_71_);
v___x_63_ = v_inst_57_;
v_isShared_64_ = v_isSharedCheck_70_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_toApplicative_61_);
lean_dec(v_inst_57_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_70_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v_toPure_65_; lean_object* v___x_67_; 
v_toPure_65_ = lean_ctor_get(v_toApplicative_61_, 1);
lean_inc(v_toPure_65_);
lean_dec_ref(v_toApplicative_61_);
if (v_isShared_64_ == 0)
{
lean_ctor_set(v___x_63_, 1, v_s_60_);
lean_ctor_set(v___x_63_, 0, v_a_59_);
v___x_67_ = v___x_63_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_a_59_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v_s_60_);
v___x_67_ = v_reuseFailAlloc_69_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
lean_object* v___x_68_; 
v___x_68_ = lean_apply_2(v_toPure_65_, lean_box(0), v___x_67_);
return v___x_68_;
}
}
}
}
LEAN_EXPORT lean_object* l_StateT_bind___redArg___lam__0(lean_object* v_f_72_, lean_object* v_____x_73_){
_start:
{
lean_object* v_fst_74_; lean_object* v_snd_75_; lean_object* v___x_76_; 
v_fst_74_ = lean_ctor_get(v_____x_73_, 0);
lean_inc(v_fst_74_);
v_snd_75_ = lean_ctor_get(v_____x_73_, 1);
lean_inc(v_snd_75_);
lean_dec_ref(v_____x_73_);
v___x_76_ = lean_apply_2(v_f_72_, v_fst_74_, v_snd_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_StateT_bind___redArg(lean_object* v_inst_77_, lean_object* v_x_78_, lean_object* v_f_79_, lean_object* v_s_80_){
_start:
{
lean_object* v_toBind_81_; lean_object* v___f_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v_toBind_81_ = lean_ctor_get(v_inst_77_, 1);
lean_inc(v_toBind_81_);
lean_dec_ref(v_inst_77_);
v___f_82_ = lean_alloc_closure((void*)(l_StateT_bind___redArg___lam__0), 2, 1);
lean_closure_set(v___f_82_, 0, v_f_79_);
v___x_83_ = lean_apply_1(v_x_78_, v_s_80_);
v___x_84_ = lean_apply_4(v_toBind_81_, lean_box(0), lean_box(0), v___x_83_, v___f_82_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_StateT_bind(lean_object* v_00_u03c3_85_, lean_object* v_m_86_, lean_object* v_inst_87_, lean_object* v_00_u03b1_88_, lean_object* v_00_u03b2_89_, lean_object* v_x_90_, lean_object* v_f_91_, lean_object* v_s_92_){
_start:
{
lean_object* v_toBind_93_; lean_object* v___f_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v_toBind_93_ = lean_ctor_get(v_inst_87_, 1);
lean_inc(v_toBind_93_);
lean_dec_ref(v_inst_87_);
v___f_94_ = lean_alloc_closure((void*)(l_StateT_bind___redArg___lam__0), 2, 1);
lean_closure_set(v___f_94_, 0, v_f_91_);
v___x_95_ = lean_apply_1(v_x_90_, v_s_92_);
v___x_96_ = lean_apply_4(v_toBind_93_, lean_box(0), lean_box(0), v___x_95_, v___f_94_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_StateT_map___redArg___lam__0(lean_object* v_f_97_, lean_object* v_toPure_98_, lean_object* v_____x_99_){
_start:
{
lean_object* v_fst_100_; lean_object* v_snd_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_110_; 
v_fst_100_ = lean_ctor_get(v_____x_99_, 0);
v_snd_101_ = lean_ctor_get(v_____x_99_, 1);
v_isSharedCheck_110_ = !lean_is_exclusive(v_____x_99_);
if (v_isSharedCheck_110_ == 0)
{
v___x_103_ = v_____x_99_;
v_isShared_104_ = v_isSharedCheck_110_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_snd_101_);
lean_inc(v_fst_100_);
lean_dec(v_____x_99_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_110_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_105_; lean_object* v___x_107_; 
v___x_105_ = lean_apply_1(v_f_97_, v_fst_100_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 0, v___x_105_);
v___x_107_ = v___x_103_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v___x_105_);
lean_ctor_set(v_reuseFailAlloc_109_, 1, v_snd_101_);
v___x_107_ = v_reuseFailAlloc_109_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
lean_object* v___x_108_; 
v___x_108_ = lean_apply_2(v_toPure_98_, lean_box(0), v___x_107_);
return v___x_108_;
}
}
}
}
LEAN_EXPORT lean_object* l_StateT_map___redArg(lean_object* v_inst_111_, lean_object* v_f_112_, lean_object* v_x_113_, lean_object* v_s_114_){
_start:
{
lean_object* v_toApplicative_115_; lean_object* v_toBind_116_; lean_object* v_toPure_117_; lean_object* v___x_118_; lean_object* v___f_119_; lean_object* v___x_120_; 
v_toApplicative_115_ = lean_ctor_get(v_inst_111_, 0);
lean_inc_ref(v_toApplicative_115_);
v_toBind_116_ = lean_ctor_get(v_inst_111_, 1);
lean_inc(v_toBind_116_);
lean_dec_ref(v_inst_111_);
v_toPure_117_ = lean_ctor_get(v_toApplicative_115_, 1);
lean_inc(v_toPure_117_);
lean_dec_ref(v_toApplicative_115_);
v___x_118_ = lean_apply_1(v_x_113_, v_s_114_);
v___f_119_ = lean_alloc_closure((void*)(l_StateT_map___redArg___lam__0), 3, 2);
lean_closure_set(v___f_119_, 0, v_f_112_);
lean_closure_set(v___f_119_, 1, v_toPure_117_);
v___x_120_ = lean_apply_4(v_toBind_116_, lean_box(0), lean_box(0), v___x_118_, v___f_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_StateT_map(lean_object* v_00_u03c3_121_, lean_object* v_m_122_, lean_object* v_inst_123_, lean_object* v_00_u03b1_124_, lean_object* v_00_u03b2_125_, lean_object* v_f_126_, lean_object* v_x_127_, lean_object* v_s_128_){
_start:
{
lean_object* v_toApplicative_129_; lean_object* v_toBind_130_; lean_object* v_toPure_131_; lean_object* v___x_132_; lean_object* v___f_133_; lean_object* v___x_134_; 
v_toApplicative_129_ = lean_ctor_get(v_inst_123_, 0);
lean_inc_ref(v_toApplicative_129_);
v_toBind_130_ = lean_ctor_get(v_inst_123_, 1);
lean_inc(v_toBind_130_);
lean_dec_ref(v_inst_123_);
v_toPure_131_ = lean_ctor_get(v_toApplicative_129_, 1);
lean_inc(v_toPure_131_);
lean_dec_ref(v_toApplicative_129_);
v___x_132_ = lean_apply_1(v_x_127_, v_s_128_);
v___f_133_ = lean_alloc_closure((void*)(l_StateT_map___redArg___lam__0), 3, 2);
lean_closure_set(v___f_133_, 0, v_f_126_);
lean_closure_set(v___f_133_, 1, v_toPure_131_);
v___x_134_ = lean_apply_4(v_toBind_130_, lean_box(0), lean_box(0), v___x_132_, v___f_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_StateT_instMonad___redArg___lam__0(lean_object* v___y_135_, lean_object* v_toPure_136_, lean_object* v_____x_137_){
_start:
{
lean_object* v_snd_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_146_; 
v_snd_138_ = lean_ctor_get(v_____x_137_, 1);
v_isSharedCheck_146_ = !lean_is_exclusive(v_____x_137_);
if (v_isSharedCheck_146_ == 0)
{
lean_object* v_unused_147_; 
v_unused_147_ = lean_ctor_get(v_____x_137_, 0);
lean_dec(v_unused_147_);
v___x_140_ = v_____x_137_;
v_isShared_141_ = v_isSharedCheck_146_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_snd_138_);
lean_dec(v_____x_137_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_146_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v___y_135_);
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___y_135_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v_snd_138_);
v___x_143_ = v_reuseFailAlloc_145_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v___x_144_; 
v___x_144_ = lean_apply_2(v_toPure_136_, lean_box(0), v___x_143_);
return v___x_144_;
}
}
}
}
LEAN_EXPORT lean_object* l_StateT_instMonad___redArg___lam__1(lean_object* v_inst_148_, lean_object* v_00_u03b1_149_, lean_object* v_00_u03b2_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v_toApplicative_154_; lean_object* v_toBind_155_; lean_object* v_toPure_156_; lean_object* v___x_157_; lean_object* v___f_158_; lean_object* v___x_159_; 
v_toApplicative_154_ = lean_ctor_get(v_inst_148_, 0);
lean_inc_ref(v_toApplicative_154_);
v_toBind_155_ = lean_ctor_get(v_inst_148_, 1);
lean_inc(v_toBind_155_);
lean_dec_ref(v_inst_148_);
v_toPure_156_ = lean_ctor_get(v_toApplicative_154_, 1);
lean_inc(v_toPure_156_);
lean_dec_ref(v_toApplicative_154_);
v___x_157_ = lean_apply_1(v___y_152_, v___y_153_);
v___f_158_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__0), 3, 2);
lean_closure_set(v___f_158_, 0, v___y_151_);
lean_closure_set(v___f_158_, 1, v_toPure_156_);
v___x_159_ = lean_apply_4(v_toBind_155_, lean_box(0), lean_box(0), v___x_157_, v___f_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_StateT_instMonad___redArg___lam__2(lean_object* v_fst_160_, lean_object* v_toPure_161_, lean_object* v_____x_162_){
_start:
{
lean_object* v_fst_163_; lean_object* v_snd_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_173_; 
v_fst_163_ = lean_ctor_get(v_____x_162_, 0);
v_snd_164_ = lean_ctor_get(v_____x_162_, 1);
v_isSharedCheck_173_ = !lean_is_exclusive(v_____x_162_);
if (v_isSharedCheck_173_ == 0)
{
v___x_166_ = v_____x_162_;
v_isShared_167_ = v_isSharedCheck_173_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_snd_164_);
lean_inc(v_fst_163_);
lean_dec(v_____x_162_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_173_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_168_; lean_object* v___x_170_; 
v___x_168_ = lean_apply_1(v_fst_160_, v_fst_163_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 0, v___x_168_);
v___x_170_ = v___x_166_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_168_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_snd_164_);
v___x_170_ = v_reuseFailAlloc_172_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
lean_object* v___x_171_; 
v___x_171_ = lean_apply_2(v_toPure_161_, lean_box(0), v___x_170_);
return v___x_171_;
}
}
}
}
LEAN_EXPORT lean_object* l_StateT_instMonad___redArg___lam__3(lean_object* v_toApplicative_174_, lean_object* v_x_175_, lean_object* v_toBind_176_, lean_object* v_____x_177_){
_start:
{
lean_object* v_fst_178_; lean_object* v_snd_179_; lean_object* v_toPure_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___f_183_; lean_object* v___x_184_; 
v_fst_178_ = lean_ctor_get(v_____x_177_, 0);
lean_inc(v_fst_178_);
v_snd_179_ = lean_ctor_get(v_____x_177_, 1);
lean_inc(v_snd_179_);
lean_dec_ref(v_____x_177_);
v_toPure_180_ = lean_ctor_get(v_toApplicative_174_, 1);
lean_inc(v_toPure_180_);
lean_dec_ref(v_toApplicative_174_);
v___x_181_ = lean_box(0);
v___x_182_ = lean_apply_2(v_x_175_, v___x_181_, v_snd_179_);
v___f_183_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__2), 3, 2);
lean_closure_set(v___f_183_, 0, v_fst_178_);
lean_closure_set(v___f_183_, 1, v_toPure_180_);
v___x_184_ = lean_apply_4(v_toBind_176_, lean_box(0), lean_box(0), v___x_182_, v___f_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_StateT_instMonad___redArg___lam__4(lean_object* v_inst_185_, lean_object* v_00_u03b1_186_, lean_object* v_00_u03b2_187_, lean_object* v_f_188_, lean_object* v_x_189_, lean_object* v___y_190_){
_start:
{
lean_object* v_toApplicative_191_; lean_object* v_toBind_192_; lean_object* v___f_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_toApplicative_191_ = lean_ctor_get(v_inst_185_, 0);
lean_inc_ref(v_toApplicative_191_);
v_toBind_192_ = lean_ctor_get(v_inst_185_, 1);
lean_inc_n(v_toBind_192_, 2);
lean_dec_ref(v_inst_185_);
v___f_193_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__3), 4, 3);
lean_closure_set(v___f_193_, 0, v_toApplicative_191_);
lean_closure_set(v___f_193_, 1, v_x_189_);
lean_closure_set(v___f_193_, 2, v_toBind_192_);
v___x_194_ = lean_apply_1(v_f_188_, v___y_190_);
v___x_195_ = lean_apply_4(v_toBind_192_, lean_box(0), lean_box(0), v___x_194_, v___f_193_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_StateT_instMonad___redArg___lam__5(lean_object* v_toApplicative_196_, lean_object* v_fst_197_, lean_object* v_____x_198_){
_start:
{
lean_object* v_snd_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_208_; 
v_snd_199_ = lean_ctor_get(v_____x_198_, 1);
v_isSharedCheck_208_ = !lean_is_exclusive(v_____x_198_);
if (v_isSharedCheck_208_ == 0)
{
lean_object* v_unused_209_; 
v_unused_209_ = lean_ctor_get(v_____x_198_, 0);
lean_dec(v_unused_209_);
v___x_201_ = v_____x_198_;
v_isShared_202_ = v_isSharedCheck_208_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_snd_199_);
lean_dec(v_____x_198_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_208_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v_toPure_203_; lean_object* v___x_205_; 
v_toPure_203_ = lean_ctor_get(v_toApplicative_196_, 1);
lean_inc(v_toPure_203_);
lean_dec_ref(v_toApplicative_196_);
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 0, v_fst_197_);
v___x_205_ = v___x_201_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_fst_197_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v_snd_199_);
v___x_205_ = v_reuseFailAlloc_207_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_206_; 
v___x_206_ = lean_apply_2(v_toPure_203_, lean_box(0), v___x_205_);
return v___x_206_;
}
}
}
}
LEAN_EXPORT lean_object* l_StateT_instMonad___redArg___lam__6(lean_object* v_toApplicative_210_, lean_object* v_y_211_, lean_object* v_toBind_212_, lean_object* v_____x_213_){
_start:
{
lean_object* v_fst_214_; lean_object* v_snd_215_; lean_object* v___f_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v_fst_214_ = lean_ctor_get(v_____x_213_, 0);
lean_inc(v_fst_214_);
v_snd_215_ = lean_ctor_get(v_____x_213_, 1);
lean_inc(v_snd_215_);
lean_dec_ref(v_____x_213_);
v___f_216_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__5), 3, 2);
lean_closure_set(v___f_216_, 0, v_toApplicative_210_);
lean_closure_set(v___f_216_, 1, v_fst_214_);
v___x_217_ = lean_box(0);
v___x_218_ = lean_apply_2(v_y_211_, v___x_217_, v_snd_215_);
v___x_219_ = lean_apply_4(v_toBind_212_, lean_box(0), lean_box(0), v___x_218_, v___f_216_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_StateT_instMonad___redArg___lam__7(lean_object* v_inst_220_, lean_object* v_00_u03b1_221_, lean_object* v_00_u03b2_222_, lean_object* v_x_223_, lean_object* v_y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v_toApplicative_226_; lean_object* v_toBind_227_; lean_object* v___f_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v_toApplicative_226_ = lean_ctor_get(v_inst_220_, 0);
lean_inc_ref(v_toApplicative_226_);
v_toBind_227_ = lean_ctor_get(v_inst_220_, 1);
lean_inc_n(v_toBind_227_, 2);
lean_dec_ref(v_inst_220_);
v___f_228_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__6), 4, 3);
lean_closure_set(v___f_228_, 0, v_toApplicative_226_);
lean_closure_set(v___f_228_, 1, v_y_224_);
lean_closure_set(v___f_228_, 2, v_toBind_227_);
v___x_229_ = lean_apply_1(v_x_223_, v___y_225_);
v___x_230_ = lean_apply_4(v_toBind_227_, lean_box(0), lean_box(0), v___x_229_, v___f_228_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_StateT_instMonad___redArg___lam__8(lean_object* v_y_231_, lean_object* v_____x_232_){
_start:
{
lean_object* v_snd_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v_snd_233_ = lean_ctor_get(v_____x_232_, 1);
lean_inc(v_snd_233_);
lean_dec_ref(v_____x_232_);
v___x_234_ = lean_box(0);
v___x_235_ = lean_apply_2(v_y_231_, v___x_234_, v_snd_233_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_StateT_instMonad___redArg___lam__9(lean_object* v_inst_236_, lean_object* v_00_u03b1_237_, lean_object* v_00_u03b2_238_, lean_object* v_x_239_, lean_object* v_y_240_, lean_object* v___y_241_){
_start:
{
lean_object* v_toBind_242_; lean_object* v___f_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v_toBind_242_ = lean_ctor_get(v_inst_236_, 1);
lean_inc(v_toBind_242_);
lean_dec_ref(v_inst_236_);
v___f_243_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__8), 2, 1);
lean_closure_set(v___f_243_, 0, v_y_240_);
v___x_244_ = lean_apply_1(v_x_239_, v___y_241_);
v___x_245_ = lean_apply_4(v_toBind_242_, lean_box(0), lean_box(0), v___x_244_, v___f_243_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_StateT_instMonad___redArg(lean_object* v_inst_246_){
_start:
{
lean_object* v___f_247_; lean_object* v___f_248_; lean_object* v___f_249_; lean_object* v___f_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
lean_inc_ref_n(v_inst_246_, 6);
v___f_247_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_247_, 0, v_inst_246_);
v___f_248_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_248_, 0, v_inst_246_);
v___f_249_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_249_, 0, v_inst_246_);
v___f_250_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_250_, 0, v_inst_246_);
v___x_251_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_251_, 0, lean_box(0));
lean_closure_set(v___x_251_, 1, lean_box(0));
lean_closure_set(v___x_251_, 2, v_inst_246_);
v___x_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v___f_247_);
v___x_253_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_253_, 0, lean_box(0));
lean_closure_set(v___x_253_, 1, lean_box(0));
lean_closure_set(v___x_253_, 2, v_inst_246_);
v___x_254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_254_, 0, v___x_252_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
lean_ctor_set(v___x_254_, 2, v___f_248_);
lean_ctor_set(v___x_254_, 3, v___f_249_);
lean_ctor_set(v___x_254_, 4, v___f_250_);
v___x_255_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_255_, 0, lean_box(0));
lean_closure_set(v___x_255_, 1, lean_box(0));
lean_closure_set(v___x_255_, 2, v_inst_246_);
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_254_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_StateT_instMonad(lean_object* v_00_u03c3_257_, lean_object* v_m_258_, lean_object* v_inst_259_){
_start:
{
lean_object* v___f_260_; lean_object* v___f_261_; lean_object* v___f_262_; lean_object* v___f_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
lean_inc_ref_n(v_inst_259_, 6);
v___f_260_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_260_, 0, v_inst_259_);
v___f_261_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_261_, 0, v_inst_259_);
v___f_262_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_262_, 0, v_inst_259_);
v___f_263_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_263_, 0, v_inst_259_);
v___x_264_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_264_, 0, lean_box(0));
lean_closure_set(v___x_264_, 1, lean_box(0));
lean_closure_set(v___x_264_, 2, v_inst_259_);
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v___f_260_);
v___x_266_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_266_, 0, lean_box(0));
lean_closure_set(v___x_266_, 1, lean_box(0));
lean_closure_set(v___x_266_, 2, v_inst_259_);
v___x_267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_267_, 0, v___x_265_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
lean_ctor_set(v___x_267_, 2, v___f_261_);
lean_ctor_set(v___x_267_, 3, v___f_262_);
lean_ctor_set(v___x_267_, 4, v___f_263_);
v___x_268_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_268_, 0, lean_box(0));
lean_closure_set(v___x_268_, 1, lean_box(0));
lean_closure_set(v___x_268_, 2, v_inst_259_);
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_267_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_StateT_orElse___redArg___lam__0(lean_object* v_x_u2082_270_, lean_object* v_s_271_, lean_object* v_x_272_){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_box(0);
v___x_274_ = lean_apply_2(v_x_u2082_270_, v___x_273_, v_s_271_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_StateT_orElse___redArg(lean_object* v_inst_275_, lean_object* v_x_u2081_276_, lean_object* v_x_u2082_277_, lean_object* v_s_278_){
_start:
{
lean_object* v_orElse_279_; lean_object* v___f_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v_orElse_279_ = lean_ctor_get(v_inst_275_, 2);
lean_inc(v_orElse_279_);
lean_dec_ref(v_inst_275_);
lean_inc(v_s_278_);
v___f_280_ = lean_alloc_closure((void*)(l_StateT_orElse___redArg___lam__0), 3, 2);
lean_closure_set(v___f_280_, 0, v_x_u2082_277_);
lean_closure_set(v___f_280_, 1, v_s_278_);
v___x_281_ = lean_apply_1(v_x_u2081_276_, v_s_278_);
v___x_282_ = lean_apply_3(v_orElse_279_, lean_box(0), v___x_281_, v___f_280_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_StateT_orElse(lean_object* v_00_u03c3_283_, lean_object* v_m_284_, lean_object* v_inst_285_, lean_object* v_00_u03b1_286_, lean_object* v_x_u2081_287_, lean_object* v_x_u2082_288_, lean_object* v_s_289_){
_start:
{
lean_object* v_orElse_290_; lean_object* v___f_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v_orElse_290_ = lean_ctor_get(v_inst_285_, 2);
lean_inc(v_orElse_290_);
lean_dec_ref(v_inst_285_);
lean_inc(v_s_289_);
v___f_291_ = lean_alloc_closure((void*)(l_StateT_orElse___redArg___lam__0), 3, 2);
lean_closure_set(v___f_291_, 0, v_x_u2082_288_);
lean_closure_set(v___f_291_, 1, v_s_289_);
v___x_292_ = lean_apply_1(v_x_u2081_287_, v_s_289_);
v___x_293_ = lean_apply_3(v_orElse_290_, lean_box(0), v___x_292_, v___f_291_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_StateT_failure___redArg(lean_object* v_inst_294_){
_start:
{
lean_object* v_failure_295_; lean_object* v___x_296_; 
v_failure_295_ = lean_ctor_get(v_inst_294_, 1);
lean_inc(v_failure_295_);
lean_dec_ref(v_inst_294_);
v___x_296_ = lean_apply_1(v_failure_295_, lean_box(0));
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_StateT_failure(lean_object* v_00_u03c3_297_, lean_object* v_m_298_, lean_object* v_inst_299_, lean_object* v_00_u03b1_300_, lean_object* v_x_301_){
_start:
{
lean_object* v_failure_302_; lean_object* v___x_303_; 
v_failure_302_ = lean_ctor_get(v_inst_299_, 1);
lean_inc(v_failure_302_);
lean_dec_ref(v_inst_299_);
v___x_303_ = lean_apply_1(v_failure_302_, lean_box(0));
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_StateT_failure___boxed(lean_object* v_00_u03c3_304_, lean_object* v_m_305_, lean_object* v_inst_306_, lean_object* v_00_u03b1_307_, lean_object* v_x_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_StateT_failure(v_00_u03c3_304_, v_m_305_, v_inst_306_, v_00_u03b1_307_, v_x_308_);
lean_dec(v_x_308_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_StateT_instAlternative___redArg(lean_object* v_inst_310_, lean_object* v_inst_311_){
_start:
{
lean_object* v___f_312_; lean_object* v___f_313_; lean_object* v___f_314_; lean_object* v___f_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
lean_inc_ref_n(v_inst_310_, 5);
v___f_312_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_312_, 0, v_inst_310_);
v___f_313_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_313_, 0, v_inst_310_);
v___f_314_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_314_, 0, v_inst_310_);
v___f_315_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_315_, 0, v_inst_310_);
v___x_316_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_316_, 0, lean_box(0));
lean_closure_set(v___x_316_, 1, lean_box(0));
lean_closure_set(v___x_316_, 2, v_inst_310_);
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v___f_312_);
v___x_318_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_318_, 0, lean_box(0));
lean_closure_set(v___x_318_, 1, lean_box(0));
lean_closure_set(v___x_318_, 2, v_inst_310_);
v___x_319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_319_, 0, v___x_317_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
lean_ctor_set(v___x_319_, 2, v___f_313_);
lean_ctor_set(v___x_319_, 3, v___f_314_);
lean_ctor_set(v___x_319_, 4, v___f_315_);
lean_inc_ref(v_inst_311_);
v___x_320_ = lean_alloc_closure((void*)(l_StateT_failure___boxed), 5, 3);
lean_closure_set(v___x_320_, 0, lean_box(0));
lean_closure_set(v___x_320_, 1, lean_box(0));
lean_closure_set(v___x_320_, 2, v_inst_311_);
v___x_321_ = lean_alloc_closure((void*)(l_StateT_orElse), 7, 3);
lean_closure_set(v___x_321_, 0, lean_box(0));
lean_closure_set(v___x_321_, 1, lean_box(0));
lean_closure_set(v___x_321_, 2, v_inst_311_);
v___x_322_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_322_, 0, v___x_319_);
lean_ctor_set(v___x_322_, 1, v___x_320_);
lean_ctor_set(v___x_322_, 2, v___x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_StateT_instAlternative(lean_object* v_00_u03c3_323_, lean_object* v_m_324_, lean_object* v_inst_325_, lean_object* v_inst_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_StateT_instAlternative___redArg(v_inst_325_, v_inst_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_StateT_get___redArg(lean_object* v_inst_328_, lean_object* v_s_329_){
_start:
{
lean_object* v_toApplicative_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_339_; 
v_toApplicative_330_ = lean_ctor_get(v_inst_328_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v_inst_328_);
if (v_isSharedCheck_339_ == 0)
{
lean_object* v_unused_340_; 
v_unused_340_ = lean_ctor_get(v_inst_328_, 1);
lean_dec(v_unused_340_);
v___x_332_ = v_inst_328_;
v_isShared_333_ = v_isSharedCheck_339_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_toApplicative_330_);
lean_dec(v_inst_328_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_339_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v_toPure_334_; lean_object* v___x_336_; 
v_toPure_334_ = lean_ctor_get(v_toApplicative_330_, 1);
lean_inc(v_toPure_334_);
lean_dec_ref(v_toApplicative_330_);
lean_inc(v_s_329_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 1, v_s_329_);
lean_ctor_set(v___x_332_, 0, v_s_329_);
v___x_336_ = v___x_332_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_s_329_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_s_329_);
v___x_336_ = v_reuseFailAlloc_338_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_337_; 
v___x_337_ = lean_apply_2(v_toPure_334_, lean_box(0), v___x_336_);
return v___x_337_;
}
}
}
}
LEAN_EXPORT lean_object* l_StateT_get(lean_object* v_00_u03c3_341_, lean_object* v_m_342_, lean_object* v_inst_343_, lean_object* v_s_344_){
_start:
{
lean_object* v_toApplicative_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_354_; 
v_toApplicative_345_ = lean_ctor_get(v_inst_343_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v_inst_343_);
if (v_isSharedCheck_354_ == 0)
{
lean_object* v_unused_355_; 
v_unused_355_ = lean_ctor_get(v_inst_343_, 1);
lean_dec(v_unused_355_);
v___x_347_ = v_inst_343_;
v_isShared_348_ = v_isSharedCheck_354_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_toApplicative_345_);
lean_dec(v_inst_343_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_354_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v_toPure_349_; lean_object* v___x_351_; 
v_toPure_349_ = lean_ctor_get(v_toApplicative_345_, 1);
lean_inc(v_toPure_349_);
lean_dec_ref(v_toApplicative_345_);
lean_inc(v_s_344_);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 1, v_s_344_);
lean_ctor_set(v___x_347_, 0, v_s_344_);
v___x_351_ = v___x_347_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_s_344_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_s_344_);
v___x_351_ = v_reuseFailAlloc_353_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_352_; 
v___x_352_ = lean_apply_2(v_toPure_349_, lean_box(0), v___x_351_);
return v___x_352_;
}
}
}
}
LEAN_EXPORT lean_object* l_StateT_set___redArg(lean_object* v_inst_356_, lean_object* v_s_x27_357_){
_start:
{
lean_object* v_toApplicative_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_368_; 
v_toApplicative_358_ = lean_ctor_get(v_inst_356_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v_inst_356_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; 
v_unused_369_ = lean_ctor_get(v_inst_356_, 1);
lean_dec(v_unused_369_);
v___x_360_ = v_inst_356_;
v_isShared_361_ = v_isSharedCheck_368_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_toApplicative_358_);
lean_dec(v_inst_356_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_368_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v_toPure_362_; lean_object* v___x_363_; lean_object* v___x_365_; 
v_toPure_362_ = lean_ctor_get(v_toApplicative_358_, 1);
lean_inc(v_toPure_362_);
lean_dec_ref(v_toApplicative_358_);
v___x_363_ = lean_box(0);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 1, v_s_x27_357_);
lean_ctor_set(v___x_360_, 0, v___x_363_);
v___x_365_ = v___x_360_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_s_x27_357_);
v___x_365_ = v_reuseFailAlloc_367_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_366_; 
v___x_366_ = lean_apply_2(v_toPure_362_, lean_box(0), v___x_365_);
return v___x_366_;
}
}
}
}
LEAN_EXPORT lean_object* l_StateT_set(lean_object* v_00_u03c3_370_, lean_object* v_m_371_, lean_object* v_inst_372_, lean_object* v_s_x27_373_, lean_object* v_x_374_){
_start:
{
lean_object* v_toApplicative_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_385_; 
v_toApplicative_375_ = lean_ctor_get(v_inst_372_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v_inst_372_);
if (v_isSharedCheck_385_ == 0)
{
lean_object* v_unused_386_; 
v_unused_386_ = lean_ctor_get(v_inst_372_, 1);
lean_dec(v_unused_386_);
v___x_377_ = v_inst_372_;
v_isShared_378_ = v_isSharedCheck_385_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_toApplicative_375_);
lean_dec(v_inst_372_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_385_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v_toPure_379_; lean_object* v___x_380_; lean_object* v___x_382_; 
v_toPure_379_ = lean_ctor_get(v_toApplicative_375_, 1);
lean_inc(v_toPure_379_);
lean_dec_ref(v_toApplicative_375_);
v___x_380_ = lean_box(0);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 1, v_s_x27_373_);
lean_ctor_set(v___x_377_, 0, v___x_380_);
v___x_382_ = v___x_377_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_380_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v_s_x27_373_);
v___x_382_ = v_reuseFailAlloc_384_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_object* v___x_383_; 
v___x_383_ = lean_apply_2(v_toPure_379_, lean_box(0), v___x_382_);
return v___x_383_;
}
}
}
}
LEAN_EXPORT lean_object* l_StateT_set___boxed(lean_object* v_00_u03c3_387_, lean_object* v_m_388_, lean_object* v_inst_389_, lean_object* v_s_x27_390_, lean_object* v_x_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_StateT_set(v_00_u03c3_387_, v_m_388_, v_inst_389_, v_s_x27_390_, v_x_391_);
lean_dec(v_x_391_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_StateT_modifyGet___redArg(lean_object* v_inst_393_, lean_object* v_f_394_, lean_object* v_s_395_){
_start:
{
lean_object* v_toApplicative_396_; lean_object* v_toPure_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v_toApplicative_396_ = lean_ctor_get(v_inst_393_, 0);
lean_inc_ref(v_toApplicative_396_);
lean_dec_ref(v_inst_393_);
v_toPure_397_ = lean_ctor_get(v_toApplicative_396_, 1);
lean_inc(v_toPure_397_);
lean_dec_ref(v_toApplicative_396_);
v___x_398_ = lean_apply_1(v_f_394_, v_s_395_);
v___x_399_ = lean_apply_2(v_toPure_397_, lean_box(0), v___x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_StateT_modifyGet(lean_object* v_00_u03c3_400_, lean_object* v_m_401_, lean_object* v_inst_402_, lean_object* v_00_u03b1_403_, lean_object* v_f_404_, lean_object* v_s_405_){
_start:
{
lean_object* v_toApplicative_406_; lean_object* v_toPure_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v_toApplicative_406_ = lean_ctor_get(v_inst_402_, 0);
lean_inc_ref(v_toApplicative_406_);
lean_dec_ref(v_inst_402_);
v_toPure_407_ = lean_ctor_get(v_toApplicative_406_, 1);
lean_inc(v_toPure_407_);
lean_dec_ref(v_toApplicative_406_);
v___x_408_ = lean_apply_1(v_f_404_, v_s_405_);
v___x_409_ = lean_apply_2(v_toPure_407_, lean_box(0), v___x_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_StateT_lift___redArg___lam__0(lean_object* v_s_410_, lean_object* v_toPure_411_, lean_object* v_a_412_){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_413_, 0, v_a_412_);
lean_ctor_set(v___x_413_, 1, v_s_410_);
v___x_414_ = lean_apply_2(v_toPure_411_, lean_box(0), v___x_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_StateT_lift___redArg(lean_object* v_inst_415_, lean_object* v_t_416_, lean_object* v_s_417_){
_start:
{
lean_object* v_toApplicative_418_; lean_object* v_toBind_419_; lean_object* v_toPure_420_; lean_object* v___f_421_; lean_object* v___x_422_; 
v_toApplicative_418_ = lean_ctor_get(v_inst_415_, 0);
lean_inc_ref(v_toApplicative_418_);
v_toBind_419_ = lean_ctor_get(v_inst_415_, 1);
lean_inc(v_toBind_419_);
lean_dec_ref(v_inst_415_);
v_toPure_420_ = lean_ctor_get(v_toApplicative_418_, 1);
lean_inc(v_toPure_420_);
lean_dec_ref(v_toApplicative_418_);
v___f_421_ = lean_alloc_closure((void*)(l_StateT_lift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_421_, 0, v_s_417_);
lean_closure_set(v___f_421_, 1, v_toPure_420_);
v___x_422_ = lean_apply_4(v_toBind_419_, lean_box(0), lean_box(0), v_t_416_, v___f_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_StateT_lift(lean_object* v_00_u03c3_423_, lean_object* v_m_424_, lean_object* v_inst_425_, lean_object* v_00_u03b1_426_, lean_object* v_t_427_, lean_object* v_s_428_){
_start:
{
lean_object* v_toApplicative_429_; lean_object* v_toBind_430_; lean_object* v_toPure_431_; lean_object* v___f_432_; lean_object* v___x_433_; 
v_toApplicative_429_ = lean_ctor_get(v_inst_425_, 0);
lean_inc_ref(v_toApplicative_429_);
v_toBind_430_ = lean_ctor_get(v_inst_425_, 1);
lean_inc(v_toBind_430_);
lean_dec_ref(v_inst_425_);
v_toPure_431_ = lean_ctor_get(v_toApplicative_429_, 1);
lean_inc(v_toPure_431_);
lean_dec_ref(v_toApplicative_429_);
v___f_432_ = lean_alloc_closure((void*)(l_StateT_lift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_432_, 0, v_s_428_);
lean_closure_set(v___f_432_, 1, v_toPure_431_);
v___x_433_ = lean_apply_4(v_toBind_430_, lean_box(0), lean_box(0), v_t_427_, v___f_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_StateT_instMonadLift___redArg(lean_object* v_inst_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 3);
lean_closure_set(v___x_435_, 0, lean_box(0));
lean_closure_set(v___x_435_, 1, lean_box(0));
lean_closure_set(v___x_435_, 2, v_inst_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_StateT_instMonadLift(lean_object* v_00_u03c3_436_, lean_object* v_m_437_, lean_object* v_inst_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 3);
lean_closure_set(v___x_439_, 0, lean_box(0));
lean_closure_set(v___x_439_, 1, lean_box(0));
lean_closure_set(v___x_439_, 2, v_inst_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_StateT_instMonadFunctor___lam__0(lean_object* v_00_u03b1_440_, lean_object* v_f_441_, lean_object* v_x_442_, lean_object* v_s_443_){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_apply_1(v_x_442_, v_s_443_);
v___x_445_ = lean_apply_2(v_f_441_, lean_box(0), v___x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_StateT_instMonadFunctor(lean_object* v_00_u03c3_447_, lean_object* v_m_448_){
_start:
{
lean_object* v___f_449_; 
v___f_449_ = ((lean_object*)(l_StateT_instMonadFunctor___closed__0));
return v___f_449_;
}
}
LEAN_EXPORT lean_object* l_StateT_instMonadExceptOf___redArg___lam__0(lean_object* v___y_450_, lean_object* v_toPure_451_, lean_object* v_a_452_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_453_, 0, v_a_452_);
lean_ctor_set(v___x_453_, 1, v___y_450_);
v___x_454_ = lean_apply_2(v_toPure_451_, lean_box(0), v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_StateT_instMonadExceptOf___redArg___lam__1(lean_object* v_inst_455_, lean_object* v_inst_456_, lean_object* v_00_u03b1_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v_toApplicative_460_; lean_object* v_throw_461_; lean_object* v_toBind_462_; lean_object* v_toPure_463_; lean_object* v___x_464_; lean_object* v___f_465_; lean_object* v___x_466_; 
v_toApplicative_460_ = lean_ctor_get(v_inst_456_, 0);
lean_inc_ref(v_toApplicative_460_);
v_throw_461_ = lean_ctor_get(v_inst_455_, 0);
lean_inc(v_throw_461_);
lean_dec_ref(v_inst_455_);
v_toBind_462_ = lean_ctor_get(v_inst_456_, 1);
lean_inc(v_toBind_462_);
lean_dec_ref(v_inst_456_);
v_toPure_463_ = lean_ctor_get(v_toApplicative_460_, 1);
lean_inc(v_toPure_463_);
lean_dec_ref(v_toApplicative_460_);
v___x_464_ = lean_apply_2(v_throw_461_, lean_box(0), v___y_458_);
v___f_465_ = lean_alloc_closure((void*)(l_StateT_instMonadExceptOf___redArg___lam__0), 3, 2);
lean_closure_set(v___f_465_, 0, v___y_459_);
lean_closure_set(v___f_465_, 1, v_toPure_463_);
v___x_466_ = lean_apply_4(v_toBind_462_, lean_box(0), lean_box(0), v___x_464_, v___f_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_StateT_instMonadExceptOf___redArg___lam__2(lean_object* v_c_467_, lean_object* v_s_468_, lean_object* v_e_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = lean_apply_2(v_c_467_, v_e_469_, v_s_468_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_StateT_instMonadExceptOf___redArg___lam__3(lean_object* v_inst_471_, lean_object* v_00_u03b1_472_, lean_object* v_x_473_, lean_object* v_c_474_, lean_object* v_s_475_){
_start:
{
lean_object* v_tryCatch_476_; lean_object* v___f_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v_tryCatch_476_ = lean_ctor_get(v_inst_471_, 1);
lean_inc(v_tryCatch_476_);
lean_dec_ref(v_inst_471_);
lean_inc(v_s_475_);
v___f_477_ = lean_alloc_closure((void*)(l_StateT_instMonadExceptOf___redArg___lam__2), 3, 2);
lean_closure_set(v___f_477_, 0, v_c_474_);
lean_closure_set(v___f_477_, 1, v_s_475_);
v___x_478_ = lean_apply_1(v_x_473_, v_s_475_);
v___x_479_ = lean_apply_3(v_tryCatch_476_, lean_box(0), v___x_478_, v___f_477_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_StateT_instMonadExceptOf___redArg(lean_object* v_inst_480_, lean_object* v_inst_481_){
_start:
{
lean_object* v___f_482_; lean_object* v___f_483_; lean_object* v___x_484_; 
lean_inc_ref(v_inst_481_);
v___f_482_ = lean_alloc_closure((void*)(l_StateT_instMonadExceptOf___redArg___lam__1), 5, 2);
lean_closure_set(v___f_482_, 0, v_inst_481_);
lean_closure_set(v___f_482_, 1, v_inst_480_);
v___f_483_ = lean_alloc_closure((void*)(l_StateT_instMonadExceptOf___redArg___lam__3), 5, 1);
lean_closure_set(v___f_483_, 0, v_inst_481_);
v___x_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_484_, 0, v___f_482_);
lean_ctor_set(v___x_484_, 1, v___f_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_StateT_instMonadExceptOf(lean_object* v_00_u03c3_485_, lean_object* v_m_486_, lean_object* v_inst_487_, lean_object* v_00_u03b5_488_, lean_object* v_inst_489_){
_start:
{
lean_object* v___f_490_; lean_object* v___f_491_; lean_object* v___x_492_; 
lean_inc_ref(v_inst_489_);
v___f_490_ = lean_alloc_closure((void*)(l_StateT_instMonadExceptOf___redArg___lam__1), 5, 2);
lean_closure_set(v___f_490_, 0, v_inst_489_);
lean_closure_set(v___f_490_, 1, v_inst_487_);
v___f_491_ = lean_alloc_closure((void*)(l_StateT_instMonadExceptOf___redArg___lam__3), 5, 1);
lean_closure_set(v___f_491_, 0, v_inst_489_);
v___x_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_492_, 0, v___f_490_);
lean_ctor_set(v___x_492_, 1, v___f_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_ForM_forIn___redArg___lam__0(lean_object* v_toPure_493_, lean_object* v_____do__lift_494_){
_start:
{
if (lean_obj_tag(v_____do__lift_494_) == 0)
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_503_; 
v_a_495_ = lean_ctor_get(v_____do__lift_494_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v_____do__lift_494_);
if (v_isSharedCheck_503_ == 0)
{
v___x_497_ = v_____do__lift_494_;
v_isShared_498_ = v_isSharedCheck_503_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v_____do__lift_494_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_503_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_495_);
v___x_500_ = v_reuseFailAlloc_502_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
lean_object* v___x_501_; 
v___x_501_ = lean_apply_2(v_toPure_493_, lean_box(0), v___x_500_);
return v___x_501_;
}
}
}
else
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_514_; 
v_a_504_ = lean_ctor_get(v_____do__lift_494_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v_____do__lift_494_);
if (v_isSharedCheck_514_ == 0)
{
v___x_506_ = v_____do__lift_494_;
v_isShared_507_ = v_isSharedCheck_514_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v_____do__lift_494_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_514_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_508_ = lean_box(0);
v___x_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
lean_ctor_set(v___x_509_, 1, v_a_504_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_509_);
v___x_511_ = v___x_506_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_509_);
v___x_511_ = v_reuseFailAlloc_513_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_512_; 
v___x_512_ = lean_apply_2(v_toPure_493_, lean_box(0), v___x_511_);
return v___x_512_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ForM_forIn___redArg___lam__1(lean_object* v_f_515_, lean_object* v_toBind_516_, lean_object* v___f_517_, lean_object* v_a_518_, lean_object* v_b_519_){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_apply_2(v_f_515_, v_a_518_, v_b_519_);
v___x_521_ = lean_apply_4(v_toBind_516_, lean_box(0), lean_box(0), v___x_520_, v___f_517_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_ForM_forIn___redArg___lam__2(lean_object* v_toPure_522_, lean_object* v_____do__lift_523_){
_start:
{
if (lean_obj_tag(v_____do__lift_523_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_525_; 
v_a_524_ = lean_ctor_get(v_____do__lift_523_, 0);
lean_inc(v_a_524_);
lean_dec_ref(v_____do__lift_523_);
v___x_525_ = lean_apply_2(v_toPure_522_, lean_box(0), v_a_524_);
return v___x_525_;
}
else
{
lean_object* v_a_526_; lean_object* v_snd_527_; lean_object* v___x_528_; 
v_a_526_ = lean_ctor_get(v_____do__lift_523_, 0);
lean_inc(v_a_526_);
lean_dec_ref(v_____do__lift_523_);
v_snd_527_ = lean_ctor_get(v_a_526_, 1);
lean_inc(v_snd_527_);
lean_dec(v_a_526_);
v___x_528_ = lean_apply_2(v_toPure_522_, lean_box(0), v_snd_527_);
return v___x_528_;
}
}
}
LEAN_EXPORT lean_object* l_ForM_forIn___redArg(lean_object* v_inst_529_, lean_object* v_inst_530_, lean_object* v_x_531_, lean_object* v_b_532_, lean_object* v_f_533_){
_start:
{
lean_object* v_toApplicative_534_; lean_object* v_toBind_535_; lean_object* v_toPure_536_; lean_object* v___f_537_; lean_object* v_g_538_; lean_object* v___f_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v_toApplicative_534_ = lean_ctor_get(v_inst_529_, 0);
lean_inc_ref(v_toApplicative_534_);
v_toBind_535_ = lean_ctor_get(v_inst_529_, 1);
lean_inc_n(v_toBind_535_, 2);
lean_dec_ref(v_inst_529_);
v_toPure_536_ = lean_ctor_get(v_toApplicative_534_, 1);
lean_inc_n(v_toPure_536_, 2);
lean_dec_ref(v_toApplicative_534_);
v___f_537_ = lean_alloc_closure((void*)(l_ForM_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_537_, 0, v_toPure_536_);
v_g_538_ = lean_alloc_closure((void*)(l_ForM_forIn___redArg___lam__1), 5, 3);
lean_closure_set(v_g_538_, 0, v_f_533_);
lean_closure_set(v_g_538_, 1, v_toBind_535_);
lean_closure_set(v_g_538_, 2, v___f_537_);
v___f_539_ = lean_alloc_closure((void*)(l_ForM_forIn___redArg___lam__2), 2, 1);
lean_closure_set(v___f_539_, 0, v_toPure_536_);
v___x_540_ = lean_apply_3(v_inst_530_, v_x_531_, v_g_538_, v_b_532_);
v___x_541_ = lean_apply_4(v_toBind_535_, lean_box(0), lean_box(0), v___x_540_, v___f_539_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_ForM_forIn(lean_object* v_m_542_, lean_object* v_00_u03b2_543_, lean_object* v_00_u03c1_544_, lean_object* v_00_u03b1_545_, lean_object* v_inst_546_, lean_object* v_inst_547_, lean_object* v_x_548_, lean_object* v_b_549_, lean_object* v_f_550_){
_start:
{
lean_object* v_toApplicative_551_; lean_object* v_toBind_552_; lean_object* v_toPure_553_; lean_object* v___f_554_; lean_object* v_g_555_; lean_object* v___f_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v_toApplicative_551_ = lean_ctor_get(v_inst_546_, 0);
lean_inc_ref(v_toApplicative_551_);
v_toBind_552_ = lean_ctor_get(v_inst_546_, 1);
lean_inc_n(v_toBind_552_, 2);
lean_dec_ref(v_inst_546_);
v_toPure_553_ = lean_ctor_get(v_toApplicative_551_, 1);
lean_inc_n(v_toPure_553_, 2);
lean_dec_ref(v_toApplicative_551_);
v___f_554_ = lean_alloc_closure((void*)(l_ForM_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_554_, 0, v_toPure_553_);
v_g_555_ = lean_alloc_closure((void*)(l_ForM_forIn___redArg___lam__1), 5, 3);
lean_closure_set(v_g_555_, 0, v_f_550_);
lean_closure_set(v_g_555_, 1, v_toBind_552_);
lean_closure_set(v_g_555_, 2, v___f_554_);
v___f_556_ = lean_alloc_closure((void*)(l_ForM_forIn___redArg___lam__2), 2, 1);
lean_closure_set(v___f_556_, 0, v_toPure_553_);
v___x_557_ = lean_apply_3(v_inst_547_, v_x_548_, v_g_555_, v_b_549_);
v___x_558_ = lean_apply_4(v_toBind_552_, lean_box(0), lean_box(0), v___x_557_, v___f_556_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_instMonadStateOfStateTOfMonad___redArg(lean_object* v_inst_559_){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
lean_inc_ref_n(v_inst_559_, 2);
v___x_560_ = lean_alloc_closure((void*)(l_StateT_get), 4, 3);
lean_closure_set(v___x_560_, 0, lean_box(0));
lean_closure_set(v___x_560_, 1, lean_box(0));
lean_closure_set(v___x_560_, 2, v_inst_559_);
v___x_561_ = lean_alloc_closure((void*)(l_StateT_set___boxed), 5, 3);
lean_closure_set(v___x_561_, 0, lean_box(0));
lean_closure_set(v___x_561_, 1, lean_box(0));
lean_closure_set(v___x_561_, 2, v_inst_559_);
v___x_562_ = lean_alloc_closure((void*)(l_StateT_modifyGet), 6, 3);
lean_closure_set(v___x_562_, 0, lean_box(0));
lean_closure_set(v___x_562_, 1, lean_box(0));
lean_closure_set(v___x_562_, 2, v_inst_559_);
v___x_563_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_563_, 0, v___x_560_);
lean_ctor_set(v___x_563_, 1, v___x_561_);
lean_ctor_set(v___x_563_, 2, v___x_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_instMonadStateOfStateTOfMonad(lean_object* v_00_u03c3_564_, lean_object* v_m_565_, lean_object* v_inst_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_instMonadStateOfStateTOfMonad___redArg(v_inst_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_StateT_monadControl___redArg___lam__0(lean_object* v_fst_568_, lean_object* v_00_u03b2_569_, lean_object* v_x_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = lean_apply_1(v_x_570_, v_fst_568_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_StateT_monadControl___redArg___lam__1(lean_object* v_snd_572_, lean_object* v_toPure_573_, lean_object* v_a_574_){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_575_, 0, v_a_574_);
lean_ctor_set(v___x_575_, 1, v_snd_572_);
v___x_576_ = lean_apply_2(v_toPure_573_, lean_box(0), v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_StateT_monadControl___redArg___lam__2(lean_object* v_f_577_, lean_object* v_toPure_578_, lean_object* v_toBind_579_, lean_object* v_____x_580_){
_start:
{
lean_object* v_fst_581_; lean_object* v_snd_582_; lean_object* v___f_583_; lean_object* v___x_584_; lean_object* v___f_585_; lean_object* v___x_586_; 
v_fst_581_ = lean_ctor_get(v_____x_580_, 0);
lean_inc(v_fst_581_);
v_snd_582_ = lean_ctor_get(v_____x_580_, 1);
lean_inc(v_snd_582_);
lean_dec_ref(v_____x_580_);
v___f_583_ = lean_alloc_closure((void*)(l_StateT_monadControl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_583_, 0, v_fst_581_);
v___x_584_ = lean_apply_1(v_f_577_, v___f_583_);
v___f_585_ = lean_alloc_closure((void*)(l_StateT_monadControl___redArg___lam__1), 3, 2);
lean_closure_set(v___f_585_, 0, v_snd_582_);
lean_closure_set(v___f_585_, 1, v_toPure_578_);
v___x_586_ = lean_apply_4(v_toBind_579_, lean_box(0), lean_box(0), v___x_584_, v___f_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_StateT_monadControl___redArg___lam__3(lean_object* v_inst_587_, lean_object* v_00_u03b1_588_, lean_object* v_f_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_toApplicative_591_; lean_object* v_toBind_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_603_; 
v_toApplicative_591_ = lean_ctor_get(v_inst_587_, 0);
v_toBind_592_ = lean_ctor_get(v_inst_587_, 1);
v_isSharedCheck_603_ = !lean_is_exclusive(v_inst_587_);
if (v_isSharedCheck_603_ == 0)
{
v___x_594_ = v_inst_587_;
v_isShared_595_ = v_isSharedCheck_603_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_toBind_592_);
lean_inc(v_toApplicative_591_);
lean_dec(v_inst_587_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_603_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v_toPure_596_; lean_object* v___f_597_; lean_object* v___x_599_; 
v_toPure_596_ = lean_ctor_get(v_toApplicative_591_, 1);
lean_inc_n(v_toPure_596_, 2);
lean_dec_ref(v_toApplicative_591_);
lean_inc(v_toBind_592_);
v___f_597_ = lean_alloc_closure((void*)(l_StateT_monadControl___redArg___lam__2), 4, 3);
lean_closure_set(v___f_597_, 0, v_f_589_);
lean_closure_set(v___f_597_, 1, v_toPure_596_);
lean_closure_set(v___f_597_, 2, v_toBind_592_);
lean_inc(v___y_590_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 1, v___y_590_);
lean_ctor_set(v___x_594_, 0, v___y_590_);
v___x_599_ = v___x_594_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___y_590_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v___y_590_);
v___x_599_ = v_reuseFailAlloc_602_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = lean_apply_2(v_toPure_596_, lean_box(0), v___x_599_);
v___x_601_ = lean_apply_4(v_toBind_592_, lean_box(0), lean_box(0), v___x_600_, v___f_597_);
return v___x_601_;
}
}
}
}
LEAN_EXPORT lean_object* l_StateT_monadControl___redArg___lam__4(lean_object* v_fst_604_, lean_object* v_toPure_605_, lean_object* v_____x_606_){
_start:
{
lean_object* v_snd_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_615_; 
v_snd_607_ = lean_ctor_get(v_____x_606_, 1);
v_isSharedCheck_615_ = !lean_is_exclusive(v_____x_606_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; 
v_unused_616_ = lean_ctor_get(v_____x_606_, 0);
lean_dec(v_unused_616_);
v___x_609_ = v_____x_606_;
v_isShared_610_ = v_isSharedCheck_615_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_snd_607_);
lean_dec(v_____x_606_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_615_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v_fst_604_);
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_fst_604_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_snd_607_);
v___x_612_ = v_reuseFailAlloc_614_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v___x_613_; 
v___x_613_ = lean_apply_2(v_toPure_605_, lean_box(0), v___x_612_);
return v___x_613_;
}
}
}
}
LEAN_EXPORT lean_object* l_StateT_monadControl___redArg___lam__5(lean_object* v_inst_617_, lean_object* v_____x_618_){
_start:
{
lean_object* v_fst_619_; lean_object* v_toApplicative_620_; lean_object* v_fst_621_; lean_object* v_snd_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_635_; 
v_fst_619_ = lean_ctor_get(v_____x_618_, 0);
lean_inc(v_fst_619_);
lean_dec_ref(v_____x_618_);
v_toApplicative_620_ = lean_ctor_get(v_inst_617_, 0);
lean_inc_ref(v_toApplicative_620_);
v_fst_621_ = lean_ctor_get(v_fst_619_, 0);
v_snd_622_ = lean_ctor_get(v_fst_619_, 1);
v_isSharedCheck_635_ = !lean_is_exclusive(v_fst_619_);
if (v_isSharedCheck_635_ == 0)
{
v___x_624_ = v_fst_619_;
v_isShared_625_ = v_isSharedCheck_635_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_snd_622_);
lean_inc(v_fst_621_);
lean_dec(v_fst_619_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_635_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v_toBind_626_; lean_object* v_toPure_627_; lean_object* v___f_628_; lean_object* v___x_629_; lean_object* v___x_631_; 
v_toBind_626_ = lean_ctor_get(v_inst_617_, 1);
lean_inc(v_toBind_626_);
lean_dec_ref(v_inst_617_);
v_toPure_627_ = lean_ctor_get(v_toApplicative_620_, 1);
lean_inc_n(v_toPure_627_, 2);
lean_dec_ref(v_toApplicative_620_);
v___f_628_ = lean_alloc_closure((void*)(l_StateT_monadControl___redArg___lam__4), 3, 2);
lean_closure_set(v___f_628_, 0, v_fst_621_);
lean_closure_set(v___f_628_, 1, v_toPure_627_);
v___x_629_ = lean_box(0);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 0, v___x_629_);
v___x_631_ = v___x_624_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_snd_622_);
v___x_631_ = v_reuseFailAlloc_634_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_apply_2(v_toPure_627_, lean_box(0), v___x_631_);
v___x_633_ = lean_apply_4(v_toBind_626_, lean_box(0), lean_box(0), v___x_632_, v___f_628_);
return v___x_633_;
}
}
}
}
LEAN_EXPORT lean_object* l_StateT_monadControl___redArg___lam__6(lean_object* v___y_636_, lean_object* v_toPure_637_, lean_object* v_a_638_){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_639_, 0, v_a_638_);
lean_ctor_set(v___x_639_, 1, v___y_636_);
v___x_640_ = lean_apply_2(v_toPure_637_, lean_box(0), v___x_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_StateT_monadControl___redArg___lam__7(lean_object* v_inst_641_, lean_object* v___f_642_, lean_object* v_00_u03b1_643_, lean_object* v_x_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_toApplicative_646_; lean_object* v_toBind_647_; lean_object* v_toPure_648_; lean_object* v___f_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v_toApplicative_646_ = lean_ctor_get(v_inst_641_, 0);
lean_inc_ref(v_toApplicative_646_);
v_toBind_647_ = lean_ctor_get(v_inst_641_, 1);
lean_inc_n(v_toBind_647_, 2);
lean_dec_ref(v_inst_641_);
v_toPure_648_ = lean_ctor_get(v_toApplicative_646_, 1);
lean_inc(v_toPure_648_);
lean_dec_ref(v_toApplicative_646_);
v___f_649_ = lean_alloc_closure((void*)(l_StateT_monadControl___redArg___lam__6), 3, 2);
lean_closure_set(v___f_649_, 0, v___y_645_);
lean_closure_set(v___f_649_, 1, v_toPure_648_);
v___x_650_ = lean_apply_4(v_toBind_647_, lean_box(0), lean_box(0), v_x_644_, v___f_649_);
v___x_651_ = lean_apply_4(v_toBind_647_, lean_box(0), lean_box(0), v___x_650_, v___f_642_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_StateT_monadControl___redArg(lean_object* v_inst_652_){
_start:
{
lean_object* v___f_653_; lean_object* v___f_654_; lean_object* v___f_655_; lean_object* v___x_656_; 
lean_inc_ref_n(v_inst_652_, 2);
v___f_653_ = lean_alloc_closure((void*)(l_StateT_monadControl___redArg___lam__3), 4, 1);
lean_closure_set(v___f_653_, 0, v_inst_652_);
v___f_654_ = lean_alloc_closure((void*)(l_StateT_monadControl___redArg___lam__5), 2, 1);
lean_closure_set(v___f_654_, 0, v_inst_652_);
v___f_655_ = lean_alloc_closure((void*)(l_StateT_monadControl___redArg___lam__7), 5, 2);
lean_closure_set(v___f_655_, 0, v_inst_652_);
lean_closure_set(v___f_655_, 1, v___f_654_);
v___x_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_656_, 0, v___f_653_);
lean_ctor_set(v___x_656_, 1, v___f_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_StateT_monadControl(lean_object* v_00_u03c3_657_, lean_object* v_m_658_, lean_object* v_inst_659_){
_start:
{
lean_object* v___f_660_; lean_object* v___f_661_; lean_object* v___f_662_; lean_object* v___x_663_; 
lean_inc_ref_n(v_inst_659_, 2);
v___f_660_ = lean_alloc_closure((void*)(l_StateT_monadControl___redArg___lam__3), 4, 1);
lean_closure_set(v___f_660_, 0, v_inst_659_);
v___f_661_ = lean_alloc_closure((void*)(l_StateT_monadControl___redArg___lam__5), 2, 1);
lean_closure_set(v___f_661_, 0, v_inst_659_);
v___f_662_ = lean_alloc_closure((void*)(l_StateT_monadControl___redArg___lam__7), 5, 2);
lean_closure_set(v___f_662_, 0, v_inst_659_);
lean_closure_set(v___f_662_, 1, v___f_661_);
v___x_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_663_, 0, v___f_660_);
lean_ctor_set(v___x_663_, 1, v___f_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_StateT_tryFinally___redArg___lam__0(lean_object* v_toPure_664_, lean_object* v_____x_665_){
_start:
{
lean_object* v_fst_666_; lean_object* v_snd_667_; lean_object* v_fst_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_685_; 
v_fst_666_ = lean_ctor_get(v_____x_665_, 0);
lean_inc(v_fst_666_);
v_snd_667_ = lean_ctor_get(v_____x_665_, 1);
lean_inc(v_snd_667_);
lean_dec_ref(v_____x_665_);
v_fst_668_ = lean_ctor_get(v_fst_666_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v_fst_666_);
if (v_isSharedCheck_685_ == 0)
{
lean_object* v_unused_686_; 
v_unused_686_ = lean_ctor_get(v_fst_666_, 1);
lean_dec(v_unused_686_);
v___x_670_ = v_fst_666_;
v_isShared_671_ = v_isSharedCheck_685_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_fst_668_);
lean_dec(v_fst_666_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_685_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v_fst_672_; lean_object* v_snd_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_684_; 
v_fst_672_ = lean_ctor_get(v_snd_667_, 0);
v_snd_673_ = lean_ctor_get(v_snd_667_, 1);
v_isSharedCheck_684_ = !lean_is_exclusive(v_snd_667_);
if (v_isSharedCheck_684_ == 0)
{
v___x_675_ = v_snd_667_;
v_isShared_676_ = v_isSharedCheck_684_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_snd_673_);
lean_inc(v_fst_672_);
lean_dec(v_snd_667_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_684_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 1, v_fst_672_);
lean_ctor_set(v___x_675_, 0, v_fst_668_);
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_fst_668_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_fst_672_);
v___x_678_ = v_reuseFailAlloc_683_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_680_; 
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 1, v_snd_673_);
lean_ctor_set(v___x_670_, 0, v___x_678_);
v___x_680_ = v___x_670_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_snd_673_);
v___x_680_ = v_reuseFailAlloc_682_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_681_; 
v___x_681_ = lean_apply_2(v_toPure_664_, lean_box(0), v___x_680_);
return v___x_681_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_StateT_tryFinally___redArg___lam__1(lean_object* v_h_687_, lean_object* v_s_688_, lean_object* v_x_689_){
_start:
{
if (lean_obj_tag(v_x_689_) == 0)
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = lean_box(0);
v___x_691_ = lean_apply_2(v_h_687_, v___x_690_, v_s_688_);
return v___x_691_;
}
else
{
lean_object* v_val_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_702_; 
lean_dec(v_s_688_);
v_val_692_ = lean_ctor_get(v_x_689_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v_x_689_);
if (v_isSharedCheck_702_ == 0)
{
v___x_694_ = v_x_689_;
v_isShared_695_ = v_isSharedCheck_702_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_val_692_);
lean_dec(v_x_689_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_702_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v_fst_696_; lean_object* v_snd_697_; lean_object* v___x_699_; 
v_fst_696_ = lean_ctor_get(v_val_692_, 0);
lean_inc(v_fst_696_);
v_snd_697_ = lean_ctor_get(v_val_692_, 1);
lean_inc(v_snd_697_);
lean_dec(v_val_692_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v_fst_696_);
v___x_699_ = v___x_694_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_fst_696_);
v___x_699_ = v_reuseFailAlloc_701_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_700_; 
v___x_700_ = lean_apply_2(v_h_687_, v___x_699_, v_snd_697_);
return v___x_700_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_StateT_tryFinally___redArg___lam__2(lean_object* v_inst_703_, lean_object* v_toBind_704_, lean_object* v___f_705_, lean_object* v_00_u03b1_706_, lean_object* v_00_u03b2_707_, lean_object* v_x_708_, lean_object* v_h_709_, lean_object* v_s_710_){
_start:
{
lean_object* v___f_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
lean_inc(v_s_710_);
v___f_711_ = lean_alloc_closure((void*)(l_StateT_tryFinally___redArg___lam__1), 3, 2);
lean_closure_set(v___f_711_, 0, v_h_709_);
lean_closure_set(v___f_711_, 1, v_s_710_);
v___x_712_ = lean_apply_1(v_x_708_, v_s_710_);
v___x_713_ = lean_apply_4(v_inst_703_, lean_box(0), lean_box(0), v___x_712_, v___f_711_);
v___x_714_ = lean_apply_4(v_toBind_704_, lean_box(0), lean_box(0), v___x_713_, v___f_705_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_StateT_tryFinally___redArg(lean_object* v_inst_715_, lean_object* v_inst_716_){
_start:
{
lean_object* v_toApplicative_717_; lean_object* v_toBind_718_; lean_object* v_toPure_719_; lean_object* v___f_720_; lean_object* v___f_721_; 
v_toApplicative_717_ = lean_ctor_get(v_inst_716_, 0);
lean_inc_ref(v_toApplicative_717_);
v_toBind_718_ = lean_ctor_get(v_inst_716_, 1);
lean_inc(v_toBind_718_);
lean_dec_ref(v_inst_716_);
v_toPure_719_ = lean_ctor_get(v_toApplicative_717_, 1);
lean_inc(v_toPure_719_);
lean_dec_ref(v_toApplicative_717_);
v___f_720_ = lean_alloc_closure((void*)(l_StateT_tryFinally___redArg___lam__0), 2, 1);
lean_closure_set(v___f_720_, 0, v_toPure_719_);
v___f_721_ = lean_alloc_closure((void*)(l_StateT_tryFinally___redArg___lam__2), 8, 3);
lean_closure_set(v___f_721_, 0, v_inst_715_);
lean_closure_set(v___f_721_, 1, v_toBind_718_);
lean_closure_set(v___f_721_, 2, v___f_720_);
return v___f_721_;
}
}
LEAN_EXPORT lean_object* l_StateT_tryFinally(lean_object* v_m_722_, lean_object* v_00_u03c3_723_, lean_object* v_inst_724_, lean_object* v_inst_725_){
_start:
{
lean_object* v_toApplicative_726_; lean_object* v_toBind_727_; lean_object* v_toPure_728_; lean_object* v___f_729_; lean_object* v___f_730_; 
v_toApplicative_726_ = lean_ctor_get(v_inst_725_, 0);
lean_inc_ref(v_toApplicative_726_);
v_toBind_727_ = lean_ctor_get(v_inst_725_, 1);
lean_inc(v_toBind_727_);
lean_dec_ref(v_inst_725_);
v_toPure_728_ = lean_ctor_get(v_toApplicative_726_, 1);
lean_inc(v_toPure_728_);
lean_dec_ref(v_toApplicative_726_);
v___f_729_ = lean_alloc_closure((void*)(l_StateT_tryFinally___redArg___lam__0), 2, 1);
lean_closure_set(v___f_729_, 0, v_toPure_728_);
v___f_730_ = lean_alloc_closure((void*)(l_StateT_tryFinally___redArg___lam__2), 8, 3);
lean_closure_set(v___f_730_, 0, v_inst_724_);
lean_closure_set(v___f_730_, 1, v_toBind_727_);
lean_closure_set(v___f_730_, 2, v___f_729_);
return v___f_730_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachStateTOfMonad___redArg___lam__0(lean_object* v_x_731_){
_start:
{
lean_object* v_fst_732_; lean_object* v_snd_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
v_fst_732_ = lean_ctor_get(v_x_731_, 0);
v_snd_733_ = lean_ctor_get(v_x_731_, 1);
v_isSharedCheck_740_ = !lean_is_exclusive(v_x_731_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v_x_731_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_snd_733_);
lean_inc(v_fst_732_);
lean_dec(v_x_731_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_fst_732_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_snd_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadAttachStateTOfMonad___redArg___lam__1(lean_object* v_toFunctor_741_, lean_object* v_inst_742_, lean_object* v___f_743_, lean_object* v_00_u03b1_744_, lean_object* v_x_745_, lean_object* v_s_746_){
_start:
{
lean_object* v_map_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v_map_747_ = lean_ctor_get(v_toFunctor_741_, 0);
lean_inc(v_map_747_);
lean_dec_ref(v_toFunctor_741_);
v___x_748_ = lean_apply_1(v_x_745_, v_s_746_);
v___x_749_ = lean_apply_2(v_inst_742_, lean_box(0), v___x_748_);
v___x_750_ = lean_apply_4(v_map_747_, lean_box(0), lean_box(0), v___f_743_, v___x_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachStateTOfMonad___redArg(lean_object* v_inst_752_, lean_object* v_inst_753_){
_start:
{
lean_object* v_toApplicative_754_; lean_object* v_toFunctor_755_; lean_object* v___f_756_; lean_object* v___f_757_; 
v_toApplicative_754_ = lean_ctor_get(v_inst_752_, 0);
lean_inc_ref(v_toApplicative_754_);
lean_dec_ref(v_inst_752_);
v_toFunctor_755_ = lean_ctor_get(v_toApplicative_754_, 0);
lean_inc_ref(v_toFunctor_755_);
lean_dec_ref(v_toApplicative_754_);
v___f_756_ = ((lean_object*)(l_instMonadAttachStateTOfMonad___redArg___closed__0));
v___f_757_ = lean_alloc_closure((void*)(l_instMonadAttachStateTOfMonad___redArg___lam__1), 6, 3);
lean_closure_set(v___f_757_, 0, v_toFunctor_755_);
lean_closure_set(v___f_757_, 1, v_inst_753_);
lean_closure_set(v___f_757_, 2, v___f_756_);
return v___f_757_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachStateTOfMonad(lean_object* v_m_758_, lean_object* v_00_u03c3_759_, lean_object* v_inst_760_, lean_object* v_inst_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_instMonadAttachStateTOfMonad___redArg(v_inst_760_, v_inst_761_);
return v___x_762_;
}
}
lean_object* runtime_initialize_Init_Control_Except(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Control_State(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Control_Except(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Control_State(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Control_Except(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Control_State(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Except(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Control_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Control_State(builtin);
}
#ifdef __cplusplus
}
#endif

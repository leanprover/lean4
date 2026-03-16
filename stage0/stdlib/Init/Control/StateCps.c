// Lean compiler output
// Module: Init.Control.StateCps
// Imports: public import Init.Control.Lawful.Basic public import Init.Ext
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
lean_object* l_Function_const___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_MonadAttach_trivial___redArg(lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_runK___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_runK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_run___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_run___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_run_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_run_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_run_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_run_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_instMonad___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_instMonad___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_instMonad___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_instMonad___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_instMonad___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_instMonad___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_instMonad___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_instMonad___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_instMonad___lam__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_instMonad___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_instMonad___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_StateCpsT_instMonad___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateCpsT_instMonad___lam__1, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_StateCpsT_instMonad___closed__0 = (const lean_object*)&l_StateCpsT_instMonad___closed__0_value;
static const lean_closure_object l_StateCpsT_instMonad___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateCpsT_instMonad___lam__2, .m_arity = 8, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_StateCpsT_instMonad___closed__0_value)} };
static const lean_object* l_StateCpsT_instMonad___closed__1 = (const lean_object*)&l_StateCpsT_instMonad___closed__1_value;
static const lean_closure_object l_StateCpsT_instMonad___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateCpsT_instMonad___lam__3, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_StateCpsT_instMonad___closed__2 = (const lean_object*)&l_StateCpsT_instMonad___closed__2_value;
static const lean_closure_object l_StateCpsT_instMonad___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateCpsT_instMonad___lam__5, .m_arity = 8, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_StateCpsT_instMonad___closed__0_value)} };
static const lean_object* l_StateCpsT_instMonad___closed__3 = (const lean_object*)&l_StateCpsT_instMonad___closed__3_value;
static const lean_closure_object l_StateCpsT_instMonad___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateCpsT_instMonad___lam__7, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_StateCpsT_instMonad___closed__4 = (const lean_object*)&l_StateCpsT_instMonad___closed__4_value;
static const lean_closure_object l_StateCpsT_instMonad___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateCpsT_instMonad___lam__10, .m_arity = 8, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_StateCpsT_instMonad___closed__4_value)} };
static const lean_object* l_StateCpsT_instMonad___closed__5 = (const lean_object*)&l_StateCpsT_instMonad___closed__5_value;
static const lean_closure_object l_StateCpsT_instMonad___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateCpsT_instMonad___lam__12, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_StateCpsT_instMonad___closed__6 = (const lean_object*)&l_StateCpsT_instMonad___closed__6_value;
static const lean_ctor_object l_StateCpsT_instMonad___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_StateCpsT_instMonad___closed__0_value),((lean_object*)&l_StateCpsT_instMonad___closed__1_value)}};
static const lean_object* l_StateCpsT_instMonad___closed__7 = (const lean_object*)&l_StateCpsT_instMonad___closed__7_value;
static const lean_ctor_object l_StateCpsT_instMonad___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_StateCpsT_instMonad___closed__7_value),((lean_object*)&l_StateCpsT_instMonad___closed__2_value),((lean_object*)&l_StateCpsT_instMonad___closed__3_value),((lean_object*)&l_StateCpsT_instMonad___closed__5_value),((lean_object*)&l_StateCpsT_instMonad___closed__6_value)}};
static const lean_object* l_StateCpsT_instMonad___closed__8 = (const lean_object*)&l_StateCpsT_instMonad___closed__8_value;
static const lean_ctor_object l_StateCpsT_instMonad___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_StateCpsT_instMonad___closed__8_value),((lean_object*)&l_StateCpsT_instMonad___closed__4_value)}};
static const lean_object* l_StateCpsT_instMonad___closed__9 = (const lean_object*)&l_StateCpsT_instMonad___closed__9_value;
LEAN_EXPORT lean_object* l_StateCpsT_instMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_instMonadStateOf___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_instMonadStateOf___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_instMonadStateOf___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_instMonadStateOf___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_StateCpsT_instMonadStateOf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateCpsT_instMonadStateOf___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_StateCpsT_instMonadStateOf___closed__0 = (const lean_object*)&l_StateCpsT_instMonadStateOf___closed__0_value;
static const lean_closure_object l_StateCpsT_instMonadStateOf___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateCpsT_instMonadStateOf___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_StateCpsT_instMonadStateOf___closed__1 = (const lean_object*)&l_StateCpsT_instMonadStateOf___closed__1_value;
static const lean_closure_object l_StateCpsT_instMonadStateOf___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateCpsT_instMonadStateOf___lam__2, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_StateCpsT_instMonadStateOf___closed__2 = (const lean_object*)&l_StateCpsT_instMonadStateOf___closed__2_value;
static const lean_ctor_object l_StateCpsT_instMonadStateOf___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_StateCpsT_instMonadStateOf___closed__0_value),((lean_object*)&l_StateCpsT_instMonadStateOf___closed__1_value),((lean_object*)&l_StateCpsT_instMonadStateOf___closed__2_value)}};
static const lean_object* l_StateCpsT_instMonadStateOf___closed__3 = (const lean_object*)&l_StateCpsT_instMonadStateOf___closed__3_value;
LEAN_EXPORT lean_object* l_StateCpsT_instMonadStateOf(lean_object*, lean_object*);
static lean_once_cell_t l_StateCpsT_instMonadAttach___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_StateCpsT_instMonadAttach___closed__0;
LEAN_EXPORT lean_object* l_StateCpsT_instMonadAttach(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_lift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_lift___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_lift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_instMonadLiftOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_instMonadLiftOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_instMonadLiftOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_instMonadLiftOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateCpsT_runK___redArg(lean_object* v_x_1_, lean_object* v_s_2_, lean_object* v_k_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_apply_3(v_x_1_, lean_box(0), v_s_2_, v_k_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_runK(lean_object* v_00_u03b1_5_, lean_object* v_00_u03c3_6_, lean_object* v_m_7_, lean_object* v_00_u03b2_8_, lean_object* v_x_9_, lean_object* v_s_10_, lean_object* v_k_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_apply_3(v_x_9_, lean_box(0), v_s_10_, v_k_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_run___redArg___lam__0(lean_object* v_toPure_13_, lean_object* v_a_14_, lean_object* v_s_15_){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_16_, 0, v_a_14_);
lean_ctor_set(v___x_16_, 1, v_s_15_);
v___x_17_ = lean_apply_2(v_toPure_13_, lean_box(0), v___x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_run___redArg(lean_object* v_inst_18_, lean_object* v_x_19_, lean_object* v_s_20_){
_start:
{
lean_object* v_toApplicative_21_; lean_object* v_toPure_22_; lean_object* v___f_23_; lean_object* v___x_24_; 
v_toApplicative_21_ = lean_ctor_get(v_inst_18_, 0);
lean_inc_ref(v_toApplicative_21_);
lean_dec_ref(v_inst_18_);
v_toPure_22_ = lean_ctor_get(v_toApplicative_21_, 1);
lean_inc(v_toPure_22_);
lean_dec_ref(v_toApplicative_21_);
v___f_23_ = lean_alloc_closure((void*)(l_StateCpsT_run___redArg___lam__0), 3, 1);
lean_closure_set(v___f_23_, 0, v_toPure_22_);
v___x_24_ = lean_apply_3(v_x_19_, lean_box(0), v_s_20_, v___f_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_run(lean_object* v_00_u03b1_25_, lean_object* v_00_u03c3_26_, lean_object* v_m_27_, lean_object* v_inst_28_, lean_object* v_x_29_, lean_object* v_s_30_){
_start:
{
lean_object* v_toApplicative_31_; lean_object* v_toPure_32_; lean_object* v___f_33_; lean_object* v___x_34_; 
v_toApplicative_31_ = lean_ctor_get(v_inst_28_, 0);
lean_inc_ref(v_toApplicative_31_);
lean_dec_ref(v_inst_28_);
v_toPure_32_ = lean_ctor_get(v_toApplicative_31_, 1);
lean_inc(v_toPure_32_);
lean_dec_ref(v_toApplicative_31_);
v___f_33_ = lean_alloc_closure((void*)(l_StateCpsT_run___redArg___lam__0), 3, 1);
lean_closure_set(v___f_33_, 0, v_toPure_32_);
v___x_34_ = lean_apply_3(v_x_29_, lean_box(0), v_s_30_, v___f_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_run_x27___redArg___lam__0(lean_object* v_toPure_35_, lean_object* v_a_36_, lean_object* v_x_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lean_apply_2(v_toPure_35_, lean_box(0), v_a_36_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_run_x27___redArg___lam__0___boxed(lean_object* v_toPure_39_, lean_object* v_a_40_, lean_object* v_x_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_StateCpsT_run_x27___redArg___lam__0(v_toPure_39_, v_a_40_, v_x_41_);
lean_dec(v_x_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_run_x27___redArg(lean_object* v_inst_43_, lean_object* v_x_44_, lean_object* v_s_45_){
_start:
{
lean_object* v_toApplicative_46_; lean_object* v_toPure_47_; lean_object* v___f_48_; lean_object* v___x_49_; 
v_toApplicative_46_ = lean_ctor_get(v_inst_43_, 0);
lean_inc_ref(v_toApplicative_46_);
lean_dec_ref(v_inst_43_);
v_toPure_47_ = lean_ctor_get(v_toApplicative_46_, 1);
lean_inc(v_toPure_47_);
lean_dec_ref(v_toApplicative_46_);
v___f_48_ = lean_alloc_closure((void*)(l_StateCpsT_run_x27___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_48_, 0, v_toPure_47_);
v___x_49_ = lean_apply_3(v_x_44_, lean_box(0), v_s_45_, v___f_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_run_x27(lean_object* v_00_u03b1_50_, lean_object* v_00_u03c3_51_, lean_object* v_m_52_, lean_object* v_inst_53_, lean_object* v_x_54_, lean_object* v_s_55_){
_start:
{
lean_object* v_toApplicative_56_; lean_object* v_toPure_57_; lean_object* v___f_58_; lean_object* v___x_59_; 
v_toApplicative_56_ = lean_ctor_get(v_inst_53_, 0);
lean_inc_ref(v_toApplicative_56_);
lean_dec_ref(v_inst_53_);
v_toPure_57_ = lean_ctor_get(v_toApplicative_56_, 1);
lean_inc(v_toPure_57_);
lean_dec_ref(v_toApplicative_56_);
v___f_58_ = lean_alloc_closure((void*)(l_StateCpsT_run_x27___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_58_, 0, v_toPure_57_);
v___x_59_ = lean_apply_3(v_x_54_, lean_box(0), v_s_55_, v___f_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_instMonad___lam__0(lean_object* v_f_60_, lean_object* v_k_61_, lean_object* v_a_62_, lean_object* v_s_63_){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = lean_apply_1(v_f_60_, v_a_62_);
v___x_65_ = lean_apply_2(v_k_61_, v___x_64_, v_s_63_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_instMonad___lam__1(lean_object* v_00_u03b1_66_, lean_object* v_00_u03b2_67_, lean_object* v_f_68_, lean_object* v_x_69_, lean_object* v_00_u03b4_70_, lean_object* v_s_71_, lean_object* v_k_72_){
_start:
{
lean_object* v___f_73_; lean_object* v___x_74_; 
v___f_73_ = lean_alloc_closure((void*)(l_StateCpsT_instMonad___lam__0), 4, 2);
lean_closure_set(v___f_73_, 0, v_f_68_);
lean_closure_set(v___f_73_, 1, v_k_72_);
v___x_74_ = lean_apply_3(v_x_69_, lean_box(0), v_s_71_, v___f_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_instMonad___lam__2(lean_object* v___f_75_, lean_object* v_00_u03b1_76_, lean_object* v_00_u03b2_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_83_, 0, lean_box(0));
lean_closure_set(v___x_83_, 1, lean_box(0));
lean_closure_set(v___x_83_, 2, v___y_78_);
v___x_84_ = lean_apply_7(v___f_75_, lean_box(0), lean_box(0), v___x_83_, v___y_79_, lean_box(0), v___y_81_, v___y_82_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_instMonad___lam__3(lean_object* v_00_u03b1_85_, lean_object* v_a_86_, lean_object* v_x_87_, lean_object* v_s_88_, lean_object* v_k_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = lean_apply_2(v_k_89_, v_a_86_, v_s_88_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_instMonad___lam__4(lean_object* v_x_91_, lean_object* v___f_92_, lean_object* v___y_93_, lean_object* v_a_94_, lean_object* v_s_95_){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = lean_box(0);
v___x_97_ = lean_apply_1(v_x_91_, v___x_96_);
v___x_98_ = lean_apply_7(v___f_92_, lean_box(0), lean_box(0), v_a_94_, v___x_97_, lean_box(0), v_s_95_, v___y_93_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_instMonad___lam__5(lean_object* v___f_99_, lean_object* v_00_u03b1_100_, lean_object* v_00_u03b2_101_, lean_object* v_f_102_, lean_object* v_x_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v___f_107_; lean_object* v___x_108_; 
v___f_107_ = lean_alloc_closure((void*)(l_StateCpsT_instMonad___lam__4), 5, 3);
lean_closure_set(v___f_107_, 0, v_x_103_);
lean_closure_set(v___f_107_, 1, v___f_99_);
lean_closure_set(v___f_107_, 2, v___y_106_);
v___x_108_ = lean_apply_3(v_f_102_, lean_box(0), v___y_105_, v___f_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_instMonad___lam__6(lean_object* v_f_109_, lean_object* v_k_110_, lean_object* v_a_111_, lean_object* v_s_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lean_apply_4(v_f_109_, v_a_111_, lean_box(0), v_s_112_, v_k_110_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_instMonad___lam__7(lean_object* v_00_u03b1_114_, lean_object* v_00_u03b2_115_, lean_object* v_x_116_, lean_object* v_f_117_, lean_object* v_00_u03b4_118_, lean_object* v_s_119_, lean_object* v_k_120_){
_start:
{
lean_object* v___f_121_; lean_object* v___x_122_; 
v___f_121_ = lean_alloc_closure((void*)(l_StateCpsT_instMonad___lam__6), 4, 2);
lean_closure_set(v___f_121_, 0, v_f_117_);
lean_closure_set(v___f_121_, 1, v_k_120_);
v___x_122_ = lean_apply_3(v_x_116_, lean_box(0), v_s_119_, v___f_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_instMonad___lam__8(lean_object* v_a_123_, lean_object* v_x_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = lean_apply_2(v___y_127_, v_a_123_, v___y_126_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_instMonad___lam__8___boxed(lean_object* v_a_129_, lean_object* v_x_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_StateCpsT_instMonad___lam__8(v_a_129_, v_x_130_, v___y_131_, v___y_132_, v___y_133_);
lean_dec(v_x_130_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_instMonad___lam__9(lean_object* v_y_135_, lean_object* v___f_136_, lean_object* v_a_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v___f_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___f_141_ = lean_alloc_closure((void*)(l_StateCpsT_instMonad___lam__8___boxed), 5, 1);
lean_closure_set(v___f_141_, 0, v_a_137_);
v___x_142_ = lean_box(0);
v___x_143_ = lean_apply_1(v_y_135_, v___x_142_);
v___x_144_ = lean_apply_7(v___f_136_, lean_box(0), lean_box(0), v___x_143_, v___f_141_, lean_box(0), v___y_139_, v___y_140_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_instMonad___lam__10(lean_object* v___f_145_, lean_object* v_00_u03b1_146_, lean_object* v_00_u03b2_147_, lean_object* v_x_148_, lean_object* v_y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v___f_153_; lean_object* v___x_154_; 
lean_inc(v___f_145_);
v___f_153_ = lean_alloc_closure((void*)(l_StateCpsT_instMonad___lam__9), 6, 2);
lean_closure_set(v___f_153_, 0, v_y_149_);
lean_closure_set(v___f_153_, 1, v___f_145_);
v___x_154_ = lean_apply_7(v___f_145_, lean_box(0), lean_box(0), v_x_148_, v___f_153_, lean_box(0), v___y_151_, v___y_152_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_instMonad___lam__11(lean_object* v_y_155_, lean_object* v___y_156_, lean_object* v_a_157_, lean_object* v_s_158_){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_box(0);
v___x_160_ = lean_apply_4(v_y_155_, v___x_159_, lean_box(0), v_s_158_, v___y_156_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_instMonad___lam__11___boxed(lean_object* v_y_161_, lean_object* v___y_162_, lean_object* v_a_163_, lean_object* v_s_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_StateCpsT_instMonad___lam__11(v_y_161_, v___y_162_, v_a_163_, v_s_164_);
lean_dec(v_a_163_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_instMonad___lam__12(lean_object* v_00_u03b1_166_, lean_object* v_00_u03b2_167_, lean_object* v_x_168_, lean_object* v_y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v___f_173_; lean_object* v___x_174_; 
v___f_173_ = lean_alloc_closure((void*)(l_StateCpsT_instMonad___lam__11___boxed), 4, 2);
lean_closure_set(v___f_173_, 0, v_y_169_);
lean_closure_set(v___f_173_, 1, v___y_172_);
v___x_174_ = lean_apply_3(v_x_168_, lean_box(0), v___y_171_, v___f_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_instMonad(lean_object* v_00_u03c3_197_, lean_object* v_m_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = ((lean_object*)(l_StateCpsT_instMonad___closed__9));
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_instMonadStateOf___lam__0(lean_object* v_x_200_, lean_object* v_s_201_, lean_object* v_k_202_){
_start:
{
lean_object* v___x_203_; 
lean_inc(v_s_201_);
v___x_203_ = lean_apply_2(v_k_202_, v_s_201_, v_s_201_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_instMonadStateOf___lam__1(lean_object* v_s_204_, lean_object* v_x_205_, lean_object* v_x_206_, lean_object* v_k_207_){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = lean_box(0);
v___x_209_ = lean_apply_2(v_k_207_, v___x_208_, v_s_204_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_instMonadStateOf___lam__1___boxed(lean_object* v_s_210_, lean_object* v_x_211_, lean_object* v_x_212_, lean_object* v_k_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_StateCpsT_instMonadStateOf___lam__1(v_s_210_, v_x_211_, v_x_212_, v_k_213_);
lean_dec(v_x_212_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_instMonadStateOf___lam__2(lean_object* v_00_u03b1_215_, lean_object* v_f_216_, lean_object* v_x_217_, lean_object* v_s_218_, lean_object* v_k_219_){
_start:
{
lean_object* v___x_220_; lean_object* v_fst_221_; lean_object* v_snd_222_; lean_object* v___x_223_; 
v___x_220_ = lean_apply_1(v_f_216_, v_s_218_);
v_fst_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_fst_221_);
v_snd_222_ = lean_ctor_get(v___x_220_, 1);
lean_inc(v_snd_222_);
lean_dec_ref(v___x_220_);
v___x_223_ = lean_apply_2(v_k_219_, v_fst_221_, v_snd_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_instMonadStateOf(lean_object* v_00_u03c3_231_, lean_object* v_m_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = ((lean_object*)(l_StateCpsT_instMonadStateOf___closed__3));
return v___x_233_;
}
}
static lean_object* _init_l_StateCpsT_instMonadAttach___closed__0(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = ((lean_object*)(l_StateCpsT_instMonad___closed__9));
v___x_235_ = l_MonadAttach_trivial___redArg(v___x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_instMonadAttach(lean_object* v_m_236_, lean_object* v_00_u03b5_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = lean_obj_once(&l_StateCpsT_instMonadAttach___closed__0, &l_StateCpsT_instMonadAttach___closed__0_once, _init_l_StateCpsT_instMonadAttach___closed__0);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_lift___redArg___lam__0(lean_object* v_k_239_, lean_object* v_s_240_, lean_object* v_x_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = lean_apply_2(v_k_239_, v_x_241_, v_s_240_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_lift___redArg(lean_object* v_inst_243_, lean_object* v_x_244_, lean_object* v_s_245_, lean_object* v_k_246_){
_start:
{
lean_object* v_toBind_247_; lean_object* v___f_248_; lean_object* v___x_249_; 
v_toBind_247_ = lean_ctor_get(v_inst_243_, 1);
lean_inc(v_toBind_247_);
lean_dec_ref(v_inst_243_);
v___f_248_ = lean_alloc_closure((void*)(l_StateCpsT_lift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_248_, 0, v_k_246_);
lean_closure_set(v___f_248_, 1, v_s_245_);
v___x_249_ = lean_apply_4(v_toBind_247_, lean_box(0), lean_box(0), v_x_244_, v___f_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_lift(lean_object* v_00_u03b1_250_, lean_object* v_00_u03c3_251_, lean_object* v_m_252_, lean_object* v_inst_253_, lean_object* v_x_254_, lean_object* v_x_255_, lean_object* v_s_256_, lean_object* v_k_257_){
_start:
{
lean_object* v_toBind_258_; lean_object* v___f_259_; lean_object* v___x_260_; 
v_toBind_258_ = lean_ctor_get(v_inst_253_, 1);
lean_inc(v_toBind_258_);
lean_dec_ref(v_inst_253_);
v___f_259_ = lean_alloc_closure((void*)(l_StateCpsT_lift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_259_, 0, v_k_257_);
lean_closure_set(v___f_259_, 1, v_s_256_);
v___x_260_ = lean_apply_4(v_toBind_258_, lean_box(0), lean_box(0), v_x_254_, v___f_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_instMonadLiftOfMonad___redArg___lam__0(lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v_x_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = lean_apply_2(v___y_261_, v_x_263_, v___y_262_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_instMonadLiftOfMonad___redArg___lam__1(lean_object* v_inst_265_, lean_object* v_00_u03b1_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v_toBind_271_; lean_object* v___f_272_; lean_object* v___x_273_; 
v_toBind_271_ = lean_ctor_get(v_inst_265_, 1);
lean_inc(v_toBind_271_);
lean_dec_ref(v_inst_265_);
v___f_272_ = lean_alloc_closure((void*)(l_StateCpsT_instMonadLiftOfMonad___redArg___lam__0), 3, 2);
lean_closure_set(v___f_272_, 0, v___y_270_);
lean_closure_set(v___f_272_, 1, v___y_269_);
v___x_273_ = lean_apply_4(v_toBind_271_, lean_box(0), lean_box(0), v___y_267_, v___f_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_instMonadLiftOfMonad___redArg(lean_object* v_inst_274_){
_start:
{
lean_object* v___f_275_; 
v___f_275_ = lean_alloc_closure((void*)(l_StateCpsT_instMonadLiftOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_275_, 0, v_inst_274_);
return v___f_275_;
}
}
LEAN_EXPORT lean_object* l_StateCpsT_instMonadLiftOfMonad(lean_object* v_00_u03c3_276_, lean_object* v_m_277_, lean_object* v_inst_278_){
_start:
{
lean_object* v___f_279_; 
v___f_279_ = lean_alloc_closure((void*)(l_StateCpsT_instMonadLiftOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_279_, 0, v_inst_278_);
return v___f_279_;
}
}
lean_object* runtime_initialize_Init_Control_Lawful_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Control_StateCps(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Control_Lawful_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Control_StateCps(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Control_Lawful_Basic(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Control_StateCps(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Lawful_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_StateCps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Control_StateCps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Control_StateCps(builtin);
}
#ifdef __cplusplus
}
#endif

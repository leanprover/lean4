// Lean compiler output
// Module: Init.Control.ExceptCps
// Imports: public import Init.Control.Lawful.Basic import Init.SimpLemmas
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
LEAN_EXPORT lean_object* l_ExceptCpsT_run___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_run___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_runK___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_runK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_runK___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_runCatch___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_runCatch(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_ExceptCpsT_instMonad___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ExceptCpsT_instMonad___lam__1, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ExceptCpsT_instMonad___closed__0 = (const lean_object*)&l_ExceptCpsT_instMonad___closed__0_value;
static const lean_closure_object l_ExceptCpsT_instMonad___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ExceptCpsT_instMonad___lam__2, .m_arity = 8, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_ExceptCpsT_instMonad___closed__0_value)} };
static const lean_object* l_ExceptCpsT_instMonad___closed__1 = (const lean_object*)&l_ExceptCpsT_instMonad___closed__1_value;
static const lean_closure_object l_ExceptCpsT_instMonad___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ExceptCpsT_instMonad___lam__3___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ExceptCpsT_instMonad___closed__2 = (const lean_object*)&l_ExceptCpsT_instMonad___closed__2_value;
static const lean_closure_object l_ExceptCpsT_instMonad___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ExceptCpsT_instMonad___lam__5, .m_arity = 8, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_ExceptCpsT_instMonad___closed__0_value)} };
static const lean_object* l_ExceptCpsT_instMonad___closed__3 = (const lean_object*)&l_ExceptCpsT_instMonad___closed__3_value;
static const lean_closure_object l_ExceptCpsT_instMonad___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ExceptCpsT_instMonad___lam__7, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ExceptCpsT_instMonad___closed__4 = (const lean_object*)&l_ExceptCpsT_instMonad___closed__4_value;
static const lean_closure_object l_ExceptCpsT_instMonad___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ExceptCpsT_instMonad___lam__10, .m_arity = 8, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_ExceptCpsT_instMonad___closed__4_value)} };
static const lean_object* l_ExceptCpsT_instMonad___closed__5 = (const lean_object*)&l_ExceptCpsT_instMonad___closed__5_value;
static const lean_closure_object l_ExceptCpsT_instMonad___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ExceptCpsT_instMonad___lam__12, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ExceptCpsT_instMonad___closed__6 = (const lean_object*)&l_ExceptCpsT_instMonad___closed__6_value;
static const lean_ctor_object l_ExceptCpsT_instMonad___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_ExceptCpsT_instMonad___closed__0_value),((lean_object*)&l_ExceptCpsT_instMonad___closed__1_value)}};
static const lean_object* l_ExceptCpsT_instMonad___closed__7 = (const lean_object*)&l_ExceptCpsT_instMonad___closed__7_value;
static const lean_ctor_object l_ExceptCpsT_instMonad___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_ExceptCpsT_instMonad___closed__7_value),((lean_object*)&l_ExceptCpsT_instMonad___closed__2_value),((lean_object*)&l_ExceptCpsT_instMonad___closed__3_value),((lean_object*)&l_ExceptCpsT_instMonad___closed__5_value),((lean_object*)&l_ExceptCpsT_instMonad___closed__6_value)}};
static const lean_object* l_ExceptCpsT_instMonad___closed__8 = (const lean_object*)&l_ExceptCpsT_instMonad___closed__8_value;
static const lean_ctor_object l_ExceptCpsT_instMonad___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_ExceptCpsT_instMonad___closed__8_value),((lean_object*)&l_ExceptCpsT_instMonad___closed__4_value)}};
static const lean_object* l_ExceptCpsT_instMonad___closed__9 = (const lean_object*)&l_ExceptCpsT_instMonad___closed__9_value;
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonadExceptOf___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonadExceptOf___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonadExceptOf___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonadExceptOf___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_ExceptCpsT_instMonadExceptOf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ExceptCpsT_instMonadExceptOf___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ExceptCpsT_instMonadExceptOf___closed__0 = (const lean_object*)&l_ExceptCpsT_instMonadExceptOf___closed__0_value;
static const lean_closure_object l_ExceptCpsT_instMonadExceptOf___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ExceptCpsT_instMonadExceptOf___lam__2, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ExceptCpsT_instMonadExceptOf___closed__1 = (const lean_object*)&l_ExceptCpsT_instMonadExceptOf___closed__1_value;
static const lean_ctor_object l_ExceptCpsT_instMonadExceptOf___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_ExceptCpsT_instMonadExceptOf___closed__0_value),((lean_object*)&l_ExceptCpsT_instMonadExceptOf___closed__1_value)}};
static const lean_object* l_ExceptCpsT_instMonadExceptOf___closed__2 = (const lean_object*)&l_ExceptCpsT_instMonadExceptOf___closed__2_value;
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonadExceptOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_lift___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_lift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonadLiftOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonadLiftOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonadLiftOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonadLiftOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_instInhabited___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_instInhabited___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_instInhabited___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_ExceptCpsT_instMonadAttach___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ExceptCpsT_instMonadAttach___closed__0;
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonadAttach(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptCpsT_run___redArg___lam__0(lean_object* v_toPure_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3_, 0, v_a_2_);
v___x_4_ = lean_apply_2(v_toPure_1_, lean_box(0), v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_run___redArg___lam__1(lean_object* v_toPure_5_, lean_object* v_e_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7_, 0, v_e_6_);
v___x_8_ = lean_apply_2(v_toPure_5_, lean_box(0), v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_run___redArg(lean_object* v_inst_9_, lean_object* v_x_10_){
_start:
{
lean_object* v_toApplicative_11_; lean_object* v_toPure_12_; lean_object* v___f_13_; lean_object* v___f_14_; lean_object* v___x_15_; 
v_toApplicative_11_ = lean_ctor_get(v_inst_9_, 0);
lean_inc_ref(v_toApplicative_11_);
lean_dec_ref(v_inst_9_);
v_toPure_12_ = lean_ctor_get(v_toApplicative_11_, 1);
lean_inc(v_toPure_12_);
lean_dec_ref(v_toApplicative_11_);
lean_inc(v_toPure_12_);
v___f_13_ = lean_alloc_closure((void*)(l_ExceptCpsT_run___redArg___lam__0), 2, 1);
lean_closure_set(v___f_13_, 0, v_toPure_12_);
v___f_14_ = lean_alloc_closure((void*)(l_ExceptCpsT_run___redArg___lam__1), 2, 1);
lean_closure_set(v___f_14_, 0, v_toPure_12_);
v___x_15_ = lean_apply_3(v_x_10_, lean_box(0), v___f_13_, v___f_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_run(lean_object* v_m_16_, lean_object* v_00_u03b5_17_, lean_object* v_00_u03b1_18_, lean_object* v_inst_19_, lean_object* v_x_20_){
_start:
{
lean_object* v_toApplicative_21_; lean_object* v_toPure_22_; lean_object* v___f_23_; lean_object* v___f_24_; lean_object* v___x_25_; 
v_toApplicative_21_ = lean_ctor_get(v_inst_19_, 0);
lean_inc_ref(v_toApplicative_21_);
lean_dec_ref(v_inst_19_);
v_toPure_22_ = lean_ctor_get(v_toApplicative_21_, 1);
lean_inc(v_toPure_22_);
lean_dec_ref(v_toApplicative_21_);
lean_inc(v_toPure_22_);
v___f_23_ = lean_alloc_closure((void*)(l_ExceptCpsT_run___redArg___lam__0), 2, 1);
lean_closure_set(v___f_23_, 0, v_toPure_22_);
v___f_24_ = lean_alloc_closure((void*)(l_ExceptCpsT_run___redArg___lam__1), 2, 1);
lean_closure_set(v___f_24_, 0, v_toPure_22_);
v___x_25_ = lean_apply_3(v_x_20_, lean_box(0), v___f_23_, v___f_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_runK___redArg(lean_object* v_x_26_, lean_object* v_ok_27_, lean_object* v_error_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lean_apply_3(v_x_26_, lean_box(0), v_ok_27_, v_error_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_runK(lean_object* v_m_30_, lean_object* v_00_u03b2_31_, lean_object* v_00_u03b5_32_, lean_object* v_00_u03b1_33_, lean_object* v_x_34_, lean_object* v_s_35_, lean_object* v_ok_36_, lean_object* v_error_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lean_apply_3(v_x_34_, lean_box(0), v_ok_36_, v_error_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_runK___boxed(lean_object* v_m_39_, lean_object* v_00_u03b2_40_, lean_object* v_00_u03b5_41_, lean_object* v_00_u03b1_42_, lean_object* v_x_43_, lean_object* v_s_44_, lean_object* v_ok_45_, lean_object* v_error_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_ExceptCpsT_runK(v_m_39_, v_00_u03b2_40_, v_00_u03b5_41_, v_00_u03b1_42_, v_x_43_, v_s_44_, v_ok_45_, v_error_46_);
lean_dec(v_s_44_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_runCatch___redArg(lean_object* v_inst_48_, lean_object* v_x_49_){
_start:
{
lean_object* v_toApplicative_50_; lean_object* v_toPure_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v_toApplicative_50_ = lean_ctor_get(v_inst_48_, 0);
lean_inc_ref(v_toApplicative_50_);
lean_dec_ref(v_inst_48_);
v_toPure_51_ = lean_ctor_get(v_toApplicative_50_, 1);
lean_inc(v_toPure_51_);
lean_dec_ref(v_toApplicative_50_);
v___x_52_ = lean_apply_1(v_toPure_51_, lean_box(0));
lean_inc(v___x_52_);
v___x_53_ = lean_apply_3(v_x_49_, lean_box(0), v___x_52_, v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_runCatch(lean_object* v_m_54_, lean_object* v_00_u03b1_55_, lean_object* v_inst_56_, lean_object* v_x_57_){
_start:
{
lean_object* v_toApplicative_58_; lean_object* v_toPure_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v_toApplicative_58_ = lean_ctor_get(v_inst_56_, 0);
lean_inc_ref(v_toApplicative_58_);
lean_dec_ref(v_inst_56_);
v_toPure_59_ = lean_ctor_get(v_toApplicative_58_, 1);
lean_inc(v_toPure_59_);
lean_dec_ref(v_toApplicative_58_);
v___x_60_ = lean_apply_1(v_toPure_59_, lean_box(0));
lean_inc(v___x_60_);
v___x_61_ = lean_apply_3(v_x_57_, lean_box(0), v___x_60_, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__0(lean_object* v_f_62_, lean_object* v_k_u2081_63_, lean_object* v_a_64_){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_apply_1(v_f_62_, v_a_64_);
v___x_66_ = lean_apply_1(v_k_u2081_63_, v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__1(lean_object* v_00_u03b1_67_, lean_object* v_00_u03b2_68_, lean_object* v_f_69_, lean_object* v_x_70_, lean_object* v_x_71_, lean_object* v_k_u2081_72_, lean_object* v_k_u2082_73_){
_start:
{
lean_object* v___f_74_; lean_object* v___x_75_; 
v___f_74_ = lean_alloc_closure((void*)(l_ExceptCpsT_instMonad___lam__0), 3, 2);
lean_closure_set(v___f_74_, 0, v_f_69_);
lean_closure_set(v___f_74_, 1, v_k_u2081_72_);
v___x_75_ = lean_apply_3(v_x_70_, lean_box(0), v___f_74_, v_k_u2082_73_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__2(lean_object* v___f_76_, lean_object* v_00_u03b1_77_, lean_object* v_00_u03b2_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_84_, 0, lean_box(0));
lean_closure_set(v___x_84_, 1, lean_box(0));
lean_closure_set(v___x_84_, 2, v___y_79_);
v___x_85_ = lean_apply_7(v___f_76_, lean_box(0), lean_box(0), v___x_84_, v___y_80_, lean_box(0), v___y_82_, v___y_83_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__3(lean_object* v_00_u03b1_86_, lean_object* v_a_87_, lean_object* v_x_88_, lean_object* v_k_89_, lean_object* v_x_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_apply_1(v_k_89_, v_a_87_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__3___boxed(lean_object* v_00_u03b1_92_, lean_object* v_a_93_, lean_object* v_x_94_, lean_object* v_k_95_, lean_object* v_x_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_ExceptCpsT_instMonad___lam__3(v_00_u03b1_92_, v_a_93_, v_x_94_, v_k_95_, v_x_96_);
lean_dec(v_x_96_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__4(lean_object* v_x_98_, lean_object* v___f_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v_a_102_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = lean_box(0);
v___x_104_ = lean_apply_1(v_x_98_, v___x_103_);
v___x_105_ = lean_apply_7(v___f_99_, lean_box(0), lean_box(0), v_a_102_, v___x_104_, lean_box(0), v___y_100_, v___y_101_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__5(lean_object* v___f_106_, lean_object* v_00_u03b1_107_, lean_object* v_00_u03b2_108_, lean_object* v_f_109_, lean_object* v_x_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v___f_114_; lean_object* v___x_115_; 
lean_inc(v___y_113_);
v___f_114_ = lean_alloc_closure((void*)(l_ExceptCpsT_instMonad___lam__4), 5, 4);
lean_closure_set(v___f_114_, 0, v_x_110_);
lean_closure_set(v___f_114_, 1, v___f_106_);
lean_closure_set(v___f_114_, 2, v___y_112_);
lean_closure_set(v___f_114_, 3, v___y_113_);
v___x_115_ = lean_apply_3(v_f_109_, lean_box(0), v___f_114_, v___y_113_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__6(lean_object* v_f_116_, lean_object* v_k_u2081_117_, lean_object* v_k_u2082_118_, lean_object* v_a_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lean_apply_4(v_f_116_, v_a_119_, lean_box(0), v_k_u2081_117_, v_k_u2082_118_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__7(lean_object* v_00_u03b1_121_, lean_object* v_00_u03b2_122_, lean_object* v_x_123_, lean_object* v_f_124_, lean_object* v_x_125_, lean_object* v_k_u2081_126_, lean_object* v_k_u2082_127_){
_start:
{
lean_object* v___f_128_; lean_object* v___x_129_; 
lean_inc(v_k_u2082_127_);
v___f_128_ = lean_alloc_closure((void*)(l_ExceptCpsT_instMonad___lam__6), 4, 3);
lean_closure_set(v___f_128_, 0, v_f_124_);
lean_closure_set(v___f_128_, 1, v_k_u2081_126_);
lean_closure_set(v___f_128_, 2, v_k_u2082_127_);
v___x_129_ = lean_apply_3(v_x_123_, lean_box(0), v___f_128_, v_k_u2082_127_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__8(lean_object* v_a_130_, lean_object* v_x_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = lean_apply_1(v___y_133_, v_a_130_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__8___boxed(lean_object* v_a_136_, lean_object* v_x_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_ExceptCpsT_instMonad___lam__8(v_a_136_, v_x_137_, v___y_138_, v___y_139_, v___y_140_);
lean_dec(v___y_140_);
lean_dec(v_x_137_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__9(lean_object* v_y_142_, lean_object* v___f_143_, lean_object* v_a_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v___f_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___f_148_ = lean_alloc_closure((void*)(l_ExceptCpsT_instMonad___lam__8___boxed), 5, 1);
lean_closure_set(v___f_148_, 0, v_a_144_);
v___x_149_ = lean_box(0);
v___x_150_ = lean_apply_1(v_y_142_, v___x_149_);
v___x_151_ = lean_apply_7(v___f_143_, lean_box(0), lean_box(0), v___x_150_, v___f_148_, lean_box(0), v___y_146_, v___y_147_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__10(lean_object* v___f_152_, lean_object* v_00_u03b1_153_, lean_object* v_00_u03b2_154_, lean_object* v_x_155_, lean_object* v_y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v___f_160_; lean_object* v___x_161_; 
lean_inc(v___f_152_);
v___f_160_ = lean_alloc_closure((void*)(l_ExceptCpsT_instMonad___lam__9), 6, 2);
lean_closure_set(v___f_160_, 0, v_y_156_);
lean_closure_set(v___f_160_, 1, v___f_152_);
v___x_161_ = lean_apply_7(v___f_152_, lean_box(0), lean_box(0), v_x_155_, v___f_160_, lean_box(0), v___y_158_, v___y_159_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__11(lean_object* v_y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v_a_165_){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_box(0);
v___x_167_ = lean_apply_4(v_y_162_, v___x_166_, lean_box(0), v___y_163_, v___y_164_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__11___boxed(lean_object* v_y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v_a_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_ExceptCpsT_instMonad___lam__11(v_y_168_, v___y_169_, v___y_170_, v_a_171_);
lean_dec(v_a_171_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__12(lean_object* v_00_u03b1_173_, lean_object* v_00_u03b2_174_, lean_object* v_x_175_, lean_object* v_y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v___f_180_; lean_object* v___x_181_; 
lean_inc(v___y_179_);
v___f_180_ = lean_alloc_closure((void*)(l_ExceptCpsT_instMonad___lam__11___boxed), 4, 3);
lean_closure_set(v___f_180_, 0, v_y_176_);
lean_closure_set(v___f_180_, 1, v___y_178_);
lean_closure_set(v___f_180_, 2, v___y_179_);
v___x_181_ = lean_apply_3(v_x_175_, lean_box(0), v___f_180_, v___y_179_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad(lean_object* v_00_u03b5_204_, lean_object* v_m_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = ((lean_object*)(l_ExceptCpsT_instMonad___closed__9));
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonadExceptOf___lam__0(lean_object* v_00_u03b1_207_, lean_object* v_e_208_, lean_object* v_x_209_, lean_object* v_x_210_, lean_object* v_k_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = lean_apply_1(v_k_211_, v_e_208_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonadExceptOf___lam__0___boxed(lean_object* v_00_u03b1_213_, lean_object* v_e_214_, lean_object* v_x_215_, lean_object* v_x_216_, lean_object* v_k_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_ExceptCpsT_instMonadExceptOf___lam__0(v_00_u03b1_213_, v_e_214_, v_x_215_, v_x_216_, v_k_217_);
lean_dec(v_x_216_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonadExceptOf___lam__1(lean_object* v_handle_219_, lean_object* v_k_u2081_220_, lean_object* v_k_u2082_221_, lean_object* v_e_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = lean_apply_4(v_handle_219_, v_e_222_, lean_box(0), v_k_u2081_220_, v_k_u2082_221_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonadExceptOf___lam__2(lean_object* v_00_u03b1_224_, lean_object* v_x_225_, lean_object* v_handle_226_, lean_object* v_x_227_, lean_object* v_k_u2081_228_, lean_object* v_k_u2082_229_){
_start:
{
lean_object* v___f_230_; lean_object* v___x_231_; 
lean_inc(v_k_u2081_228_);
v___f_230_ = lean_alloc_closure((void*)(l_ExceptCpsT_instMonadExceptOf___lam__1), 4, 3);
lean_closure_set(v___f_230_, 0, v_handle_226_);
lean_closure_set(v___f_230_, 1, v_k_u2081_228_);
lean_closure_set(v___f_230_, 2, v_k_u2082_229_);
v___x_231_ = lean_apply_3(v_x_225_, lean_box(0), v_k_u2081_228_, v___f_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonadExceptOf(lean_object* v_00_u03b5_237_, lean_object* v_m_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = ((lean_object*)(l_ExceptCpsT_instMonadExceptOf___closed__2));
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_lift___redArg(lean_object* v_inst_240_, lean_object* v_x_241_, lean_object* v_k_242_){
_start:
{
lean_object* v_toBind_243_; lean_object* v___x_244_; 
v_toBind_243_ = lean_ctor_get(v_inst_240_, 1);
lean_inc(v_toBind_243_);
lean_dec_ref(v_inst_240_);
v___x_244_ = lean_apply_4(v_toBind_243_, lean_box(0), lean_box(0), v_x_241_, v_k_242_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_lift(lean_object* v_m_245_, lean_object* v_00_u03b1_246_, lean_object* v_00_u03b5_247_, lean_object* v_inst_248_, lean_object* v_x_249_, lean_object* v_x_250_, lean_object* v_k_251_, lean_object* v_x_252_){
_start:
{
lean_object* v_toBind_253_; lean_object* v___x_254_; 
v_toBind_253_ = lean_ctor_get(v_inst_248_, 1);
lean_inc(v_toBind_253_);
lean_dec_ref(v_inst_248_);
v___x_254_ = lean_apply_4(v_toBind_253_, lean_box(0), lean_box(0), v_x_249_, v_k_251_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_lift___boxed(lean_object* v_m_255_, lean_object* v_00_u03b1_256_, lean_object* v_00_u03b5_257_, lean_object* v_inst_258_, lean_object* v_x_259_, lean_object* v_x_260_, lean_object* v_k_261_, lean_object* v_x_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_ExceptCpsT_lift(v_m_255_, v_00_u03b1_256_, v_00_u03b5_257_, v_inst_258_, v_x_259_, v_x_260_, v_k_261_, v_x_262_);
lean_dec(v_x_262_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonadLiftOfMonad___redArg___lam__0(lean_object* v_inst_264_, lean_object* v_00_u03b1_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v_toBind_270_; lean_object* v___x_271_; 
v_toBind_270_ = lean_ctor_get(v_inst_264_, 1);
lean_inc(v_toBind_270_);
lean_dec_ref(v_inst_264_);
v___x_271_ = lean_apply_4(v_toBind_270_, lean_box(0), lean_box(0), v___y_266_, v___y_268_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonadLiftOfMonad___redArg___lam__0___boxed(lean_object* v_inst_272_, lean_object* v_00_u03b1_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_ExceptCpsT_instMonadLiftOfMonad___redArg___lam__0(v_inst_272_, v_00_u03b1_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
lean_dec(v___y_277_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonadLiftOfMonad___redArg(lean_object* v_inst_279_){
_start:
{
lean_object* v___f_280_; 
v___f_280_ = lean_alloc_closure((void*)(l_ExceptCpsT_instMonadLiftOfMonad___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_280_, 0, v_inst_279_);
return v___f_280_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonadLiftOfMonad(lean_object* v_m_281_, lean_object* v_00_u03c3_282_, lean_object* v_inst_283_){
_start:
{
lean_object* v___f_284_; 
v___f_284_ = lean_alloc_closure((void*)(l_ExceptCpsT_instMonadLiftOfMonad___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_284_, 0, v_inst_283_);
return v___f_284_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instInhabited___redArg___lam__0(lean_object* v_inst_285_, lean_object* v_x_286_, lean_object* v_x_287_, lean_object* v_k_u2082_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = lean_apply_1(v_k_u2082_288_, v_inst_285_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instInhabited___redArg___lam__0___boxed(lean_object* v_inst_290_, lean_object* v_x_291_, lean_object* v_x_292_, lean_object* v_k_u2082_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_ExceptCpsT_instInhabited___redArg___lam__0(v_inst_290_, v_x_291_, v_x_292_, v_k_u2082_293_);
lean_dec(v_x_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instInhabited___redArg(lean_object* v_inst_295_){
_start:
{
lean_object* v___f_296_; 
v___f_296_ = lean_alloc_closure((void*)(l_ExceptCpsT_instInhabited___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_296_, 0, v_inst_295_);
return v___f_296_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instInhabited(lean_object* v_00_u03b5_297_, lean_object* v_m_298_, lean_object* v_00_u03b1_299_, lean_object* v_inst_300_){
_start:
{
lean_object* v___f_301_; 
v___f_301_ = lean_alloc_closure((void*)(l_ExceptCpsT_instInhabited___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_301_, 0, v_inst_300_);
return v___f_301_;
}
}
static lean_object* _init_l_ExceptCpsT_instMonadAttach___closed__0(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = ((lean_object*)(l_ExceptCpsT_instMonad___closed__9));
v___x_303_ = l_MonadAttach_trivial___redArg(v___x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonadAttach(lean_object* v_00_u03b5_304_, lean_object* v_m_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = lean_obj_once(&l_ExceptCpsT_instMonadAttach___closed__0, &l_ExceptCpsT_instMonadAttach___closed__0_once, _init_l_ExceptCpsT_instMonadAttach___closed__0);
return v___x_306_;
}
}
lean_object* runtime_initialize_Init_Control_Lawful_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_SimpLemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Control_ExceptCps(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Control_Lawful_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_SimpLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Control_ExceptCps(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Control_Lawful_Basic(uint8_t builtin);
lean_object* initialize_Init_SimpLemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Control_ExceptCps(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Lawful_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_SimpLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_ExceptCps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Control_ExceptCps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Control_ExceptCps(builtin);
}
#ifdef __cplusplus
}
#endif

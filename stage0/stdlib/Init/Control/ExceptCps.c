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
LEAN_EXPORT lean_object* l_ExceptCpsT_runK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc_n(v_toPure_12_, 2);
lean_dec_ref(v_toApplicative_11_);
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
lean_inc_n(v_toPure_22_, 2);
lean_dec_ref(v_toApplicative_21_);
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
LEAN_EXPORT lean_object* l_ExceptCpsT_runK(lean_object* v_m_30_, lean_object* v_00_u03b2_31_, lean_object* v_00_u03b5_32_, lean_object* v_00_u03b1_33_, lean_object* v_x_34_, lean_object* v_ok_35_, lean_object* v_error_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_apply_3(v_x_34_, lean_box(0), v_ok_35_, v_error_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_runCatch___redArg(lean_object* v_inst_38_, lean_object* v_x_39_){
_start:
{
lean_object* v_toApplicative_40_; lean_object* v_toPure_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v_toApplicative_40_ = lean_ctor_get(v_inst_38_, 0);
lean_inc_ref(v_toApplicative_40_);
lean_dec_ref(v_inst_38_);
v_toPure_41_ = lean_ctor_get(v_toApplicative_40_, 1);
lean_inc(v_toPure_41_);
lean_dec_ref(v_toApplicative_40_);
v___x_42_ = lean_apply_1(v_toPure_41_, lean_box(0));
lean_inc(v___x_42_);
v___x_43_ = lean_apply_3(v_x_39_, lean_box(0), v___x_42_, v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_runCatch(lean_object* v_m_44_, lean_object* v_00_u03b1_45_, lean_object* v_inst_46_, lean_object* v_x_47_){
_start:
{
lean_object* v_toApplicative_48_; lean_object* v_toPure_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v_toApplicative_48_ = lean_ctor_get(v_inst_46_, 0);
lean_inc_ref(v_toApplicative_48_);
lean_dec_ref(v_inst_46_);
v_toPure_49_ = lean_ctor_get(v_toApplicative_48_, 1);
lean_inc(v_toPure_49_);
lean_dec_ref(v_toApplicative_48_);
v___x_50_ = lean_apply_1(v_toPure_49_, lean_box(0));
lean_inc(v___x_50_);
v___x_51_ = lean_apply_3(v_x_47_, lean_box(0), v___x_50_, v___x_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__0(lean_object* v_f_52_, lean_object* v_k_u2081_53_, lean_object* v_a_54_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_apply_1(v_f_52_, v_a_54_);
v___x_56_ = lean_apply_1(v_k_u2081_53_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__1(lean_object* v_00_u03b1_57_, lean_object* v_00_u03b2_58_, lean_object* v_f_59_, lean_object* v_x_60_, lean_object* v_x_61_, lean_object* v_k_u2081_62_, lean_object* v_k_u2082_63_){
_start:
{
lean_object* v___f_64_; lean_object* v___x_65_; 
v___f_64_ = lean_alloc_closure((void*)(l_ExceptCpsT_instMonad___lam__0), 3, 2);
lean_closure_set(v___f_64_, 0, v_f_59_);
lean_closure_set(v___f_64_, 1, v_k_u2081_62_);
v___x_65_ = lean_apply_3(v_x_60_, lean_box(0), v___f_64_, v_k_u2082_63_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__2(lean_object* v___f_66_, lean_object* v_00_u03b1_67_, lean_object* v_00_u03b2_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_74_, 0, lean_box(0));
lean_closure_set(v___x_74_, 1, lean_box(0));
lean_closure_set(v___x_74_, 2, v___y_69_);
v___x_75_ = lean_apply_7(v___f_66_, lean_box(0), lean_box(0), v___x_74_, v___y_70_, lean_box(0), v___y_72_, v___y_73_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__3(lean_object* v_00_u03b1_76_, lean_object* v_a_77_, lean_object* v_x_78_, lean_object* v_k_79_, lean_object* v_x_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lean_apply_1(v_k_79_, v_a_77_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__3___boxed(lean_object* v_00_u03b1_82_, lean_object* v_a_83_, lean_object* v_x_84_, lean_object* v_k_85_, lean_object* v_x_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_ExceptCpsT_instMonad___lam__3(v_00_u03b1_82_, v_a_83_, v_x_84_, v_k_85_, v_x_86_);
lean_dec(v_x_86_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__4(lean_object* v_x_88_, lean_object* v___f_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v_a_92_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = lean_box(0);
v___x_94_ = lean_apply_1(v_x_88_, v___x_93_);
v___x_95_ = lean_apply_7(v___f_89_, lean_box(0), lean_box(0), v_a_92_, v___x_94_, lean_box(0), v___y_90_, v___y_91_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__5(lean_object* v___f_96_, lean_object* v_00_u03b1_97_, lean_object* v_00_u03b2_98_, lean_object* v_f_99_, lean_object* v_x_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v___f_104_; lean_object* v___x_105_; 
lean_inc(v___y_103_);
v___f_104_ = lean_alloc_closure((void*)(l_ExceptCpsT_instMonad___lam__4), 5, 4);
lean_closure_set(v___f_104_, 0, v_x_100_);
lean_closure_set(v___f_104_, 1, v___f_96_);
lean_closure_set(v___f_104_, 2, v___y_102_);
lean_closure_set(v___f_104_, 3, v___y_103_);
v___x_105_ = lean_apply_3(v_f_99_, lean_box(0), v___f_104_, v___y_103_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__6(lean_object* v_f_106_, lean_object* v_k_u2081_107_, lean_object* v_k_u2082_108_, lean_object* v_a_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_apply_4(v_f_106_, v_a_109_, lean_box(0), v_k_u2081_107_, v_k_u2082_108_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__7(lean_object* v_00_u03b1_111_, lean_object* v_00_u03b2_112_, lean_object* v_x_113_, lean_object* v_f_114_, lean_object* v_x_115_, lean_object* v_k_u2081_116_, lean_object* v_k_u2082_117_){
_start:
{
lean_object* v___f_118_; lean_object* v___x_119_; 
lean_inc(v_k_u2082_117_);
v___f_118_ = lean_alloc_closure((void*)(l_ExceptCpsT_instMonad___lam__6), 4, 3);
lean_closure_set(v___f_118_, 0, v_f_114_);
lean_closure_set(v___f_118_, 1, v_k_u2081_116_);
lean_closure_set(v___f_118_, 2, v_k_u2082_117_);
v___x_119_ = lean_apply_3(v_x_113_, lean_box(0), v___f_118_, v_k_u2082_117_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__8(lean_object* v_a_120_, lean_object* v_x_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = lean_apply_1(v___y_123_, v_a_120_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__8___boxed(lean_object* v_a_126_, lean_object* v_x_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_ExceptCpsT_instMonad___lam__8(v_a_126_, v_x_127_, v___y_128_, v___y_129_, v___y_130_);
lean_dec(v___y_130_);
lean_dec(v_x_127_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__9(lean_object* v_y_132_, lean_object* v___f_133_, lean_object* v_a_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v___f_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___f_138_ = lean_alloc_closure((void*)(l_ExceptCpsT_instMonad___lam__8___boxed), 5, 1);
lean_closure_set(v___f_138_, 0, v_a_134_);
v___x_139_ = lean_box(0);
v___x_140_ = lean_apply_1(v_y_132_, v___x_139_);
v___x_141_ = lean_apply_7(v___f_133_, lean_box(0), lean_box(0), v___x_140_, v___f_138_, lean_box(0), v___y_136_, v___y_137_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__10(lean_object* v___f_142_, lean_object* v_00_u03b1_143_, lean_object* v_00_u03b2_144_, lean_object* v_x_145_, lean_object* v_y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v___f_150_; lean_object* v___x_151_; 
lean_inc(v___f_142_);
v___f_150_ = lean_alloc_closure((void*)(l_ExceptCpsT_instMonad___lam__9), 6, 2);
lean_closure_set(v___f_150_, 0, v_y_146_);
lean_closure_set(v___f_150_, 1, v___f_142_);
v___x_151_ = lean_apply_7(v___f_142_, lean_box(0), lean_box(0), v_x_145_, v___f_150_, lean_box(0), v___y_148_, v___y_149_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__11(lean_object* v_y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v_a_155_){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_box(0);
v___x_157_ = lean_apply_4(v_y_152_, v___x_156_, lean_box(0), v___y_153_, v___y_154_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__11___boxed(lean_object* v_y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_ExceptCpsT_instMonad___lam__11(v_y_158_, v___y_159_, v___y_160_, v_a_161_);
lean_dec(v_a_161_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad___lam__12(lean_object* v_00_u03b1_163_, lean_object* v_00_u03b2_164_, lean_object* v_x_165_, lean_object* v_y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v___f_170_; lean_object* v___x_171_; 
lean_inc(v___y_169_);
v___f_170_ = lean_alloc_closure((void*)(l_ExceptCpsT_instMonad___lam__11___boxed), 4, 3);
lean_closure_set(v___f_170_, 0, v_y_166_);
lean_closure_set(v___f_170_, 1, v___y_168_);
lean_closure_set(v___f_170_, 2, v___y_169_);
v___x_171_ = lean_apply_3(v_x_165_, lean_box(0), v___f_170_, v___y_169_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonad(lean_object* v_00_u03b5_194_, lean_object* v_m_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = ((lean_object*)(l_ExceptCpsT_instMonad___closed__9));
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonadExceptOf___lam__0(lean_object* v_00_u03b1_197_, lean_object* v_e_198_, lean_object* v_x_199_, lean_object* v_x_200_, lean_object* v_k_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = lean_apply_1(v_k_201_, v_e_198_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonadExceptOf___lam__0___boxed(lean_object* v_00_u03b1_203_, lean_object* v_e_204_, lean_object* v_x_205_, lean_object* v_x_206_, lean_object* v_k_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_ExceptCpsT_instMonadExceptOf___lam__0(v_00_u03b1_203_, v_e_204_, v_x_205_, v_x_206_, v_k_207_);
lean_dec(v_x_206_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonadExceptOf___lam__1(lean_object* v_handle_209_, lean_object* v_k_u2081_210_, lean_object* v_k_u2082_211_, lean_object* v_e_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = lean_apply_4(v_handle_209_, v_e_212_, lean_box(0), v_k_u2081_210_, v_k_u2082_211_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonadExceptOf___lam__2(lean_object* v_00_u03b1_214_, lean_object* v_x_215_, lean_object* v_handle_216_, lean_object* v_x_217_, lean_object* v_k_u2081_218_, lean_object* v_k_u2082_219_){
_start:
{
lean_object* v___f_220_; lean_object* v___x_221_; 
lean_inc(v_k_u2081_218_);
v___f_220_ = lean_alloc_closure((void*)(l_ExceptCpsT_instMonadExceptOf___lam__1), 4, 3);
lean_closure_set(v___f_220_, 0, v_handle_216_);
lean_closure_set(v___f_220_, 1, v_k_u2081_218_);
lean_closure_set(v___f_220_, 2, v_k_u2082_219_);
v___x_221_ = lean_apply_3(v_x_215_, lean_box(0), v_k_u2081_218_, v___f_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonadExceptOf(lean_object* v_00_u03b5_227_, lean_object* v_m_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = ((lean_object*)(l_ExceptCpsT_instMonadExceptOf___closed__2));
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_lift___redArg(lean_object* v_inst_230_, lean_object* v_x_231_, lean_object* v_k_232_){
_start:
{
lean_object* v_toBind_233_; lean_object* v___x_234_; 
v_toBind_233_ = lean_ctor_get(v_inst_230_, 1);
lean_inc(v_toBind_233_);
lean_dec_ref(v_inst_230_);
v___x_234_ = lean_apply_4(v_toBind_233_, lean_box(0), lean_box(0), v_x_231_, v_k_232_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_lift(lean_object* v_m_235_, lean_object* v_00_u03b1_236_, lean_object* v_00_u03b5_237_, lean_object* v_inst_238_, lean_object* v_x_239_, lean_object* v_x_240_, lean_object* v_k_241_, lean_object* v_x_242_){
_start:
{
lean_object* v_toBind_243_; lean_object* v___x_244_; 
v_toBind_243_ = lean_ctor_get(v_inst_238_, 1);
lean_inc(v_toBind_243_);
lean_dec_ref(v_inst_238_);
v___x_244_ = lean_apply_4(v_toBind_243_, lean_box(0), lean_box(0), v_x_239_, v_k_241_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_lift___boxed(lean_object* v_m_245_, lean_object* v_00_u03b1_246_, lean_object* v_00_u03b5_247_, lean_object* v_inst_248_, lean_object* v_x_249_, lean_object* v_x_250_, lean_object* v_k_251_, lean_object* v_x_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_ExceptCpsT_lift(v_m_245_, v_00_u03b1_246_, v_00_u03b5_247_, v_inst_248_, v_x_249_, v_x_250_, v_k_251_, v_x_252_);
lean_dec(v_x_252_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonadLiftOfMonad___redArg___lam__0(lean_object* v_inst_254_, lean_object* v_00_u03b1_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_toBind_260_; lean_object* v___x_261_; 
v_toBind_260_ = lean_ctor_get(v_inst_254_, 1);
lean_inc(v_toBind_260_);
lean_dec_ref(v_inst_254_);
v___x_261_ = lean_apply_4(v_toBind_260_, lean_box(0), lean_box(0), v___y_256_, v___y_258_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonadLiftOfMonad___redArg___lam__0___boxed(lean_object* v_inst_262_, lean_object* v_00_u03b1_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_ExceptCpsT_instMonadLiftOfMonad___redArg___lam__0(v_inst_262_, v_00_u03b1_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_);
lean_dec(v___y_267_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonadLiftOfMonad___redArg(lean_object* v_inst_269_){
_start:
{
lean_object* v___f_270_; 
v___f_270_ = lean_alloc_closure((void*)(l_ExceptCpsT_instMonadLiftOfMonad___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_270_, 0, v_inst_269_);
return v___f_270_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonadLiftOfMonad(lean_object* v_m_271_, lean_object* v_00_u03c3_272_, lean_object* v_inst_273_){
_start:
{
lean_object* v___f_274_; 
v___f_274_ = lean_alloc_closure((void*)(l_ExceptCpsT_instMonadLiftOfMonad___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_274_, 0, v_inst_273_);
return v___f_274_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instInhabited___redArg___lam__0(lean_object* v_inst_275_, lean_object* v_x_276_, lean_object* v_x_277_, lean_object* v_k_u2082_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = lean_apply_1(v_k_u2082_278_, v_inst_275_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instInhabited___redArg___lam__0___boxed(lean_object* v_inst_280_, lean_object* v_x_281_, lean_object* v_x_282_, lean_object* v_k_u2082_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_ExceptCpsT_instInhabited___redArg___lam__0(v_inst_280_, v_x_281_, v_x_282_, v_k_u2082_283_);
lean_dec(v_x_282_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instInhabited___redArg(lean_object* v_inst_285_){
_start:
{
lean_object* v___f_286_; 
v___f_286_ = lean_alloc_closure((void*)(l_ExceptCpsT_instInhabited___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_286_, 0, v_inst_285_);
return v___f_286_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instInhabited(lean_object* v_00_u03b5_287_, lean_object* v_m_288_, lean_object* v_00_u03b1_289_, lean_object* v_inst_290_){
_start:
{
lean_object* v___f_291_; 
v___f_291_ = lean_alloc_closure((void*)(l_ExceptCpsT_instInhabited___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_291_, 0, v_inst_290_);
return v___f_291_;
}
}
static lean_object* _init_l_ExceptCpsT_instMonadAttach___closed__0(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = ((lean_object*)(l_ExceptCpsT_instMonad___closed__9));
v___x_293_ = l_MonadAttach_trivial___redArg(v___x_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_ExceptCpsT_instMonadAttach(lean_object* v_00_u03b5_294_, lean_object* v_m_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = lean_obj_once(&l_ExceptCpsT_instMonadAttach___closed__0, &l_ExceptCpsT_instMonadAttach___closed__0_once, _init_l_ExceptCpsT_instMonadAttach___closed__0);
return v___x_296_;
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

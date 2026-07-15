// Lean compiler output
// Module: Init.Control.StateRef
// Imports: public import Init.System.ST public import Init.Control.Reader
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
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_run___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_run___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_run___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_run_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_run_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_run_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_lift___redArg(lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_lift___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_lift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__5___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__7___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_StateRefT_x27_instMonadLift___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_StateRefT_x27_instMonadLift___closed__0 = (const lean_object*)&l_StateRefT_x27_instMonadLift___closed__0_value;
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadLift(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_StateRefT_x27_instMonadFunctor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_StateRefT_x27_instMonadFunctor___closed__0 = (const lean_object*)&l_StateRefT_x27_instMonadFunctor___closed__0_value;
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg___closed__0 = (const lean_object*)&l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_get___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_get___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_set___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_set___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_set(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_modifyGet___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_modifyGet___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_modifyGet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_modifyGet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg(lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadStateOfOfMonadLiftTST(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadExceptOf___redArg(lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadExceptOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instMonadControlStateRefT_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadControlStateRefT_x27___aux__1___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadControlStateRefT_x27___closed__0 = (const lean_object*)&l_instMonadControlStateRefT_x27___closed__0_value;
static const lean_closure_object l_instMonadControlStateRefT_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadControlStateRefT_x27___aux__3___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadControlStateRefT_x27___closed__1 = (const lean_object*)&l_instMonadControlStateRefT_x27___closed__1_value;
static const lean_ctor_object l_instMonadControlStateRefT_x27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_instMonadControlStateRefT_x27___closed__0_value),((lean_object*)&l_instMonadControlStateRefT_x27___closed__1_value)}};
static const lean_object* l_instMonadControlStateRefT_x27___closed__2 = (const lean_object*)&l_instMonadControlStateRefT_x27___closed__2_value;
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_run___redArg___lam__0(lean_object* v_a_1_, lean_object* v_toPure_2_, lean_object* v_s_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4_, 0, v_a_1_);
lean_ctor_set(v___x_4_, 1, v_s_3_);
v___x_5_ = lean_apply_2(v_toPure_2_, lean_box(0), v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_run___redArg___lam__1(lean_object* v_toPure_6_, lean_object* v_ref_7_, lean_object* v_inst_8_, lean_object* v_toBind_9_, lean_object* v_a_10_){
_start:
{
lean_object* v___f_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___f_11_ = lean_alloc_closure((void*)(l_StateRefT_x27_run___redArg___lam__0), 3, 2);
lean_closure_set(v___f_11_, 0, v_a_10_);
lean_closure_set(v___f_11_, 1, v_toPure_6_);
v___x_12_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_12_, 0, lean_box(0));
lean_closure_set(v___x_12_, 1, lean_box(0));
lean_closure_set(v___x_12_, 2, v_ref_7_);
v___x_13_ = lean_apply_2(v_inst_8_, lean_box(0), v___x_12_);
v___x_14_ = lean_apply_4(v_toBind_9_, lean_box(0), lean_box(0), v___x_13_, v___f_11_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_run___redArg___lam__2(lean_object* v_toPure_15_, lean_object* v_inst_16_, lean_object* v_toBind_17_, lean_object* v_x_18_, lean_object* v_ref_19_){
_start:
{
lean_object* v___f_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
lean_inc(v_toBind_17_);
lean_inc(v_ref_19_);
v___f_20_ = lean_alloc_closure((void*)(l_StateRefT_x27_run___redArg___lam__1), 5, 4);
lean_closure_set(v___f_20_, 0, v_toPure_15_);
lean_closure_set(v___f_20_, 1, v_ref_19_);
lean_closure_set(v___f_20_, 2, v_inst_16_);
lean_closure_set(v___f_20_, 3, v_toBind_17_);
v___x_21_ = lean_apply_1(v_x_18_, v_ref_19_);
v___x_22_ = lean_apply_4(v_toBind_17_, lean_box(0), lean_box(0), v___x_21_, v___f_20_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_run___redArg(lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_x_25_, lean_object* v_s_26_){
_start:
{
lean_object* v_toApplicative_27_; lean_object* v_toBind_28_; lean_object* v_toPure_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___f_32_; lean_object* v___x_33_; 
v_toApplicative_27_ = lean_ctor_get(v_inst_23_, 0);
lean_inc_ref(v_toApplicative_27_);
v_toBind_28_ = lean_ctor_get(v_inst_23_, 1);
lean_inc_n(v_toBind_28_, 2);
lean_dec_ref(v_inst_23_);
v_toPure_29_ = lean_ctor_get(v_toApplicative_27_, 1);
lean_inc(v_toPure_29_);
lean_dec_ref(v_toApplicative_27_);
v___x_30_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_30_, 0, lean_box(0));
lean_closure_set(v___x_30_, 1, lean_box(0));
lean_closure_set(v___x_30_, 2, v_s_26_);
lean_inc(v_inst_24_);
v___x_31_ = lean_apply_2(v_inst_24_, lean_box(0), v___x_30_);
v___f_32_ = lean_alloc_closure((void*)(l_StateRefT_x27_run___redArg___lam__2), 5, 4);
lean_closure_set(v___f_32_, 0, v_toPure_29_);
lean_closure_set(v___f_32_, 1, v_inst_24_);
lean_closure_set(v___f_32_, 2, v_toBind_28_);
lean_closure_set(v___f_32_, 3, v_x_25_);
v___x_33_ = lean_apply_4(v_toBind_28_, lean_box(0), lean_box(0), v___x_31_, v___f_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_run(lean_object* v_00_u03c9_34_, lean_object* v_00_u03c3_35_, lean_object* v_m_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_00_u03b1_39_, lean_object* v_x_40_, lean_object* v_s_41_){
_start:
{
lean_object* v_toApplicative_42_; lean_object* v_toBind_43_; lean_object* v_toPure_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___f_47_; lean_object* v___x_48_; 
v_toApplicative_42_ = lean_ctor_get(v_inst_37_, 0);
lean_inc_ref(v_toApplicative_42_);
v_toBind_43_ = lean_ctor_get(v_inst_37_, 1);
lean_inc_n(v_toBind_43_, 2);
lean_dec_ref(v_inst_37_);
v_toPure_44_ = lean_ctor_get(v_toApplicative_42_, 1);
lean_inc(v_toPure_44_);
lean_dec_ref(v_toApplicative_42_);
v___x_45_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_45_, 0, lean_box(0));
lean_closure_set(v___x_45_, 1, lean_box(0));
lean_closure_set(v___x_45_, 2, v_s_41_);
lean_inc(v_inst_38_);
v___x_46_ = lean_apply_2(v_inst_38_, lean_box(0), v___x_45_);
v___f_47_ = lean_alloc_closure((void*)(l_StateRefT_x27_run___redArg___lam__2), 5, 4);
lean_closure_set(v___f_47_, 0, v_toPure_44_);
lean_closure_set(v___f_47_, 1, v_inst_38_);
lean_closure_set(v___f_47_, 2, v_toBind_43_);
lean_closure_set(v___f_47_, 3, v_x_40_);
v___x_48_ = lean_apply_4(v_toBind_43_, lean_box(0), lean_box(0), v___x_46_, v___f_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_run_x27___redArg___lam__0(lean_object* v_toPure_49_, lean_object* v_____x_50_){
_start:
{
lean_object* v_fst_51_; lean_object* v___x_52_; 
v_fst_51_ = lean_ctor_get(v_____x_50_, 0);
lean_inc(v_fst_51_);
lean_dec_ref(v_____x_50_);
v___x_52_ = lean_apply_2(v_toPure_49_, lean_box(0), v_fst_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_run_x27___redArg(lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_x_55_, lean_object* v_s_56_){
_start:
{
lean_object* v_toApplicative_57_; lean_object* v_toBind_58_; lean_object* v_toPure_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___f_62_; lean_object* v___f_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v_toApplicative_57_ = lean_ctor_get(v_inst_53_, 0);
lean_inc_ref(v_toApplicative_57_);
v_toBind_58_ = lean_ctor_get(v_inst_53_, 1);
lean_inc_n(v_toBind_58_, 3);
lean_dec_ref(v_inst_53_);
v_toPure_59_ = lean_ctor_get(v_toApplicative_57_, 1);
lean_inc_n(v_toPure_59_, 2);
lean_dec_ref(v_toApplicative_57_);
v___x_60_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_60_, 0, lean_box(0));
lean_closure_set(v___x_60_, 1, lean_box(0));
lean_closure_set(v___x_60_, 2, v_s_56_);
lean_inc(v_inst_54_);
v___x_61_ = lean_apply_2(v_inst_54_, lean_box(0), v___x_60_);
v___f_62_ = lean_alloc_closure((void*)(l_StateRefT_x27_run_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_62_, 0, v_toPure_59_);
v___f_63_ = lean_alloc_closure((void*)(l_StateRefT_x27_run___redArg___lam__2), 5, 4);
lean_closure_set(v___f_63_, 0, v_toPure_59_);
lean_closure_set(v___f_63_, 1, v_inst_54_);
lean_closure_set(v___f_63_, 2, v_toBind_58_);
lean_closure_set(v___f_63_, 3, v_x_55_);
v___x_64_ = lean_apply_4(v_toBind_58_, lean_box(0), lean_box(0), v___x_61_, v___f_63_);
v___x_65_ = lean_apply_4(v_toBind_58_, lean_box(0), lean_box(0), v___x_64_, v___f_62_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_run_x27(lean_object* v_00_u03c9_66_, lean_object* v_00_u03c3_67_, lean_object* v_m_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_00_u03b1_71_, lean_object* v_x_72_, lean_object* v_s_73_){
_start:
{
lean_object* v_toApplicative_74_; lean_object* v_toBind_75_; lean_object* v_toPure_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___f_79_; lean_object* v___f_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v_toApplicative_74_ = lean_ctor_get(v_inst_69_, 0);
lean_inc_ref(v_toApplicative_74_);
v_toBind_75_ = lean_ctor_get(v_inst_69_, 1);
lean_inc_n(v_toBind_75_, 3);
lean_dec_ref(v_inst_69_);
v_toPure_76_ = lean_ctor_get(v_toApplicative_74_, 1);
lean_inc_n(v_toPure_76_, 2);
lean_dec_ref(v_toApplicative_74_);
v___x_77_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_77_, 0, lean_box(0));
lean_closure_set(v___x_77_, 1, lean_box(0));
lean_closure_set(v___x_77_, 2, v_s_73_);
lean_inc(v_inst_70_);
v___x_78_ = lean_apply_2(v_inst_70_, lean_box(0), v___x_77_);
v___f_79_ = lean_alloc_closure((void*)(l_StateRefT_x27_run_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_79_, 0, v_toPure_76_);
v___f_80_ = lean_alloc_closure((void*)(l_StateRefT_x27_run___redArg___lam__2), 5, 4);
lean_closure_set(v___f_80_, 0, v_toPure_76_);
lean_closure_set(v___f_80_, 1, v_inst_70_);
lean_closure_set(v___f_80_, 2, v_toBind_75_);
lean_closure_set(v___f_80_, 3, v_x_72_);
v___x_81_ = lean_apply_4(v_toBind_75_, lean_box(0), lean_box(0), v___x_78_, v___f_80_);
v___x_82_ = lean_apply_4(v_toBind_75_, lean_box(0), lean_box(0), v___x_81_, v___f_79_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_lift___redArg(lean_object* v_x_83_){
_start:
{
lean_inc(v_x_83_);
return v_x_83_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_lift___redArg___boxed(lean_object* v_x_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_StateRefT_x27_lift___redArg(v_x_84_);
lean_dec(v_x_84_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_lift(lean_object* v_00_u03c9_86_, lean_object* v_00_u03c3_87_, lean_object* v_m_88_, lean_object* v_00_u03b1_89_, lean_object* v_x_90_, lean_object* v_x_91_){
_start:
{
lean_inc(v_x_90_);
return v_x_90_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_lift___boxed(lean_object* v_00_u03c9_92_, lean_object* v_00_u03c3_93_, lean_object* v_m_94_, lean_object* v_00_u03b1_95_, lean_object* v_x_96_, lean_object* v_x_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_StateRefT_x27_lift(v_00_u03c9_92_, v_00_u03c3_93_, v_m_94_, v_00_u03b1_95_, v_x_96_, v_x_97_);
lean_dec(v_x_97_);
lean_dec(v_x_96_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__1___redArg(lean_object* v_inst_99_, lean_object* v_f_100_, lean_object* v_x_101_, lean_object* v_r_102_){
_start:
{
lean_object* v_toApplicative_103_; lean_object* v_toFunctor_104_; lean_object* v_map_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v_toApplicative_103_ = lean_ctor_get(v_inst_99_, 0);
lean_inc_ref(v_toApplicative_103_);
lean_dec_ref(v_inst_99_);
v_toFunctor_104_ = lean_ctor_get(v_toApplicative_103_, 0);
lean_inc_ref(v_toFunctor_104_);
lean_dec_ref(v_toApplicative_103_);
v_map_105_ = lean_ctor_get(v_toFunctor_104_, 0);
lean_inc(v_map_105_);
lean_dec_ref(v_toFunctor_104_);
lean_inc(v_r_102_);
v___x_106_ = lean_apply_1(v_x_101_, v_r_102_);
v___x_107_ = lean_apply_4(v_map_105_, lean_box(0), lean_box(0), v_f_100_, v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__1___redArg___boxed(lean_object* v_inst_108_, lean_object* v_f_109_, lean_object* v_x_110_, lean_object* v_r_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_StateRefT_x27_instMonad___aux__1___redArg(v_inst_108_, v_f_109_, v_x_110_, v_r_111_);
lean_dec(v_r_111_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__1(lean_object* v_00_u03c9_113_, lean_object* v_00_u03c3_114_, lean_object* v_m_115_, lean_object* v_inst_116_, lean_object* v_00_u03b1_117_, lean_object* v_00_u03b2_118_, lean_object* v_f_119_, lean_object* v_x_120_, lean_object* v_r_121_){
_start:
{
lean_object* v_toApplicative_122_; lean_object* v_toFunctor_123_; lean_object* v_map_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v_toApplicative_122_ = lean_ctor_get(v_inst_116_, 0);
lean_inc_ref(v_toApplicative_122_);
lean_dec_ref(v_inst_116_);
v_toFunctor_123_ = lean_ctor_get(v_toApplicative_122_, 0);
lean_inc_ref(v_toFunctor_123_);
lean_dec_ref(v_toApplicative_122_);
v_map_124_ = lean_ctor_get(v_toFunctor_123_, 0);
lean_inc(v_map_124_);
lean_dec_ref(v_toFunctor_123_);
lean_inc(v_r_121_);
v___x_125_ = lean_apply_1(v_x_120_, v_r_121_);
v___x_126_ = lean_apply_4(v_map_124_, lean_box(0), lean_box(0), v_f_119_, v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__1___boxed(lean_object* v_00_u03c9_127_, lean_object* v_00_u03c3_128_, lean_object* v_m_129_, lean_object* v_inst_130_, lean_object* v_00_u03b1_131_, lean_object* v_00_u03b2_132_, lean_object* v_f_133_, lean_object* v_x_134_, lean_object* v_r_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_StateRefT_x27_instMonad___aux__1(v_00_u03c9_127_, v_00_u03c3_128_, v_m_129_, v_inst_130_, v_00_u03b1_131_, v_00_u03b2_132_, v_f_133_, v_x_134_, v_r_135_);
lean_dec(v_r_135_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__3___redArg(lean_object* v_inst_137_, lean_object* v_a_138_, lean_object* v_x_139_, lean_object* v_r_140_){
_start:
{
lean_object* v_toApplicative_141_; lean_object* v_toFunctor_142_; lean_object* v_mapConst_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v_toApplicative_141_ = lean_ctor_get(v_inst_137_, 0);
lean_inc_ref(v_toApplicative_141_);
lean_dec_ref(v_inst_137_);
v_toFunctor_142_ = lean_ctor_get(v_toApplicative_141_, 0);
lean_inc_ref(v_toFunctor_142_);
lean_dec_ref(v_toApplicative_141_);
v_mapConst_143_ = lean_ctor_get(v_toFunctor_142_, 1);
lean_inc(v_mapConst_143_);
lean_dec_ref(v_toFunctor_142_);
lean_inc(v_r_140_);
v___x_144_ = lean_apply_1(v_x_139_, v_r_140_);
v___x_145_ = lean_apply_4(v_mapConst_143_, lean_box(0), lean_box(0), v_a_138_, v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__3___redArg___boxed(lean_object* v_inst_146_, lean_object* v_a_147_, lean_object* v_x_148_, lean_object* v_r_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_StateRefT_x27_instMonad___aux__3___redArg(v_inst_146_, v_a_147_, v_x_148_, v_r_149_);
lean_dec(v_r_149_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__3(lean_object* v_00_u03c9_151_, lean_object* v_00_u03c3_152_, lean_object* v_m_153_, lean_object* v_inst_154_, lean_object* v_00_u03b1_155_, lean_object* v_00_u03b2_156_, lean_object* v_a_157_, lean_object* v_x_158_, lean_object* v_r_159_){
_start:
{
lean_object* v_toApplicative_160_; lean_object* v_toFunctor_161_; lean_object* v_mapConst_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v_toApplicative_160_ = lean_ctor_get(v_inst_154_, 0);
lean_inc_ref(v_toApplicative_160_);
lean_dec_ref(v_inst_154_);
v_toFunctor_161_ = lean_ctor_get(v_toApplicative_160_, 0);
lean_inc_ref(v_toFunctor_161_);
lean_dec_ref(v_toApplicative_160_);
v_mapConst_162_ = lean_ctor_get(v_toFunctor_161_, 1);
lean_inc(v_mapConst_162_);
lean_dec_ref(v_toFunctor_161_);
lean_inc(v_r_159_);
v___x_163_ = lean_apply_1(v_x_158_, v_r_159_);
v___x_164_ = lean_apply_4(v_mapConst_162_, lean_box(0), lean_box(0), v_a_157_, v___x_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__3___boxed(lean_object* v_00_u03c9_165_, lean_object* v_00_u03c3_166_, lean_object* v_m_167_, lean_object* v_inst_168_, lean_object* v_00_u03b1_169_, lean_object* v_00_u03b2_170_, lean_object* v_a_171_, lean_object* v_x_172_, lean_object* v_r_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_StateRefT_x27_instMonad___aux__3(v_00_u03c9_165_, v_00_u03c3_166_, v_m_167_, v_inst_168_, v_00_u03b1_169_, v_00_u03b2_170_, v_a_171_, v_x_172_, v_r_173_);
lean_dec(v_r_173_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__5___redArg___lam__0(lean_object* v_x_175_, lean_object* v_r_176_, lean_object* v_x_177_){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_box(0);
lean_inc(v_r_176_);
v___x_179_ = lean_apply_2(v_x_175_, v___x_178_, v_r_176_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__5___redArg___lam__0___boxed(lean_object* v_x_180_, lean_object* v_r_181_, lean_object* v_x_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_StateRefT_x27_instMonad___aux__5___redArg___lam__0(v_x_180_, v_r_181_, v_x_182_);
lean_dec(v_r_181_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__5___redArg(lean_object* v_inst_184_, lean_object* v_f_185_, lean_object* v_x_186_, lean_object* v_r_187_){
_start:
{
lean_object* v_toApplicative_188_; lean_object* v_toSeq_189_; lean_object* v___f_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v_toApplicative_188_ = lean_ctor_get(v_inst_184_, 0);
lean_inc_ref(v_toApplicative_188_);
lean_dec_ref(v_inst_184_);
v_toSeq_189_ = lean_ctor_get(v_toApplicative_188_, 2);
lean_inc(v_toSeq_189_);
lean_dec_ref(v_toApplicative_188_);
lean_inc_n(v_r_187_, 2);
v___f_190_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__5___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_190_, 0, v_x_186_);
lean_closure_set(v___f_190_, 1, v_r_187_);
v___x_191_ = lean_apply_1(v_f_185_, v_r_187_);
v___x_192_ = lean_apply_4(v_toSeq_189_, lean_box(0), lean_box(0), v___x_191_, v___f_190_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__5___redArg___boxed(lean_object* v_inst_193_, lean_object* v_f_194_, lean_object* v_x_195_, lean_object* v_r_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_StateRefT_x27_instMonad___aux__5___redArg(v_inst_193_, v_f_194_, v_x_195_, v_r_196_);
lean_dec(v_r_196_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__5(lean_object* v_00_u03c9_198_, lean_object* v_00_u03c3_199_, lean_object* v_m_200_, lean_object* v_inst_201_, lean_object* v_00_u03b1_202_, lean_object* v_00_u03b2_203_, lean_object* v_f_204_, lean_object* v_x_205_, lean_object* v_r_206_){
_start:
{
lean_object* v_toApplicative_207_; lean_object* v_toSeq_208_; lean_object* v___f_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v_toApplicative_207_ = lean_ctor_get(v_inst_201_, 0);
lean_inc_ref(v_toApplicative_207_);
lean_dec_ref(v_inst_201_);
v_toSeq_208_ = lean_ctor_get(v_toApplicative_207_, 2);
lean_inc(v_toSeq_208_);
lean_dec_ref(v_toApplicative_207_);
lean_inc_n(v_r_206_, 2);
v___f_209_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__5___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_209_, 0, v_x_205_);
lean_closure_set(v___f_209_, 1, v_r_206_);
v___x_210_ = lean_apply_1(v_f_204_, v_r_206_);
v___x_211_ = lean_apply_4(v_toSeq_208_, lean_box(0), lean_box(0), v___x_210_, v___f_209_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__5___boxed(lean_object* v_00_u03c9_212_, lean_object* v_00_u03c3_213_, lean_object* v_m_214_, lean_object* v_inst_215_, lean_object* v_00_u03b1_216_, lean_object* v_00_u03b2_217_, lean_object* v_f_218_, lean_object* v_x_219_, lean_object* v_r_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_StateRefT_x27_instMonad___aux__5(v_00_u03c9_212_, v_00_u03c3_213_, v_m_214_, v_inst_215_, v_00_u03b1_216_, v_00_u03b2_217_, v_f_218_, v_x_219_, v_r_220_);
lean_dec(v_r_220_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__7___redArg___lam__0(lean_object* v_b_222_, lean_object* v_r_223_, lean_object* v_x_224_){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_box(0);
lean_inc(v_r_223_);
v___x_226_ = lean_apply_2(v_b_222_, v___x_225_, v_r_223_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__7___redArg___lam__0___boxed(lean_object* v_b_227_, lean_object* v_r_228_, lean_object* v_x_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_StateRefT_x27_instMonad___aux__7___redArg___lam__0(v_b_227_, v_r_228_, v_x_229_);
lean_dec(v_r_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__7___redArg(lean_object* v_inst_231_, lean_object* v_a_232_, lean_object* v_b_233_, lean_object* v_r_234_){
_start:
{
lean_object* v_toApplicative_235_; lean_object* v_toSeqLeft_236_; lean_object* v___f_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v_toApplicative_235_ = lean_ctor_get(v_inst_231_, 0);
lean_inc_ref(v_toApplicative_235_);
lean_dec_ref(v_inst_231_);
v_toSeqLeft_236_ = lean_ctor_get(v_toApplicative_235_, 3);
lean_inc(v_toSeqLeft_236_);
lean_dec_ref(v_toApplicative_235_);
lean_inc_n(v_r_234_, 2);
v___f_237_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__7___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_237_, 0, v_b_233_);
lean_closure_set(v___f_237_, 1, v_r_234_);
v___x_238_ = lean_apply_1(v_a_232_, v_r_234_);
v___x_239_ = lean_apply_4(v_toSeqLeft_236_, lean_box(0), lean_box(0), v___x_238_, v___f_237_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__7___redArg___boxed(lean_object* v_inst_240_, lean_object* v_a_241_, lean_object* v_b_242_, lean_object* v_r_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_StateRefT_x27_instMonad___aux__7___redArg(v_inst_240_, v_a_241_, v_b_242_, v_r_243_);
lean_dec(v_r_243_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__7(lean_object* v_00_u03c9_245_, lean_object* v_00_u03c3_246_, lean_object* v_m_247_, lean_object* v_inst_248_, lean_object* v_00_u03b1_249_, lean_object* v_00_u03b2_250_, lean_object* v_a_251_, lean_object* v_b_252_, lean_object* v_r_253_){
_start:
{
lean_object* v_toApplicative_254_; lean_object* v_toSeqLeft_255_; lean_object* v___f_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_toApplicative_254_ = lean_ctor_get(v_inst_248_, 0);
lean_inc_ref(v_toApplicative_254_);
lean_dec_ref(v_inst_248_);
v_toSeqLeft_255_ = lean_ctor_get(v_toApplicative_254_, 3);
lean_inc(v_toSeqLeft_255_);
lean_dec_ref(v_toApplicative_254_);
lean_inc_n(v_r_253_, 2);
v___f_256_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__7___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_256_, 0, v_b_252_);
lean_closure_set(v___f_256_, 1, v_r_253_);
v___x_257_ = lean_apply_1(v_a_251_, v_r_253_);
v___x_258_ = lean_apply_4(v_toSeqLeft_255_, lean_box(0), lean_box(0), v___x_257_, v___f_256_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__7___boxed(lean_object* v_00_u03c9_259_, lean_object* v_00_u03c3_260_, lean_object* v_m_261_, lean_object* v_inst_262_, lean_object* v_00_u03b1_263_, lean_object* v_00_u03b2_264_, lean_object* v_a_265_, lean_object* v_b_266_, lean_object* v_r_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_StateRefT_x27_instMonad___aux__7(v_00_u03c9_259_, v_00_u03c3_260_, v_m_261_, v_inst_262_, v_00_u03b1_263_, v_00_u03b2_264_, v_a_265_, v_b_266_, v_r_267_);
lean_dec(v_r_267_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__9___redArg(lean_object* v_inst_269_, lean_object* v_a_270_, lean_object* v_b_271_, lean_object* v_r_272_){
_start:
{
lean_object* v_toApplicative_273_; lean_object* v_toSeqRight_274_; lean_object* v___f_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v_toApplicative_273_ = lean_ctor_get(v_inst_269_, 0);
lean_inc_ref(v_toApplicative_273_);
lean_dec_ref(v_inst_269_);
v_toSeqRight_274_ = lean_ctor_get(v_toApplicative_273_, 4);
lean_inc(v_toSeqRight_274_);
lean_dec_ref(v_toApplicative_273_);
lean_inc_n(v_r_272_, 2);
v___f_275_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__7___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_275_, 0, v_b_271_);
lean_closure_set(v___f_275_, 1, v_r_272_);
v___x_276_ = lean_apply_1(v_a_270_, v_r_272_);
v___x_277_ = lean_apply_4(v_toSeqRight_274_, lean_box(0), lean_box(0), v___x_276_, v___f_275_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__9___redArg___boxed(lean_object* v_inst_278_, lean_object* v_a_279_, lean_object* v_b_280_, lean_object* v_r_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_StateRefT_x27_instMonad___aux__9___redArg(v_inst_278_, v_a_279_, v_b_280_, v_r_281_);
lean_dec(v_r_281_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__9(lean_object* v_00_u03c9_283_, lean_object* v_00_u03c3_284_, lean_object* v_m_285_, lean_object* v_inst_286_, lean_object* v_00_u03b1_287_, lean_object* v_00_u03b2_288_, lean_object* v_a_289_, lean_object* v_b_290_, lean_object* v_r_291_){
_start:
{
lean_object* v_toApplicative_292_; lean_object* v_toSeqRight_293_; lean_object* v___f_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v_toApplicative_292_ = lean_ctor_get(v_inst_286_, 0);
lean_inc_ref(v_toApplicative_292_);
lean_dec_ref(v_inst_286_);
v_toSeqRight_293_ = lean_ctor_get(v_toApplicative_292_, 4);
lean_inc(v_toSeqRight_293_);
lean_dec_ref(v_toApplicative_292_);
lean_inc_n(v_r_291_, 2);
v___f_294_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__7___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_294_, 0, v_b_290_);
lean_closure_set(v___f_294_, 1, v_r_291_);
v___x_295_ = lean_apply_1(v_a_289_, v_r_291_);
v___x_296_ = lean_apply_4(v_toSeqRight_293_, lean_box(0), lean_box(0), v___x_295_, v___f_294_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__9___boxed(lean_object* v_00_u03c9_297_, lean_object* v_00_u03c3_298_, lean_object* v_m_299_, lean_object* v_inst_300_, lean_object* v_00_u03b1_301_, lean_object* v_00_u03b2_302_, lean_object* v_a_303_, lean_object* v_b_304_, lean_object* v_r_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_StateRefT_x27_instMonad___aux__9(v_00_u03c9_297_, v_00_u03c3_298_, v_m_299_, v_inst_300_, v_00_u03b1_301_, v_00_u03b2_302_, v_a_303_, v_b_304_, v_r_305_);
lean_dec(v_r_305_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___redArg(lean_object* v_inst_307_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
lean_inc_ref_n(v_inst_307_, 6);
v___x_308_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__1___boxed), 9, 4);
lean_closure_set(v___x_308_, 0, lean_box(0));
lean_closure_set(v___x_308_, 1, lean_box(0));
lean_closure_set(v___x_308_, 2, lean_box(0));
lean_closure_set(v___x_308_, 3, v_inst_307_);
v___x_309_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__3___boxed), 9, 4);
lean_closure_set(v___x_309_, 0, lean_box(0));
lean_closure_set(v___x_309_, 1, lean_box(0));
lean_closure_set(v___x_309_, 2, lean_box(0));
lean_closure_set(v___x_309_, 3, v_inst_307_);
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_308_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
v___x_311_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_311_, 0, lean_box(0));
lean_closure_set(v___x_311_, 1, lean_box(0));
lean_closure_set(v___x_311_, 2, v_inst_307_);
v___x_312_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__5___boxed), 9, 4);
lean_closure_set(v___x_312_, 0, lean_box(0));
lean_closure_set(v___x_312_, 1, lean_box(0));
lean_closure_set(v___x_312_, 2, lean_box(0));
lean_closure_set(v___x_312_, 3, v_inst_307_);
v___x_313_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__7___boxed), 9, 4);
lean_closure_set(v___x_313_, 0, lean_box(0));
lean_closure_set(v___x_313_, 1, lean_box(0));
lean_closure_set(v___x_313_, 2, lean_box(0));
lean_closure_set(v___x_313_, 3, v_inst_307_);
v___x_314_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__9___boxed), 9, 4);
lean_closure_set(v___x_314_, 0, lean_box(0));
lean_closure_set(v___x_314_, 1, lean_box(0));
lean_closure_set(v___x_314_, 2, lean_box(0));
lean_closure_set(v___x_314_, 3, v_inst_307_);
v___x_315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_315_, 0, v___x_310_);
lean_ctor_set(v___x_315_, 1, v___x_311_);
lean_ctor_set(v___x_315_, 2, v___x_312_);
lean_ctor_set(v___x_315_, 3, v___x_313_);
lean_ctor_set(v___x_315_, 4, v___x_314_);
v___x_316_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 3);
lean_closure_set(v___x_316_, 0, lean_box(0));
lean_closure_set(v___x_316_, 1, lean_box(0));
lean_closure_set(v___x_316_, 2, v_inst_307_);
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_315_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad(lean_object* v_00_u03c9_318_, lean_object* v_00_u03c3_319_, lean_object* v_m_320_, lean_object* v_inst_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_StateRefT_x27_instMonad___redArg(v_inst_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadLift(lean_object* v_00_u03c9_324_, lean_object* v_00_u03c3_325_, lean_object* v_m_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = ((lean_object*)(l_StateRefT_x27_instMonadLift___closed__0));
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___redArg(lean_object* v_f_328_, lean_object* v_x_329_, lean_object* v_ctx_330_){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
lean_inc(v_ctx_330_);
v___x_331_ = lean_apply_1(v_x_329_, v_ctx_330_);
v___x_332_ = lean_apply_2(v_f_328_, lean_box(0), v___x_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___redArg___boxed(lean_object* v_f_333_, lean_object* v_x_334_, lean_object* v_ctx_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_StateRefT_x27_instMonadFunctor___aux__1___redArg(v_f_333_, v_x_334_, v_ctx_335_);
lean_dec(v_ctx_335_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor___aux__1(lean_object* v_00_u03c9_337_, lean_object* v_00_u03c3_338_, lean_object* v_m_339_, lean_object* v_00_u03b1_340_, lean_object* v_f_341_, lean_object* v_x_342_, lean_object* v_ctx_343_){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
lean_inc(v_ctx_343_);
v___x_344_ = lean_apply_1(v_x_342_, v_ctx_343_);
v___x_345_ = lean_apply_2(v_f_341_, lean_box(0), v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object* v_00_u03c9_346_, lean_object* v_00_u03c3_347_, lean_object* v_m_348_, lean_object* v_00_u03b1_349_, lean_object* v_f_350_, lean_object* v_x_351_, lean_object* v_ctx_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_StateRefT_x27_instMonadFunctor___aux__1(v_00_u03c9_346_, v_00_u03c3_347_, v_m_348_, v_00_u03b1_349_, v_f_350_, v_x_351_, v_ctx_352_);
lean_dec(v_ctx_352_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor(lean_object* v_00_u03c9_355_, lean_object* v_00_u03c3_356_, lean_object* v_m_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = ((lean_object*)(l_StateRefT_x27_instMonadFunctor___closed__0));
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__0(lean_object* v_inst_359_, lean_object* v_00_u03b1_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_failure_362_; lean_object* v___x_363_; 
v_failure_362_ = lean_ctor_get(v_inst_359_, 1);
lean_inc(v_failure_362_);
lean_dec_ref(v_inst_359_);
v___x_363_ = lean_apply_1(v_failure_362_, lean_box(0));
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__0___boxed(lean_object* v_inst_364_, lean_object* v_00_u03b1_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__0(v_inst_364_, v_00_u03b1_365_, v___y_366_);
lean_dec(v___y_366_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__1(lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v_x_370_){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_box(0);
lean_inc(v___y_369_);
v___x_372_ = lean_apply_2(v___y_368_, v___x_371_, v___y_369_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__1___boxed(lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v_x_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__1(v___y_373_, v___y_374_, v_x_375_);
lean_dec(v___y_374_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__2(lean_object* v_inst_377_, lean_object* v_00_u03b1_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_orElse_382_; lean_object* v___f_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_orElse_382_ = lean_ctor_get(v_inst_377_, 2);
lean_inc(v_orElse_382_);
lean_dec_ref(v_inst_377_);
lean_inc_n(v___y_381_, 2);
v___f_383_ = lean_alloc_closure((void*)(l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_383_, 0, v___y_380_);
lean_closure_set(v___f_383_, 1, v___y_381_);
v___x_384_ = lean_apply_1(v___y_379_, v___y_381_);
v___x_385_ = lean_apply_3(v_orElse_382_, lean_box(0), v___x_384_, v___f_383_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__2___boxed(lean_object* v_inst_386_, lean_object* v_00_u03b1_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__2(v_inst_386_, v_00_u03b1_387_, v___y_388_, v___y_389_, v___y_390_);
lean_dec(v___y_390_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg(lean_object* v_inst_392_, lean_object* v_inst_393_){
_start:
{
lean_object* v___x_394_; lean_object* v_toApplicative_395_; lean_object* v___f_396_; lean_object* v___f_397_; lean_object* v___x_398_; 
v___x_394_ = l_StateRefT_x27_instMonad___redArg(v_inst_393_);
v_toApplicative_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc_ref(v_toApplicative_395_);
lean_dec_ref(v___x_394_);
lean_inc_ref(v_inst_392_);
v___f_396_ = lean_alloc_closure((void*)(l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_396_, 0, v_inst_392_);
v___f_397_ = lean_alloc_closure((void*)(l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__2___boxed), 5, 1);
lean_closure_set(v___f_397_, 0, v_inst_392_);
v___x_398_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_398_, 0, v_toApplicative_395_);
lean_ctor_set(v___x_398_, 1, v___f_396_);
lean_ctor_set(v___x_398_, 2, v___f_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad(lean_object* v_00_u03c9_399_, lean_object* v_00_u03c3_400_, lean_object* v_m_401_, lean_object* v_inst_402_, lean_object* v_inst_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_StateRefT_x27_instAlternativeOfMonad___redArg(v_inst_402_, v_inst_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg___lam__0(lean_object* v_x_405_){
_start:
{
lean_inc(v_x_405_);
return v_x_405_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg___lam__0___boxed(lean_object* v_x_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg___lam__0(v_x_406_);
lean_dec(v_x_406_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg(lean_object* v_inst_409_, lean_object* v_inst_410_, lean_object* v_x_411_, lean_object* v_r_412_){
_start:
{
lean_object* v_toApplicative_413_; lean_object* v_toFunctor_414_; lean_object* v_map_415_; lean_object* v___f_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v_toApplicative_413_ = lean_ctor_get(v_inst_409_, 0);
lean_inc_ref(v_toApplicative_413_);
lean_dec_ref(v_inst_409_);
v_toFunctor_414_ = lean_ctor_get(v_toApplicative_413_, 0);
lean_inc_ref(v_toFunctor_414_);
lean_dec_ref(v_toApplicative_413_);
v_map_415_ = lean_ctor_get(v_toFunctor_414_, 0);
lean_inc(v_map_415_);
lean_dec_ref(v_toFunctor_414_);
v___f_416_ = ((lean_object*)(l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg___closed__0));
lean_inc(v_r_412_);
v___x_417_ = lean_apply_1(v_x_411_, v_r_412_);
v___x_418_ = lean_apply_2(v_inst_410_, lean_box(0), v___x_417_);
v___x_419_ = lean_apply_4(v_map_415_, lean_box(0), lean_box(0), v___f_416_, v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg___boxed(lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_x_422_, lean_object* v_r_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg(v_inst_420_, v_inst_421_, v_x_422_, v_r_423_);
lean_dec(v_r_423_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__1(lean_object* v_00_u03c9_425_, lean_object* v_00_u03c3_426_, lean_object* v_m_427_, lean_object* v_inst_428_, lean_object* v_inst_429_, lean_object* v_00_u03b1_430_, lean_object* v_x_431_, lean_object* v_r_432_){
_start:
{
lean_object* v_toApplicative_433_; lean_object* v_toFunctor_434_; lean_object* v_map_435_; lean_object* v___f_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v_toApplicative_433_ = lean_ctor_get(v_inst_428_, 0);
lean_inc_ref(v_toApplicative_433_);
lean_dec_ref(v_inst_428_);
v_toFunctor_434_ = lean_ctor_get(v_toApplicative_433_, 0);
lean_inc_ref(v_toFunctor_434_);
lean_dec_ref(v_toApplicative_433_);
v_map_435_ = lean_ctor_get(v_toFunctor_434_, 0);
lean_inc(v_map_435_);
lean_dec_ref(v_toFunctor_434_);
v___f_436_ = ((lean_object*)(l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg___closed__0));
lean_inc(v_r_432_);
v___x_437_ = lean_apply_1(v_x_431_, v_r_432_);
v___x_438_ = lean_apply_2(v_inst_429_, lean_box(0), v___x_437_);
v___x_439_ = lean_apply_4(v_map_435_, lean_box(0), lean_box(0), v___f_436_, v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__1___boxed(lean_object* v_00_u03c9_440_, lean_object* v_00_u03c3_441_, lean_object* v_m_442_, lean_object* v_inst_443_, lean_object* v_inst_444_, lean_object* v_00_u03b1_445_, lean_object* v_x_446_, lean_object* v_r_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_StateRefT_x27_instMonadAttachOfMonad___aux__1(v_00_u03c9_440_, v_00_u03c3_441_, v_m_442_, v_inst_443_, v_inst_444_, v_00_u03b1_445_, v_x_446_, v_r_447_);
lean_dec(v_r_447_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___redArg(lean_object* v_inst_449_, lean_object* v_inst_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadAttachOfMonad___aux__1___boxed), 8, 5);
lean_closure_set(v___x_451_, 0, lean_box(0));
lean_closure_set(v___x_451_, 1, lean_box(0));
lean_closure_set(v___x_451_, 2, lean_box(0));
lean_closure_set(v___x_451_, 3, v_inst_449_);
lean_closure_set(v___x_451_, 4, v_inst_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad(lean_object* v_00_u03c9_452_, lean_object* v_00_u03c3_453_, lean_object* v_m_454_, lean_object* v_inst_455_, lean_object* v_inst_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadAttachOfMonad___aux__1___boxed), 8, 5);
lean_closure_set(v___x_457_, 0, lean_box(0));
lean_closure_set(v___x_457_, 1, lean_box(0));
lean_closure_set(v___x_457_, 2, lean_box(0));
lean_closure_set(v___x_457_, 3, v_inst_455_);
lean_closure_set(v___x_457_, 4, v_inst_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_get___redArg(lean_object* v_inst_458_, lean_object* v_ref_459_){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
lean_inc(v_ref_459_);
v___x_460_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_460_, 0, lean_box(0));
lean_closure_set(v___x_460_, 1, lean_box(0));
lean_closure_set(v___x_460_, 2, v_ref_459_);
v___x_461_ = lean_apply_2(v_inst_458_, lean_box(0), v___x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_get___redArg___boxed(lean_object* v_inst_462_, lean_object* v_ref_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_StateRefT_x27_get___redArg(v_inst_462_, v_ref_463_);
lean_dec(v_ref_463_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_get(lean_object* v_00_u03c9_465_, lean_object* v_00_u03c3_466_, lean_object* v_m_467_, lean_object* v_inst_468_, lean_object* v_ref_469_){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
lean_inc(v_ref_469_);
v___x_470_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_470_, 0, lean_box(0));
lean_closure_set(v___x_470_, 1, lean_box(0));
lean_closure_set(v___x_470_, 2, v_ref_469_);
v___x_471_ = lean_apply_2(v_inst_468_, lean_box(0), v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_get___boxed(lean_object* v_00_u03c9_472_, lean_object* v_00_u03c3_473_, lean_object* v_m_474_, lean_object* v_inst_475_, lean_object* v_ref_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_StateRefT_x27_get(v_00_u03c9_472_, v_00_u03c3_473_, v_m_474_, v_inst_475_, v_ref_476_);
lean_dec(v_ref_476_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_set___redArg(lean_object* v_inst_478_, lean_object* v_s_479_, lean_object* v_ref_480_){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
lean_inc(v_ref_480_);
v___x_481_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_481_, 0, lean_box(0));
lean_closure_set(v___x_481_, 1, lean_box(0));
lean_closure_set(v___x_481_, 2, v_ref_480_);
lean_closure_set(v___x_481_, 3, v_s_479_);
v___x_482_ = lean_apply_2(v_inst_478_, lean_box(0), v___x_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_set___redArg___boxed(lean_object* v_inst_483_, lean_object* v_s_484_, lean_object* v_ref_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_StateRefT_x27_set___redArg(v_inst_483_, v_s_484_, v_ref_485_);
lean_dec(v_ref_485_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_set(lean_object* v_00_u03c9_487_, lean_object* v_00_u03c3_488_, lean_object* v_m_489_, lean_object* v_inst_490_, lean_object* v_s_491_, lean_object* v_ref_492_){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
lean_inc(v_ref_492_);
v___x_493_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_493_, 0, lean_box(0));
lean_closure_set(v___x_493_, 1, lean_box(0));
lean_closure_set(v___x_493_, 2, v_ref_492_);
lean_closure_set(v___x_493_, 3, v_s_491_);
v___x_494_ = lean_apply_2(v_inst_490_, lean_box(0), v___x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_set___boxed(lean_object* v_00_u03c9_495_, lean_object* v_00_u03c3_496_, lean_object* v_m_497_, lean_object* v_inst_498_, lean_object* v_s_499_, lean_object* v_ref_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_StateRefT_x27_set(v_00_u03c9_495_, v_00_u03c3_496_, v_m_497_, v_inst_498_, v_s_499_, v_ref_500_);
lean_dec(v_ref_500_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_modifyGet___redArg(lean_object* v_inst_502_, lean_object* v_f_503_, lean_object* v_ref_504_){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
lean_inc(v_ref_504_);
v___x_505_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_505_, 0, lean_box(0));
lean_closure_set(v___x_505_, 1, lean_box(0));
lean_closure_set(v___x_505_, 2, lean_box(0));
lean_closure_set(v___x_505_, 3, v_ref_504_);
lean_closure_set(v___x_505_, 4, v_f_503_);
v___x_506_ = lean_apply_2(v_inst_502_, lean_box(0), v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_modifyGet___redArg___boxed(lean_object* v_inst_507_, lean_object* v_f_508_, lean_object* v_ref_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_StateRefT_x27_modifyGet___redArg(v_inst_507_, v_f_508_, v_ref_509_);
lean_dec(v_ref_509_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_modifyGet(lean_object* v_00_u03c9_511_, lean_object* v_00_u03c3_512_, lean_object* v_m_513_, lean_object* v_00_u03b1_514_, lean_object* v_inst_515_, lean_object* v_f_516_, lean_object* v_ref_517_){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
lean_inc(v_ref_517_);
v___x_518_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_518_, 0, lean_box(0));
lean_closure_set(v___x_518_, 1, lean_box(0));
lean_closure_set(v___x_518_, 2, lean_box(0));
lean_closure_set(v___x_518_, 3, v_ref_517_);
lean_closure_set(v___x_518_, 4, v_f_516_);
v___x_519_ = lean_apply_2(v_inst_515_, lean_box(0), v___x_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_modifyGet___boxed(lean_object* v_00_u03c9_520_, lean_object* v_00_u03c3_521_, lean_object* v_m_522_, lean_object* v_00_u03b1_523_, lean_object* v_inst_524_, lean_object* v_f_525_, lean_object* v_ref_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_StateRefT_x27_modifyGet(v_00_u03c9_520_, v_00_u03c3_521_, v_m_522_, v_00_u03b1_523_, v_inst_524_, v_f_525_, v_ref_526_);
lean_dec(v_ref_526_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg___lam__0(lean_object* v_inst_528_, lean_object* v_00_u03b1_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
lean_inc(v___y_531_);
v___x_532_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_532_, 0, lean_box(0));
lean_closure_set(v___x_532_, 1, lean_box(0));
lean_closure_set(v___x_532_, 2, lean_box(0));
lean_closure_set(v___x_532_, 3, v___y_531_);
lean_closure_set(v___x_532_, 4, v___y_530_);
v___x_533_ = lean_apply_2(v_inst_528_, lean_box(0), v___x_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg___lam__0___boxed(lean_object* v_inst_534_, lean_object* v_00_u03b1_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg___lam__0(v_inst_534_, v_00_u03b1_535_, v___y_536_, v___y_537_);
lean_dec(v___y_537_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg(lean_object* v_inst_539_){
_start:
{
lean_object* v___f_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
lean_inc_n(v_inst_539_, 2);
v___f_540_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_540_, 0, v_inst_539_);
v___x_541_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_541_, 0, lean_box(0));
lean_closure_set(v___x_541_, 1, lean_box(0));
lean_closure_set(v___x_541_, 2, lean_box(0));
lean_closure_set(v___x_541_, 3, v_inst_539_);
v___x_542_ = lean_alloc_closure((void*)(l_StateRefT_x27_set___boxed), 6, 4);
lean_closure_set(v___x_542_, 0, lean_box(0));
lean_closure_set(v___x_542_, 1, lean_box(0));
lean_closure_set(v___x_542_, 2, lean_box(0));
lean_closure_set(v___x_542_, 3, v_inst_539_);
v___x_543_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_543_, 0, v___x_541_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
lean_ctor_set(v___x_543_, 2, v___f_540_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadStateOfOfMonadLiftTST(lean_object* v_00_u03c9_544_, lean_object* v_00_u03c3_545_, lean_object* v_m_546_, lean_object* v_inst_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg(v_inst_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0(lean_object* v_inst_549_, lean_object* v_00_u03b1_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v_throw_553_; lean_object* v___x_554_; 
v_throw_553_ = lean_ctor_get(v_inst_549_, 0);
lean_inc(v_throw_553_);
lean_dec_ref(v_inst_549_);
v___x_554_ = lean_apply_2(v_throw_553_, lean_box(0), v___y_551_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object* v_inst_555_, lean_object* v_00_u03b1_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_StateRefT_x27_instMonadExceptOf___redArg___lam__0(v_inst_555_, v_00_u03b1_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__1(lean_object* v_c_560_, lean_object* v_s_561_, lean_object* v_e_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = lean_apply_2(v_c_560_, v_e_562_, v_s_561_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object* v_inst_564_, lean_object* v_00_u03b1_565_, lean_object* v_x_566_, lean_object* v_c_567_, lean_object* v_s_568_){
_start:
{
lean_object* v_tryCatch_569_; lean_object* v___f_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v_tryCatch_569_ = lean_ctor_get(v_inst_564_, 1);
lean_inc(v_tryCatch_569_);
lean_dec_ref(v_inst_564_);
lean_inc(v_s_568_);
v___f_570_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__1), 3, 2);
lean_closure_set(v___f_570_, 0, v_c_567_);
lean_closure_set(v___f_570_, 1, v_s_568_);
v___x_571_ = lean_apply_1(v_x_566_, v_s_568_);
v___x_572_ = lean_apply_3(v_tryCatch_569_, lean_box(0), v___x_571_, v___f_570_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadExceptOf___redArg(lean_object* v_inst_573_){
_start:
{
lean_object* v___f_574_; lean_object* v___f_575_; lean_object* v___x_576_; 
lean_inc_ref(v_inst_573_);
v___f_574_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_574_, 0, v_inst_573_);
v___f_575_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_575_, 0, v_inst_573_);
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v___f_574_);
lean_ctor_set(v___x_576_, 1, v___f_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadExceptOf(lean_object* v_00_u03c9_577_, lean_object* v_00_u03c3_578_, lean_object* v_m_579_, lean_object* v_00_u03b5_580_, lean_object* v_inst_581_){
_start:
{
lean_object* v___f_582_; lean_object* v___f_583_; lean_object* v___x_584_; 
lean_inc_ref(v_inst_581_);
v___f_582_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_582_, 0, v_inst_581_);
v___f_583_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_583_, 0, v_inst_581_);
v___x_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_584_, 0, v___f_582_);
lean_ctor_set(v___x_584_, 1, v___f_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0(lean_object* v_ctx_585_, lean_object* v_00_u03b2_586_, lean_object* v_x_587_){
_start:
{
lean_object* v___x_588_; 
lean_inc(v_ctx_585_);
v___x_588_ = lean_apply_1(v_x_587_, v_ctx_585_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0___boxed(lean_object* v_ctx_589_, lean_object* v_00_u03b2_590_, lean_object* v_x_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0(v_ctx_589_, v_00_u03b2_590_, v_x_591_);
lean_dec(v_ctx_589_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__1___redArg(lean_object* v_f_593_, lean_object* v_ctx_594_){
_start:
{
lean_object* v___f_595_; lean_object* v___x_596_; 
lean_inc(v_ctx_594_);
v___f_595_ = lean_alloc_closure((void*)(l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_595_, 0, v_ctx_594_);
v___x_596_ = lean_apply_1(v_f_593_, v___f_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__1___redArg___boxed(lean_object* v_f_597_, lean_object* v_ctx_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_instMonadControlStateRefT_x27___aux__1___redArg(v_f_597_, v_ctx_598_);
lean_dec(v_ctx_598_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__1(lean_object* v_00_u03c9_600_, lean_object* v_00_u03c3_601_, lean_object* v_m_602_, lean_object* v_00_u03b1_603_, lean_object* v_f_604_, lean_object* v_ctx_605_){
_start:
{
lean_object* v___f_606_; lean_object* v___x_607_; 
lean_inc(v_ctx_605_);
v___f_606_ = lean_alloc_closure((void*)(l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_606_, 0, v_ctx_605_);
v___x_607_ = lean_apply_1(v_f_604_, v___f_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__1___boxed(lean_object* v_00_u03c9_608_, lean_object* v_00_u03c3_609_, lean_object* v_m_610_, lean_object* v_00_u03b1_611_, lean_object* v_f_612_, lean_object* v_ctx_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_instMonadControlStateRefT_x27___aux__1(v_00_u03c9_608_, v_00_u03c3_609_, v_m_610_, v_00_u03b1_611_, v_f_612_, v_ctx_613_);
lean_dec(v_ctx_613_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__3___redArg(lean_object* v_x_615_){
_start:
{
lean_inc(v_x_615_);
return v_x_615_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__3___redArg___boxed(lean_object* v_x_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_instMonadControlStateRefT_x27___aux__3___redArg(v_x_616_);
lean_dec(v_x_616_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__3(lean_object* v_00_u03c9_618_, lean_object* v_00_u03c3_619_, lean_object* v_m_620_, lean_object* v_00_u03b1_621_, lean_object* v_x_622_, lean_object* v_x_623_){
_start:
{
lean_inc(v_x_622_);
return v_x_622_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__3___boxed(lean_object* v_00_u03c9_624_, lean_object* v_00_u03c3_625_, lean_object* v_m_626_, lean_object* v_00_u03b1_627_, lean_object* v_x_628_, lean_object* v_x_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_instMonadControlStateRefT_x27___aux__3(v_00_u03c9_624_, v_00_u03c3_625_, v_m_626_, v_00_u03b1_627_, v_x_628_, v_x_629_);
lean_dec(v_x_629_);
lean_dec(v_x_628_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27(lean_object* v_00_u03c9_636_, lean_object* v_00_u03c3_637_, lean_object* v_m_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = ((lean_object*)(l_instMonadControlStateRefT_x27___closed__2));
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0(lean_object* v_h_640_, lean_object* v_ctx_641_, lean_object* v_a_x3f_642_){
_start:
{
lean_object* v___x_643_; 
lean_inc(v_ctx_641_);
v___x_643_ = lean_apply_2(v_h_640_, v_a_x3f_642_, v_ctx_641_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0___boxed(lean_object* v_h_644_, lean_object* v_ctx_645_, lean_object* v_a_x3f_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0(v_h_644_, v_ctx_645_, v_a_x3f_646_);
lean_dec(v_ctx_645_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___aux__1___redArg(lean_object* v_inst_648_, lean_object* v_x_649_, lean_object* v_h_650_, lean_object* v_ctx_651_){
_start:
{
lean_object* v___f_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
lean_inc_n(v_ctx_651_, 2);
v___f_652_ = lean_alloc_closure((void*)(l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_652_, 0, v_h_650_);
lean_closure_set(v___f_652_, 1, v_ctx_651_);
v___x_653_ = lean_apply_1(v_x_649_, v_ctx_651_);
v___x_654_ = lean_apply_4(v_inst_648_, lean_box(0), lean_box(0), v___x_653_, v___f_652_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___aux__1___redArg___boxed(lean_object* v_inst_655_, lean_object* v_x_656_, lean_object* v_h_657_, lean_object* v_ctx_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_instMonadFinallyStateRefT_x27___aux__1___redArg(v_inst_655_, v_x_656_, v_h_657_, v_ctx_658_);
lean_dec(v_ctx_658_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___aux__1(lean_object* v_m_660_, lean_object* v_00_u03c9_661_, lean_object* v_00_u03c3_662_, lean_object* v_inst_663_, lean_object* v_00_u03b1_664_, lean_object* v_00_u03b2_665_, lean_object* v_x_666_, lean_object* v_h_667_, lean_object* v_ctx_668_){
_start:
{
lean_object* v___f_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
lean_inc_n(v_ctx_668_, 2);
v___f_669_ = lean_alloc_closure((void*)(l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_669_, 0, v_h_667_);
lean_closure_set(v___f_669_, 1, v_ctx_668_);
v___x_670_ = lean_apply_1(v_x_666_, v_ctx_668_);
v___x_671_ = lean_apply_4(v_inst_663_, lean_box(0), lean_box(0), v___x_670_, v___f_669_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___aux__1___boxed(lean_object* v_m_672_, lean_object* v_00_u03c9_673_, lean_object* v_00_u03c3_674_, lean_object* v_inst_675_, lean_object* v_00_u03b1_676_, lean_object* v_00_u03b2_677_, lean_object* v_x_678_, lean_object* v_h_679_, lean_object* v_ctx_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_instMonadFinallyStateRefT_x27___aux__1(v_m_672_, v_00_u03c9_673_, v_00_u03c3_674_, v_inst_675_, v_00_u03b1_676_, v_00_u03b2_677_, v_x_678_, v_h_679_, v_ctx_680_);
lean_dec(v_ctx_680_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___redArg(lean_object* v_inst_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = lean_alloc_closure((void*)(l_instMonadFinallyStateRefT_x27___aux__1___boxed), 9, 4);
lean_closure_set(v___x_683_, 0, lean_box(0));
lean_closure_set(v___x_683_, 1, lean_box(0));
lean_closure_set(v___x_683_, 2, lean_box(0));
lean_closure_set(v___x_683_, 3, v_inst_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27(lean_object* v_m_684_, lean_object* v_00_u03c9_685_, lean_object* v_00_u03c3_686_, lean_object* v_inst_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = lean_alloc_closure((void*)(l_instMonadFinallyStateRefT_x27___aux__1___boxed), 9, 4);
lean_closure_set(v___x_688_, 0, lean_box(0));
lean_closure_set(v___x_688_, 1, lean_box(0));
lean_closure_set(v___x_688_, 2, lean_box(0));
lean_closure_set(v___x_688_, 3, v_inst_687_);
return v___x_688_;
}
}
lean_object* runtime_initialize_Init_System_ST(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Reader(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Control_StateRef(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_System_ST(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Reader(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Control_StateRef(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_ST(uint8_t builtin);
lean_object* initialize_Init_Control_Reader(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Control_StateRef(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_ST(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Reader(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_StateRef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Control_StateRef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Control_StateRef(builtin);
}
#ifdef __cplusplus
}
#endif

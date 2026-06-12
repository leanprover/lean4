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
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__7___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__9___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__13___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__13___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___aux__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___aux__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___aux__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___closed__0 = (const lean_object*)&l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__5___redArg(lean_object* v_inst_175_, lean_object* v_a_176_){
_start:
{
lean_object* v_toApplicative_177_; lean_object* v_toPure_178_; lean_object* v___x_179_; 
v_toApplicative_177_ = lean_ctor_get(v_inst_175_, 0);
lean_inc_ref(v_toApplicative_177_);
lean_dec_ref(v_inst_175_);
v_toPure_178_ = lean_ctor_get(v_toApplicative_177_, 1);
lean_inc(v_toPure_178_);
lean_dec_ref(v_toApplicative_177_);
v___x_179_ = lean_apply_2(v_toPure_178_, lean_box(0), v_a_176_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__5(lean_object* v_00_u03c9_180_, lean_object* v_00_u03c3_181_, lean_object* v_m_182_, lean_object* v_inst_183_, lean_object* v_00_u03b1_184_, lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
lean_object* v_toApplicative_187_; lean_object* v_toPure_188_; lean_object* v___x_189_; 
v_toApplicative_187_ = lean_ctor_get(v_inst_183_, 0);
lean_inc_ref(v_toApplicative_187_);
lean_dec_ref(v_inst_183_);
v_toPure_188_ = lean_ctor_get(v_toApplicative_187_, 1);
lean_inc(v_toPure_188_);
lean_dec_ref(v_toApplicative_187_);
v___x_189_ = lean_apply_2(v_toPure_188_, lean_box(0), v_a_185_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__5___boxed(lean_object* v_00_u03c9_190_, lean_object* v_00_u03c3_191_, lean_object* v_m_192_, lean_object* v_inst_193_, lean_object* v_00_u03b1_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_StateRefT_x27_instMonad___aux__5(v_00_u03c9_190_, v_00_u03c3_191_, v_m_192_, v_inst_193_, v_00_u03b1_194_, v_a_195_, v_a_196_);
lean_dec(v_a_196_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__7___redArg___lam__0(lean_object* v_x_198_, lean_object* v_r_199_, lean_object* v_x_200_){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_box(0);
lean_inc(v_r_199_);
v___x_202_ = lean_apply_2(v_x_198_, v___x_201_, v_r_199_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__7___redArg___lam__0___boxed(lean_object* v_x_203_, lean_object* v_r_204_, lean_object* v_x_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_StateRefT_x27_instMonad___aux__7___redArg___lam__0(v_x_203_, v_r_204_, v_x_205_);
lean_dec(v_r_204_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__7___redArg(lean_object* v_inst_207_, lean_object* v_f_208_, lean_object* v_x_209_, lean_object* v_r_210_){
_start:
{
lean_object* v_toApplicative_211_; lean_object* v_toSeq_212_; lean_object* v___f_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_toApplicative_211_ = lean_ctor_get(v_inst_207_, 0);
lean_inc_ref(v_toApplicative_211_);
lean_dec_ref(v_inst_207_);
v_toSeq_212_ = lean_ctor_get(v_toApplicative_211_, 2);
lean_inc(v_toSeq_212_);
lean_dec_ref(v_toApplicative_211_);
lean_inc_n(v_r_210_, 2);
v___f_213_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__7___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_213_, 0, v_x_209_);
lean_closure_set(v___f_213_, 1, v_r_210_);
v___x_214_ = lean_apply_1(v_f_208_, v_r_210_);
v___x_215_ = lean_apply_4(v_toSeq_212_, lean_box(0), lean_box(0), v___x_214_, v___f_213_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__7___redArg___boxed(lean_object* v_inst_216_, lean_object* v_f_217_, lean_object* v_x_218_, lean_object* v_r_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_StateRefT_x27_instMonad___aux__7___redArg(v_inst_216_, v_f_217_, v_x_218_, v_r_219_);
lean_dec(v_r_219_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__7(lean_object* v_00_u03c9_221_, lean_object* v_00_u03c3_222_, lean_object* v_m_223_, lean_object* v_inst_224_, lean_object* v_00_u03b1_225_, lean_object* v_00_u03b2_226_, lean_object* v_f_227_, lean_object* v_x_228_, lean_object* v_r_229_){
_start:
{
lean_object* v_toApplicative_230_; lean_object* v_toSeq_231_; lean_object* v___f_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v_toApplicative_230_ = lean_ctor_get(v_inst_224_, 0);
lean_inc_ref(v_toApplicative_230_);
lean_dec_ref(v_inst_224_);
v_toSeq_231_ = lean_ctor_get(v_toApplicative_230_, 2);
lean_inc(v_toSeq_231_);
lean_dec_ref(v_toApplicative_230_);
lean_inc_n(v_r_229_, 2);
v___f_232_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__7___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_232_, 0, v_x_228_);
lean_closure_set(v___f_232_, 1, v_r_229_);
v___x_233_ = lean_apply_1(v_f_227_, v_r_229_);
v___x_234_ = lean_apply_4(v_toSeq_231_, lean_box(0), lean_box(0), v___x_233_, v___f_232_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__7___boxed(lean_object* v_00_u03c9_235_, lean_object* v_00_u03c3_236_, lean_object* v_m_237_, lean_object* v_inst_238_, lean_object* v_00_u03b1_239_, lean_object* v_00_u03b2_240_, lean_object* v_f_241_, lean_object* v_x_242_, lean_object* v_r_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_StateRefT_x27_instMonad___aux__7(v_00_u03c9_235_, v_00_u03c3_236_, v_m_237_, v_inst_238_, v_00_u03b1_239_, v_00_u03b2_240_, v_f_241_, v_x_242_, v_r_243_);
lean_dec(v_r_243_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__9___redArg___lam__0(lean_object* v_b_245_, lean_object* v_r_246_, lean_object* v_x_247_){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = lean_box(0);
lean_inc(v_r_246_);
v___x_249_ = lean_apply_2(v_b_245_, v___x_248_, v_r_246_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__9___redArg___lam__0___boxed(lean_object* v_b_250_, lean_object* v_r_251_, lean_object* v_x_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_StateRefT_x27_instMonad___aux__9___redArg___lam__0(v_b_250_, v_r_251_, v_x_252_);
lean_dec(v_r_251_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__9___redArg(lean_object* v_inst_254_, lean_object* v_a_255_, lean_object* v_b_256_, lean_object* v_r_257_){
_start:
{
lean_object* v_toApplicative_258_; lean_object* v_toSeqLeft_259_; lean_object* v___f_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_toApplicative_258_ = lean_ctor_get(v_inst_254_, 0);
lean_inc_ref(v_toApplicative_258_);
lean_dec_ref(v_inst_254_);
v_toSeqLeft_259_ = lean_ctor_get(v_toApplicative_258_, 3);
lean_inc(v_toSeqLeft_259_);
lean_dec_ref(v_toApplicative_258_);
lean_inc_n(v_r_257_, 2);
v___f_260_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__9___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_260_, 0, v_b_256_);
lean_closure_set(v___f_260_, 1, v_r_257_);
v___x_261_ = lean_apply_1(v_a_255_, v_r_257_);
v___x_262_ = lean_apply_4(v_toSeqLeft_259_, lean_box(0), lean_box(0), v___x_261_, v___f_260_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__9___redArg___boxed(lean_object* v_inst_263_, lean_object* v_a_264_, lean_object* v_b_265_, lean_object* v_r_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_StateRefT_x27_instMonad___aux__9___redArg(v_inst_263_, v_a_264_, v_b_265_, v_r_266_);
lean_dec(v_r_266_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__9(lean_object* v_00_u03c9_268_, lean_object* v_00_u03c3_269_, lean_object* v_m_270_, lean_object* v_inst_271_, lean_object* v_00_u03b1_272_, lean_object* v_00_u03b2_273_, lean_object* v_a_274_, lean_object* v_b_275_, lean_object* v_r_276_){
_start:
{
lean_object* v_toApplicative_277_; lean_object* v_toSeqLeft_278_; lean_object* v___f_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v_toApplicative_277_ = lean_ctor_get(v_inst_271_, 0);
lean_inc_ref(v_toApplicative_277_);
lean_dec_ref(v_inst_271_);
v_toSeqLeft_278_ = lean_ctor_get(v_toApplicative_277_, 3);
lean_inc(v_toSeqLeft_278_);
lean_dec_ref(v_toApplicative_277_);
lean_inc_n(v_r_276_, 2);
v___f_279_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__9___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_279_, 0, v_b_275_);
lean_closure_set(v___f_279_, 1, v_r_276_);
v___x_280_ = lean_apply_1(v_a_274_, v_r_276_);
v___x_281_ = lean_apply_4(v_toSeqLeft_278_, lean_box(0), lean_box(0), v___x_280_, v___f_279_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__9___boxed(lean_object* v_00_u03c9_282_, lean_object* v_00_u03c3_283_, lean_object* v_m_284_, lean_object* v_inst_285_, lean_object* v_00_u03b1_286_, lean_object* v_00_u03b2_287_, lean_object* v_a_288_, lean_object* v_b_289_, lean_object* v_r_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_StateRefT_x27_instMonad___aux__9(v_00_u03c9_282_, v_00_u03c3_283_, v_m_284_, v_inst_285_, v_00_u03b1_286_, v_00_u03b2_287_, v_a_288_, v_b_289_, v_r_290_);
lean_dec(v_r_290_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__11___redArg(lean_object* v_inst_292_, lean_object* v_a_293_, lean_object* v_b_294_, lean_object* v_r_295_){
_start:
{
lean_object* v_toApplicative_296_; lean_object* v_toSeqRight_297_; lean_object* v___f_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v_toApplicative_296_ = lean_ctor_get(v_inst_292_, 0);
lean_inc_ref(v_toApplicative_296_);
lean_dec_ref(v_inst_292_);
v_toSeqRight_297_ = lean_ctor_get(v_toApplicative_296_, 4);
lean_inc(v_toSeqRight_297_);
lean_dec_ref(v_toApplicative_296_);
lean_inc_n(v_r_295_, 2);
v___f_298_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__9___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_298_, 0, v_b_294_);
lean_closure_set(v___f_298_, 1, v_r_295_);
v___x_299_ = lean_apply_1(v_a_293_, v_r_295_);
v___x_300_ = lean_apply_4(v_toSeqRight_297_, lean_box(0), lean_box(0), v___x_299_, v___f_298_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__11___redArg___boxed(lean_object* v_inst_301_, lean_object* v_a_302_, lean_object* v_b_303_, lean_object* v_r_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_StateRefT_x27_instMonad___aux__11___redArg(v_inst_301_, v_a_302_, v_b_303_, v_r_304_);
lean_dec(v_r_304_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__11(lean_object* v_00_u03c9_306_, lean_object* v_00_u03c3_307_, lean_object* v_m_308_, lean_object* v_inst_309_, lean_object* v_00_u03b1_310_, lean_object* v_00_u03b2_311_, lean_object* v_a_312_, lean_object* v_b_313_, lean_object* v_r_314_){
_start:
{
lean_object* v_toApplicative_315_; lean_object* v_toSeqRight_316_; lean_object* v___f_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v_toApplicative_315_ = lean_ctor_get(v_inst_309_, 0);
lean_inc_ref(v_toApplicative_315_);
lean_dec_ref(v_inst_309_);
v_toSeqRight_316_ = lean_ctor_get(v_toApplicative_315_, 4);
lean_inc(v_toSeqRight_316_);
lean_dec_ref(v_toApplicative_315_);
lean_inc_n(v_r_314_, 2);
v___f_317_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__9___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_317_, 0, v_b_313_);
lean_closure_set(v___f_317_, 1, v_r_314_);
v___x_318_ = lean_apply_1(v_a_312_, v_r_314_);
v___x_319_ = lean_apply_4(v_toSeqRight_316_, lean_box(0), lean_box(0), v___x_318_, v___f_317_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__11___boxed(lean_object* v_00_u03c9_320_, lean_object* v_00_u03c3_321_, lean_object* v_m_322_, lean_object* v_inst_323_, lean_object* v_00_u03b1_324_, lean_object* v_00_u03b2_325_, lean_object* v_a_326_, lean_object* v_b_327_, lean_object* v_r_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_StateRefT_x27_instMonad___aux__11(v_00_u03c9_320_, v_00_u03c3_321_, v_m_322_, v_inst_323_, v_00_u03b1_324_, v_00_u03b2_325_, v_a_326_, v_b_327_, v_r_328_);
lean_dec(v_r_328_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__13___redArg___lam__0(lean_object* v_f_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v___x_333_; 
lean_inc(v_a_331_);
v___x_333_ = lean_apply_2(v_f_330_, v_a_332_, v_a_331_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__13___redArg___lam__0___boxed(lean_object* v_f_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_StateRefT_x27_instMonad___aux__13___redArg___lam__0(v_f_334_, v_a_335_, v_a_336_);
lean_dec(v_a_335_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__13___redArg(lean_object* v_inst_338_, lean_object* v_x_339_, lean_object* v_f_340_, lean_object* v_a_341_){
_start:
{
lean_object* v_toBind_342_; lean_object* v___f_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v_toBind_342_ = lean_ctor_get(v_inst_338_, 1);
lean_inc(v_toBind_342_);
lean_dec_ref(v_inst_338_);
lean_inc_n(v_a_341_, 2);
v___f_343_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_343_, 0, v_f_340_);
lean_closure_set(v___f_343_, 1, v_a_341_);
v___x_344_ = lean_apply_1(v_x_339_, v_a_341_);
v___x_345_ = lean_apply_4(v_toBind_342_, lean_box(0), lean_box(0), v___x_344_, v___f_343_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__13___redArg___boxed(lean_object* v_inst_346_, lean_object* v_x_347_, lean_object* v_f_348_, lean_object* v_a_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_StateRefT_x27_instMonad___aux__13___redArg(v_inst_346_, v_x_347_, v_f_348_, v_a_349_);
lean_dec(v_a_349_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__13(lean_object* v_00_u03c9_351_, lean_object* v_00_u03c3_352_, lean_object* v_m_353_, lean_object* v_inst_354_, lean_object* v_00_u03b1_355_, lean_object* v_00_u03b2_356_, lean_object* v_x_357_, lean_object* v_f_358_, lean_object* v_a_359_){
_start:
{
lean_object* v_toBind_360_; lean_object* v___f_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v_toBind_360_ = lean_ctor_get(v_inst_354_, 1);
lean_inc(v_toBind_360_);
lean_dec_ref(v_inst_354_);
lean_inc_n(v_a_359_, 2);
v___f_361_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_361_, 0, v_f_358_);
lean_closure_set(v___f_361_, 1, v_a_359_);
v___x_362_ = lean_apply_1(v_x_357_, v_a_359_);
v___x_363_ = lean_apply_4(v_toBind_360_, lean_box(0), lean_box(0), v___x_362_, v___f_361_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___aux__13___boxed(lean_object* v_00_u03c9_364_, lean_object* v_00_u03c3_365_, lean_object* v_m_366_, lean_object* v_inst_367_, lean_object* v_00_u03b1_368_, lean_object* v_00_u03b2_369_, lean_object* v_x_370_, lean_object* v_f_371_, lean_object* v_a_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_StateRefT_x27_instMonad___aux__13(v_00_u03c9_364_, v_00_u03c3_365_, v_m_366_, v_inst_367_, v_00_u03b1_368_, v_00_u03b2_369_, v_x_370_, v_f_371_, v_a_372_);
lean_dec(v_a_372_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad___redArg(lean_object* v_inst_374_){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
lean_inc_ref_n(v_inst_374_, 6);
v___x_375_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__1___boxed), 9, 4);
lean_closure_set(v___x_375_, 0, lean_box(0));
lean_closure_set(v___x_375_, 1, lean_box(0));
lean_closure_set(v___x_375_, 2, lean_box(0));
lean_closure_set(v___x_375_, 3, v_inst_374_);
v___x_376_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__3___boxed), 9, 4);
lean_closure_set(v___x_376_, 0, lean_box(0));
lean_closure_set(v___x_376_, 1, lean_box(0));
lean_closure_set(v___x_376_, 2, lean_box(0));
lean_closure_set(v___x_376_, 3, v_inst_374_);
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_375_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
v___x_378_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__5___boxed), 7, 4);
lean_closure_set(v___x_378_, 0, lean_box(0));
lean_closure_set(v___x_378_, 1, lean_box(0));
lean_closure_set(v___x_378_, 2, lean_box(0));
lean_closure_set(v___x_378_, 3, v_inst_374_);
v___x_379_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__7___boxed), 9, 4);
lean_closure_set(v___x_379_, 0, lean_box(0));
lean_closure_set(v___x_379_, 1, lean_box(0));
lean_closure_set(v___x_379_, 2, lean_box(0));
lean_closure_set(v___x_379_, 3, v_inst_374_);
v___x_380_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__9___boxed), 9, 4);
lean_closure_set(v___x_380_, 0, lean_box(0));
lean_closure_set(v___x_380_, 1, lean_box(0));
lean_closure_set(v___x_380_, 2, lean_box(0));
lean_closure_set(v___x_380_, 3, v_inst_374_);
v___x_381_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__11___boxed), 9, 4);
lean_closure_set(v___x_381_, 0, lean_box(0));
lean_closure_set(v___x_381_, 1, lean_box(0));
lean_closure_set(v___x_381_, 2, lean_box(0));
lean_closure_set(v___x_381_, 3, v_inst_374_);
v___x_382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_382_, 0, v___x_377_);
lean_ctor_set(v___x_382_, 1, v___x_378_);
lean_ctor_set(v___x_382_, 2, v___x_379_);
lean_ctor_set(v___x_382_, 3, v___x_380_);
lean_ctor_set(v___x_382_, 4, v___x_381_);
v___x_383_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 4);
lean_closure_set(v___x_383_, 0, lean_box(0));
lean_closure_set(v___x_383_, 1, lean_box(0));
lean_closure_set(v___x_383_, 2, lean_box(0));
lean_closure_set(v___x_383_, 3, v_inst_374_);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_382_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonad(lean_object* v_00_u03c9_385_, lean_object* v_00_u03c3_386_, lean_object* v_m_387_, lean_object* v_inst_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_StateRefT_x27_instMonad___redArg(v_inst_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadLift(lean_object* v_00_u03c9_391_, lean_object* v_00_u03c3_392_, lean_object* v_m_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = ((lean_object*)(l_StateRefT_x27_instMonadLift___closed__0));
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___redArg(lean_object* v_f_395_, lean_object* v_x_396_, lean_object* v_ctx_397_){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
lean_inc(v_ctx_397_);
v___x_398_ = lean_apply_1(v_x_396_, v_ctx_397_);
v___x_399_ = lean_apply_2(v_f_395_, lean_box(0), v___x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___redArg___boxed(lean_object* v_f_400_, lean_object* v_x_401_, lean_object* v_ctx_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_StateRefT_x27_instMonadFunctor___aux__1___redArg(v_f_400_, v_x_401_, v_ctx_402_);
lean_dec(v_ctx_402_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor___aux__1(lean_object* v_00_u03c9_404_, lean_object* v_00_u03c3_405_, lean_object* v_m_406_, lean_object* v_00_u03b1_407_, lean_object* v_f_408_, lean_object* v_x_409_, lean_object* v_ctx_410_){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
lean_inc(v_ctx_410_);
v___x_411_ = lean_apply_1(v_x_409_, v_ctx_410_);
v___x_412_ = lean_apply_2(v_f_408_, lean_box(0), v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object* v_00_u03c9_413_, lean_object* v_00_u03c3_414_, lean_object* v_m_415_, lean_object* v_00_u03b1_416_, lean_object* v_f_417_, lean_object* v_x_418_, lean_object* v_ctx_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_StateRefT_x27_instMonadFunctor___aux__1(v_00_u03c9_413_, v_00_u03c3_414_, v_m_415_, v_00_u03b1_416_, v_f_417_, v_x_418_, v_ctx_419_);
lean_dec(v_ctx_419_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor(lean_object* v_00_u03c9_422_, lean_object* v_00_u03c3_423_, lean_object* v_m_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = ((lean_object*)(l_StateRefT_x27_instMonadFunctor___closed__0));
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___aux__1___redArg(lean_object* v_inst_426_){
_start:
{
lean_object* v_failure_427_; lean_object* v___x_428_; 
v_failure_427_ = lean_ctor_get(v_inst_426_, 1);
lean_inc(v_failure_427_);
lean_dec_ref(v_inst_426_);
v___x_428_ = lean_apply_1(v_failure_427_, lean_box(0));
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___aux__1(lean_object* v_00_u03c9_429_, lean_object* v_00_u03c3_430_, lean_object* v_m_431_, lean_object* v_inst_432_, lean_object* v_00_u03b1_433_, lean_object* v_a_434_){
_start:
{
lean_object* v_failure_435_; lean_object* v___x_436_; 
v_failure_435_ = lean_ctor_get(v_inst_432_, 1);
lean_inc(v_failure_435_);
lean_dec_ref(v_inst_432_);
v___x_436_ = lean_apply_1(v_failure_435_, lean_box(0));
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___aux__1___boxed(lean_object* v_00_u03c9_437_, lean_object* v_00_u03c3_438_, lean_object* v_m_439_, lean_object* v_inst_440_, lean_object* v_00_u03b1_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_StateRefT_x27_instAlternativeOfMonad___aux__1(v_00_u03c9_437_, v_00_u03c3_438_, v_m_439_, v_inst_440_, v_00_u03b1_441_, v_a_442_);
lean_dec(v_a_442_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg___lam__0(lean_object* v_x_u2082_444_, lean_object* v_a_445_, lean_object* v_x_446_){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = lean_box(0);
lean_inc(v_a_445_);
v___x_448_ = lean_apply_2(v_x_u2082_444_, v___x_447_, v_a_445_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg___lam__0___boxed(lean_object* v_x_u2082_449_, lean_object* v_a_450_, lean_object* v_x_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg___lam__0(v_x_u2082_449_, v_a_450_, v_x_451_);
lean_dec(v_a_450_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg(lean_object* v_inst_453_, lean_object* v_x_u2081_454_, lean_object* v_x_u2082_455_, lean_object* v_a_456_){
_start:
{
lean_object* v_orElse_457_; lean_object* v___f_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v_orElse_457_ = lean_ctor_get(v_inst_453_, 2);
lean_inc(v_orElse_457_);
lean_dec_ref(v_inst_453_);
lean_inc_n(v_a_456_, 2);
v___f_458_ = lean_alloc_closure((void*)(l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_458_, 0, v_x_u2082_455_);
lean_closure_set(v___f_458_, 1, v_a_456_);
v___x_459_ = lean_apply_1(v_x_u2081_454_, v_a_456_);
v___x_460_ = lean_apply_3(v_orElse_457_, lean_box(0), v___x_459_, v___f_458_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg___boxed(lean_object* v_inst_461_, lean_object* v_x_u2081_462_, lean_object* v_x_u2082_463_, lean_object* v_a_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg(v_inst_461_, v_x_u2081_462_, v_x_u2082_463_, v_a_464_);
lean_dec(v_a_464_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___aux__3(lean_object* v_00_u03c9_466_, lean_object* v_00_u03c3_467_, lean_object* v_m_468_, lean_object* v_inst_469_, lean_object* v_00_u03b1_470_, lean_object* v_x_u2081_471_, lean_object* v_x_u2082_472_, lean_object* v_a_473_){
_start:
{
lean_object* v_orElse_474_; lean_object* v___f_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v_orElse_474_ = lean_ctor_get(v_inst_469_, 2);
lean_inc(v_orElse_474_);
lean_dec_ref(v_inst_469_);
lean_inc_n(v_a_473_, 2);
v___f_475_ = lean_alloc_closure((void*)(l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_475_, 0, v_x_u2082_472_);
lean_closure_set(v___f_475_, 1, v_a_473_);
v___x_476_ = lean_apply_1(v_x_u2081_471_, v_a_473_);
v___x_477_ = lean_apply_3(v_orElse_474_, lean_box(0), v___x_476_, v___f_475_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___aux__3___boxed(lean_object* v_00_u03c9_478_, lean_object* v_00_u03c3_479_, lean_object* v_m_480_, lean_object* v_inst_481_, lean_object* v_00_u03b1_482_, lean_object* v_x_u2081_483_, lean_object* v_x_u2082_484_, lean_object* v_a_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_StateRefT_x27_instAlternativeOfMonad___aux__3(v_00_u03c9_478_, v_00_u03c3_479_, v_m_480_, v_inst_481_, v_00_u03b1_482_, v_x_u2081_483_, v_x_u2082_484_, v_a_485_);
lean_dec(v_a_485_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg(lean_object* v_inst_487_, lean_object* v_inst_488_){
_start:
{
lean_object* v___x_489_; lean_object* v_toApplicative_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_489_ = l_StateRefT_x27_instMonad___redArg(v_inst_488_);
v_toApplicative_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc_ref(v_toApplicative_490_);
lean_dec_ref(v___x_489_);
lean_inc_ref(v_inst_487_);
v___x_491_ = lean_alloc_closure((void*)(l_StateRefT_x27_instAlternativeOfMonad___aux__1___boxed), 6, 4);
lean_closure_set(v___x_491_, 0, lean_box(0));
lean_closure_set(v___x_491_, 1, lean_box(0));
lean_closure_set(v___x_491_, 2, lean_box(0));
lean_closure_set(v___x_491_, 3, v_inst_487_);
v___x_492_ = lean_alloc_closure((void*)(l_StateRefT_x27_instAlternativeOfMonad___aux__3___boxed), 8, 4);
lean_closure_set(v___x_492_, 0, lean_box(0));
lean_closure_set(v___x_492_, 1, lean_box(0));
lean_closure_set(v___x_492_, 2, lean_box(0));
lean_closure_set(v___x_492_, 3, v_inst_487_);
v___x_493_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_493_, 0, v_toApplicative_490_);
lean_ctor_set(v___x_493_, 1, v___x_491_);
lean_ctor_set(v___x_493_, 2, v___x_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad(lean_object* v_00_u03c9_494_, lean_object* v_00_u03c3_495_, lean_object* v_m_496_, lean_object* v_inst_497_, lean_object* v_inst_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_StateRefT_x27_instAlternativeOfMonad___redArg(v_inst_497_, v_inst_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___lam__0(lean_object* v_x_500_){
_start:
{
lean_inc(v_x_500_);
return v_x_500_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___lam__0___boxed(lean_object* v_x_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___lam__0(v_x_501_);
lean_dec(v_x_501_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg(lean_object* v_inst_504_, lean_object* v_inst_505_, lean_object* v_x_506_, lean_object* v_r_507_){
_start:
{
lean_object* v_toApplicative_508_; lean_object* v_toFunctor_509_; lean_object* v_map_510_; lean_object* v___f_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v_toApplicative_508_ = lean_ctor_get(v_inst_504_, 0);
lean_inc_ref(v_toApplicative_508_);
lean_dec_ref(v_inst_504_);
v_toFunctor_509_ = lean_ctor_get(v_toApplicative_508_, 0);
lean_inc_ref(v_toFunctor_509_);
lean_dec_ref(v_toApplicative_508_);
v_map_510_ = lean_ctor_get(v_toFunctor_509_, 0);
lean_inc(v_map_510_);
lean_dec_ref(v_toFunctor_509_);
v___f_511_ = ((lean_object*)(l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___closed__0));
lean_inc(v_r_507_);
v___x_512_ = lean_apply_1(v_x_506_, v_r_507_);
v___x_513_ = lean_apply_2(v_inst_505_, lean_box(0), v___x_512_);
v___x_514_ = lean_apply_4(v_map_510_, lean_box(0), lean_box(0), v___f_511_, v___x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___boxed(lean_object* v_inst_515_, lean_object* v_inst_516_, lean_object* v_x_517_, lean_object* v_r_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg(v_inst_515_, v_inst_516_, v_x_517_, v_r_518_);
lean_dec(v_r_518_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__3(lean_object* v_00_u03c9_520_, lean_object* v_00_u03c3_521_, lean_object* v_m_522_, lean_object* v_inst_523_, lean_object* v_inst_524_, lean_object* v_00_u03b1_525_, lean_object* v_x_526_, lean_object* v_r_527_){
_start:
{
lean_object* v_toApplicative_528_; lean_object* v_toFunctor_529_; lean_object* v_map_530_; lean_object* v___f_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v_toApplicative_528_ = lean_ctor_get(v_inst_523_, 0);
lean_inc_ref(v_toApplicative_528_);
lean_dec_ref(v_inst_523_);
v_toFunctor_529_ = lean_ctor_get(v_toApplicative_528_, 0);
lean_inc_ref(v_toFunctor_529_);
lean_dec_ref(v_toApplicative_528_);
v_map_530_ = lean_ctor_get(v_toFunctor_529_, 0);
lean_inc(v_map_530_);
lean_dec_ref(v_toFunctor_529_);
v___f_531_ = ((lean_object*)(l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___closed__0));
lean_inc(v_r_527_);
v___x_532_ = lean_apply_1(v_x_526_, v_r_527_);
v___x_533_ = lean_apply_2(v_inst_524_, lean_box(0), v___x_532_);
v___x_534_ = lean_apply_4(v_map_530_, lean_box(0), lean_box(0), v___f_531_, v___x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__3___boxed(lean_object* v_00_u03c9_535_, lean_object* v_00_u03c3_536_, lean_object* v_m_537_, lean_object* v_inst_538_, lean_object* v_inst_539_, lean_object* v_00_u03b1_540_, lean_object* v_x_541_, lean_object* v_r_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_StateRefT_x27_instMonadAttachOfMonad___aux__3(v_00_u03c9_535_, v_00_u03c3_536_, v_m_537_, v_inst_538_, v_inst_539_, v_00_u03b1_540_, v_x_541_, v_r_542_);
lean_dec(v_r_542_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___redArg(lean_object* v_inst_544_, lean_object* v_inst_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadAttachOfMonad___aux__3___boxed), 8, 5);
lean_closure_set(v___x_546_, 0, lean_box(0));
lean_closure_set(v___x_546_, 1, lean_box(0));
lean_closure_set(v___x_546_, 2, lean_box(0));
lean_closure_set(v___x_546_, 3, v_inst_544_);
lean_closure_set(v___x_546_, 4, v_inst_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad(lean_object* v_00_u03c9_547_, lean_object* v_00_u03c3_548_, lean_object* v_m_549_, lean_object* v_inst_550_, lean_object* v_inst_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadAttachOfMonad___aux__3___boxed), 8, 5);
lean_closure_set(v___x_552_, 0, lean_box(0));
lean_closure_set(v___x_552_, 1, lean_box(0));
lean_closure_set(v___x_552_, 2, lean_box(0));
lean_closure_set(v___x_552_, 3, v_inst_550_);
lean_closure_set(v___x_552_, 4, v_inst_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_get___redArg(lean_object* v_inst_553_, lean_object* v_ref_554_){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
lean_inc(v_ref_554_);
v___x_555_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_555_, 0, lean_box(0));
lean_closure_set(v___x_555_, 1, lean_box(0));
lean_closure_set(v___x_555_, 2, v_ref_554_);
v___x_556_ = lean_apply_2(v_inst_553_, lean_box(0), v___x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_get___redArg___boxed(lean_object* v_inst_557_, lean_object* v_ref_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_StateRefT_x27_get___redArg(v_inst_557_, v_ref_558_);
lean_dec(v_ref_558_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_get(lean_object* v_00_u03c9_560_, lean_object* v_00_u03c3_561_, lean_object* v_m_562_, lean_object* v_inst_563_, lean_object* v_ref_564_){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
lean_inc(v_ref_564_);
v___x_565_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_565_, 0, lean_box(0));
lean_closure_set(v___x_565_, 1, lean_box(0));
lean_closure_set(v___x_565_, 2, v_ref_564_);
v___x_566_ = lean_apply_2(v_inst_563_, lean_box(0), v___x_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_get___boxed(lean_object* v_00_u03c9_567_, lean_object* v_00_u03c3_568_, lean_object* v_m_569_, lean_object* v_inst_570_, lean_object* v_ref_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_StateRefT_x27_get(v_00_u03c9_567_, v_00_u03c3_568_, v_m_569_, v_inst_570_, v_ref_571_);
lean_dec(v_ref_571_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_set___redArg(lean_object* v_inst_573_, lean_object* v_s_574_, lean_object* v_ref_575_){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
lean_inc(v_ref_575_);
v___x_576_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_576_, 0, lean_box(0));
lean_closure_set(v___x_576_, 1, lean_box(0));
lean_closure_set(v___x_576_, 2, v_ref_575_);
lean_closure_set(v___x_576_, 3, v_s_574_);
v___x_577_ = lean_apply_2(v_inst_573_, lean_box(0), v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_set___redArg___boxed(lean_object* v_inst_578_, lean_object* v_s_579_, lean_object* v_ref_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_StateRefT_x27_set___redArg(v_inst_578_, v_s_579_, v_ref_580_);
lean_dec(v_ref_580_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_set(lean_object* v_00_u03c9_582_, lean_object* v_00_u03c3_583_, lean_object* v_m_584_, lean_object* v_inst_585_, lean_object* v_s_586_, lean_object* v_ref_587_){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
lean_inc(v_ref_587_);
v___x_588_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_588_, 0, lean_box(0));
lean_closure_set(v___x_588_, 1, lean_box(0));
lean_closure_set(v___x_588_, 2, v_ref_587_);
lean_closure_set(v___x_588_, 3, v_s_586_);
v___x_589_ = lean_apply_2(v_inst_585_, lean_box(0), v___x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_set___boxed(lean_object* v_00_u03c9_590_, lean_object* v_00_u03c3_591_, lean_object* v_m_592_, lean_object* v_inst_593_, lean_object* v_s_594_, lean_object* v_ref_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_StateRefT_x27_set(v_00_u03c9_590_, v_00_u03c3_591_, v_m_592_, v_inst_593_, v_s_594_, v_ref_595_);
lean_dec(v_ref_595_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_modifyGet___redArg(lean_object* v_inst_597_, lean_object* v_f_598_, lean_object* v_ref_599_){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
lean_inc(v_ref_599_);
v___x_600_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_600_, 0, lean_box(0));
lean_closure_set(v___x_600_, 1, lean_box(0));
lean_closure_set(v___x_600_, 2, lean_box(0));
lean_closure_set(v___x_600_, 3, v_ref_599_);
lean_closure_set(v___x_600_, 4, v_f_598_);
v___x_601_ = lean_apply_2(v_inst_597_, lean_box(0), v___x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_modifyGet___redArg___boxed(lean_object* v_inst_602_, lean_object* v_f_603_, lean_object* v_ref_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_StateRefT_x27_modifyGet___redArg(v_inst_602_, v_f_603_, v_ref_604_);
lean_dec(v_ref_604_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_modifyGet(lean_object* v_00_u03c9_606_, lean_object* v_00_u03c3_607_, lean_object* v_m_608_, lean_object* v_00_u03b1_609_, lean_object* v_inst_610_, lean_object* v_f_611_, lean_object* v_ref_612_){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
lean_inc(v_ref_612_);
v___x_613_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_613_, 0, lean_box(0));
lean_closure_set(v___x_613_, 1, lean_box(0));
lean_closure_set(v___x_613_, 2, lean_box(0));
lean_closure_set(v___x_613_, 3, v_ref_612_);
lean_closure_set(v___x_613_, 4, v_f_611_);
v___x_614_ = lean_apply_2(v_inst_610_, lean_box(0), v___x_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_modifyGet___boxed(lean_object* v_00_u03c9_615_, lean_object* v_00_u03c3_616_, lean_object* v_m_617_, lean_object* v_00_u03b1_618_, lean_object* v_inst_619_, lean_object* v_f_620_, lean_object* v_ref_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_StateRefT_x27_modifyGet(v_00_u03c9_615_, v_00_u03c3_616_, v_m_617_, v_00_u03b1_618_, v_inst_619_, v_f_620_, v_ref_621_);
lean_dec(v_ref_621_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg___lam__0(lean_object* v_inst_623_, lean_object* v_00_u03b1_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
lean_inc(v___y_626_);
v___x_627_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_627_, 0, lean_box(0));
lean_closure_set(v___x_627_, 1, lean_box(0));
lean_closure_set(v___x_627_, 2, lean_box(0));
lean_closure_set(v___x_627_, 3, v___y_626_);
lean_closure_set(v___x_627_, 4, v___y_625_);
v___x_628_ = lean_apply_2(v_inst_623_, lean_box(0), v___x_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg___lam__0___boxed(lean_object* v_inst_629_, lean_object* v_00_u03b1_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg___lam__0(v_inst_629_, v_00_u03b1_630_, v___y_631_, v___y_632_);
lean_dec(v___y_632_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg(lean_object* v_inst_634_){
_start:
{
lean_object* v___f_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
lean_inc_n(v_inst_634_, 2);
v___f_635_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_635_, 0, v_inst_634_);
v___x_636_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_636_, 0, lean_box(0));
lean_closure_set(v___x_636_, 1, lean_box(0));
lean_closure_set(v___x_636_, 2, lean_box(0));
lean_closure_set(v___x_636_, 3, v_inst_634_);
v___x_637_ = lean_alloc_closure((void*)(l_StateRefT_x27_set___boxed), 6, 4);
lean_closure_set(v___x_637_, 0, lean_box(0));
lean_closure_set(v___x_637_, 1, lean_box(0));
lean_closure_set(v___x_637_, 2, lean_box(0));
lean_closure_set(v___x_637_, 3, v_inst_634_);
v___x_638_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_638_, 0, v___x_636_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
lean_ctor_set(v___x_638_, 2, v___f_635_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadStateOfOfMonadLiftTST(lean_object* v_00_u03c9_639_, lean_object* v_00_u03c3_640_, lean_object* v_m_641_, lean_object* v_inst_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg(v_inst_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0(lean_object* v_inst_644_, lean_object* v_00_u03b1_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v_throw_648_; lean_object* v___x_649_; 
v_throw_648_ = lean_ctor_get(v_inst_644_, 0);
lean_inc(v_throw_648_);
lean_dec_ref(v_inst_644_);
v___x_649_ = lean_apply_2(v_throw_648_, lean_box(0), v___y_646_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object* v_inst_650_, lean_object* v_00_u03b1_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_StateRefT_x27_instMonadExceptOf___redArg___lam__0(v_inst_650_, v_00_u03b1_651_, v___y_652_, v___y_653_);
lean_dec(v___y_653_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__1(lean_object* v_c_655_, lean_object* v_s_656_, lean_object* v_e_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = lean_apply_2(v_c_655_, v_e_657_, v_s_656_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object* v_inst_659_, lean_object* v_00_u03b1_660_, lean_object* v_x_661_, lean_object* v_c_662_, lean_object* v_s_663_){
_start:
{
lean_object* v_tryCatch_664_; lean_object* v___f_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v_tryCatch_664_ = lean_ctor_get(v_inst_659_, 1);
lean_inc(v_tryCatch_664_);
lean_dec_ref(v_inst_659_);
lean_inc(v_s_663_);
v___f_665_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__1), 3, 2);
lean_closure_set(v___f_665_, 0, v_c_662_);
lean_closure_set(v___f_665_, 1, v_s_663_);
v___x_666_ = lean_apply_1(v_x_661_, v_s_663_);
v___x_667_ = lean_apply_3(v_tryCatch_664_, lean_box(0), v___x_666_, v___f_665_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadExceptOf___redArg(lean_object* v_inst_668_){
_start:
{
lean_object* v___f_669_; lean_object* v___f_670_; lean_object* v___x_671_; 
lean_inc_ref(v_inst_668_);
v___f_669_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_669_, 0, v_inst_668_);
v___f_670_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_670_, 0, v_inst_668_);
v___x_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_671_, 0, v___f_669_);
lean_ctor_set(v___x_671_, 1, v___f_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadExceptOf(lean_object* v_00_u03c9_672_, lean_object* v_00_u03c3_673_, lean_object* v_m_674_, lean_object* v_00_u03b5_675_, lean_object* v_inst_676_){
_start:
{
lean_object* v___f_677_; lean_object* v___f_678_; lean_object* v___x_679_; 
lean_inc_ref(v_inst_676_);
v___f_677_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_677_, 0, v_inst_676_);
v___f_678_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_678_, 0, v_inst_676_);
v___x_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_679_, 0, v___f_677_);
lean_ctor_set(v___x_679_, 1, v___f_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0(lean_object* v_ctx_680_, lean_object* v_00_u03b2_681_, lean_object* v_x_682_){
_start:
{
lean_object* v___x_683_; 
lean_inc(v_ctx_680_);
v___x_683_ = lean_apply_1(v_x_682_, v_ctx_680_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0___boxed(lean_object* v_ctx_684_, lean_object* v_00_u03b2_685_, lean_object* v_x_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0(v_ctx_684_, v_00_u03b2_685_, v_x_686_);
lean_dec(v_ctx_684_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__1___redArg(lean_object* v_f_688_, lean_object* v_ctx_689_){
_start:
{
lean_object* v___f_690_; lean_object* v___x_691_; 
lean_inc(v_ctx_689_);
v___f_690_ = lean_alloc_closure((void*)(l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_690_, 0, v_ctx_689_);
v___x_691_ = lean_apply_1(v_f_688_, v___f_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__1___redArg___boxed(lean_object* v_f_692_, lean_object* v_ctx_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_instMonadControlStateRefT_x27___aux__1___redArg(v_f_692_, v_ctx_693_);
lean_dec(v_ctx_693_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__1(lean_object* v_00_u03c9_695_, lean_object* v_00_u03c3_696_, lean_object* v_m_697_, lean_object* v_00_u03b1_698_, lean_object* v_f_699_, lean_object* v_ctx_700_){
_start:
{
lean_object* v___f_701_; lean_object* v___x_702_; 
lean_inc(v_ctx_700_);
v___f_701_ = lean_alloc_closure((void*)(l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_701_, 0, v_ctx_700_);
v___x_702_ = lean_apply_1(v_f_699_, v___f_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__1___boxed(lean_object* v_00_u03c9_703_, lean_object* v_00_u03c3_704_, lean_object* v_m_705_, lean_object* v_00_u03b1_706_, lean_object* v_f_707_, lean_object* v_ctx_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_instMonadControlStateRefT_x27___aux__1(v_00_u03c9_703_, v_00_u03c3_704_, v_m_705_, v_00_u03b1_706_, v_f_707_, v_ctx_708_);
lean_dec(v_ctx_708_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__3___redArg(lean_object* v_x_710_){
_start:
{
lean_inc(v_x_710_);
return v_x_710_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__3___redArg___boxed(lean_object* v_x_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_instMonadControlStateRefT_x27___aux__3___redArg(v_x_711_);
lean_dec(v_x_711_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__3(lean_object* v_00_u03c9_713_, lean_object* v_00_u03c3_714_, lean_object* v_m_715_, lean_object* v_00_u03b1_716_, lean_object* v_x_717_, lean_object* v_x_718_){
_start:
{
lean_inc(v_x_717_);
return v_x_717_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__3___boxed(lean_object* v_00_u03c9_719_, lean_object* v_00_u03c3_720_, lean_object* v_m_721_, lean_object* v_00_u03b1_722_, lean_object* v_x_723_, lean_object* v_x_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_instMonadControlStateRefT_x27___aux__3(v_00_u03c9_719_, v_00_u03c3_720_, v_m_721_, v_00_u03b1_722_, v_x_723_, v_x_724_);
lean_dec(v_x_724_);
lean_dec(v_x_723_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27(lean_object* v_00_u03c9_731_, lean_object* v_00_u03c3_732_, lean_object* v_m_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = ((lean_object*)(l_instMonadControlStateRefT_x27___closed__2));
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0(lean_object* v_h_735_, lean_object* v_ctx_736_, lean_object* v_a_x3f_737_){
_start:
{
lean_object* v___x_738_; 
lean_inc(v_ctx_736_);
v___x_738_ = lean_apply_2(v_h_735_, v_a_x3f_737_, v_ctx_736_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0___boxed(lean_object* v_h_739_, lean_object* v_ctx_740_, lean_object* v_a_x3f_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0(v_h_739_, v_ctx_740_, v_a_x3f_741_);
lean_dec(v_ctx_740_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___aux__1___redArg(lean_object* v_inst_743_, lean_object* v_x_744_, lean_object* v_h_745_, lean_object* v_ctx_746_){
_start:
{
lean_object* v___f_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
lean_inc_n(v_ctx_746_, 2);
v___f_747_ = lean_alloc_closure((void*)(l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_747_, 0, v_h_745_);
lean_closure_set(v___f_747_, 1, v_ctx_746_);
v___x_748_ = lean_apply_1(v_x_744_, v_ctx_746_);
v___x_749_ = lean_apply_4(v_inst_743_, lean_box(0), lean_box(0), v___x_748_, v___f_747_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___aux__1___redArg___boxed(lean_object* v_inst_750_, lean_object* v_x_751_, lean_object* v_h_752_, lean_object* v_ctx_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_instMonadFinallyStateRefT_x27___aux__1___redArg(v_inst_750_, v_x_751_, v_h_752_, v_ctx_753_);
lean_dec(v_ctx_753_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___aux__1(lean_object* v_m_755_, lean_object* v_00_u03c9_756_, lean_object* v_00_u03c3_757_, lean_object* v_inst_758_, lean_object* v_00_u03b1_759_, lean_object* v_00_u03b2_760_, lean_object* v_x_761_, lean_object* v_h_762_, lean_object* v_ctx_763_){
_start:
{
lean_object* v___f_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
lean_inc_n(v_ctx_763_, 2);
v___f_764_ = lean_alloc_closure((void*)(l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_764_, 0, v_h_762_);
lean_closure_set(v___f_764_, 1, v_ctx_763_);
v___x_765_ = lean_apply_1(v_x_761_, v_ctx_763_);
v___x_766_ = lean_apply_4(v_inst_758_, lean_box(0), lean_box(0), v___x_765_, v___f_764_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___aux__1___boxed(lean_object* v_m_767_, lean_object* v_00_u03c9_768_, lean_object* v_00_u03c3_769_, lean_object* v_inst_770_, lean_object* v_00_u03b1_771_, lean_object* v_00_u03b2_772_, lean_object* v_x_773_, lean_object* v_h_774_, lean_object* v_ctx_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_instMonadFinallyStateRefT_x27___aux__1(v_m_767_, v_00_u03c9_768_, v_00_u03c3_769_, v_inst_770_, v_00_u03b1_771_, v_00_u03b2_772_, v_x_773_, v_h_774_, v_ctx_775_);
lean_dec(v_ctx_775_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___redArg(lean_object* v_inst_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = lean_alloc_closure((void*)(l_instMonadFinallyStateRefT_x27___aux__1___boxed), 9, 4);
lean_closure_set(v___x_778_, 0, lean_box(0));
lean_closure_set(v___x_778_, 1, lean_box(0));
lean_closure_set(v___x_778_, 2, lean_box(0));
lean_closure_set(v___x_778_, 3, v_inst_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27(lean_object* v_m_779_, lean_object* v_00_u03c9_780_, lean_object* v_00_u03c3_781_, lean_object* v_inst_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = lean_alloc_closure((void*)(l_instMonadFinallyStateRefT_x27___aux__1___boxed), 9, 4);
lean_closure_set(v___x_783_, 0, lean_box(0));
lean_closure_set(v___x_783_, 1, lean_box(0));
lean_closure_set(v___x_783_, 2, lean_box(0));
lean_closure_set(v___x_783_, 3, v_inst_782_);
return v___x_783_;
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

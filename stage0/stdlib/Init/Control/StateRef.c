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
static const lean_closure_object l_StateRefT_x27_instMonadLift___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_StateRefT_x27_instMonadLift___redArg___closed__0 = (const lean_object*)&l_StateRefT_x27_instMonadLift___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadLift___redArg();
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadLift___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadLift(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_StateRefT_x27_instMonadFunctor___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_StateRefT_x27_instMonadFunctor___redArg___closed__0 = (const lean_object*)&l_StateRefT_x27_instMonadFunctor___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor___redArg();
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor___redArg___boxed(lean_object*);
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
static const lean_closure_object l_instMonadControlStateRefT_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadControlStateRefT_x27___aux__1___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadControlStateRefT_x27___redArg___closed__0 = (const lean_object*)&l_instMonadControlStateRefT_x27___redArg___closed__0_value;
static const lean_closure_object l_instMonadControlStateRefT_x27___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadControlStateRefT_x27___aux__3___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadControlStateRefT_x27___redArg___closed__1 = (const lean_object*)&l_instMonadControlStateRefT_x27___redArg___closed__1_value;
static const lean_ctor_object l_instMonadControlStateRefT_x27___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_instMonadControlStateRefT_x27___redArg___closed__0_value),((lean_object*)&l_instMonadControlStateRefT_x27___redArg___closed__1_value)}};
static const lean_object* l_instMonadControlStateRefT_x27___redArg___closed__2 = (const lean_object*)&l_instMonadControlStateRefT_x27___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___redArg();
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___redArg___boxed(lean_object*);
static lean_once_cell_t l_instMonadControlStateRefT_x27___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instMonadControlStateRefT_x27___closed__0;
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
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadLift___redArg(){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = ((lean_object*)(l_StateRefT_x27_instMonadLift___redArg___closed__0));
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadLift___redArg___boxed(lean_object* v___dummy_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_StateRefT_x27_instMonadLift___redArg();
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadLift(lean_object* v_00_u03c9_328_, lean_object* v_00_u03c3_329_, lean_object* v_m_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = ((lean_object*)(l_StateRefT_x27_instMonadLift___redArg___closed__0));
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___redArg(lean_object* v_f_332_, lean_object* v_x_333_, lean_object* v_ctx_334_){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
lean_inc(v_ctx_334_);
v___x_335_ = lean_apply_1(v_x_333_, v_ctx_334_);
v___x_336_ = lean_apply_2(v_f_332_, lean_box(0), v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___redArg___boxed(lean_object* v_f_337_, lean_object* v_x_338_, lean_object* v_ctx_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_StateRefT_x27_instMonadFunctor___aux__1___redArg(v_f_337_, v_x_338_, v_ctx_339_);
lean_dec(v_ctx_339_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor___aux__1(lean_object* v_00_u03c9_341_, lean_object* v_00_u03c3_342_, lean_object* v_m_343_, lean_object* v_00_u03b1_344_, lean_object* v_f_345_, lean_object* v_x_346_, lean_object* v_ctx_347_){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
lean_inc(v_ctx_347_);
v___x_348_ = lean_apply_1(v_x_346_, v_ctx_347_);
v___x_349_ = lean_apply_2(v_f_345_, lean_box(0), v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object* v_00_u03c9_350_, lean_object* v_00_u03c3_351_, lean_object* v_m_352_, lean_object* v_00_u03b1_353_, lean_object* v_f_354_, lean_object* v_x_355_, lean_object* v_ctx_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_StateRefT_x27_instMonadFunctor___aux__1(v_00_u03c9_350_, v_00_u03c3_351_, v_m_352_, v_00_u03b1_353_, v_f_354_, v_x_355_, v_ctx_356_);
lean_dec(v_ctx_356_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor___redArg(){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = ((lean_object*)(l_StateRefT_x27_instMonadFunctor___redArg___closed__0));
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor___redArg___boxed(lean_object* v___dummy_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_StateRefT_x27_instMonadFunctor___redArg();
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor(lean_object* v_00_u03c9_363_, lean_object* v_00_u03c3_364_, lean_object* v_m_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = ((lean_object*)(l_StateRefT_x27_instMonadFunctor___redArg___closed__0));
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__0(lean_object* v_inst_367_, lean_object* v_00_u03b1_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_failure_370_; lean_object* v___x_371_; 
v_failure_370_ = lean_ctor_get(v_inst_367_, 1);
lean_inc(v_failure_370_);
lean_dec_ref(v_inst_367_);
v___x_371_ = lean_apply_1(v_failure_370_, lean_box(0));
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__0___boxed(lean_object* v_inst_372_, lean_object* v_00_u03b1_373_, lean_object* v___y_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__0(v_inst_372_, v_00_u03b1_373_, v___y_374_);
lean_dec(v___y_374_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__1(lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v_x_378_){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = lean_box(0);
lean_inc(v___y_377_);
v___x_380_ = lean_apply_2(v___y_376_, v___x_379_, v___y_377_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__1___boxed(lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v_x_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__1(v___y_381_, v___y_382_, v_x_383_);
lean_dec(v___y_382_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__2(lean_object* v_inst_385_, lean_object* v_00_u03b1_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_orElse_390_; lean_object* v___f_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v_orElse_390_ = lean_ctor_get(v_inst_385_, 2);
lean_inc(v_orElse_390_);
lean_dec_ref(v_inst_385_);
lean_inc_n(v___y_389_, 2);
v___f_391_ = lean_alloc_closure((void*)(l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_391_, 0, v___y_388_);
lean_closure_set(v___f_391_, 1, v___y_389_);
v___x_392_ = lean_apply_1(v___y_387_, v___y_389_);
v___x_393_ = lean_apply_3(v_orElse_390_, lean_box(0), v___x_392_, v___f_391_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__2___boxed(lean_object* v_inst_394_, lean_object* v_00_u03b1_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__2(v_inst_394_, v_00_u03b1_395_, v___y_396_, v___y_397_, v___y_398_);
lean_dec(v___y_398_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg(lean_object* v_inst_400_, lean_object* v_inst_401_){
_start:
{
lean_object* v___x_402_; lean_object* v_toApplicative_403_; lean_object* v___f_404_; lean_object* v___f_405_; lean_object* v___x_406_; 
v___x_402_ = l_StateRefT_x27_instMonad___redArg(v_inst_401_);
v_toApplicative_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc_ref(v_toApplicative_403_);
lean_dec_ref(v___x_402_);
lean_inc_ref(v_inst_400_);
v___f_404_ = lean_alloc_closure((void*)(l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_404_, 0, v_inst_400_);
v___f_405_ = lean_alloc_closure((void*)(l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__2___boxed), 5, 1);
lean_closure_set(v___f_405_, 0, v_inst_400_);
v___x_406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_406_, 0, v_toApplicative_403_);
lean_ctor_set(v___x_406_, 1, v___f_404_);
lean_ctor_set(v___x_406_, 2, v___f_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad(lean_object* v_00_u03c9_407_, lean_object* v_00_u03c3_408_, lean_object* v_m_409_, lean_object* v_inst_410_, lean_object* v_inst_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_StateRefT_x27_instAlternativeOfMonad___redArg(v_inst_410_, v_inst_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg___lam__0(lean_object* v_x_413_){
_start:
{
lean_inc(v_x_413_);
return v_x_413_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg___lam__0___boxed(lean_object* v_x_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg___lam__0(v_x_414_);
lean_dec(v_x_414_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg(lean_object* v_inst_417_, lean_object* v_inst_418_, lean_object* v_x_419_, lean_object* v_r_420_){
_start:
{
lean_object* v_toApplicative_421_; lean_object* v_toFunctor_422_; lean_object* v_map_423_; lean_object* v___f_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v_toApplicative_421_ = lean_ctor_get(v_inst_417_, 0);
lean_inc_ref(v_toApplicative_421_);
lean_dec_ref(v_inst_417_);
v_toFunctor_422_ = lean_ctor_get(v_toApplicative_421_, 0);
lean_inc_ref(v_toFunctor_422_);
lean_dec_ref(v_toApplicative_421_);
v_map_423_ = lean_ctor_get(v_toFunctor_422_, 0);
lean_inc(v_map_423_);
lean_dec_ref(v_toFunctor_422_);
v___f_424_ = ((lean_object*)(l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg___closed__0));
lean_inc(v_r_420_);
v___x_425_ = lean_apply_1(v_x_419_, v_r_420_);
v___x_426_ = lean_apply_2(v_inst_418_, lean_box(0), v___x_425_);
v___x_427_ = lean_apply_4(v_map_423_, lean_box(0), lean_box(0), v___f_424_, v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg___boxed(lean_object* v_inst_428_, lean_object* v_inst_429_, lean_object* v_x_430_, lean_object* v_r_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg(v_inst_428_, v_inst_429_, v_x_430_, v_r_431_);
lean_dec(v_r_431_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__1(lean_object* v_00_u03c9_433_, lean_object* v_00_u03c3_434_, lean_object* v_m_435_, lean_object* v_inst_436_, lean_object* v_inst_437_, lean_object* v_00_u03b1_438_, lean_object* v_x_439_, lean_object* v_r_440_){
_start:
{
lean_object* v_toApplicative_441_; lean_object* v_toFunctor_442_; lean_object* v_map_443_; lean_object* v___f_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v_toApplicative_441_ = lean_ctor_get(v_inst_436_, 0);
lean_inc_ref(v_toApplicative_441_);
lean_dec_ref(v_inst_436_);
v_toFunctor_442_ = lean_ctor_get(v_toApplicative_441_, 0);
lean_inc_ref(v_toFunctor_442_);
lean_dec_ref(v_toApplicative_441_);
v_map_443_ = lean_ctor_get(v_toFunctor_442_, 0);
lean_inc(v_map_443_);
lean_dec_ref(v_toFunctor_442_);
v___f_444_ = ((lean_object*)(l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg___closed__0));
lean_inc(v_r_440_);
v___x_445_ = lean_apply_1(v_x_439_, v_r_440_);
v___x_446_ = lean_apply_2(v_inst_437_, lean_box(0), v___x_445_);
v___x_447_ = lean_apply_4(v_map_443_, lean_box(0), lean_box(0), v___f_444_, v___x_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__1___boxed(lean_object* v_00_u03c9_448_, lean_object* v_00_u03c3_449_, lean_object* v_m_450_, lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_00_u03b1_453_, lean_object* v_x_454_, lean_object* v_r_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_StateRefT_x27_instMonadAttachOfMonad___aux__1(v_00_u03c9_448_, v_00_u03c3_449_, v_m_450_, v_inst_451_, v_inst_452_, v_00_u03b1_453_, v_x_454_, v_r_455_);
lean_dec(v_r_455_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___redArg(lean_object* v_inst_457_, lean_object* v_inst_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadAttachOfMonad___aux__1___boxed), 8, 5);
lean_closure_set(v___x_459_, 0, lean_box(0));
lean_closure_set(v___x_459_, 1, lean_box(0));
lean_closure_set(v___x_459_, 2, lean_box(0));
lean_closure_set(v___x_459_, 3, v_inst_457_);
lean_closure_set(v___x_459_, 4, v_inst_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad(lean_object* v_00_u03c9_460_, lean_object* v_00_u03c3_461_, lean_object* v_m_462_, lean_object* v_inst_463_, lean_object* v_inst_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadAttachOfMonad___aux__1___boxed), 8, 5);
lean_closure_set(v___x_465_, 0, lean_box(0));
lean_closure_set(v___x_465_, 1, lean_box(0));
lean_closure_set(v___x_465_, 2, lean_box(0));
lean_closure_set(v___x_465_, 3, v_inst_463_);
lean_closure_set(v___x_465_, 4, v_inst_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_get___redArg(lean_object* v_inst_466_, lean_object* v_ref_467_){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
lean_inc(v_ref_467_);
v___x_468_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_468_, 0, lean_box(0));
lean_closure_set(v___x_468_, 1, lean_box(0));
lean_closure_set(v___x_468_, 2, v_ref_467_);
v___x_469_ = lean_apply_2(v_inst_466_, lean_box(0), v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_get___redArg___boxed(lean_object* v_inst_470_, lean_object* v_ref_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_StateRefT_x27_get___redArg(v_inst_470_, v_ref_471_);
lean_dec(v_ref_471_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_get(lean_object* v_00_u03c9_473_, lean_object* v_00_u03c3_474_, lean_object* v_m_475_, lean_object* v_inst_476_, lean_object* v_ref_477_){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
lean_inc(v_ref_477_);
v___x_478_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_478_, 0, lean_box(0));
lean_closure_set(v___x_478_, 1, lean_box(0));
lean_closure_set(v___x_478_, 2, v_ref_477_);
v___x_479_ = lean_apply_2(v_inst_476_, lean_box(0), v___x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_get___boxed(lean_object* v_00_u03c9_480_, lean_object* v_00_u03c3_481_, lean_object* v_m_482_, lean_object* v_inst_483_, lean_object* v_ref_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_StateRefT_x27_get(v_00_u03c9_480_, v_00_u03c3_481_, v_m_482_, v_inst_483_, v_ref_484_);
lean_dec(v_ref_484_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_set___redArg(lean_object* v_inst_486_, lean_object* v_s_487_, lean_object* v_ref_488_){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
lean_inc(v_ref_488_);
v___x_489_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_489_, 0, lean_box(0));
lean_closure_set(v___x_489_, 1, lean_box(0));
lean_closure_set(v___x_489_, 2, v_ref_488_);
lean_closure_set(v___x_489_, 3, v_s_487_);
v___x_490_ = lean_apply_2(v_inst_486_, lean_box(0), v___x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_set___redArg___boxed(lean_object* v_inst_491_, lean_object* v_s_492_, lean_object* v_ref_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_StateRefT_x27_set___redArg(v_inst_491_, v_s_492_, v_ref_493_);
lean_dec(v_ref_493_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_set(lean_object* v_00_u03c9_495_, lean_object* v_00_u03c3_496_, lean_object* v_m_497_, lean_object* v_inst_498_, lean_object* v_s_499_, lean_object* v_ref_500_){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
lean_inc(v_ref_500_);
v___x_501_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_501_, 0, lean_box(0));
lean_closure_set(v___x_501_, 1, lean_box(0));
lean_closure_set(v___x_501_, 2, v_ref_500_);
lean_closure_set(v___x_501_, 3, v_s_499_);
v___x_502_ = lean_apply_2(v_inst_498_, lean_box(0), v___x_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_set___boxed(lean_object* v_00_u03c9_503_, lean_object* v_00_u03c3_504_, lean_object* v_m_505_, lean_object* v_inst_506_, lean_object* v_s_507_, lean_object* v_ref_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_StateRefT_x27_set(v_00_u03c9_503_, v_00_u03c3_504_, v_m_505_, v_inst_506_, v_s_507_, v_ref_508_);
lean_dec(v_ref_508_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_modifyGet___redArg(lean_object* v_inst_510_, lean_object* v_f_511_, lean_object* v_ref_512_){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
lean_inc(v_ref_512_);
v___x_513_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_513_, 0, lean_box(0));
lean_closure_set(v___x_513_, 1, lean_box(0));
lean_closure_set(v___x_513_, 2, lean_box(0));
lean_closure_set(v___x_513_, 3, v_ref_512_);
lean_closure_set(v___x_513_, 4, v_f_511_);
v___x_514_ = lean_apply_2(v_inst_510_, lean_box(0), v___x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_modifyGet___redArg___boxed(lean_object* v_inst_515_, lean_object* v_f_516_, lean_object* v_ref_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_StateRefT_x27_modifyGet___redArg(v_inst_515_, v_f_516_, v_ref_517_);
lean_dec(v_ref_517_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_modifyGet(lean_object* v_00_u03c9_519_, lean_object* v_00_u03c3_520_, lean_object* v_m_521_, lean_object* v_00_u03b1_522_, lean_object* v_inst_523_, lean_object* v_f_524_, lean_object* v_ref_525_){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
lean_inc(v_ref_525_);
v___x_526_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_526_, 0, lean_box(0));
lean_closure_set(v___x_526_, 1, lean_box(0));
lean_closure_set(v___x_526_, 2, lean_box(0));
lean_closure_set(v___x_526_, 3, v_ref_525_);
lean_closure_set(v___x_526_, 4, v_f_524_);
v___x_527_ = lean_apply_2(v_inst_523_, lean_box(0), v___x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_modifyGet___boxed(lean_object* v_00_u03c9_528_, lean_object* v_00_u03c3_529_, lean_object* v_m_530_, lean_object* v_00_u03b1_531_, lean_object* v_inst_532_, lean_object* v_f_533_, lean_object* v_ref_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_StateRefT_x27_modifyGet(v_00_u03c9_528_, v_00_u03c3_529_, v_m_530_, v_00_u03b1_531_, v_inst_532_, v_f_533_, v_ref_534_);
lean_dec(v_ref_534_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg___lam__0(lean_object* v_inst_536_, lean_object* v_00_u03b1_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
lean_inc(v___y_539_);
v___x_540_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_540_, 0, lean_box(0));
lean_closure_set(v___x_540_, 1, lean_box(0));
lean_closure_set(v___x_540_, 2, lean_box(0));
lean_closure_set(v___x_540_, 3, v___y_539_);
lean_closure_set(v___x_540_, 4, v___y_538_);
v___x_541_ = lean_apply_2(v_inst_536_, lean_box(0), v___x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg___lam__0___boxed(lean_object* v_inst_542_, lean_object* v_00_u03b1_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg___lam__0(v_inst_542_, v_00_u03b1_543_, v___y_544_, v___y_545_);
lean_dec(v___y_545_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg(lean_object* v_inst_547_){
_start:
{
lean_object* v___f_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
lean_inc_n(v_inst_547_, 2);
v___f_548_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_548_, 0, v_inst_547_);
v___x_549_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_549_, 0, lean_box(0));
lean_closure_set(v___x_549_, 1, lean_box(0));
lean_closure_set(v___x_549_, 2, lean_box(0));
lean_closure_set(v___x_549_, 3, v_inst_547_);
v___x_550_ = lean_alloc_closure((void*)(l_StateRefT_x27_set___boxed), 6, 4);
lean_closure_set(v___x_550_, 0, lean_box(0));
lean_closure_set(v___x_550_, 1, lean_box(0));
lean_closure_set(v___x_550_, 2, lean_box(0));
lean_closure_set(v___x_550_, 3, v_inst_547_);
v___x_551_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_551_, 0, v___x_549_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
lean_ctor_set(v___x_551_, 2, v___f_548_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadStateOfOfMonadLiftTST(lean_object* v_00_u03c9_552_, lean_object* v_00_u03c3_553_, lean_object* v_m_554_, lean_object* v_inst_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg(v_inst_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0(lean_object* v_inst_557_, lean_object* v_00_u03b1_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v_throw_561_; lean_object* v___x_562_; 
v_throw_561_ = lean_ctor_get(v_inst_557_, 0);
lean_inc(v_throw_561_);
lean_dec_ref(v_inst_557_);
v___x_562_ = lean_apply_2(v_throw_561_, lean_box(0), v___y_559_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object* v_inst_563_, lean_object* v_00_u03b1_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_StateRefT_x27_instMonadExceptOf___redArg___lam__0(v_inst_563_, v_00_u03b1_564_, v___y_565_, v___y_566_);
lean_dec(v___y_566_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__1(lean_object* v_c_568_, lean_object* v_s_569_, lean_object* v_e_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = lean_apply_2(v_c_568_, v_e_570_, v_s_569_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object* v_inst_572_, lean_object* v_00_u03b1_573_, lean_object* v_x_574_, lean_object* v_c_575_, lean_object* v_s_576_){
_start:
{
lean_object* v_tryCatch_577_; lean_object* v___f_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v_tryCatch_577_ = lean_ctor_get(v_inst_572_, 1);
lean_inc(v_tryCatch_577_);
lean_dec_ref(v_inst_572_);
lean_inc(v_s_576_);
v___f_578_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__1), 3, 2);
lean_closure_set(v___f_578_, 0, v_c_575_);
lean_closure_set(v___f_578_, 1, v_s_576_);
v___x_579_ = lean_apply_1(v_x_574_, v_s_576_);
v___x_580_ = lean_apply_3(v_tryCatch_577_, lean_box(0), v___x_579_, v___f_578_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadExceptOf___redArg(lean_object* v_inst_581_){
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
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadExceptOf(lean_object* v_00_u03c9_585_, lean_object* v_00_u03c3_586_, lean_object* v_m_587_, lean_object* v_00_u03b5_588_, lean_object* v_inst_589_){
_start:
{
lean_object* v___f_590_; lean_object* v___f_591_; lean_object* v___x_592_; 
lean_inc_ref(v_inst_589_);
v___f_590_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_590_, 0, v_inst_589_);
v___f_591_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_591_, 0, v_inst_589_);
v___x_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_592_, 0, v___f_590_);
lean_ctor_set(v___x_592_, 1, v___f_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0(lean_object* v_ctx_593_, lean_object* v_00_u03b2_594_, lean_object* v_x_595_){
_start:
{
lean_object* v___x_596_; 
lean_inc(v_ctx_593_);
v___x_596_ = lean_apply_1(v_x_595_, v_ctx_593_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0___boxed(lean_object* v_ctx_597_, lean_object* v_00_u03b2_598_, lean_object* v_x_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0(v_ctx_597_, v_00_u03b2_598_, v_x_599_);
lean_dec(v_ctx_597_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__1___redArg(lean_object* v_f_601_, lean_object* v_ctx_602_){
_start:
{
lean_object* v___f_603_; lean_object* v___x_604_; 
lean_inc(v_ctx_602_);
v___f_603_ = lean_alloc_closure((void*)(l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_603_, 0, v_ctx_602_);
v___x_604_ = lean_apply_1(v_f_601_, v___f_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__1___redArg___boxed(lean_object* v_f_605_, lean_object* v_ctx_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_instMonadControlStateRefT_x27___aux__1___redArg(v_f_605_, v_ctx_606_);
lean_dec(v_ctx_606_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__1(lean_object* v_00_u03c9_608_, lean_object* v_00_u03c3_609_, lean_object* v_m_610_, lean_object* v_00_u03b1_611_, lean_object* v_f_612_, lean_object* v_ctx_613_){
_start:
{
lean_object* v___f_614_; lean_object* v___x_615_; 
lean_inc(v_ctx_613_);
v___f_614_ = lean_alloc_closure((void*)(l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_614_, 0, v_ctx_613_);
v___x_615_ = lean_apply_1(v_f_612_, v___f_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__1___boxed(lean_object* v_00_u03c9_616_, lean_object* v_00_u03c3_617_, lean_object* v_m_618_, lean_object* v_00_u03b1_619_, lean_object* v_f_620_, lean_object* v_ctx_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_instMonadControlStateRefT_x27___aux__1(v_00_u03c9_616_, v_00_u03c3_617_, v_m_618_, v_00_u03b1_619_, v_f_620_, v_ctx_621_);
lean_dec(v_ctx_621_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__3___redArg(lean_object* v_x_623_){
_start:
{
lean_inc(v_x_623_);
return v_x_623_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__3___redArg___boxed(lean_object* v_x_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_instMonadControlStateRefT_x27___aux__3___redArg(v_x_624_);
lean_dec(v_x_624_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__3(lean_object* v_00_u03c9_626_, lean_object* v_00_u03c3_627_, lean_object* v_m_628_, lean_object* v_00_u03b1_629_, lean_object* v_x_630_, lean_object* v_x_631_){
_start:
{
lean_inc(v_x_630_);
return v_x_630_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__3___boxed(lean_object* v_00_u03c9_632_, lean_object* v_00_u03c3_633_, lean_object* v_m_634_, lean_object* v_00_u03b1_635_, lean_object* v_x_636_, lean_object* v_x_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_instMonadControlStateRefT_x27___aux__3(v_00_u03c9_632_, v_00_u03c3_633_, v_m_634_, v_00_u03b1_635_, v_x_636_, v_x_637_);
lean_dec(v_x_637_);
lean_dec(v_x_636_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___redArg(){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = ((lean_object*)(l_instMonadControlStateRefT_x27___redArg___closed__2));
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___redArg___boxed(lean_object* v___dummy_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_instMonadControlStateRefT_x27___redArg();
return v_res_647_;
}
}
static lean_object* _init_l_instMonadControlStateRefT_x27___closed__0(void){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_instMonadControlStateRefT_x27___redArg();
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27(lean_object* v_00_u03c9_649_, lean_object* v_00_u03c3_650_, lean_object* v_m_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = lean_obj_once(&l_instMonadControlStateRefT_x27___closed__0, &l_instMonadControlStateRefT_x27___closed__0_once, _init_l_instMonadControlStateRefT_x27___closed__0);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0(lean_object* v_h_653_, lean_object* v_ctx_654_, lean_object* v_a_x3f_655_){
_start:
{
lean_object* v___x_656_; 
lean_inc(v_ctx_654_);
v___x_656_ = lean_apply_2(v_h_653_, v_a_x3f_655_, v_ctx_654_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0___boxed(lean_object* v_h_657_, lean_object* v_ctx_658_, lean_object* v_a_x3f_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0(v_h_657_, v_ctx_658_, v_a_x3f_659_);
lean_dec(v_ctx_658_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___aux__1___redArg(lean_object* v_inst_661_, lean_object* v_x_662_, lean_object* v_h_663_, lean_object* v_ctx_664_){
_start:
{
lean_object* v___f_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
lean_inc_n(v_ctx_664_, 2);
v___f_665_ = lean_alloc_closure((void*)(l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_665_, 0, v_h_663_);
lean_closure_set(v___f_665_, 1, v_ctx_664_);
v___x_666_ = lean_apply_1(v_x_662_, v_ctx_664_);
v___x_667_ = lean_apply_4(v_inst_661_, lean_box(0), lean_box(0), v___x_666_, v___f_665_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___aux__1___redArg___boxed(lean_object* v_inst_668_, lean_object* v_x_669_, lean_object* v_h_670_, lean_object* v_ctx_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_instMonadFinallyStateRefT_x27___aux__1___redArg(v_inst_668_, v_x_669_, v_h_670_, v_ctx_671_);
lean_dec(v_ctx_671_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___aux__1(lean_object* v_m_673_, lean_object* v_00_u03c9_674_, lean_object* v_00_u03c3_675_, lean_object* v_inst_676_, lean_object* v_00_u03b1_677_, lean_object* v_00_u03b2_678_, lean_object* v_x_679_, lean_object* v_h_680_, lean_object* v_ctx_681_){
_start:
{
lean_object* v___f_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
lean_inc_n(v_ctx_681_, 2);
v___f_682_ = lean_alloc_closure((void*)(l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_682_, 0, v_h_680_);
lean_closure_set(v___f_682_, 1, v_ctx_681_);
v___x_683_ = lean_apply_1(v_x_679_, v_ctx_681_);
v___x_684_ = lean_apply_4(v_inst_676_, lean_box(0), lean_box(0), v___x_683_, v___f_682_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___aux__1___boxed(lean_object* v_m_685_, lean_object* v_00_u03c9_686_, lean_object* v_00_u03c3_687_, lean_object* v_inst_688_, lean_object* v_00_u03b1_689_, lean_object* v_00_u03b2_690_, lean_object* v_x_691_, lean_object* v_h_692_, lean_object* v_ctx_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_instMonadFinallyStateRefT_x27___aux__1(v_m_685_, v_00_u03c9_686_, v_00_u03c3_687_, v_inst_688_, v_00_u03b1_689_, v_00_u03b2_690_, v_x_691_, v_h_692_, v_ctx_693_);
lean_dec(v_ctx_693_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___redArg(lean_object* v_inst_695_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = lean_alloc_closure((void*)(l_instMonadFinallyStateRefT_x27___aux__1___boxed), 9, 4);
lean_closure_set(v___x_696_, 0, lean_box(0));
lean_closure_set(v___x_696_, 1, lean_box(0));
lean_closure_set(v___x_696_, 2, lean_box(0));
lean_closure_set(v___x_696_, 3, v_inst_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27(lean_object* v_m_697_, lean_object* v_00_u03c9_698_, lean_object* v_00_u03c3_699_, lean_object* v_inst_700_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = lean_alloc_closure((void*)(l_instMonadFinallyStateRefT_x27___aux__1___boxed), 9, 4);
lean_closure_set(v___x_701_, 0, lean_box(0));
lean_closure_set(v___x_701_, 1, lean_box(0));
lean_closure_set(v___x_701_, 2, lean_box(0));
lean_closure_set(v___x_701_, 3, v_inst_700_);
return v___x_701_;
}
}
lean_object* runtime_initialize_Init_System_ST(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Reader(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Control_StateRef(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

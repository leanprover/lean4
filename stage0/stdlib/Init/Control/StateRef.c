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
lean_object* l_StateRefT_x27_instMonadLift___redArg(){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = ((lean_object*)(l_StateRefT_x27_instMonadLift___redArg___closed__0));
return v___x_325_;
}
}
LEAN_EXPORT void l_StateRefT_x27_instMonadLift___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_326_;
v_res_326_ = l_StateRefT_x27_instMonadLift___redArg();
stack->m_obj
 = v_res_326_;
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadLift___redArg___boxed(lean_object* v___dummy_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_StateRefT_x27_instMonadLift___redArg();
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadLift(lean_object* v_00_u03c9_329_, lean_object* v_00_u03c3_330_, lean_object* v_m_331_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = ((lean_object*)(l_StateRefT_x27_instMonadLift___redArg___closed__0));
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___redArg(lean_object* v_f_333_, lean_object* v_x_334_, lean_object* v_ctx_335_){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
lean_inc(v_ctx_335_);
v___x_336_ = lean_apply_1(v_x_334_, v_ctx_335_);
v___x_337_ = lean_apply_2(v_f_333_, lean_box(0), v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___redArg___boxed(lean_object* v_f_338_, lean_object* v_x_339_, lean_object* v_ctx_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_StateRefT_x27_instMonadFunctor___aux__1___redArg(v_f_338_, v_x_339_, v_ctx_340_);
lean_dec(v_ctx_340_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor___aux__1(lean_object* v_00_u03c9_342_, lean_object* v_00_u03c3_343_, lean_object* v_m_344_, lean_object* v_00_u03b1_345_, lean_object* v_f_346_, lean_object* v_x_347_, lean_object* v_ctx_348_){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
lean_inc(v_ctx_348_);
v___x_349_ = lean_apply_1(v_x_347_, v_ctx_348_);
v___x_350_ = lean_apply_2(v_f_346_, lean_box(0), v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object* v_00_u03c9_351_, lean_object* v_00_u03c3_352_, lean_object* v_m_353_, lean_object* v_00_u03b1_354_, lean_object* v_f_355_, lean_object* v_x_356_, lean_object* v_ctx_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_StateRefT_x27_instMonadFunctor___aux__1(v_00_u03c9_351_, v_00_u03c3_352_, v_m_353_, v_00_u03b1_354_, v_f_355_, v_x_356_, v_ctx_357_);
lean_dec(v_ctx_357_);
return v_res_358_;
}
}
lean_object* l_StateRefT_x27_instMonadFunctor___redArg(){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = ((lean_object*)(l_StateRefT_x27_instMonadFunctor___redArg___closed__0));
return v___x_361_;
}
}
LEAN_EXPORT void l_StateRefT_x27_instMonadFunctor___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_362_;
v_res_362_ = l_StateRefT_x27_instMonadFunctor___redArg();
stack->m_obj
 = v_res_362_;
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor___redArg___boxed(lean_object* v___dummy_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_StateRefT_x27_instMonadFunctor___redArg();
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadFunctor(lean_object* v_00_u03c9_365_, lean_object* v_00_u03c3_366_, lean_object* v_m_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = ((lean_object*)(l_StateRefT_x27_instMonadFunctor___redArg___closed__0));
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__0(lean_object* v_inst_369_, lean_object* v_00_u03b1_370_, lean_object* v___y_371_){
_start:
{
lean_object* v_failure_372_; lean_object* v___x_373_; 
v_failure_372_ = lean_ctor_get(v_inst_369_, 1);
lean_inc(v_failure_372_);
lean_dec_ref(v_inst_369_);
v___x_373_ = lean_apply_1(v_failure_372_, lean_box(0));
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__0___boxed(lean_object* v_inst_374_, lean_object* v_00_u03b1_375_, lean_object* v___y_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__0(v_inst_374_, v_00_u03b1_375_, v___y_376_);
lean_dec(v___y_376_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__1(lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v_x_380_){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = lean_box(0);
lean_inc(v___y_379_);
v___x_382_ = lean_apply_2(v___y_378_, v___x_381_, v___y_379_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__1___boxed(lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v_x_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__1(v___y_383_, v___y_384_, v_x_385_);
lean_dec(v___y_384_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__2(lean_object* v_inst_387_, lean_object* v_00_u03b1_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v_orElse_392_; lean_object* v___f_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v_orElse_392_ = lean_ctor_get(v_inst_387_, 2);
lean_inc(v_orElse_392_);
lean_dec_ref(v_inst_387_);
lean_inc_n(v___y_391_, 2);
v___f_393_ = lean_alloc_closure((void*)(l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_393_, 0, v___y_390_);
lean_closure_set(v___f_393_, 1, v___y_391_);
v___x_394_ = lean_apply_1(v___y_389_, v___y_391_);
v___x_395_ = lean_apply_3(v_orElse_392_, lean_box(0), v___x_394_, v___f_393_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__2___boxed(lean_object* v_inst_396_, lean_object* v_00_u03b1_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__2(v_inst_396_, v_00_u03b1_397_, v___y_398_, v___y_399_, v___y_400_);
lean_dec(v___y_400_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg(lean_object* v_inst_402_, lean_object* v_inst_403_){
_start:
{
lean_object* v___x_404_; lean_object* v_toApplicative_405_; lean_object* v___f_406_; lean_object* v___f_407_; lean_object* v___x_408_; 
v___x_404_ = l_StateRefT_x27_instMonad___redArg(v_inst_403_);
v_toApplicative_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc_ref(v_toApplicative_405_);
lean_dec_ref(v___x_404_);
lean_inc_ref(v_inst_402_);
v___f_406_ = lean_alloc_closure((void*)(l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_406_, 0, v_inst_402_);
v___f_407_ = lean_alloc_closure((void*)(l_StateRefT_x27_instAlternativeOfMonad___redArg___lam__2___boxed), 5, 1);
lean_closure_set(v___f_407_, 0, v_inst_402_);
v___x_408_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_408_, 0, v_toApplicative_405_);
lean_ctor_set(v___x_408_, 1, v___f_406_);
lean_ctor_set(v___x_408_, 2, v___f_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instAlternativeOfMonad(lean_object* v_00_u03c9_409_, lean_object* v_00_u03c3_410_, lean_object* v_m_411_, lean_object* v_inst_412_, lean_object* v_inst_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_StateRefT_x27_instAlternativeOfMonad___redArg(v_inst_412_, v_inst_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg___lam__0(lean_object* v_x_415_){
_start:
{
lean_inc(v_x_415_);
return v_x_415_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg___lam__0___boxed(lean_object* v_x_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg___lam__0(v_x_416_);
lean_dec(v_x_416_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg(lean_object* v_inst_419_, lean_object* v_inst_420_, lean_object* v_x_421_, lean_object* v_r_422_){
_start:
{
lean_object* v_toApplicative_423_; lean_object* v_toFunctor_424_; lean_object* v_map_425_; lean_object* v___f_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v_toApplicative_423_ = lean_ctor_get(v_inst_419_, 0);
lean_inc_ref(v_toApplicative_423_);
lean_dec_ref(v_inst_419_);
v_toFunctor_424_ = lean_ctor_get(v_toApplicative_423_, 0);
lean_inc_ref(v_toFunctor_424_);
lean_dec_ref(v_toApplicative_423_);
v_map_425_ = lean_ctor_get(v_toFunctor_424_, 0);
lean_inc(v_map_425_);
lean_dec_ref(v_toFunctor_424_);
v___f_426_ = ((lean_object*)(l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg___closed__0));
lean_inc(v_r_422_);
v___x_427_ = lean_apply_1(v_x_421_, v_r_422_);
v___x_428_ = lean_apply_2(v_inst_420_, lean_box(0), v___x_427_);
v___x_429_ = lean_apply_4(v_map_425_, lean_box(0), lean_box(0), v___f_426_, v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg___boxed(lean_object* v_inst_430_, lean_object* v_inst_431_, lean_object* v_x_432_, lean_object* v_r_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg(v_inst_430_, v_inst_431_, v_x_432_, v_r_433_);
lean_dec(v_r_433_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__1(lean_object* v_00_u03c9_435_, lean_object* v_00_u03c3_436_, lean_object* v_m_437_, lean_object* v_inst_438_, lean_object* v_inst_439_, lean_object* v_00_u03b1_440_, lean_object* v_x_441_, lean_object* v_r_442_){
_start:
{
lean_object* v_toApplicative_443_; lean_object* v_toFunctor_444_; lean_object* v_map_445_; lean_object* v___f_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v_toApplicative_443_ = lean_ctor_get(v_inst_438_, 0);
lean_inc_ref(v_toApplicative_443_);
lean_dec_ref(v_inst_438_);
v_toFunctor_444_ = lean_ctor_get(v_toApplicative_443_, 0);
lean_inc_ref(v_toFunctor_444_);
lean_dec_ref(v_toApplicative_443_);
v_map_445_ = lean_ctor_get(v_toFunctor_444_, 0);
lean_inc(v_map_445_);
lean_dec_ref(v_toFunctor_444_);
v___f_446_ = ((lean_object*)(l_StateRefT_x27_instMonadAttachOfMonad___aux__1___redArg___closed__0));
lean_inc(v_r_442_);
v___x_447_ = lean_apply_1(v_x_441_, v_r_442_);
v___x_448_ = lean_apply_2(v_inst_439_, lean_box(0), v___x_447_);
v___x_449_ = lean_apply_4(v_map_445_, lean_box(0), lean_box(0), v___f_446_, v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___aux__1___boxed(lean_object* v_00_u03c9_450_, lean_object* v_00_u03c3_451_, lean_object* v_m_452_, lean_object* v_inst_453_, lean_object* v_inst_454_, lean_object* v_00_u03b1_455_, lean_object* v_x_456_, lean_object* v_r_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_StateRefT_x27_instMonadAttachOfMonad___aux__1(v_00_u03c9_450_, v_00_u03c3_451_, v_m_452_, v_inst_453_, v_inst_454_, v_00_u03b1_455_, v_x_456_, v_r_457_);
lean_dec(v_r_457_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad___redArg(lean_object* v_inst_459_, lean_object* v_inst_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadAttachOfMonad___aux__1___boxed), 8, 5);
lean_closure_set(v___x_461_, 0, lean_box(0));
lean_closure_set(v___x_461_, 1, lean_box(0));
lean_closure_set(v___x_461_, 2, lean_box(0));
lean_closure_set(v___x_461_, 3, v_inst_459_);
lean_closure_set(v___x_461_, 4, v_inst_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadAttachOfMonad(lean_object* v_00_u03c9_462_, lean_object* v_00_u03c3_463_, lean_object* v_m_464_, lean_object* v_inst_465_, lean_object* v_inst_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadAttachOfMonad___aux__1___boxed), 8, 5);
lean_closure_set(v___x_467_, 0, lean_box(0));
lean_closure_set(v___x_467_, 1, lean_box(0));
lean_closure_set(v___x_467_, 2, lean_box(0));
lean_closure_set(v___x_467_, 3, v_inst_465_);
lean_closure_set(v___x_467_, 4, v_inst_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_get___redArg(lean_object* v_inst_468_, lean_object* v_ref_469_){
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
LEAN_EXPORT lean_object* l_StateRefT_x27_get___redArg___boxed(lean_object* v_inst_472_, lean_object* v_ref_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_StateRefT_x27_get___redArg(v_inst_472_, v_ref_473_);
lean_dec(v_ref_473_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_get(lean_object* v_00_u03c9_475_, lean_object* v_00_u03c3_476_, lean_object* v_m_477_, lean_object* v_inst_478_, lean_object* v_ref_479_){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
lean_inc(v_ref_479_);
v___x_480_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_480_, 0, lean_box(0));
lean_closure_set(v___x_480_, 1, lean_box(0));
lean_closure_set(v___x_480_, 2, v_ref_479_);
v___x_481_ = lean_apply_2(v_inst_478_, lean_box(0), v___x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_get___boxed(lean_object* v_00_u03c9_482_, lean_object* v_00_u03c3_483_, lean_object* v_m_484_, lean_object* v_inst_485_, lean_object* v_ref_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_StateRefT_x27_get(v_00_u03c9_482_, v_00_u03c3_483_, v_m_484_, v_inst_485_, v_ref_486_);
lean_dec(v_ref_486_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_set___redArg(lean_object* v_inst_488_, lean_object* v_s_489_, lean_object* v_ref_490_){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
lean_inc(v_ref_490_);
v___x_491_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_491_, 0, lean_box(0));
lean_closure_set(v___x_491_, 1, lean_box(0));
lean_closure_set(v___x_491_, 2, v_ref_490_);
lean_closure_set(v___x_491_, 3, v_s_489_);
v___x_492_ = lean_apply_2(v_inst_488_, lean_box(0), v___x_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_set___redArg___boxed(lean_object* v_inst_493_, lean_object* v_s_494_, lean_object* v_ref_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_StateRefT_x27_set___redArg(v_inst_493_, v_s_494_, v_ref_495_);
lean_dec(v_ref_495_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_set(lean_object* v_00_u03c9_497_, lean_object* v_00_u03c3_498_, lean_object* v_m_499_, lean_object* v_inst_500_, lean_object* v_s_501_, lean_object* v_ref_502_){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
lean_inc(v_ref_502_);
v___x_503_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_503_, 0, lean_box(0));
lean_closure_set(v___x_503_, 1, lean_box(0));
lean_closure_set(v___x_503_, 2, v_ref_502_);
lean_closure_set(v___x_503_, 3, v_s_501_);
v___x_504_ = lean_apply_2(v_inst_500_, lean_box(0), v___x_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_set___boxed(lean_object* v_00_u03c9_505_, lean_object* v_00_u03c3_506_, lean_object* v_m_507_, lean_object* v_inst_508_, lean_object* v_s_509_, lean_object* v_ref_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_StateRefT_x27_set(v_00_u03c9_505_, v_00_u03c3_506_, v_m_507_, v_inst_508_, v_s_509_, v_ref_510_);
lean_dec(v_ref_510_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_modifyGet___redArg(lean_object* v_inst_512_, lean_object* v_f_513_, lean_object* v_ref_514_){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
lean_inc(v_ref_514_);
v___x_515_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_515_, 0, lean_box(0));
lean_closure_set(v___x_515_, 1, lean_box(0));
lean_closure_set(v___x_515_, 2, lean_box(0));
lean_closure_set(v___x_515_, 3, v_ref_514_);
lean_closure_set(v___x_515_, 4, v_f_513_);
v___x_516_ = lean_apply_2(v_inst_512_, lean_box(0), v___x_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_modifyGet___redArg___boxed(lean_object* v_inst_517_, lean_object* v_f_518_, lean_object* v_ref_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_StateRefT_x27_modifyGet___redArg(v_inst_517_, v_f_518_, v_ref_519_);
lean_dec(v_ref_519_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_modifyGet(lean_object* v_00_u03c9_521_, lean_object* v_00_u03c3_522_, lean_object* v_m_523_, lean_object* v_00_u03b1_524_, lean_object* v_inst_525_, lean_object* v_f_526_, lean_object* v_ref_527_){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
lean_inc(v_ref_527_);
v___x_528_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_528_, 0, lean_box(0));
lean_closure_set(v___x_528_, 1, lean_box(0));
lean_closure_set(v___x_528_, 2, lean_box(0));
lean_closure_set(v___x_528_, 3, v_ref_527_);
lean_closure_set(v___x_528_, 4, v_f_526_);
v___x_529_ = lean_apply_2(v_inst_525_, lean_box(0), v___x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_modifyGet___boxed(lean_object* v_00_u03c9_530_, lean_object* v_00_u03c3_531_, lean_object* v_m_532_, lean_object* v_00_u03b1_533_, lean_object* v_inst_534_, lean_object* v_f_535_, lean_object* v_ref_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_StateRefT_x27_modifyGet(v_00_u03c9_530_, v_00_u03c3_531_, v_m_532_, v_00_u03b1_533_, v_inst_534_, v_f_535_, v_ref_536_);
lean_dec(v_ref_536_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg___lam__0(lean_object* v_inst_538_, lean_object* v_00_u03b1_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
lean_inc(v___y_541_);
v___x_542_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_542_, 0, lean_box(0));
lean_closure_set(v___x_542_, 1, lean_box(0));
lean_closure_set(v___x_542_, 2, lean_box(0));
lean_closure_set(v___x_542_, 3, v___y_541_);
lean_closure_set(v___x_542_, 4, v___y_540_);
v___x_543_ = lean_apply_2(v_inst_538_, lean_box(0), v___x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg___lam__0___boxed(lean_object* v_inst_544_, lean_object* v_00_u03b1_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg___lam__0(v_inst_544_, v_00_u03b1_545_, v___y_546_, v___y_547_);
lean_dec(v___y_547_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg(lean_object* v_inst_549_){
_start:
{
lean_object* v___f_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
lean_inc_n(v_inst_549_, 2);
v___f_550_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_550_, 0, v_inst_549_);
v___x_551_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_551_, 0, lean_box(0));
lean_closure_set(v___x_551_, 1, lean_box(0));
lean_closure_set(v___x_551_, 2, lean_box(0));
lean_closure_set(v___x_551_, 3, v_inst_549_);
v___x_552_ = lean_alloc_closure((void*)(l_StateRefT_x27_set___boxed), 6, 4);
lean_closure_set(v___x_552_, 0, lean_box(0));
lean_closure_set(v___x_552_, 1, lean_box(0));
lean_closure_set(v___x_552_, 2, lean_box(0));
lean_closure_set(v___x_552_, 3, v_inst_549_);
v___x_553_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_553_, 0, v___x_551_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
lean_ctor_set(v___x_553_, 2, v___f_550_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadStateOfOfMonadLiftTST(lean_object* v_00_u03c9_554_, lean_object* v_00_u03c3_555_, lean_object* v_m_556_, lean_object* v_inst_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg(v_inst_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0(lean_object* v_inst_559_, lean_object* v_00_u03b1_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_throw_563_; lean_object* v___x_564_; 
v_throw_563_ = lean_ctor_get(v_inst_559_, 0);
lean_inc(v_throw_563_);
lean_dec_ref(v_inst_559_);
v___x_564_ = lean_apply_2(v_throw_563_, lean_box(0), v___y_561_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object* v_inst_565_, lean_object* v_00_u03b1_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_StateRefT_x27_instMonadExceptOf___redArg___lam__0(v_inst_565_, v_00_u03b1_566_, v___y_567_, v___y_568_);
lean_dec(v___y_568_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__1(lean_object* v_c_570_, lean_object* v_s_571_, lean_object* v_e_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = lean_apply_2(v_c_570_, v_e_572_, v_s_571_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object* v_inst_574_, lean_object* v_00_u03b1_575_, lean_object* v_x_576_, lean_object* v_c_577_, lean_object* v_s_578_){
_start:
{
lean_object* v_tryCatch_579_; lean_object* v___f_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_tryCatch_579_ = lean_ctor_get(v_inst_574_, 1);
lean_inc(v_tryCatch_579_);
lean_dec_ref(v_inst_574_);
lean_inc(v_s_578_);
v___f_580_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__1), 3, 2);
lean_closure_set(v___f_580_, 0, v_c_577_);
lean_closure_set(v___f_580_, 1, v_s_578_);
v___x_581_ = lean_apply_1(v_x_576_, v_s_578_);
v___x_582_ = lean_apply_3(v_tryCatch_579_, lean_box(0), v___x_581_, v___f_580_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadExceptOf___redArg(lean_object* v_inst_583_){
_start:
{
lean_object* v___f_584_; lean_object* v___f_585_; lean_object* v___x_586_; 
lean_inc_ref(v_inst_583_);
v___f_584_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_584_, 0, v_inst_583_);
v___f_585_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_585_, 0, v_inst_583_);
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v___f_584_);
lean_ctor_set(v___x_586_, 1, v___f_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_instMonadExceptOf(lean_object* v_00_u03c9_587_, lean_object* v_00_u03c3_588_, lean_object* v_m_589_, lean_object* v_00_u03b5_590_, lean_object* v_inst_591_){
_start:
{
lean_object* v___f_592_; lean_object* v___f_593_; lean_object* v___x_594_; 
lean_inc_ref(v_inst_591_);
v___f_592_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_592_, 0, v_inst_591_);
v___f_593_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_593_, 0, v_inst_591_);
v___x_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_594_, 0, v___f_592_);
lean_ctor_set(v___x_594_, 1, v___f_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0(lean_object* v_ctx_595_, lean_object* v_00_u03b2_596_, lean_object* v_x_597_){
_start:
{
lean_object* v___x_598_; 
lean_inc(v_ctx_595_);
v___x_598_ = lean_apply_1(v_x_597_, v_ctx_595_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0___boxed(lean_object* v_ctx_599_, lean_object* v_00_u03b2_600_, lean_object* v_x_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0(v_ctx_599_, v_00_u03b2_600_, v_x_601_);
lean_dec(v_ctx_599_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__1___redArg(lean_object* v_f_603_, lean_object* v_ctx_604_){
_start:
{
lean_object* v___f_605_; lean_object* v___x_606_; 
lean_inc(v_ctx_604_);
v___f_605_ = lean_alloc_closure((void*)(l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_605_, 0, v_ctx_604_);
v___x_606_ = lean_apply_1(v_f_603_, v___f_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__1___redArg___boxed(lean_object* v_f_607_, lean_object* v_ctx_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_instMonadControlStateRefT_x27___aux__1___redArg(v_f_607_, v_ctx_608_);
lean_dec(v_ctx_608_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__1(lean_object* v_00_u03c9_610_, lean_object* v_00_u03c3_611_, lean_object* v_m_612_, lean_object* v_00_u03b1_613_, lean_object* v_f_614_, lean_object* v_ctx_615_){
_start:
{
lean_object* v___f_616_; lean_object* v___x_617_; 
lean_inc(v_ctx_615_);
v___f_616_ = lean_alloc_closure((void*)(l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_616_, 0, v_ctx_615_);
v___x_617_ = lean_apply_1(v_f_614_, v___f_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__1___boxed(lean_object* v_00_u03c9_618_, lean_object* v_00_u03c3_619_, lean_object* v_m_620_, lean_object* v_00_u03b1_621_, lean_object* v_f_622_, lean_object* v_ctx_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_instMonadControlStateRefT_x27___aux__1(v_00_u03c9_618_, v_00_u03c3_619_, v_m_620_, v_00_u03b1_621_, v_f_622_, v_ctx_623_);
lean_dec(v_ctx_623_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__3___redArg(lean_object* v_x_625_){
_start:
{
lean_inc(v_x_625_);
return v_x_625_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__3___redArg___boxed(lean_object* v_x_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_instMonadControlStateRefT_x27___aux__3___redArg(v_x_626_);
lean_dec(v_x_626_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__3(lean_object* v_00_u03c9_628_, lean_object* v_00_u03c3_629_, lean_object* v_m_630_, lean_object* v_00_u03b1_631_, lean_object* v_x_632_, lean_object* v_x_633_){
_start:
{
lean_inc(v_x_632_);
return v_x_632_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___aux__3___boxed(lean_object* v_00_u03c9_634_, lean_object* v_00_u03c3_635_, lean_object* v_m_636_, lean_object* v_00_u03b1_637_, lean_object* v_x_638_, lean_object* v_x_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_instMonadControlStateRefT_x27___aux__3(v_00_u03c9_634_, v_00_u03c3_635_, v_m_636_, v_00_u03b1_637_, v_x_638_, v_x_639_);
lean_dec(v_x_639_);
lean_dec(v_x_638_);
return v_res_640_;
}
}
lean_object* l_instMonadControlStateRefT_x27___redArg(){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = ((lean_object*)(l_instMonadControlStateRefT_x27___redArg___closed__2));
return v___x_647_;
}
}
LEAN_EXPORT void l_instMonadControlStateRefT_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_648_;
v_res_648_ = l_instMonadControlStateRefT_x27___redArg();
stack->m_obj
 = v_res_648_;
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27___redArg___boxed(lean_object* v___dummy_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_instMonadControlStateRefT_x27___redArg();
return v_res_650_;
}
}
static lean_object* _init_l_instMonadControlStateRefT_x27___closed__0(void){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_instMonadControlStateRefT_x27___redArg();
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlStateRefT_x27(lean_object* v_00_u03c9_652_, lean_object* v_00_u03c3_653_, lean_object* v_m_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = lean_obj_once(&l_instMonadControlStateRefT_x27___closed__0, &l_instMonadControlStateRefT_x27___closed__0_once, _init_l_instMonadControlStateRefT_x27___closed__0);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0(lean_object* v_h_656_, lean_object* v_ctx_657_, lean_object* v_a_x3f_658_){
_start:
{
lean_object* v___x_659_; 
lean_inc(v_ctx_657_);
v___x_659_ = lean_apply_2(v_h_656_, v_a_x3f_658_, v_ctx_657_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0___boxed(lean_object* v_h_660_, lean_object* v_ctx_661_, lean_object* v_a_x3f_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0(v_h_660_, v_ctx_661_, v_a_x3f_662_);
lean_dec(v_ctx_661_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___aux__1___redArg(lean_object* v_inst_664_, lean_object* v_x_665_, lean_object* v_h_666_, lean_object* v_ctx_667_){
_start:
{
lean_object* v___f_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
lean_inc_n(v_ctx_667_, 2);
v___f_668_ = lean_alloc_closure((void*)(l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_668_, 0, v_h_666_);
lean_closure_set(v___f_668_, 1, v_ctx_667_);
v___x_669_ = lean_apply_1(v_x_665_, v_ctx_667_);
v___x_670_ = lean_apply_4(v_inst_664_, lean_box(0), lean_box(0), v___x_669_, v___f_668_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___aux__1___redArg___boxed(lean_object* v_inst_671_, lean_object* v_x_672_, lean_object* v_h_673_, lean_object* v_ctx_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_instMonadFinallyStateRefT_x27___aux__1___redArg(v_inst_671_, v_x_672_, v_h_673_, v_ctx_674_);
lean_dec(v_ctx_674_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___aux__1(lean_object* v_m_676_, lean_object* v_00_u03c9_677_, lean_object* v_00_u03c3_678_, lean_object* v_inst_679_, lean_object* v_00_u03b1_680_, lean_object* v_00_u03b2_681_, lean_object* v_x_682_, lean_object* v_h_683_, lean_object* v_ctx_684_){
_start:
{
lean_object* v___f_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
lean_inc_n(v_ctx_684_, 2);
v___f_685_ = lean_alloc_closure((void*)(l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_685_, 0, v_h_683_);
lean_closure_set(v___f_685_, 1, v_ctx_684_);
v___x_686_ = lean_apply_1(v_x_682_, v_ctx_684_);
v___x_687_ = lean_apply_4(v_inst_679_, lean_box(0), lean_box(0), v___x_686_, v___f_685_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___aux__1___boxed(lean_object* v_m_688_, lean_object* v_00_u03c9_689_, lean_object* v_00_u03c3_690_, lean_object* v_inst_691_, lean_object* v_00_u03b1_692_, lean_object* v_00_u03b2_693_, lean_object* v_x_694_, lean_object* v_h_695_, lean_object* v_ctx_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_instMonadFinallyStateRefT_x27___aux__1(v_m_688_, v_00_u03c9_689_, v_00_u03c3_690_, v_inst_691_, v_00_u03b1_692_, v_00_u03b2_693_, v_x_694_, v_h_695_, v_ctx_696_);
lean_dec(v_ctx_696_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27___redArg(lean_object* v_inst_698_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = lean_alloc_closure((void*)(l_instMonadFinallyStateRefT_x27___aux__1___boxed), 9, 4);
lean_closure_set(v___x_699_, 0, lean_box(0));
lean_closure_set(v___x_699_, 1, lean_box(0));
lean_closure_set(v___x_699_, 2, lean_box(0));
lean_closure_set(v___x_699_, 3, v_inst_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyStateRefT_x27(lean_object* v_m_700_, lean_object* v_00_u03c9_701_, lean_object* v_00_u03c3_702_, lean_object* v_inst_703_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = lean_alloc_closure((void*)(l_instMonadFinallyStateRefT_x27___aux__1___boxed), 9, 4);
lean_closure_set(v___x_704_, 0, lean_box(0));
lean_closure_set(v___x_704_, 1, lean_box(0));
lean_closure_set(v___x_704_, 2, lean_box(0));
lean_closure_set(v___x_704_, 3, v_inst_703_);
return v___x_704_;
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

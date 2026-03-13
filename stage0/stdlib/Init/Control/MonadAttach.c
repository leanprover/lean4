// Lean compiler output
// Module: Init.Control.MonadAttach
// Imports: public import Init.Core
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
LEAN_EXPORT lean_object* l_MonadAttach_pbind___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadAttach_pbind___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadAttach_pbind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadAttach_trivial___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_MonadAttach_trivial___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadAttach_trivial___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_MonadAttach_trivial___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_MonadAttach_trivial___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_MonadAttach_trivial___redArg___closed__0 = (const lean_object*)&l_MonadAttach_trivial___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_MonadAttach_trivial___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadAttach_trivial(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadAttach_pbind___redArg___lam__0(lean_object* v_f_1_, lean_object* v_x_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_2(v_f_1_, v_x_2_, lean_box(0));
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_MonadAttach_pbind___redArg(lean_object* v_inst_4_, lean_object* v_inst_5_, lean_object* v_x_6_, lean_object* v_f_7_){
_start:
{
lean_object* v_toBind_8_; lean_object* v___f_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_toBind_8_ = lean_ctor_get(v_inst_4_, 1);
lean_inc(v_toBind_8_);
lean_dec_ref(v_inst_4_);
v___f_9_ = lean_alloc_closure((void*)(l_MonadAttach_pbind___redArg___lam__0), 2, 1);
lean_closure_set(v___f_9_, 0, v_f_7_);
v___x_10_ = lean_apply_2(v_inst_5_, lean_box(0), v_x_6_);
v___x_11_ = lean_apply_4(v_toBind_8_, lean_box(0), lean_box(0), v___x_10_, v___f_9_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_MonadAttach_pbind(lean_object* v_m_12_, lean_object* v_00_u03b1_13_, lean_object* v_00_u03b2_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_x_17_, lean_object* v_f_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_MonadAttach_pbind___redArg(v_inst_15_, v_inst_16_, v_x_17_, v_f_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_MonadAttach_trivial___redArg___lam__0(lean_object* v_x_20_){
_start:
{
lean_inc(v_x_20_);
return v_x_20_;
}
}
LEAN_EXPORT lean_object* l_MonadAttach_trivial___redArg___lam__0___boxed(lean_object* v_x_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_MonadAttach_trivial___redArg___lam__0(v_x_21_);
lean_dec(v_x_21_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_MonadAttach_trivial___redArg___lam__1(lean_object* v_toFunctor_23_, lean_object* v___f_24_, lean_object* v_00_u03b1_25_, lean_object* v_x_26_){
_start:
{
lean_object* v_map_27_; lean_object* v___x_28_; 
v_map_27_ = lean_ctor_get(v_toFunctor_23_, 0);
lean_inc(v_map_27_);
lean_dec_ref(v_toFunctor_23_);
v___x_28_ = lean_apply_4(v_map_27_, lean_box(0), lean_box(0), v___f_24_, v_x_26_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_MonadAttach_trivial___redArg(lean_object* v_inst_30_){
_start:
{
lean_object* v_toApplicative_31_; lean_object* v_toFunctor_32_; lean_object* v___f_33_; lean_object* v___f_34_; 
v_toApplicative_31_ = lean_ctor_get(v_inst_30_, 0);
lean_inc_ref(v_toApplicative_31_);
lean_dec_ref(v_inst_30_);
v_toFunctor_32_ = lean_ctor_get(v_toApplicative_31_, 0);
lean_inc_ref(v_toFunctor_32_);
lean_dec_ref(v_toApplicative_31_);
v___f_33_ = ((lean_object*)(l_MonadAttach_trivial___redArg___closed__0));
v___f_34_ = lean_alloc_closure((void*)(l_MonadAttach_trivial___redArg___lam__1), 4, 2);
lean_closure_set(v___f_34_, 0, v_toFunctor_32_);
lean_closure_set(v___f_34_, 1, v___f_33_);
return v___f_34_;
}
}
LEAN_EXPORT lean_object* l_MonadAttach_trivial(lean_object* v_m_35_, lean_object* v_inst_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_MonadAttach_trivial___redArg(v_inst_36_);
return v___x_37_;
}
}
lean_object* runtime_initialize_Init_Core(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Control_MonadAttach(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Control_MonadAttach(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Core(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Control_MonadAttach(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_MonadAttach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Control_MonadAttach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Control_MonadAttach(builtin);
}
#ifdef __cplusplus
}
#endif

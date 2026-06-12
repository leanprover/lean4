// Lean compiler output
// Module: Std.Do.SPred.Laws
// Imports: public import Std.Do.SPred.Notation
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
lean_object* l_Std_Do_SPred_pure___redArg(lean_object*);
lean_object* l_Std_Do_SVal_curry___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_Laws_0__Std_Do_SPred_entails_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_Laws_0__Std_Do_SPred_entails_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransEntails(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransEntails___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransBientails(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransBientails___boxed(lean_object*);
static lean_once_cell_t l_Std_Do_SVal_evalsTo___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do_SVal_evalsTo___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_Do_SVal_evalsTo___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SVal_evalsTo___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Do_SVal_evalsTo___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Do_SVal_evalsTo___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Do_SVal_evalsTo___redArg___closed__0 = (const lean_object*)&l_Std_Do_SVal_evalsTo___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Do_SVal_evalsTo___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SVal_evalsTo(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SVal_evalsTo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_Laws_0__Std_Do_SPred_entails_match__1_splitter___redArg(lean_object* v_00_u03c3s_1_, lean_object* v_P_2_, lean_object* v_Q_3_, lean_object* v_h__1_4_, lean_object* v_h__2_5_){
_start:
{
if (lean_obj_tag(v_00_u03c3s_1_) == 0)
{
lean_object* v___x_6_; 
lean_dec(v_h__2_5_);
v___x_6_ = lean_apply_2(v_h__1_4_, v_P_2_, v_Q_3_);
return v___x_6_;
}
else
{
lean_object* v_tail_7_; lean_object* v___x_8_; 
lean_dec(v_h__1_4_);
v_tail_7_ = lean_ctor_get(v_00_u03c3s_1_, 1);
lean_inc(v_tail_7_);
lean_dec_ref_known(v_00_u03c3s_1_, 2);
v___x_8_ = lean_apply_4(v_h__2_5_, lean_box(0), v_tail_7_, v_P_2_, v_Q_3_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_Laws_0__Std_Do_SPred_entails_match__1_splitter(lean_object* v_motive_9_, lean_object* v_00_u03c3s_10_, lean_object* v_P_11_, lean_object* v_Q_12_, lean_object* v_h__1_13_, lean_object* v_h__2_14_){
_start:
{
if (lean_obj_tag(v_00_u03c3s_10_) == 0)
{
lean_object* v___x_15_; 
lean_dec(v_h__2_14_);
v___x_15_ = lean_apply_2(v_h__1_13_, v_P_11_, v_Q_12_);
return v___x_15_;
}
else
{
lean_object* v_tail_16_; lean_object* v___x_17_; 
lean_dec(v_h__1_13_);
v_tail_16_ = lean_ctor_get(v_00_u03c3s_10_, 1);
lean_inc(v_tail_16_);
lean_dec_ref_known(v_00_u03c3s_10_, 2);
v___x_17_ = lean_apply_4(v_h__2_14_, lean_box(0), v_tail_16_, v_P_11_, v_Q_12_);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransEntails(lean_object* v_00_u03c3s_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lean_box(0);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransEntails___boxed(lean_object* v_00_u03c3s_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Std_Do_SPred_instTransEntails(v_00_u03c3s_20_);
lean_dec(v_00_u03c3s_20_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransBientails(lean_object* v_00_u03c3s_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lean_box(0);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransBientails___boxed(lean_object* v_00_u03c3s_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Std_Do_SPred_instTransBientails(v_00_u03c3s_24_);
lean_dec(v_00_u03c3s_24_);
return v_res_25_;
}
}
static lean_object* _init_l_Std_Do_SVal_evalsTo___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_box(0);
v___x_27_ = l_Std_Do_SPred_pure___redArg(v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_evalsTo___redArg___lam__0(lean_object* v_t_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lean_obj_once(&l_Std_Do_SVal_evalsTo___redArg___lam__0___closed__0, &l_Std_Do_SVal_evalsTo___redArg___lam__0___closed__0_once, _init_l_Std_Do_SVal_evalsTo___redArg___lam__0___closed__0);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_evalsTo___redArg___lam__0___boxed(lean_object* v_t_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Std_Do_SVal_evalsTo___redArg___lam__0(v_t_30_);
lean_dec(v_t_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_evalsTo___redArg(lean_object* v_00_u03c3s_33_){
_start:
{
lean_object* v___f_34_; lean_object* v___x_35_; 
v___f_34_ = ((lean_object*)(l_Std_Do_SVal_evalsTo___redArg___closed__0));
v___x_35_ = l_Std_Do_SVal_curry___redArg(v_00_u03c3s_33_, v___f_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_evalsTo(lean_object* v_00_u03b1_36_, lean_object* v_00_u03c3s_37_, lean_object* v_f_38_, lean_object* v_a_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Std_Do_SVal_evalsTo___redArg(v_00_u03c3s_37_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_evalsTo___boxed(lean_object* v_00_u03b1_41_, lean_object* v_00_u03c3s_42_, lean_object* v_f_43_, lean_object* v_a_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Std_Do_SVal_evalsTo(v_00_u03b1_41_, v_00_u03c3s_42_, v_f_43_, v_a_44_);
lean_dec(v_a_44_);
lean_dec(v_f_43_);
return v_res_45_;
}
}
lean_object* runtime_initialize_Std_Do_SPred_Notation(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Do_SPred_Laws(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Do_SPred_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Do_SPred_Laws(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Do_SPred_Notation(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Do_SPred_Laws(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Do_SPred_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Do_SPred_Laws(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Do_SPred_Laws(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Do_SPred_Laws(builtin);
}
#ifdef __cplusplus
}
#endif

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
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_Laws_0__Std_Do_SPred_entails_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_Laws_0__Std_Do_SPred_entails_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransEntails(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransEntails___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransBientails(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransBientails___boxed(lean_object*);
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
lean_dec_ref(v_00_u03c3s_1_);
v___x_8_ = lean_apply_4(v_h__2_5_, lean_box(0), v_tail_7_, v_P_2_, v_Q_3_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_Laws_0__Std_Do_SPred_entails_match__1_splitter(lean_object* v_motive_9_, lean_object* v_00_u03c3s_10_, lean_object* v_P_11_, lean_object* v_Q_12_, lean_object* v_h__1_13_, lean_object* v_h__2_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l___private_Std_Do_SPred_Laws_0__Std_Do_SPred_entails_match__1_splitter___redArg(v_00_u03c3s_10_, v_P_11_, v_Q_12_, v_h__1_13_, v_h__2_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransEntails(lean_object* v_00_u03c3s_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_box(0);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransEntails___boxed(lean_object* v_00_u03c3s_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Std_Do_SPred_instTransEntails(v_00_u03c3s_18_);
lean_dec(v_00_u03c3s_18_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransBientails(lean_object* v_00_u03c3s_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lean_box(0);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransBientails___boxed(lean_object* v_00_u03c3s_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Std_Do_SPred_instTransBientails(v_00_u03c3s_22_);
lean_dec(v_00_u03c3s_22_);
return v_res_23_;
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

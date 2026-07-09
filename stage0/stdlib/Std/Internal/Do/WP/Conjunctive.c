// Lean compiler output
// Module: Std.Internal.Do.WP.Conjunctive
// Imports: public import Std.Internal.Do.WP.Basic public import Std.Internal.Do.Order.Lemmas
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Conjunctive_0__Std_Internal_Do_EStateM_wpInst_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Conjunctive_0__Std_Internal_Do_EStateM_wpInst_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Conjunctive_0__Std_Internal_Do_EStateM_wpInst_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v_a_4_; lean_object* v_a_5_; lean_object* v___x_6_; 
lean_dec(v_h__2_3_);
v_a_4_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_a_4_);
v_a_5_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_a_5_);
lean_dec_ref_known(v_x_1_, 2);
v___x_6_ = lean_apply_2(v_h__1_2_, v_a_4_, v_a_5_);
return v___x_6_;
}
else
{
lean_object* v_a_7_; lean_object* v_a_8_; lean_object* v___x_9_; 
lean_dec(v_h__1_2_);
v_a_7_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_a_7_);
v_a_8_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_a_8_);
lean_dec_ref_known(v_x_1_, 2);
v___x_9_ = lean_apply_2(v_h__2_3_, v_a_7_, v_a_8_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Conjunctive_0__Std_Internal_Do_EStateM_wpInst_match__1_splitter(lean_object* v_00_u03b5_10_, lean_object* v_00_u03c3_11_, lean_object* v_00_u03b1_12_, lean_object* v_motive_13_, lean_object* v_x_14_, lean_object* v_h__1_15_, lean_object* v_h__2_16_){
_start:
{
if (lean_obj_tag(v_x_14_) == 0)
{
lean_object* v_a_17_; lean_object* v_a_18_; lean_object* v___x_19_; 
lean_dec(v_h__2_16_);
v_a_17_ = lean_ctor_get(v_x_14_, 0);
lean_inc(v_a_17_);
v_a_18_ = lean_ctor_get(v_x_14_, 1);
lean_inc(v_a_18_);
lean_dec_ref_known(v_x_14_, 2);
v___x_19_ = lean_apply_2(v_h__1_15_, v_a_17_, v_a_18_);
return v___x_19_;
}
else
{
lean_object* v_a_20_; lean_object* v_a_21_; lean_object* v___x_22_; 
lean_dec(v_h__1_15_);
v_a_20_ = lean_ctor_get(v_x_14_, 0);
lean_inc(v_a_20_);
v_a_21_ = lean_ctor_get(v_x_14_, 1);
lean_inc(v_a_21_);
lean_dec_ref_known(v_x_14_, 2);
v___x_22_ = lean_apply_2(v_h__2_16_, v_a_20_, v_a_21_);
return v___x_22_;
}
}
}
lean_object* runtime_initialize_Std_Internal_Do_WP_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Do_Order_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Do_WP_Conjunctive(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Internal_Do_WP_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Do_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Do_WP_Conjunctive(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Internal_Do_WP_Basic(uint8_t builtin);
lean_object* initialize_Std_Internal_Do_Order_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Do_WP_Conjunctive(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Do_WP_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Do_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Do_WP_Conjunctive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Do_WP_Conjunctive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Do_WP_Conjunctive(builtin);
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Std.WP.Basic
// Imports: public import Std.WP.Assertion public import Std.Internal.Order.PredTrans
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
LEAN_EXPORT lean_object* l_Std_WP_WP_wp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_WP_wp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_WP_wp___redArg(lean_object* v_self_1_, lean_object* v_x_2_, lean_object* v_post_3_, lean_object* v_eposts_4_){
_start:
{
lean_object* v_trans_5_; lean_object* v___x_6_; 
v_trans_5_ = lean_ctor_get(v_self_1_, 0);
lean_inc(v_trans_5_);
lean_dec_ref(v_self_1_);
v___x_6_ = lean_apply_3(v_trans_5_, v_x_2_, v_post_3_, v_eposts_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_WP_wp(lean_object* v_Prog_7_, lean_object* v_Value_8_, lean_object* v_Pred_9_, lean_object* v_EPosts_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_self_13_, lean_object* v_x_14_, lean_object* v_post_15_, lean_object* v_eposts_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Std_WP_WP_wp___redArg(v_self_13_, v_x_14_, v_post_15_, v_eposts_16_);
return v___x_17_;
}
}
lean_object* runtime_initialize_Std_WP_Assertion(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Order_PredTrans(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_WP_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_WP_Assertion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Order_PredTrans(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_WP_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_WP_Assertion(uint8_t builtin);
lean_object* initialize_Std_Internal_Order_PredTrans(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_WP_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_WP_Assertion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Order_PredTrans(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_WP_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_WP_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_WP_Basic(builtin);
}
#ifdef __cplusplus
}
#endif

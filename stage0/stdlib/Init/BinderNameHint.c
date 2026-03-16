// Lean compiler output
// Module: Init.BinderNameHint
// Imports: public import Init.Prelude import Init.Tactics
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
LEAN_EXPORT lean_object* l_binderNameHint___redArg(lean_object*);
LEAN_EXPORT lean_object* l_binderNameHint___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_binderNameHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_binderNameHint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_binderNameHint___redArg(lean_object* v_e_1_){
_start:
{
lean_inc(v_e_1_);
return v_e_1_;
}
}
LEAN_EXPORT lean_object* l_binderNameHint___redArg___boxed(lean_object* v_e_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l_binderNameHint___redArg(v_e_2_);
lean_dec(v_e_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l_binderNameHint(lean_object* v_00_u03b1_4_, lean_object* v_00_u03b2_5_, lean_object* v_00_u03b3_6_, lean_object* v_v_7_, lean_object* v_binder_8_, lean_object* v_e_9_){
_start:
{
lean_inc(v_e_9_);
return v_e_9_;
}
}
LEAN_EXPORT lean_object* l_binderNameHint___boxed(lean_object* v_00_u03b1_10_, lean_object* v_00_u03b2_11_, lean_object* v_00_u03b3_12_, lean_object* v_v_13_, lean_object* v_binder_14_, lean_object* v_e_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_binderNameHint(v_00_u03b1_10_, v_00_u03b2_11_, v_00_u03b3_12_, v_v_13_, v_binder_14_, v_e_15_);
lean_dec(v_e_15_);
lean_dec(v_binder_14_);
lean_dec(v_v_13_);
return v_res_16_;
}
}
lean_object* runtime_initialize_Init_Prelude(uint8_t builtin);
lean_object* runtime_initialize_Init_Tactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_BinderNameHint(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_BinderNameHint(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Prelude(uint8_t builtin);
lean_object* initialize_Init_Tactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_BinderNameHint(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_BinderNameHint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_BinderNameHint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_BinderNameHint(builtin);
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Std.Internal.UV.Timer
// Imports: public import Init.System.Promise
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
LEAN_EXPORT lean_object* l___private_Std_Internal_UV_Timer_0__Std_Internal_UV_TimerImpl;
lean_object* lean_uv_timer_mk(uint64_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_UV_Timer_mk___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_timer_next(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_Timer_next___boxed(lean_object*, lean_object*);
lean_object* lean_uv_timer_reset(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_Timer_reset___boxed(lean_object*, lean_object*);
lean_object* lean_uv_timer_stop(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_Timer_stop___boxed(lean_object*, lean_object*);
lean_object* lean_uv_timer_cancel(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_Timer_cancel___boxed(lean_object*, lean_object*);
static lean_object* _init_l___private_Std_Internal_UV_Timer_0__Std_Internal_UV_TimerImpl(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_Timer_mk___boxed(lean_object* v_timeout_5_, lean_object* v_repeating_6_, lean_object* v_a_00___x40___internal___hyg_7_){
_start:
{
uint64_t v_timeout_boxed_8_; uint8_t v_repeating_boxed_9_; lean_object* v_res_10_; 
v_timeout_boxed_8_ = lean_unbox_uint64(v_timeout_5_);
lean_dec_ref(v_timeout_5_);
v_repeating_boxed_9_ = lean_unbox(v_repeating_6_);
v_res_10_ = lean_uv_timer_mk(v_timeout_boxed_8_, v_repeating_boxed_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_Timer_next___boxed(lean_object* v_timer_13_, lean_object* v_a_00___x40___internal___hyg_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = lean_uv_timer_next(v_timer_13_);
lean_dec(v_timer_13_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_Timer_reset___boxed(lean_object* v_timer_18_, lean_object* v_a_00___x40___internal___hyg_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lean_uv_timer_reset(v_timer_18_);
lean_dec(v_timer_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_Timer_stop___boxed(lean_object* v_timer_23_, lean_object* v_a_00___x40___internal___hyg_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lean_uv_timer_stop(v_timer_23_);
lean_dec(v_timer_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_Timer_cancel___boxed(lean_object* v_timer_28_, lean_object* v_a_00___x40___internal___hyg_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lean_uv_timer_cancel(v_timer_28_);
lean_dec(v_timer_28_);
return v_res_30_;
}
}
lean_object* runtime_initialize_Init_System_Promise(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_UV_Timer(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_System_Promise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Std_Internal_UV_Timer_0__Std_Internal_UV_TimerImpl = _init_l___private_Std_Internal_UV_Timer_0__Std_Internal_UV_TimerImpl();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_UV_Timer(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_Promise(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_UV_Timer(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_Promise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_UV_Timer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_UV_Timer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_UV_Timer(builtin);
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Std.Internal.UV.Signal
// Imports: public import Init.System.Promise public import Init.Data.SInt public import Std.Net
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
LEAN_EXPORT lean_object* l___private_Std_Internal_UV_Signal_0__Std_Internal_UV_SignalImpl;
lean_object* lean_uv_signal_mk(uint32_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_UV_Signal_mk___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_signal_next(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_Signal_next___boxed(lean_object*, lean_object*);
lean_object* lean_uv_signal_stop(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_Signal_stop___boxed(lean_object*, lean_object*);
lean_object* lean_uv_signal_cancel(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_Signal_cancel___boxed(lean_object*, lean_object*);
static lean_object* _init_l___private_Std_Internal_UV_Signal_0__Std_Internal_UV_SignalImpl(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_Signal_mk_0interp(lean_interpreter_value* stack)
{
uint32_t v_signum_2_ = stack[0].m_num;
uint8_t v_repeating_3_ = stack[1].m_num;
lean_object* v_res_5_;
v_res_5_ = lean_uv_signal_mk(v_signum_2_, v_repeating_3_);
stack->m_obj
 = v_res_5_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_Signal_mk___boxed(lean_object* v_signum_6_, lean_object* v_repeating_7_, lean_object* v_a_00___x40___internal___hyg_8_){
_start:
{
uint32_t v_signum_boxed_9_; uint8_t v_repeating_boxed_10_; lean_object* v_res_11_; 
v_signum_boxed_9_ = lean_unbox_uint32(v_signum_6_);
lean_dec(v_signum_6_);
v_repeating_boxed_10_ = lean_unbox(v_repeating_7_);
v_res_11_ = lean_uv_signal_mk(v_signum_boxed_9_, v_repeating_boxed_10_);
return v_res_11_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_Signal_next_0interp(lean_interpreter_value* stack)
{
lean_object* v_signal_12_ = stack[0].m_obj;
lean_object* v_res_14_;
v_res_14_ = lean_uv_signal_next(v_signal_12_);
stack->m_obj
 = v_res_14_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_Signal_next___boxed(lean_object* v_signal_15_, lean_object* v_a_00___x40___internal___hyg_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lean_uv_signal_next(v_signal_15_);
lean_dec(v_signal_15_);
return v_res_17_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_Signal_stop_0interp(lean_interpreter_value* stack)
{
lean_object* v_signal_18_ = stack[0].m_obj;
lean_object* v_res_20_;
v_res_20_ = lean_uv_signal_stop(v_signal_18_);
stack->m_obj
 = v_res_20_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_Signal_stop___boxed(lean_object* v_signal_21_, lean_object* v_a_00___x40___internal___hyg_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lean_uv_signal_stop(v_signal_21_);
lean_dec(v_signal_21_);
return v_res_23_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_Signal_cancel_0interp(lean_interpreter_value* stack)
{
lean_object* v_signal_24_ = stack[0].m_obj;
lean_object* v_res_26_;
v_res_26_ = lean_uv_signal_cancel(v_signal_24_);
stack->m_obj
 = v_res_26_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_Signal_cancel___boxed(lean_object* v_signal_27_, lean_object* v_a_00___x40___internal___hyg_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = lean_uv_signal_cancel(v_signal_27_);
lean_dec(v_signal_27_);
return v_res_29_;
}
}
lean_object* runtime_initialize_Init_System_Promise(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt(uint8_t builtin);
lean_object* runtime_initialize_Std_Net(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_UV_Signal(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_System_Promise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Net(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Std_Internal_UV_Signal_0__Std_Internal_UV_SignalImpl = _init_l___private_Std_Internal_UV_Signal_0__Std_Internal_UV_SignalImpl();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_UV_Signal(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_Promise(uint8_t builtin);
lean_object* initialize_Init_Data_SInt(uint8_t builtin);
lean_object* initialize_Std_Net(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_UV_Signal(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_Promise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Net(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_UV_Signal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_UV_Signal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_UV_Signal(builtin);
}
#ifdef __cplusplus
}
#endif

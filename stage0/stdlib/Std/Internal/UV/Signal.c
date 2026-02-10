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
static lean_object* _init_l___private_Std_Internal_UV_Signal_0__Std_Internal_UV_SignalImpl() {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_Signal_mk___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
x_6 = lean_uv_signal_mk(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_Signal_next___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_signal_next(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_Signal_stop___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_signal_stop(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_Signal_cancel___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_signal_cancel(x_1);
lean_dec(x_1);
return x_3;
}
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
l___private_Std_Internal_UV_Signal_0__Std_Internal_UV_SignalImpl = _init_l___private_Std_Internal_UV_Signal_0__Std_Internal_UV_SignalImpl();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

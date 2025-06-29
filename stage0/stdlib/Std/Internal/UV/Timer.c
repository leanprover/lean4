// Lean compiler output
// Module: Std.Internal.UV.Timer
// Imports: Init.System.IO Init.System.Promise
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
LEAN_EXPORT lean_object* l_Std_Internal_UV_Timer_reset___boxed(lean_object*, lean_object*);
lean_object* lean_uv_timer_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_Timer_next___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_Timer_mk___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_timer_stop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_UV_Timer_0__Std_Internal_UV_TimerImpl;
lean_object* lean_uv_timer_reset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_Timer_stop___boxed(lean_object*, lean_object*);
lean_object* lean_uv_timer_mk(uint64_t, uint8_t, lean_object*);
static lean_object* _init_l___private_Std_Internal_UV_Timer_0__Std_Internal_UV_TimerImpl() {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_Timer_mk___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_uv_timer_mk(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_Timer_next___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_timer_next(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_Timer_reset___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_timer_reset(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_Timer_stop___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_timer_stop(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Init_System_Promise(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_UV_Timer(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Promise(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Std_Internal_UV_Timer_0__Std_Internal_UV_TimerImpl = _init_l___private_Std_Internal_UV_Timer_0__Std_Internal_UV_TimerImpl();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

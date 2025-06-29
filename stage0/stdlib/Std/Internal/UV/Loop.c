// Lean compiler output
// Module: Std.Internal.UV.Loop
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
LEAN_EXPORT lean_object* l_Std_Internal_UV_Loop_configure___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_Loop_alive___boxed(lean_object*);
lean_object* lean_uv_event_loop_configure(lean_object*, lean_object*);
lean_object* lean_uv_event_loop_alive(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_Loop_configure___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_event_loop_configure(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_Loop_alive___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_uv_event_loop_alive(x_1);
return x_2;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Init_System_Promise(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_UV_Loop(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Promise(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Std.Internal.UV.Loop
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
lean_object* lean_uv_event_loop_configure(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_Loop_configure___boxed(lean_object*, lean_object*);
uint8_t lean_uv_event_loop_alive();
LEAN_EXPORT lean_object* l_Std_Internal_UV_Loop_alive___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_Loop_configure___boxed(lean_object* v_options_3_, lean_object* v_a_00___x40___internal___hyg_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lean_uv_event_loop_configure(v_options_3_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_Loop_alive___boxed(lean_object* v_a_00___x40___internal___hyg_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = lean_uv_event_loop_alive();
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
lean_object* runtime_initialize_Init_System_Promise(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_UV_Loop(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_System_Promise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_UV_Loop(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_Promise(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_UV_Loop(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_Promise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_UV_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_UV_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_UV_Loop(builtin);
}
#ifdef __cplusplus
}
#endif

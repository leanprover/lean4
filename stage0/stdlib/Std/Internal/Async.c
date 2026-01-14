// Lean compiler output
// Module: Std.Internal.Async
// Imports: public import Std.Internal.Async.Basic public import Std.Internal.Async.ContextAsync public import Std.Internal.Async.Timer public import Std.Internal.Async.TCP public import Std.Internal.Async.UDP public import Std.Internal.Async.DNS public import Std.Internal.Async.Select public import Std.Internal.Async.Process public import Std.Internal.Async.System public import Std.Internal.Async.Signal public import Std.Internal.Async.IO
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
lean_object* initialize_Std_Internal_Async_Basic(uint8_t builtin);
lean_object* initialize_Std_Internal_Async_ContextAsync(uint8_t builtin);
lean_object* initialize_Std_Internal_Async_Timer(uint8_t builtin);
lean_object* initialize_Std_Internal_Async_TCP(uint8_t builtin);
lean_object* initialize_Std_Internal_Async_UDP(uint8_t builtin);
lean_object* initialize_Std_Internal_Async_DNS(uint8_t builtin);
lean_object* initialize_Std_Internal_Async_Select(uint8_t builtin);
lean_object* initialize_Std_Internal_Async_Process(uint8_t builtin);
lean_object* initialize_Std_Internal_Async_System(uint8_t builtin);
lean_object* initialize_Std_Internal_Async_Signal(uint8_t builtin);
lean_object* initialize_Std_Internal_Async_IO(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Async(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Async_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Async_ContextAsync(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Async_Timer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Async_TCP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Async_UDP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Async_DNS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Async_Select(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Async_Process(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Async_System(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Async_Signal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Async_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

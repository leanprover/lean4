// Lean compiler output
// Module: init.util
// Imports: init.data.string.basic
#include "runtime/lean.h"
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
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_dbgTrace(lean_object*, lean_object*, lean_object*);
lean_object* l_dbgSleep___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_dbgTraceIfShared___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_dbgSleep(lean_object*, uint32_t, lean_object*);
lean_object* l_unsafeCast___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_dbgTrace___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_dbgTraceIfShared(lean_object*, lean_object*, lean_object*);
lean_object* l_dbgTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_dbg_trace(x_2, x_3);
return x_4;
}
}
lean_object* l_dbgTraceIfShared___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_dbg_trace_if_shared(x_2, x_3);
return x_4;
}
}
lean_object* l_dbgSleep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
x_5 = lean_dbg_sleep(x_4, x_3);
return x_5;
}
}
lean_object* l_unsafeCast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = x_4;
return x_5;
}
}
lean_object* initialize_init_data_string_basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_init_util(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_string_basic(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif

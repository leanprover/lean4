// Lean compiler output
// Module: init.default
// Imports: init.core init.control.default init.data.basic init.coe init.wf init.data.default init.system.default init.util init.fix
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
lean_object* initialize_init_core(lean_object*);
lean_object* initialize_init_control_default(lean_object*);
lean_object* initialize_init_data_basic(lean_object*);
lean_object* initialize_init_coe(lean_object*);
lean_object* initialize_init_wf(lean_object*);
lean_object* initialize_init_data_default(lean_object*);
lean_object* initialize_init_system_default(lean_object*);
lean_object* initialize_init_util(lean_object*);
lean_object* initialize_init_fix(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_init_default(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_init_core(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_control_default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_coe(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_wf(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_system_default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_util(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_fix(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif

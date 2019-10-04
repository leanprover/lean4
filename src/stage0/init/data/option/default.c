// Lean compiler output
// Module: init.data.option.default
// Imports: init.data.option.basic init.data.option.basicaux init.data.option.instances
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
lean_object* initialize_init_data_option_basic(lean_object*);
lean_object* initialize_init_data_option_basicaux(lean_object*);
lean_object* initialize_init_data_option_instances(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_init_data_option_default(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_option_basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_option_basicaux(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_option_instances(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif

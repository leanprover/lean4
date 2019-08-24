// Lean compiler output
// Module: init.data.basic
// Imports: init.data.nat.basic init.data.fin.basic init.data.list.basic init.data.char.basic init.data.string.basic init.data.option.basic init.data.uint init.data.repr init.data.tostring
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
lean_object* initialize_init_data_nat_basic(lean_object*);
lean_object* initialize_init_data_fin_basic(lean_object*);
lean_object* initialize_init_data_list_basic(lean_object*);
lean_object* initialize_init_data_char_basic(lean_object*);
lean_object* initialize_init_data_string_basic(lean_object*);
lean_object* initialize_init_data_option_basic(lean_object*);
lean_object* initialize_init_data_uint(lean_object*);
lean_object* initialize_init_data_repr(lean_object*);
lean_object* initialize_init_data_tostring(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_init_data_basic(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_nat_basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_fin_basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_list_basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_char_basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_string_basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_option_basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_uint(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_repr(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_tostring(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif

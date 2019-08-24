// Lean compiler output
// Module: init.data.default
// Imports: init.data.basic init.data.nat.default init.data.char.default init.data.string.default init.data.list.default init.data.int.default init.data.array.default init.data.bytearray.default init.data.fin.default init.data.uint init.data.rbtree.default init.data.rbmap.default init.data.option.basic init.data.option.instances init.data.hashmap.default init.data.random
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
lean_object* initialize_init_data_basic(lean_object*);
lean_object* initialize_init_data_nat_default(lean_object*);
lean_object* initialize_init_data_char_default(lean_object*);
lean_object* initialize_init_data_string_default(lean_object*);
lean_object* initialize_init_data_list_default(lean_object*);
lean_object* initialize_init_data_int_default(lean_object*);
lean_object* initialize_init_data_array_default(lean_object*);
lean_object* initialize_init_data_bytearray_default(lean_object*);
lean_object* initialize_init_data_fin_default(lean_object*);
lean_object* initialize_init_data_uint(lean_object*);
lean_object* initialize_init_data_rbtree_default(lean_object*);
lean_object* initialize_init_data_rbmap_default(lean_object*);
lean_object* initialize_init_data_option_basic(lean_object*);
lean_object* initialize_init_data_option_instances(lean_object*);
lean_object* initialize_init_data_hashmap_default(lean_object*);
lean_object* initialize_init_data_random(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_init_data_default(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_nat_default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_char_default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_string_default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_list_default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_int_default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_array_default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_bytearray_default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_fin_default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_uint(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_rbtree_default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_rbmap_default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_option_basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_option_instances(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_hashmap_default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_random(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif

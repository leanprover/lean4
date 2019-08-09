// Lean compiler output
// Module: init.data.default
// Imports: init.data.basic init.data.nat.default init.data.char.default init.data.string.default init.data.list.default init.data.int.default init.data.array.default init.data.bytearray.default init.data.fin.default init.data.uint init.data.rbtree.default init.data.rbmap.default init.data.option.basic init.data.option.instances init.data.hashmap.default init.data.random
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* initialize_init_data_basic(obj*);
obj* initialize_init_data_nat_default(obj*);
obj* initialize_init_data_char_default(obj*);
obj* initialize_init_data_string_default(obj*);
obj* initialize_init_data_list_default(obj*);
obj* initialize_init_data_int_default(obj*);
obj* initialize_init_data_array_default(obj*);
obj* initialize_init_data_bytearray_default(obj*);
obj* initialize_init_data_fin_default(obj*);
obj* initialize_init_data_uint(obj*);
obj* initialize_init_data_rbtree_default(obj*);
obj* initialize_init_data_rbmap_default(obj*);
obj* initialize_init_data_option_basic(obj*);
obj* initialize_init_data_option_instances(obj*);
obj* initialize_init_data_hashmap_default(obj*);
obj* initialize_init_data_random(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_default(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_nat_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_char_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_string_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_list_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_int_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_array_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_bytearray_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_fin_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_uint(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_rbtree_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_rbmap_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_option_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_option_instances(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_hashmap_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_random(w);
if (io_result_is_error(w)) return w;
return w;
}

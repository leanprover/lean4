// Lean compiler output
// Module: init.data.basic
// Imports: init.data.nat.basic init.data.fin.basic init.data.list.basic init.data.char.basic init.data.string.basic init.data.option.basic init.data.uint init.data.ordering.basic init.data.repr init.data.tostring
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
obj* initialize_init_data_nat_basic(obj*);
obj* initialize_init_data_fin_basic(obj*);
obj* initialize_init_data_list_basic(obj*);
obj* initialize_init_data_char_basic(obj*);
obj* initialize_init_data_string_basic(obj*);
obj* initialize_init_data_option_basic(obj*);
obj* initialize_init_data_uint(obj*);
obj* initialize_init_data_ordering_basic(obj*);
obj* initialize_init_data_repr(obj*);
obj* initialize_init_data_tostring(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_basic(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_nat_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_fin_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_list_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_char_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_string_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_option_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_uint(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_ordering_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_repr(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_tostring(w);
if (io_result_is_error(w)) return w;
return w;
}

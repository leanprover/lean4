// Lean compiler output
// Module: init.data.basic
// Imports: init.data.nat.basic init.data.fin.basic init.data.list.basic init.data.char.basic init.data.string.basic init.data.option.basic init.data.uint init.data.ordering.basic init.data.repr init.data.to_string
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
void initialize_init_data_nat_basic();
void initialize_init_data_fin_basic();
void initialize_init_data_list_basic();
void initialize_init_data_char_basic();
void initialize_init_data_string_basic();
void initialize_init_data_option_basic();
void initialize_init_data_uint();
void initialize_init_data_ordering_basic();
void initialize_init_data_repr();
void initialize_init_data_to__string();
static bool _G_initialized = false;
void initialize_init_data_basic() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_nat_basic();
 initialize_init_data_fin_basic();
 initialize_init_data_list_basic();
 initialize_init_data_char_basic();
 initialize_init_data_string_basic();
 initialize_init_data_option_basic();
 initialize_init_data_uint();
 initialize_init_data_ordering_basic();
 initialize_init_data_repr();
 initialize_init_data_to__string();
}

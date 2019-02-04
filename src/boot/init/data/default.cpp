// Lean compiler output
// Module: init.data.default
// Imports: init.data.basic init.data.nat.default init.data.char.default init.data.string.default init.data.list.default init.data.int.default init.data.array.default init.data.fin.default init.data.uint init.data.ordering.default init.data.rbtree.default init.data.rbmap.default init.data.option.basic init.data.option.instances
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
void initialize_init_data_basic();
void initialize_init_data_nat_default();
void initialize_init_data_char_default();
void initialize_init_data_string_default();
void initialize_init_data_list_default();
void initialize_init_data_int_default();
void initialize_init_data_array_default();
void initialize_init_data_fin_default();
void initialize_init_data_uint();
void initialize_init_data_ordering_default();
void initialize_init_data_rbtree_default();
void initialize_init_data_rbmap_default();
void initialize_init_data_option_basic();
void initialize_init_data_option_instances();
static bool _G_initialized = false;
void initialize_init_data_default() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_basic();
 initialize_init_data_nat_default();
 initialize_init_data_char_default();
 initialize_init_data_string_default();
 initialize_init_data_list_default();
 initialize_init_data_int_default();
 initialize_init_data_array_default();
 initialize_init_data_fin_default();
 initialize_init_data_uint();
 initialize_init_data_ordering_default();
 initialize_init_data_rbtree_default();
 initialize_init_data_rbmap_default();
 initialize_init_data_option_basic();
 initialize_init_data_option_instances();
}

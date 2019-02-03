// Lean compiler output
// Module: init.data.list.default
// Imports: init.data.list.basic init.data.list.instances
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
void _l_initialize__l_s4_init_s4_data_s4_list_s5_basic();
void _l_initialize__l_s4_init_s4_data_s4_list_s9_instances();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_data_s4_list_s7_default() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_data_s4_list_s5_basic();
 _l_initialize__l_s4_init_s4_data_s4_list_s9_instances();
}

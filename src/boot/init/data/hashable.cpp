// Lean compiler output
// Module: init.data.hashable
// Imports: init.data.usize init.data.string.default
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#endif
void _l_initialize__l_s4_init_s4_data_s5_usize();
void _l_initialize__l_s4_init_s4_data_s6_string_s7_default();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_data_s8_hashable() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_data_s5_usize();
 _l_initialize__l_s4_init_s4_data_s6_string_s7_default();
}

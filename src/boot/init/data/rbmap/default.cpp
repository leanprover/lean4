// Lean compiler output
// Module: init.data.rbmap.default
// Imports: init.data.rbtree.default init.data.rbmap.basic
#include "runtime/object.h"
#include "runtime/apply.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#endif
void _l_initialize__l_s4_init_s4_data_s6_rbtree_s7_default();
void _l_initialize__l_s4_init_s4_data_s5_rbmap_s5_basic();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_data_s5_rbmap_s7_default() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_data_s6_rbtree_s7_default();
 _l_initialize__l_s4_init_s4_data_s5_rbmap_s5_basic();
}

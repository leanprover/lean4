// Lean compiler output
// Module: init.wf
// Imports: init.data.nat.basic
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#endif
void _l_initialize__l_s4_init_s4_data_s3_nat_s5_basic();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s2_wf() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_data_s3_nat_s5_basic();
}

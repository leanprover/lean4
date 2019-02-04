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
#pragma clang diagnostic ignored "-Wunused-label"
#endif
void initialize_init_data_nat_basic();
static bool _G_initialized = false;
void initialize_init_wf() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_nat_basic();
}

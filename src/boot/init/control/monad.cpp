// Lean compiler output
// Module: init.control.monad
// Imports: init.control.applicative
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#endif
void _l_initialize__l_s4_init_s7_control_s11_applicative();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s7_control_s5_monad() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s7_control_s11_applicative();
}

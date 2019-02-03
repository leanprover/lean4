// Lean compiler output
// Module: init.control.default
// Imports: init.control.applicative init.control.functor init.control.alternative init.control.monad init.control.lift init.control.state init.control.id init.control.except init.control.reader init.control.option
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
void _l_initialize__l_s4_init_s7_control_s11_applicative();
void _l_initialize__l_s4_init_s7_control_s7_functor();
void _l_initialize__l_s4_init_s7_control_s11_alternative();
void _l_initialize__l_s4_init_s7_control_s5_monad();
void _l_initialize__l_s4_init_s7_control_s4_lift();
void _l_initialize__l_s4_init_s7_control_s5_state();
void _l_initialize__l_s4_init_s7_control_s2_id();
void _l_initialize__l_s4_init_s7_control_s6_except();
void _l_initialize__l_s4_init_s7_control_s6_reader();
void _l_initialize__l_s4_init_s7_control_s6_option();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s7_control_s7_default() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s7_control_s11_applicative();
 _l_initialize__l_s4_init_s7_control_s7_functor();
 _l_initialize__l_s4_init_s7_control_s11_alternative();
 _l_initialize__l_s4_init_s7_control_s5_monad();
 _l_initialize__l_s4_init_s7_control_s4_lift();
 _l_initialize__l_s4_init_s7_control_s5_state();
 _l_initialize__l_s4_init_s7_control_s2_id();
 _l_initialize__l_s4_init_s7_control_s6_except();
 _l_initialize__l_s4_init_s7_control_s6_reader();
 _l_initialize__l_s4_init_s7_control_s6_option();
}

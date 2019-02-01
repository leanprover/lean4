// Lean compiler output
// Module: init.platform
// Imports: init.core
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#endif
obj* _l_s6_system_s8_platform_s5_nbits;
obj* _init__l_s6_system_s8_platform_s5_nbits() {
{
obj* x_0; 
x_0 = lean::mk_nat_obj(64u);
return x_0;
}
}
void _l_initialize__l_s4_init_s4_core();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s8_platform() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_core();
 _l_s6_system_s8_platform_s5_nbits = _init__l_s6_system_s8_platform_s5_nbits();
}

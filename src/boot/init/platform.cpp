// Lean compiler output
// Module: init.platform
// Imports: init.core
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* l_system_platform_nbits;
obj* _init_l_system_platform_nbits() {
_start:
{
obj* x_0; 
x_0 = lean::mk_nat_obj(64u);
return x_0;
}
}
void initialize_init_core();
static bool _G_initialized = false;
void initialize_init_platform() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_core();
 l_system_platform_nbits = _init_l_system_platform_nbits();
}

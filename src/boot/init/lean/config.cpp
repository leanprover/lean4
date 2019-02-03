// Lean compiler output
// Module: init.lean.config
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
obj* _l_s4_lean_s18_closure__max__args;
obj* _init__l_s4_lean_s18_closure__max__args(){
_start:
{
obj* x_0; 
x_0 = lean::mk_nat_obj(16u);
return x_0;
}
}
void _l_initialize__l_s4_init_s4_core();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_lean_s6_config() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_core();
 _l_s4_lean_s18_closure__max__args = _init__l_s4_lean_s18_closure__max__args();
}

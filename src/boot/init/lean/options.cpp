// Lean compiler output
// Module: init.lean.options
// Imports: init.lean.kvmap
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;
obj* _l_s4_lean_s7_options_s2_mk;
obj* _l_s4_lean_s7_options;
obj* _init__l_s4_lean_s7_options() {
{
obj* x_0;
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s4_lean_s7_options_s2_mk() {
{
obj* x_0;
x_0 = lean::box(0);
return x_0;
}
}
void _l_initialize__l_s4_init_s4_lean_s5_kvmap();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_lean_s7_options() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_lean_s5_kvmap();
 _l_s4_lean_s7_options = _init__l_s4_lean_s7_options();
 _l_s4_lean_s7_options_s2_mk = _init__l_s4_lean_s7_options_s2_mk();
}

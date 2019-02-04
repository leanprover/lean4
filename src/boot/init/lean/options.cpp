// Lean compiler output
// Module: init.lean.options
// Imports: init.lean.kvmap
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* l_lean_options_mk;
obj* l_lean_options;
obj* _init_l_lean_options() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_options_mk() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
void initialize_init_lean_kvmap();
static bool _G_initialized = false;
void initialize_init_lean_options() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_kvmap();
 l_lean_options = _init_l_lean_options();
 l_lean_options_mk = _init_l_lean_options_mk();
}

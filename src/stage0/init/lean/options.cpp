// Lean compiler output
// Module: init.lean.options
// Imports: init.lean.kvmap
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_lean_options_mk;
obj* _init_l_lean_options_mk() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* initialize_init_lean_kvmap(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_options(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
w = initialize_init_lean_kvmap(w);
 l_lean_options_mk = _init_l_lean_options_mk();
lean::mark_persistent(l_lean_options_mk);
return w;
}

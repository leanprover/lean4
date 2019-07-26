// Lean compiler output
// Module: init.lean.modulename
// Imports: init.lean.name
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
obj* l_Lean_ModuleName_Inhabited___closed__1;
obj* l_Lean_ModuleName_HasCoe(obj*);
obj* l_Lean_ModuleName_Inhabited;
obj* _init_l_Lean_ModuleName_Inhabited___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_ModuleName_Inhabited() {
_start:
{
obj* x_1; 
x_1 = l_Lean_ModuleName_Inhabited___closed__1;
return x_1;
}
}
obj* l_Lean_ModuleName_HasCoe(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* initialize_init_lean_name(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_modulename(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_name(w);
if (io_result_is_error(w)) return w;
l_Lean_ModuleName_Inhabited___closed__1 = _init_l_Lean_ModuleName_Inhabited___closed__1();
lean::mark_persistent(l_Lean_ModuleName_Inhabited___closed__1);
l_Lean_ModuleName_Inhabited = _init_l_Lean_ModuleName_Inhabited();
lean::mark_persistent(l_Lean_ModuleName_Inhabited);
return w;
}

// Lean compiler output
// Module: init.lean.util
// Imports: init.lean.position init.io
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
obj* l_lean_profileit__pure(obj*);
extern "C" obj* lean_lean_profileit(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_profileit___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_profileit__pure___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_io_lazy__pure___rarg(obj*, obj*);
obj* l_lean_profileit__pure___boxed(obj*);
obj* l_lean_profileit__pure___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_profileit___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean_lean_profileit(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_lean_profileit__pure___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_io_lazy__pure___rarg), 2, 1);
lean::closure_set(x_4, 0, x_2);
x_5 = lean_lean_profileit(lean::box(0), x_0, x_1, x_4, x_3);
return x_5;
}
}
obj* l_lean_profileit__pure(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_profileit__pure___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_lean_profileit__pure___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_profileit__pure___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_profileit__pure___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_profileit__pure(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* initialize_init_lean_position(obj*);
obj* initialize_init_io(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_util(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_position(w);
if (io_result_is_error(w)) return w;
w = initialize_init_io(w);
return w;
}

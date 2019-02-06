// Lean compiler output
// Module: init.control.functor
// Imports: init.core init.function
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
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
obj* l_functor_map__rev___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_functor_map__rev(obj*);
obj* l_functor_map__const__rev___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_functor_map__const__rev(obj*);
obj* l_functor_map__const__rev___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_10; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_4, x_3);
return x_10;
}
}
obj* l_functor_map__const__rev(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_functor_map__const__rev___rarg), 5, 0);
return x_2;
}
}
obj* l_functor_map__rev___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_10; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_4, x_3);
return x_10;
}
}
obj* l_functor_map__rev(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_functor_map__rev___rarg), 5, 0);
return x_2;
}
}
void initialize_init_core();
void initialize_init_function();
static bool _G_initialized = false;
void initialize_init_control_functor() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_core();
 initialize_init_function();
}

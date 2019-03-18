// Lean compiler output
// Module: init.control.functor
// Imports: init.core init.function
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
obj* l_functor_map__const__rev___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_functor_map__rev___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_functor_map__rev(obj*);
obj* l_functor_map__rev___boxed(obj*);
obj* l_functor_map__rev___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_functor_map__const__rev___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_functor_map__const__rev(obj*);
obj* l_functor_map__const__rev___boxed(obj*);
obj* l_functor_map__const__rev___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_4, x_3);
return x_8;
}
}
obj* l_functor_map__const__rev(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_functor_map__const__rev___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_functor_map__const__rev___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_functor_map__const__rev___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_functor_map__const__rev___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_functor_map__const__rev(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_functor_map__rev___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_4, x_3);
return x_8;
}
}
obj* l_functor_map__rev(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_functor_map__rev___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_functor_map__rev___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_functor_map__rev___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_functor_map__rev___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_functor_map__rev(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* initialize_init_core(obj*);
obj* initialize_init_function(obj*);
static bool _G_initialized = false;
obj* initialize_init_control_functor(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_core(w);
if (io_result_is_error(w)) return w;
w = initialize_init_function(w);
return w;
}

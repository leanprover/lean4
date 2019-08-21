// Lean compiler output
// Module: init.control.functor
// Imports: init.core
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
obj* l_Functor_mapRev___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Functor_mapConstRev___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Functor_mapConstRev(obj*);
obj* l_Functor_mapRev(obj*);
obj* l_Functor_mapConstRev___boxed(obj*);
obj* l_Functor_mapRev___boxed(obj*);
obj* l_Functor_mapConstRev___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_5, x_4);
return x_7;
}
}
obj* l_Functor_mapConstRev(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Functor_mapConstRev___rarg), 5, 0);
return x_2;
}
}
obj* l_Functor_mapConstRev___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Functor_mapConstRev(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Functor_mapRev___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_5, x_4);
return x_7;
}
}
obj* l_Functor_mapRev(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Functor_mapRev___rarg), 5, 0);
return x_2;
}
}
obj* l_Functor_mapRev___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Functor_mapRev(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* initialize_init_core(obj*);
static bool _G_initialized = false;
obj* initialize_init_control_functor(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_core(w);
if (lean::io_result_is_error(w)) return w;
return w;
}

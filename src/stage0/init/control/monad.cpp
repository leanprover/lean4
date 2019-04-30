// Lean compiler output
// Module: init.control.monad
// Imports: init.control.applicative
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
obj* l_mcomp___boxed(obj*, obj*, obj*, obj*);
obj* l_monadInhabited_x_27___rarg(obj*);
obj* l_monadInhabited___rarg(obj*, obj*);
obj* l_monadInhabited(obj*, obj*);
obj* l_mcomp(obj*, obj*, obj*, obj*);
obj* l_monadInhabited_x_27___boxed(obj*, obj*);
obj* l_mcomp___rarg(obj*, obj*, obj*, obj*);
obj* l_monadInhabited___boxed(obj*, obj*);
obj* l_monadInhabited_x_27(obj*, obj*);
obj* l_mcomp___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::apply_4(x_0, lean::box(0), lean::box(0), x_4, x_2);
return x_5;
}
}
obj* l_mcomp(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_mcomp___rarg), 4, 0);
return x_4;
}
}
obj* l_mcomp___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_mcomp(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_monadInhabited___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::apply_2(x_5, lean::box(0), x_1);
return x_8;
}
}
obj* l_monadInhabited(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_monadInhabited___rarg), 2, 0);
return x_2;
}
}
obj* l_monadInhabited___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_monadInhabited(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_monadInhabited_x_27___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_4; obj* x_7; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::apply_1(x_4, lean::box(0));
return x_7;
}
}
obj* l_monadInhabited_x_27(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_monadInhabited_x_27___rarg), 1, 0);
return x_2;
}
}
obj* l_monadInhabited_x_27___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_monadInhabited_x_27(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* initialize_init_control_applicative(obj*);
static bool _G_initialized = false;
obj* initialize_init_control_monad(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_control_applicative(w);
if (io_result_is_error(w)) return w;
return w;
}

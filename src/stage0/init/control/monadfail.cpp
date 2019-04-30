// Lean compiler output
// Module: init.control.monadfail
// Imports: init.control.lift init.data.string.basic
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
obj* l_monadFailLift(obj*, obj*);
obj* l_matchFailed(obj*, obj*);
obj* l_matchFailed___boxed(obj*, obj*);
obj* l_monadFailLift___boxed(obj*, obj*);
obj* l_monadFailLift___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_matchFailed___rarg___closed__1;
obj* l_matchFailed___rarg(obj*);
obj* l_monadFailLift___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _init_l_matchFailed___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("match failed");
return x_0;
}
}
obj* l_matchFailed___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_matchFailed___rarg___closed__1;
x_2 = lean::apply_2(x_0, lean::box(0), x_1);
return x_2;
}
}
obj* l_matchFailed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_matchFailed___rarg), 1, 0);
return x_2;
}
}
obj* l_matchFailed___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_matchFailed(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_monadFailLift___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::apply_2(x_1, lean::box(0), x_4);
x_6 = lean::apply_2(x_0, lean::box(0), x_5);
return x_6;
}
}
obj* l_monadFailLift(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_monadFailLift___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_monadFailLift___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_monadFailLift___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_3);
return x_5;
}
}
obj* l_monadFailLift___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_monadFailLift(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* initialize_init_control_lift(obj*);
obj* initialize_init_data_string_basic(obj*);
static bool _G_initialized = false;
obj* initialize_init_control_monadfail(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_control_lift(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_string_basic(w);
if (io_result_is_error(w)) return w;
 l_matchFailed___rarg___closed__1 = _init_l_matchFailed___rarg___closed__1();
lean::mark_persistent(l_matchFailed___rarg___closed__1);
return w;
}

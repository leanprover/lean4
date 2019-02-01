// Lean compiler output
// Module: init.control.monad_fail
// Imports: init.control.lift init.data.string.basic
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#endif
obj* _l_s13_match__failed_s6___rarg_s11___closed__1;
obj* _l_s13_match__failed_s6___rarg(obj*);
obj* _l_s17_monad__fail__lift(obj*, obj*);
obj* _l_s13_match__failed(obj*, obj*);
obj* _l_s17_monad__fail__lift_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s13_match__failed_s6___rarg(obj* x_0) {
{
obj* x_1; obj* x_3; 
x_1 = _l_s13_match__failed_s6___rarg_s11___closed__1;
lean::inc(x_1);
x_3 = lean::apply_2(x_0, lean::box(0), x_1);
return x_3;
}
}
obj* _init__l_s13_match__failed_s6___rarg_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string("match failed");
return x_0;
}
}
obj* _l_s13_match__failed(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_match__failed_s6___rarg), 1, 0);
return x_4;
}
}
obj* _l_s17_monad__fail__lift_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_7; obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
x_7 = lean::apply_2(x_1, lean::box(0), x_4);
x_8 = lean::apply_2(x_0, lean::box(0), x_7);
return x_8;
}
}
obj* _l_s17_monad__fail__lift(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s17_monad__fail__lift_s6___rarg), 5, 0);
return x_4;
}
}
void _l_initialize__l_s4_init_s7_control_s4_lift();
void _l_initialize__l_s4_init_s4_data_s6_string_s5_basic();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s7_control_s11_monad__fail() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s7_control_s4_lift();
 _l_initialize__l_s4_init_s4_data_s6_string_s5_basic();
 _l_s13_match__failed_s6___rarg_s11___closed__1 = _init__l_s13_match__failed_s6___rarg_s11___closed__1();
}

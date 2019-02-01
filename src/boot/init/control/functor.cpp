// Lean compiler output
// Module: init.control.functor
// Imports: init.core init.function
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#endif
obj* _l_s7_functor_s8_map__rev_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s7_functor_s8_map__rev(obj*);
obj* _l_s7_functor_s15_map__const__rev_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s7_functor_s15_map__const__rev(obj*);
obj* _l_s7_functor_s15_map__const__rev_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* _l_s7_functor_s15_map__const__rev(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s7_functor_s15_map__const__rev_s6___rarg), 5, 0);
return x_2;
}
}
obj* _l_s7_functor_s8_map__rev_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* _l_s7_functor_s8_map__rev(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s7_functor_s8_map__rev_s6___rarg), 5, 0);
return x_2;
}
}
void _l_initialize__l_s4_init_s4_core();
void _l_initialize__l_s4_init_s8_function();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s7_control_s7_functor() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_core();
 _l_initialize__l_s4_init_s8_function();
}

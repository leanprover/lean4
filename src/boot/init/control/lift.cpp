// Lean compiler output
// Module: init.control.lift
// Imports: init.function init.coe init.control.monad
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* l_monad__functor__t__refl(obj*, obj*, obj*);
obj* l_has__monad__lift__t__refl(obj*, obj*);
obj* l_monad__functor__t__trans___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_has__monad__lift__to__has__coe(obj*, obj*);
obj* l_has__monad__lift__t__trans___rarg(obj*, obj*, obj*, obj*);
obj* l_has__monad__lift__to__has__coe___rarg(obj*, obj*);
obj* l_monad__functor__t__trans(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_monad__functor__t__refl___rarg(obj*, obj*);
obj* l_has__monad__lift__t__refl___rarg(obj*);
obj* l_has__monad__lift__t__trans(obj*, obj*, obj*);
obj* l_monad__functor__t__trans___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_has__monad__lift__to__has__coe___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::apply_1(x_0, lean::box(0));
return x_3;
}
}
obj* l_has__monad__lift__to__has__coe(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_has__monad__lift__to__has__coe___rarg), 2, 0);
return x_4;
}
}
obj* l_has__monad__lift__t__trans___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; 
lean::dec(x_2);
x_5 = lean::apply_2(x_1, lean::box(0), x_3);
x_6 = lean::apply_2(x_0, lean::box(0), x_5);
return x_6;
}
}
obj* l_has__monad__lift__t__trans(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_has__monad__lift__t__trans___rarg), 4, 0);
return x_6;
}
}
obj* l_has__monad__lift__t__refl___rarg(obj* x_0) {
_start:
{
return x_0;
}
}
obj* l_has__monad__lift__t__refl(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_has__monad__lift__t__refl___rarg), 1, 0);
return x_4;
}
}
obj* l_monad__functor__t__trans___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; 
lean::dec(x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__functor__t__trans___rarg___lambda__1), 4, 2);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_3);
x_7 = lean::apply_3(x_0, lean::box(0), x_6, x_4);
return x_7;
}
}
obj* l_monad__functor__t__trans___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::dec(x_2);
x_5 = lean::apply_3(x_0, lean::box(0), x_1, x_3);
return x_5;
}
}
obj* l_monad__functor__t__trans(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_12; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__functor__t__trans___rarg), 5, 0);
return x_12;
}
}
obj* l_monad__functor__t__refl___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_2(x_0, lean::box(0), x_1);
return x_2;
}
}
obj* l_monad__functor__t__refl(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__functor__t__refl___rarg), 2, 0);
return x_6;
}
}
void initialize_init_function();
void initialize_init_coe();
void initialize_init_control_monad();
static bool _G_initialized = false;
void initialize_init_control_lift() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_function();
 initialize_init_coe();
 initialize_init_control_monad();
}

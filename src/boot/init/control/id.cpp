// Lean compiler output
// Module: init.control.id
// Imports: init.control.lift
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
obj* l_id_run(obj*);
obj* l_id_monad___lambda__1(obj*, obj*, obj*, obj*);
obj* l_id_bind___rarg(obj*, obj*);
obj* l_id_bind(obj*, obj*);
obj* l_id(obj*);
obj* l_id_monad;
obj* l_id_run___rarg(obj*);
obj* l_id_monad___lambda__3(obj*, obj*, obj*, obj*);
obj* l_id_monad__run;
obj* l_id_monad___lambda__2(obj*, obj*, obj*, obj*);
obj* l_id_bind___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_1, x_0);
return x_2;
}
}
obj* l_id_bind(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___rarg), 2, 0);
return x_4;
}
}
obj* _init_l_id_monad() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* l_id_monad___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; 
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::apply_1(x_2, x_3);
return x_6;
}
}
obj* l_id_monad___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
lean::dec(x_3);
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_id_monad___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
return x_3;
}
}
obj* l_id_run___rarg(obj* x_0) {
_start:
{
return x_0;
}
}
obj* l_id_run(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_id_run___rarg), 1, 0);
return x_2;
}
}
obj* _init_l_id_monad__run() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_run), 1, 0);
return x_0;
}
}
void initialize_init_control_lift();
static bool _G_initialized = false;
void initialize_init_control_id() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_control_lift();
 l_id_monad = _init_l_id_monad();
 l_id_monad__run = _init_l_id_monad__run();
}

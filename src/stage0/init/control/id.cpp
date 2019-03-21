// Lean compiler output
// Module: init.control.id
// Imports: init.control.lift
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
obj* l_id___boxed(obj*);
obj* l_id_run___boxed(obj*);
obj* l_id_run(obj*);
obj* l_id_Monad___lambda__3(obj*, obj*, obj*, obj*);
obj* l_id_bind___rarg(obj*, obj*);
obj* l_id_Monad___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_id_bind(obj*, obj*);
obj* l_id_MonadRun;
obj* l_id_run___rarg(obj*);
obj* l_id_run___rarg___boxed(obj*);
obj* l_id_Monad___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_id_Monad___lambda__1(obj*, obj*, obj*, obj*);
obj* l_id_Monad___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_id_bind___boxed(obj*, obj*);
obj* l_id_Monad;
obj* l_id_Monad___lambda__2(obj*, obj*, obj*, obj*);
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
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___rarg), 2, 0);
return x_2;
}
}
obj* l_id_bind___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_id_bind(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_id_Monad___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::apply_1(x_2, x_3);
return x_4;
}
}
obj* l_id_Monad___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
lean::inc(x_2);
return x_2;
}
}
obj* l_id_Monad___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
lean::inc(x_3);
return x_3;
}
}
obj* _init_l_id_Monad() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_Monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_Monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_Monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* l_id_Monad___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_id_Monad___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_id_Monad___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_id_Monad___lambda__2(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_id_Monad___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_id_Monad___lambda__3(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_id_run___rarg(obj* x_0) {
_start:
{
lean::inc(x_0);
return x_0;
}
}
obj* l_id_run(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_run___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_id_run___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_id_run___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_id_run___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_id_run(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_id_MonadRun() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_run___boxed), 1, 0);
return x_0;
}
}
obj* initialize_init_control_lift(obj*);
static bool _G_initialized = false;
obj* initialize_init_control_id(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_control_lift(w);
 l_id_Monad = _init_l_id_Monad();
lean::mark_persistent(l_id_Monad);
 l_id_MonadRun = _init_l_id_MonadRun();
lean::mark_persistent(l_id_MonadRun);
return w;
}

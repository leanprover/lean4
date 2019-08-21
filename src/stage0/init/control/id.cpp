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
obj* l_Id_run___rarg(obj*);
obj* l_Id_Monad___closed__5;
obj* l_Id_pure___rarg(obj*);
obj* l_Id_MonadRun___closed__1;
obj* l_Id_pure___rarg___boxed(obj*);
obj* l_Id_Monad___closed__9;
obj* l_Id_Monad___closed__7;
obj* l_Id_Monad___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Id_pure(obj*);
obj* l_Id_bind(obj*, obj*);
obj* l_Id_Monad;
obj* l_Id_Monad___closed__3;
obj* l_Id_MonadRun;
obj* l_Id_run___rarg___boxed(obj*);
obj* l_Id_Monad___lambda__2(obj*, obj*, obj*, obj*);
obj* l_Id_Monad___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Id_Monad___closed__1;
obj* l_Id_bind___rarg(obj*, obj*);
obj* l_Id_map___rarg(obj*, obj*);
obj* l_Id_Monad___closed__6;
obj* l_Id_Monad___closed__4;
obj* l_Id_Monad___closed__2;
obj* l_Id_Monad___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_Id_map(obj*, obj*);
obj* l_Id_Monad___closed__8;
obj* l_Id_Monad___lambda__3(obj*, obj*, obj*, obj*);
obj* l_Id_run(obj*);
obj* l_Id_pure___rarg(obj* x_1) {
_start:
{
lean::inc(x_1);
return x_1;
}
}
obj* l_Id_pure(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_pure___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Id_pure___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Id_pure___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Id_bind___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_1(x_2, x_1);
return x_3;
}
}
obj* l_Id_bind(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_bind___rarg), 2, 0);
return x_3;
}
}
obj* l_Id_map___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_1(x_1, x_2);
return x_3;
}
}
obj* l_Id_map(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_map___rarg), 2, 0);
return x_3;
}
}
obj* l_Id_Monad___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::inc(x_3);
return x_3;
}
}
obj* l_Id_Monad___lambda__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::apply_1(x_3, x_4);
return x_5;
}
}
obj* l_Id_Monad___lambda__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::inc(x_4);
return x_4;
}
}
obj* _init_l_Id_Monad___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_map), 2, 0);
return x_1;
}
}
obj* _init_l_Id_Monad___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__1___boxed), 4, 0);
return x_1;
}
}
obj* _init_l_Id_Monad___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Id_Monad___closed__1;
x_2 = l_Id_Monad___closed__2;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Id_Monad___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_pure), 1, 0);
return x_1;
}
}
obj* _init_l_Id_Monad___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__2), 4, 0);
return x_1;
}
}
obj* _init_l_Id_Monad___closed__6() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__3___boxed), 4, 0);
return x_1;
}
}
obj* _init_l_Id_Monad___closed__7() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = l_Id_Monad___closed__3;
x_2 = l_Id_Monad___closed__4;
x_3 = l_Id_Monad___closed__5;
x_4 = l_Id_Monad___closed__2;
x_5 = l_Id_Monad___closed__6;
x_6 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_4);
lean::cnstr_set(x_6, 4, x_5);
return x_6;
}
}
obj* _init_l_Id_Monad___closed__8() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_bind), 2, 0);
return x_1;
}
}
obj* _init_l_Id_Monad___closed__9() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Id_Monad___closed__7;
x_2 = l_Id_Monad___closed__8;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Id_Monad() {
_start:
{
obj* x_1; 
x_1 = l_Id_Monad___closed__9;
return x_1;
}
}
obj* l_Id_Monad___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Id_Monad___lambda__1(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_Id_Monad___lambda__3___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Id_Monad___lambda__3(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_Id_run___rarg(obj* x_1) {
_start:
{
lean::inc(x_1);
return x_1;
}
}
obj* l_Id_run(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_run___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Id_run___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Id_run___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Id_MonadRun___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_run), 1, 0);
return x_1;
}
}
obj* _init_l_Id_MonadRun() {
_start:
{
obj* x_1; 
x_1 = l_Id_MonadRun___closed__1;
return x_1;
}
}
obj* initialize_init_control_lift(obj*);
static bool _G_initialized = false;
obj* initialize_init_control_id(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_control_lift(w);
if (lean::io_result_is_error(w)) return w;
l_Id_Monad___closed__1 = _init_l_Id_Monad___closed__1();
lean::mark_persistent(l_Id_Monad___closed__1);
l_Id_Monad___closed__2 = _init_l_Id_Monad___closed__2();
lean::mark_persistent(l_Id_Monad___closed__2);
l_Id_Monad___closed__3 = _init_l_Id_Monad___closed__3();
lean::mark_persistent(l_Id_Monad___closed__3);
l_Id_Monad___closed__4 = _init_l_Id_Monad___closed__4();
lean::mark_persistent(l_Id_Monad___closed__4);
l_Id_Monad___closed__5 = _init_l_Id_Monad___closed__5();
lean::mark_persistent(l_Id_Monad___closed__5);
l_Id_Monad___closed__6 = _init_l_Id_Monad___closed__6();
lean::mark_persistent(l_Id_Monad___closed__6);
l_Id_Monad___closed__7 = _init_l_Id_Monad___closed__7();
lean::mark_persistent(l_Id_Monad___closed__7);
l_Id_Monad___closed__8 = _init_l_Id_Monad___closed__8();
lean::mark_persistent(l_Id_Monad___closed__8);
l_Id_Monad___closed__9 = _init_l_Id_Monad___closed__9();
lean::mark_persistent(l_Id_Monad___closed__9);
l_Id_Monad = _init_l_Id_Monad();
lean::mark_persistent(l_Id_Monad);
l_Id_MonadRun___closed__1 = _init_l_Id_MonadRun___closed__1();
lean::mark_persistent(l_Id_MonadRun___closed__1);
l_Id_MonadRun = _init_l_Id_MonadRun();
lean::mark_persistent(l_Id_MonadRun);
return w;
}

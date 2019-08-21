// Lean compiler output
// Module: init.control.lift
// Imports: init.coe init.control.monad
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
obj* l_hasMonadLiftToHasCoe___elambda__1___rarg(obj*, obj*);
obj* l_hasMonadLiftToHasCoe___elambda__1___boxed(obj*, obj*, obj*);
obj* l_monadFunctorTTrans(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_hasMonadLiftTRefl___rarg(obj*);
obj* l_hasMonadLiftToHasCoe___boxed(obj*, obj*);
obj* l_hasMonadLiftTRefl___rarg___boxed(obj*);
obj* l_monadFunctorTTrans___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_monadFunctorTRefl___boxed(obj*, obj*, obj*);
obj* l_hasMonadLiftTTrans___rarg(obj*, obj*, obj*, obj*);
obj* l_hasMonadLiftTRefl___boxed(obj*, obj*);
obj* l_monadFunctorTRefl___rarg(obj*, obj*);
obj* l_hasMonadLiftToHasCoe___elambda__1(obj*, obj*, obj*);
obj* l_monadFunctorTRefl(obj*, obj*, obj*);
obj* l_hasMonadLiftTRefl(obj*, obj*);
obj* l_hasMonadLiftTTrans(obj*, obj*, obj*);
obj* l_hasMonadLiftToHasCoe(obj*, obj*);
obj* l_hasMonadLiftTTrans___boxed(obj*, obj*, obj*);
obj* l_monadFunctorTTrans___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_hasMonadLiftToHasCoe___rarg(obj*, obj*);
obj* l_monadFunctorTTrans___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_hasMonadLiftToHasCoe___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_2(x_1, lean::box(0), x_2);
return x_3;
}
}
obj* l_hasMonadLiftToHasCoe___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_hasMonadLiftToHasCoe___elambda__1___rarg), 2, 0);
return x_4;
}
}
obj* l_hasMonadLiftToHasCoe___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_hasMonadLiftToHasCoe___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
return x_3;
}
}
obj* l_hasMonadLiftToHasCoe(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_hasMonadLiftToHasCoe___rarg), 2, 0);
return x_3;
}
}
obj* l_hasMonadLiftToHasCoe___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_hasMonadLiftToHasCoe___elambda__1(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_hasMonadLiftToHasCoe___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_hasMonadLiftToHasCoe(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_hasMonadLiftTTrans___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::apply_2(x_2, lean::box(0), x_4);
x_6 = lean::apply_2(x_1, lean::box(0), x_5);
return x_6;
}
}
obj* l_hasMonadLiftTTrans(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_hasMonadLiftTTrans___rarg), 4, 0);
return x_4;
}
}
obj* l_hasMonadLiftTTrans___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_hasMonadLiftTTrans(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_hasMonadLiftTRefl___rarg(obj* x_1) {
_start:
{
lean::inc(x_1);
return x_1;
}
}
obj* l_hasMonadLiftTRefl(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_hasMonadLiftTRefl___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_hasMonadLiftTRefl___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_hasMonadLiftTRefl___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_hasMonadLiftTRefl___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_hasMonadLiftTRefl(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_monadFunctorTTrans___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::apply_3(x_1, lean::box(0), x_2, x_4);
return x_5;
}
}
obj* l_monadFunctorTTrans___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_monadFunctorTTrans___rarg___lambda__1), 4, 2);
lean::closure_set(x_6, 0, x_2);
lean::closure_set(x_6, 1, x_4);
x_7 = lean::apply_3(x_1, lean::box(0), x_6, x_5);
return x_7;
}
}
obj* l_monadFunctorTTrans(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_monadFunctorTTrans___rarg), 5, 0);
return x_7;
}
}
obj* l_monadFunctorTTrans___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_monadFunctorTTrans(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
}
obj* l_monadFunctorTRefl___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_2(x_1, lean::box(0), x_2);
return x_3;
}
}
obj* l_monadFunctorTRefl(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_monadFunctorTRefl___rarg), 2, 0);
return x_4;
}
}
obj* l_monadFunctorTRefl___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_monadFunctorTRefl(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* initialize_init_coe(obj*);
obj* initialize_init_control_monad(obj*);
static bool _G_initialized = false;
obj* initialize_init_control_lift(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_coe(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_control_monad(w);
if (lean::io_result_is_error(w)) return w;
return w;
}

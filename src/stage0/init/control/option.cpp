// Lean compiler output
// Module: init.control.option
// Imports: init.control.alternative init.control.lift init.control.except
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
obj* l_option__t_bind__cont___at_option__t_monad___spec__7___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_alternative___rarg___lambda__3(obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__5___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_lift___boxed(obj*);
obj* l_option__t_alternative___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_monad__run___rarg(obj*, obj*, obj*);
obj* l_option__t_monad__run(obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__4(obj*);
obj* l_option__t_run(obj*, obj*);
obj* l_option__t_fail___rarg___boxed(obj*, obj*);
obj* l_option__t_alternative___rarg___lambda__6(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_monad__except(obj*);
obj* l_option__t_catch___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_option__t_alternative___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__2(obj*);
obj* l_option__t_run___rarg___boxed(obj*);
obj* l_option__t_monad__except___rarg___lambda__1(obj*, obj*, obj*);
obj* l_option__t_bind__cont___main___boxed(obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__6___boxed(obj*);
obj* l_option__t_catch___rarg(obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__4___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_monad___rarg___lambda__5___boxed(obj*, obj*, obj*);
obj* l_option__t_monad___rarg___lambda__3(obj*, obj*, obj*);
obj* l_option__t_has__monad__lift___rarg(obj*);
obj* l_option__t_has__monad__lift___boxed(obj*);
obj* l_option__t_bind___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__4(obj*);
obj* l_option__t_monad___boxed(obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__3___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__6___boxed(obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__6___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__4___boxed(obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__5___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_monad___rarg___lambda__8(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__7(obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_monad___rarg___lambda__6(obj*, obj*, obj*);
obj* l_option__t_catch___rarg___lambda__1(obj*, obj*, obj*);
obj* l_option__t_alternative___boxed(obj*);
obj* l_option__t_bind__cont___main(obj*);
obj* l_function_const___rarg___boxed(obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_monad___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_monad___rarg___lambda__8___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__7___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_function_comp___rarg(obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__1___boxed(obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__6(obj*);
obj* l_option__t_orelse(obj*);
obj* l_option__t_monad___rarg___lambda__7(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_alternative(obj*);
obj* l_option__t_monad__functor___rarg(obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__4___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_run___boxed(obj*, obj*);
obj* l_option__t_fail___rarg(obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__3___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__1(obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_monad___rarg___lambda__4(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__3___boxed(obj*);
obj* l_option__t_catch(obj*);
obj* l_option__t_monad___rarg___lambda__5(obj*, obj*, obj*);
obj* l_except__t_monad___rarg___lambda__8___boxed(obj*, obj*);
obj* l_option__t_lift(obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__5(obj*);
obj* l_option__t_bind__cont___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__5___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_monad___rarg(obj*);
obj* l_option__t_pure___rarg(obj*, obj*, obj*);
obj* l_option__t_lift___rarg___boxed(obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__2(obj*);
obj* l_option__t_monad(obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__5(obj*);
obj* l_option__t_pure(obj*);
obj* l_option__t_monad__except___rarg(obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__7(obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__3___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__4___boxed(obj*);
obj* l_option__t_has__monad__lift(obj*);
obj* l_option__t_catch___boxed(obj*);
obj* l_option__t_monad___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__5___boxed(obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_alternative___rarg___lambda__5(obj*, obj*, obj*);
obj* l_option__t_bind(obj*);
obj* l_option__t_fail(obj*);
obj* l_option__t_monad___rarg___lambda__7___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_monad__run___rarg___boxed(obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__7___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__2___boxed(obj*);
obj* l_option__t_monad__functor(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__3(obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__4___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_alternative___rarg___lambda__7___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__5___boxed(obj*);
obj* l_option__t_monad__map___rarg(obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__2___boxed(obj*);
obj* l_option__t_monad__except___boxed(obj*);
obj* l_option__t_alternative___rarg(obj*);
obj* l_option__t_bind__cont___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__3___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__3___boxed(obj*);
extern obj* l_optional___rarg___closed__1;
obj* l_option__t_bind__cont___at_option__t_alternative___spec__6___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_monad___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___boxed(obj*);
obj* l_option__t_pure___rarg___boxed(obj*, obj*, obj*);
obj* l_option__t_alternative___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_alternative___rarg___lambda__4___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_monad___rarg___lambda__4___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_monad__functor___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_alternative___rarg___lambda__7(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__7___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__1___boxed(obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__3(obj*);
obj* l_option__t_bind__cont___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_fail___boxed(obj*);
obj* l_option__t_alternative___rarg___lambda__4(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_alternative___rarg___lambda__6___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_monad__map(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_orelse___rarg(obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont(obj*);
obj* l_option__t_monad__run___boxed(obj*, obj*);
obj* l_option__t_monad__except___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_option__t_pure___boxed(obj*);
obj* l_option__t_orelse___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_option__t_orelse___boxed(obj*);
obj* l_option__t_alternative___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__1(obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__7___boxed(obj*);
obj* l_option__t_lift___rarg(obj*, obj*, obj*);
obj* l_option__t_run___rarg(obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__7___boxed(obj*);
obj* l_option__t_bind___boxed(obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_monad__map___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_orelse___rarg___lambda__1(obj*, obj*, obj*);
obj* l_option__t_monad___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_orelse___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__4___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__6(obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__5___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_run___rarg(obj* x_0) {
_start:
{
lean::inc(x_0);
return x_0;
}
}
obj* l_option__t_run(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_run___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_option__t_run___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option__t_run___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_option__t_run___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_option__t_run(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_option__t_bind__cont___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_9; obj* x_12; obj* x_13; 
lean::dec(x_3);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::box(0);
x_13 = lean::apply_2(x_9, lean::box(0), x_12);
return x_13;
}
else
{
obj* x_15; obj* x_18; 
lean::dec(x_0);
x_15 = lean::cnstr_get(x_4, 0);
lean::inc(x_15);
lean::dec(x_4);
x_18 = lean::apply_1(x_3, x_15);
return x_18;
}
}
}
obj* l_option__t_bind__cont___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___main___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_option__t_bind__cont___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_option__t_bind__cont___main___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_option__t_bind__cont___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option__t_bind__cont___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_option__t_bind__cont___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_9; obj* x_12; obj* x_13; 
lean::dec(x_3);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::box(0);
x_13 = lean::apply_2(x_9, lean::box(0), x_12);
return x_13;
}
else
{
obj* x_15; obj* x_18; 
lean::dec(x_0);
x_15 = lean::cnstr_get(x_4, 0);
lean::inc(x_15);
lean::dec(x_4);
x_18 = lean::apply_1(x_3, x_15);
return x_18;
}
}
}
obj* l_option__t_bind__cont(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_option__t_bind__cont___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_option__t_bind__cont___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_option__t_bind__cont___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option__t_bind__cont(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_option__t_bind___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___rarg___boxed), 5, 4);
lean::closure_set(x_7, 0, x_0);
lean::closure_set(x_7, 1, lean::box(0));
lean::closure_set(x_7, 2, lean::box(0));
lean::closure_set(x_7, 3, x_4);
x_8 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_3, x_7);
return x_8;
}
}
obj* l_option__t_bind(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_option__t_bind___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_option__t_bind___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_option__t_bind___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option__t_bind(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_option__t_pure___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_2);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
}
obj* l_option__t_pure(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_pure___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_option__t_pure___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_option__t_pure___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_option__t_pure___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option__t_pure(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_9; obj* x_12; obj* x_13; 
lean::dec(x_3);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::box(0);
x_13 = lean::apply_2(x_9, lean::box(0), x_12);
return x_13;
}
else
{
obj* x_15; obj* x_18; 
lean::dec(x_0);
x_15 = lean::cnstr_get(x_4, 0);
lean::inc(x_15);
lean::dec(x_4);
x_18 = lean::apply_1(x_3, x_15);
return x_18;
}
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_monad___spec__1___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_9; obj* x_12; obj* x_13; 
lean::dec(x_3);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::box(0);
x_13 = lean::apply_2(x_9, lean::box(0), x_12);
return x_13;
}
else
{
obj* x_15; obj* x_18; 
lean::dec(x_0);
x_15 = lean::cnstr_get(x_4, 0);
lean::inc(x_15);
lean::dec(x_4);
x_18 = lean::apply_1(x_3, x_15);
return x_18;
}
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_monad___spec__2___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_9; obj* x_12; obj* x_13; 
lean::dec(x_3);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::box(0);
x_13 = lean::apply_2(x_9, lean::box(0), x_12);
return x_13;
}
else
{
obj* x_15; obj* x_18; 
lean::dec(x_0);
x_15 = lean::cnstr_get(x_4, 0);
lean::inc(x_15);
lean::dec(x_4);
x_18 = lean::apply_1(x_3, x_15);
return x_18;
}
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_monad___spec__3___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_9; obj* x_12; obj* x_13; 
lean::dec(x_3);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::box(0);
x_13 = lean::apply_2(x_9, lean::box(0), x_12);
return x_13;
}
else
{
obj* x_15; obj* x_18; 
lean::dec(x_0);
x_15 = lean::cnstr_get(x_4, 0);
lean::inc(x_15);
lean::dec(x_4);
x_18 = lean::apply_1(x_3, x_15);
return x_18;
}
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__4(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_monad___spec__4___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_9; obj* x_12; obj* x_13; 
lean::dec(x_3);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::box(0);
x_13 = lean::apply_2(x_9, lean::box(0), x_12);
return x_13;
}
else
{
obj* x_15; obj* x_18; 
lean::dec(x_0);
x_15 = lean::cnstr_get(x_4, 0);
lean::inc(x_15);
lean::dec(x_4);
x_18 = lean::apply_1(x_3, x_15);
return x_18;
}
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__5(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_monad___spec__5___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_9; obj* x_12; obj* x_13; 
lean::dec(x_3);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::box(0);
x_13 = lean::apply_2(x_9, lean::box(0), x_12);
return x_13;
}
else
{
obj* x_15; obj* x_18; 
lean::dec(x_0);
x_15 = lean::cnstr_get(x_4, 0);
lean::inc(x_15);
lean::dec(x_4);
x_18 = lean::apply_1(x_3, x_15);
return x_18;
}
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__6(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_monad___spec__6___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__7___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_9; obj* x_12; obj* x_13; 
lean::dec(x_3);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::box(0);
x_13 = lean::apply_2(x_9, lean::box(0), x_12);
return x_13;
}
else
{
obj* x_15; obj* x_18; 
lean::dec(x_0);
x_15 = lean::cnstr_get(x_4, 0);
lean::inc(x_15);
lean::dec(x_4);
x_18 = lean::apply_1(x_3, x_15);
return x_18;
}
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__7(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_monad___spec__7___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_option__t_monad___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; 
lean::inc(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_pure___rarg___boxed), 3, 2);
lean::closure_set(x_6, 0, x_0);
lean::closure_set(x_6, 1, lean::box(0));
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_7, 0, x_6);
lean::closure_set(x_7, 1, x_3);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_monad___spec__1___rarg___boxed), 5, 4);
lean::closure_set(x_10, 0, x_0);
lean::closure_set(x_10, 1, lean::box(0));
lean::closure_set(x_10, 2, lean::box(0));
lean::closure_set(x_10, 3, x_7);
x_11 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_4, x_10);
return x_11;
}
}
obj* l_option__t_monad___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_function_const___rarg___boxed), 2, 1);
lean::closure_set(x_5, 0, x_3);
lean::inc(x_0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_pure___rarg___boxed), 3, 2);
lean::closure_set(x_7, 0, x_0);
lean::closure_set(x_7, 1, lean::box(0));
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_8, 0, x_7);
lean::closure_set(x_8, 1, x_5);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_monad___spec__2___rarg___boxed), 5, 4);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, lean::box(0));
lean::closure_set(x_11, 2, lean::box(0));
lean::closure_set(x_11, 3, x_8);
x_12 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_4, x_11);
return x_12;
}
}
obj* l_option__t_monad___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_9; 
lean::inc(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_pure___rarg___boxed), 3, 2);
lean::closure_set(x_4, 0, x_0);
lean::closure_set(x_4, 1, lean::box(0));
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_5, 0, x_4);
lean::closure_set(x_5, 1, x_2);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_monad___spec__3___rarg___boxed), 5, 4);
lean::closure_set(x_8, 0, x_0);
lean::closure_set(x_8, 1, lean::box(0));
lean::closure_set(x_8, 2, lean::box(0));
lean::closure_set(x_8, 3, x_5);
x_9 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_1, x_8);
return x_9;
}
}
obj* l_option__t_monad___rarg___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_10; 
lean::inc(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_monad___rarg___lambda__3), 3, 2);
lean::closure_set(x_6, 0, x_0);
lean::closure_set(x_6, 1, x_4);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_monad___spec__4___rarg___boxed), 5, 4);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, lean::box(0));
lean::closure_set(x_9, 2, lean::box(0));
lean::closure_set(x_9, 3, x_6);
x_10 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_3, x_9);
return x_10;
}
}
obj* l_option__t_monad___rarg___lambda__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_1);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
}
obj* l_option__t_monad___rarg___lambda__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
lean::inc(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_monad___rarg___lambda__5___boxed), 3, 2);
lean::closure_set(x_4, 0, x_0);
lean::closure_set(x_4, 1, x_2);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_monad___spec__5___rarg___boxed), 5, 4);
lean::closure_set(x_7, 0, x_0);
lean::closure_set(x_7, 1, lean::box(0));
lean::closure_set(x_7, 2, lean::box(0));
lean::closure_set(x_7, 3, x_4);
x_8 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_1, x_7);
return x_8;
}
}
obj* l_option__t_monad___rarg___lambda__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_10; 
lean::inc(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_monad___rarg___lambda__6), 3, 2);
lean::closure_set(x_6, 0, x_0);
lean::closure_set(x_6, 1, x_4);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_monad___spec__6___rarg___boxed), 5, 4);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, lean::box(0));
lean::closure_set(x_9, 2, lean::box(0));
lean::closure_set(x_9, 3, x_6);
x_10 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_3, x_9);
return x_10;
}
}
obj* l_option__t_monad___rarg___lambda__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_9; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_monad___rarg___lambda__8___boxed), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_monad___spec__7___rarg___boxed), 5, 4);
lean::closure_set(x_8, 0, x_0);
lean::closure_set(x_8, 1, lean::box(0));
lean::closure_set(x_8, 2, lean::box(0));
lean::closure_set(x_8, 3, x_5);
x_9 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_3, x_8);
return x_9;
}
}
obj* l_option__t_monad___rarg(obj* x_0) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_monad___rarg___lambda__1___boxed), 5, 1);
lean::closure_set(x_2, 0, x_0);
lean::inc(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_monad___rarg___lambda__2___boxed), 5, 1);
lean::closure_set(x_4, 0, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_4);
lean::inc(x_0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_pure___rarg___boxed), 3, 1);
lean::closure_set(x_7, 0, x_0);
lean::inc(x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_monad___rarg___lambda__4___boxed), 5, 1);
lean::closure_set(x_9, 0, x_0);
lean::inc(x_0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_monad___rarg___lambda__7___boxed), 5, 1);
lean::closure_set(x_11, 0, x_0);
lean::inc(x_0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_monad___rarg___lambda__8___boxed), 5, 1);
lean::closure_set(x_13, 0, x_0);
x_14 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_14, 0, x_5);
lean::cnstr_set(x_14, 1, x_7);
lean::cnstr_set(x_14, 2, x_9);
lean::cnstr_set(x_14, 3, x_11);
lean::cnstr_set(x_14, 4, x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind___rarg___boxed), 5, 1);
lean::closure_set(x_15, 0, x_0);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
obj* l_option__t_monad(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_monad___rarg), 1, 0);
return x_1;
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_option__t_bind__cont___at_option__t_monad___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option__t_bind__cont___at_option__t_monad___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_option__t_bind__cont___at_option__t_monad___spec__2___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option__t_bind__cont___at_option__t_monad___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__3___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_option__t_bind__cont___at_option__t_monad___spec__3___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option__t_bind__cont___at_option__t_monad___spec__3(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__4___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_option__t_bind__cont___at_option__t_monad___spec__4___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__4___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option__t_bind__cont___at_option__t_monad___spec__4(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__5___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_option__t_bind__cont___at_option__t_monad___spec__5___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__5___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option__t_bind__cont___at_option__t_monad___spec__5(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__6___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_option__t_bind__cont___at_option__t_monad___spec__6___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__6___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option__t_bind__cont___at_option__t_monad___spec__6(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__7___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_option__t_bind__cont___at_option__t_monad___spec__7___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__7___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option__t_bind__cont___at_option__t_monad___spec__7(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_option__t_monad___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_option__t_monad___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_option__t_monad___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_option__t_monad___rarg___lambda__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_option__t_monad___rarg___lambda__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_option__t_monad___rarg___lambda__4(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_option__t_monad___rarg___lambda__5___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_option__t_monad___rarg___lambda__5(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_option__t_monad___rarg___lambda__7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_option__t_monad___rarg___lambda__7(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_option__t_monad___rarg___lambda__8___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_option__t_monad___rarg___lambda__8(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_option__t_monad___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option__t_monad(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_option__t_orelse___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_1);
lean::inc(x_0);
return x_0;
}
else
{
obj* x_5; obj* x_8; obj* x_11; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::apply_2(x_8, lean::box(0), x_2);
return x_11;
}
}
}
obj* l_option__t_orelse___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_orelse___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_6, 0, x_3);
lean::closure_set(x_6, 1, x_0);
x_7 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_2, x_6);
return x_7;
}
}
obj* l_option__t_orelse(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_orelse___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_option__t_orelse___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_option__t_orelse___rarg___lambda__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_option__t_orelse___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_option__t_orelse___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_option__t_orelse___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option__t_orelse(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_option__t_fail___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::box(0);
x_9 = lean::apply_2(x_5, lean::box(0), x_8);
return x_9;
}
}
obj* l_option__t_fail(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_fail___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_option__t_fail___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_option__t_fail___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_option__t_fail___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option__t_fail(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_9; obj* x_12; obj* x_13; 
lean::dec(x_3);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::box(0);
x_13 = lean::apply_2(x_9, lean::box(0), x_12);
return x_13;
}
else
{
obj* x_15; obj* x_18; 
lean::dec(x_0);
x_15 = lean::cnstr_get(x_4, 0);
lean::inc(x_15);
lean::dec(x_4);
x_18 = lean::apply_1(x_3, x_15);
return x_18;
}
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_alternative___spec__1___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_9; obj* x_12; obj* x_13; 
lean::dec(x_3);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::box(0);
x_13 = lean::apply_2(x_9, lean::box(0), x_12);
return x_13;
}
else
{
obj* x_15; obj* x_18; 
lean::dec(x_0);
x_15 = lean::cnstr_get(x_4, 0);
lean::inc(x_15);
lean::dec(x_4);
x_18 = lean::apply_1(x_3, x_15);
return x_18;
}
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_alternative___spec__2___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_9; obj* x_12; obj* x_13; 
lean::dec(x_3);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::box(0);
x_13 = lean::apply_2(x_9, lean::box(0), x_12);
return x_13;
}
else
{
obj* x_15; obj* x_18; 
lean::dec(x_0);
x_15 = lean::cnstr_get(x_4, 0);
lean::inc(x_15);
lean::dec(x_4);
x_18 = lean::apply_1(x_3, x_15);
return x_18;
}
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_alternative___spec__3___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_9; obj* x_12; obj* x_13; 
lean::dec(x_3);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::box(0);
x_13 = lean::apply_2(x_9, lean::box(0), x_12);
return x_13;
}
else
{
obj* x_15; obj* x_18; 
lean::dec(x_0);
x_15 = lean::cnstr_get(x_4, 0);
lean::inc(x_15);
lean::dec(x_4);
x_18 = lean::apply_1(x_3, x_15);
return x_18;
}
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__4(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_alternative___spec__4___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_9; obj* x_12; obj* x_13; 
lean::dec(x_3);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::box(0);
x_13 = lean::apply_2(x_9, lean::box(0), x_12);
return x_13;
}
else
{
obj* x_15; obj* x_18; 
lean::dec(x_0);
x_15 = lean::cnstr_get(x_4, 0);
lean::inc(x_15);
lean::dec(x_4);
x_18 = lean::apply_1(x_3, x_15);
return x_18;
}
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__5(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_alternative___spec__5___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_9; obj* x_12; obj* x_13; 
lean::dec(x_3);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::box(0);
x_13 = lean::apply_2(x_9, lean::box(0), x_12);
return x_13;
}
else
{
obj* x_15; obj* x_18; 
lean::dec(x_0);
x_15 = lean::cnstr_get(x_4, 0);
lean::inc(x_15);
lean::dec(x_4);
x_18 = lean::apply_1(x_3, x_15);
return x_18;
}
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__6(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_alternative___spec__6___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__7___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_9; obj* x_12; obj* x_13; 
lean::dec(x_3);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::box(0);
x_13 = lean::apply_2(x_9, lean::box(0), x_12);
return x_13;
}
else
{
obj* x_15; obj* x_18; 
lean::dec(x_0);
x_15 = lean::cnstr_get(x_4, 0);
lean::inc(x_15);
lean::dec(x_4);
x_18 = lean::apply_1(x_3, x_15);
return x_18;
}
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__7(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_alternative___spec__7___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_option__t_alternative___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; 
lean::inc(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_pure___rarg___boxed), 3, 2);
lean::closure_set(x_6, 0, x_0);
lean::closure_set(x_6, 1, lean::box(0));
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_7, 0, x_6);
lean::closure_set(x_7, 1, x_3);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_alternative___spec__1___rarg___boxed), 5, 4);
lean::closure_set(x_10, 0, x_0);
lean::closure_set(x_10, 1, lean::box(0));
lean::closure_set(x_10, 2, lean::box(0));
lean::closure_set(x_10, 3, x_7);
x_11 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_4, x_10);
return x_11;
}
}
obj* l_option__t_alternative___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_function_const___rarg___boxed), 2, 1);
lean::closure_set(x_5, 0, x_3);
lean::inc(x_0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_pure___rarg___boxed), 3, 2);
lean::closure_set(x_7, 0, x_0);
lean::closure_set(x_7, 1, lean::box(0));
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_8, 0, x_7);
lean::closure_set(x_8, 1, x_5);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_alternative___spec__2___rarg___boxed), 5, 4);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, lean::box(0));
lean::closure_set(x_11, 2, lean::box(0));
lean::closure_set(x_11, 3, x_8);
x_12 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_4, x_11);
return x_12;
}
}
obj* l_option__t_alternative___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_9; 
lean::inc(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_pure___rarg___boxed), 3, 2);
lean::closure_set(x_4, 0, x_0);
lean::closure_set(x_4, 1, lean::box(0));
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_5, 0, x_4);
lean::closure_set(x_5, 1, x_2);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_alternative___spec__3___rarg___boxed), 5, 4);
lean::closure_set(x_8, 0, x_0);
lean::closure_set(x_8, 1, lean::box(0));
lean::closure_set(x_8, 2, lean::box(0));
lean::closure_set(x_8, 3, x_5);
x_9 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_1, x_8);
return x_9;
}
}
obj* l_option__t_alternative___rarg___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_10; 
lean::inc(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_alternative___rarg___lambda__3), 3, 2);
lean::closure_set(x_6, 0, x_0);
lean::closure_set(x_6, 1, x_4);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_alternative___spec__4___rarg___boxed), 5, 4);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, lean::box(0));
lean::closure_set(x_9, 2, lean::box(0));
lean::closure_set(x_9, 3, x_6);
x_10 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_3, x_9);
return x_10;
}
}
obj* l_option__t_alternative___rarg___lambda__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
lean::inc(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_monad___rarg___lambda__5___boxed), 3, 2);
lean::closure_set(x_4, 0, x_0);
lean::closure_set(x_4, 1, x_2);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_alternative___spec__5___rarg___boxed), 5, 4);
lean::closure_set(x_7, 0, x_0);
lean::closure_set(x_7, 1, lean::box(0));
lean::closure_set(x_7, 2, lean::box(0));
lean::closure_set(x_7, 3, x_4);
x_8 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_1, x_7);
return x_8;
}
}
obj* l_option__t_alternative___rarg___lambda__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_10; 
lean::inc(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_alternative___rarg___lambda__5), 3, 2);
lean::closure_set(x_6, 0, x_0);
lean::closure_set(x_6, 1, x_4);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_alternative___spec__6___rarg___boxed), 5, 4);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, lean::box(0));
lean::closure_set(x_9, 2, lean::box(0));
lean::closure_set(x_9, 3, x_6);
x_10 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_3, x_9);
return x_10;
}
}
obj* l_option__t_alternative___rarg___lambda__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_9; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_monad___rarg___lambda__8___boxed), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_alternative___spec__7___rarg___boxed), 5, 4);
lean::closure_set(x_8, 0, x_0);
lean::closure_set(x_8, 1, lean::box(0));
lean::closure_set(x_8, 2, lean::box(0));
lean::closure_set(x_8, 3, x_5);
x_9 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_3, x_8);
return x_9;
}
}
obj* l_option__t_alternative___rarg(obj* x_0) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_alternative___rarg___lambda__1___boxed), 5, 1);
lean::closure_set(x_2, 0, x_0);
lean::inc(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_alternative___rarg___lambda__2___boxed), 5, 1);
lean::closure_set(x_4, 0, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_4);
lean::inc(x_0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_pure___rarg___boxed), 3, 1);
lean::closure_set(x_7, 0, x_0);
lean::inc(x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_alternative___rarg___lambda__4___boxed), 5, 1);
lean::closure_set(x_9, 0, x_0);
lean::inc(x_0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_alternative___rarg___lambda__6___boxed), 5, 1);
lean::closure_set(x_11, 0, x_0);
lean::inc(x_0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_alternative___rarg___lambda__7___boxed), 5, 1);
lean::closure_set(x_13, 0, x_0);
x_14 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_14, 0, x_5);
lean::cnstr_set(x_14, 1, x_7);
lean::cnstr_set(x_14, 2, x_9);
lean::cnstr_set(x_14, 3, x_11);
lean::cnstr_set(x_14, 4, x_13);
lean::inc(x_0);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_orelse___rarg___boxed), 4, 1);
lean::closure_set(x_16, 0, x_0);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_fail___rarg___boxed), 2, 1);
lean::closure_set(x_17, 0, x_0);
x_18 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_18, 0, x_14);
lean::cnstr_set(x_18, 1, x_16);
lean::cnstr_set(x_18, 2, x_17);
return x_18;
}
}
obj* l_option__t_alternative(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_alternative___rarg), 1, 0);
return x_1;
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_option__t_bind__cont___at_option__t_alternative___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option__t_bind__cont___at_option__t_alternative___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_option__t_bind__cont___at_option__t_alternative___spec__2___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option__t_bind__cont___at_option__t_alternative___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__3___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_option__t_bind__cont___at_option__t_alternative___spec__3___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option__t_bind__cont___at_option__t_alternative___spec__3(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__4___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_option__t_bind__cont___at_option__t_alternative___spec__4___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__4___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option__t_bind__cont___at_option__t_alternative___spec__4(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__5___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_option__t_bind__cont___at_option__t_alternative___spec__5___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__5___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option__t_bind__cont___at_option__t_alternative___spec__5(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__6___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_option__t_bind__cont___at_option__t_alternative___spec__6___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__6___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option__t_bind__cont___at_option__t_alternative___spec__6(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__7___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_option__t_bind__cont___at_option__t_alternative___spec__7___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__7___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option__t_bind__cont___at_option__t_alternative___spec__7(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_option__t_alternative___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_option__t_alternative___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_option__t_alternative___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_option__t_alternative___rarg___lambda__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_option__t_alternative___rarg___lambda__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_option__t_alternative___rarg___lambda__4(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_option__t_alternative___rarg___lambda__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_option__t_alternative___rarg___lambda__6(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_option__t_alternative___rarg___lambda__7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_option__t_alternative___rarg___lambda__7(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_option__t_alternative___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option__t_alternative(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_option__t_lift___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; obj* x_12; obj* x_13; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_6, 0);
lean::inc(x_9);
lean::dec(x_6);
x_12 = l_optional___rarg___closed__1;
x_13 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_12, x_2);
return x_13;
}
}
obj* l_option__t_lift(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_lift___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_option__t_lift___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_option__t_lift___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_option__t_lift___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option__t_lift(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_option__t_has__monad__lift___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_lift___rarg___boxed), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_option__t_has__monad__lift(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_has__monad__lift___rarg), 1, 0);
return x_1;
}
}
obj* l_option__t_has__monad__lift___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option__t_has__monad__lift(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_option__t_monad__map___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_2(x_0, lean::box(0), x_1);
return x_2;
}
}
obj* l_option__t_monad__map(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_monad__map___rarg), 2, 0);
return x_5;
}
}
obj* l_option__t_monad__map___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_option__t_monad__map(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_option__t_monad__functor___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_2(x_0, lean::box(0), x_1);
return x_2;
}
}
obj* l_option__t_monad__functor(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_monad__functor___rarg), 2, 0);
return x_5;
}
}
obj* l_option__t_monad__functor___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_option__t_monad__functor(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_option__t_catch___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = lean::box(0);
x_5 = lean::apply_1(x_0, x_4);
return x_5;
}
else
{
obj* x_7; obj* x_9; obj* x_10; obj* x_13; obj* x_16; obj* x_17; 
lean::dec(x_0);
x_7 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 x_9 = x_2;
} else {
 lean::inc(x_7);
 lean::dec(x_2);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
lean::dec(x_1);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
if (lean::is_scalar(x_9)) {
 x_16 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_16 = x_9;
}
lean::cnstr_set(x_16, 0, x_7);
x_17 = lean::apply_2(x_13, lean::box(0), x_16);
return x_17;
}
}
}
obj* l_option__t_catch___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_catch___rarg___lambda__1), 3, 2);
lean::closure_set(x_6, 0, x_3);
lean::closure_set(x_6, 1, x_0);
x_7 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_2, x_6);
return x_7;
}
}
obj* l_option__t_catch(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_catch___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_option__t_catch___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_option__t_catch___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_option__t_catch___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option__t_catch(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_option__t_monad__except___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::box(0);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
}
obj* l_option__t_monad__except___rarg(obj* x_0) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_monad__except___rarg___lambda__1___boxed), 3, 1);
lean::closure_set(x_2, 0, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_catch___rarg___boxed), 4, 1);
lean::closure_set(x_3, 0, x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_option__t_monad__except(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_monad__except___rarg), 1, 0);
return x_1;
}
}
obj* l_option__t_monad__except___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_option__t_monad__except___rarg___lambda__1(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_option__t_monad__except___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option__t_monad__except(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_option__t_monad__run___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_2(x_0, lean::box(0), x_2);
return x_3;
}
}
obj* l_option__t_monad__run(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_monad__run___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_option__t_monad__run___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_option__t_monad__run___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_option__t_monad__run___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_option__t_monad__run(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* initialize_init_control_alternative(obj*);
obj* initialize_init_control_lift(obj*);
obj* initialize_init_control_except(obj*);
static bool _G_initialized = false;
obj* initialize_init_control_option(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
w = initialize_init_control_alternative(w);
w = initialize_init_control_lift(w);
w = initialize_init_control_except(w);
return w;
}

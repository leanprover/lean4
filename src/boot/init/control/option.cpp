// Lean compiler output
// Module: init.control.option
// Imports: init.control.alternative init.control.lift init.control.except
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
#endif
obj* l_option__t_alternative___rarg___lambda__3(obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__5___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_monad__run___rarg(obj*, obj*, obj*);
obj* l_option__t_monad__run(obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__4(obj*);
obj* l_option__t_run(obj*, obj*);
obj* l_option__t_alternative___rarg___lambda__6(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_monad__except(obj*);
obj* l_option__t_bind___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__2(obj*);
obj* l_option__t_monad__except___rarg___lambda__1(obj*, obj*, obj*);
obj* l_option__t_catch___rarg(obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__4___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_monad___rarg___lambda__3(obj*, obj*, obj*);
obj* l_option__t_has__monad__lift___rarg(obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__4(obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__3___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_monad___rarg___lambda__8(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__7(obj*);
obj* l_function_const___rarg(obj*, obj*);
obj* l_option__t_monad___rarg___lambda__6(obj*, obj*, obj*);
obj* l_option__t_catch___rarg___lambda__1(obj*, obj*, obj*);
obj* l_option__t_bind__cont___main(obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_monad___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__7___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_function_comp___rarg(obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__6(obj*);
obj* l_option__t_orelse(obj*);
obj* l_option__t_monad___rarg___lambda__7(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_alternative(obj*);
obj* l_option__t_monad__functor___rarg(obj*, obj*);
obj* l_option__t_fail___rarg(obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__1(obj*);
obj* l_option__t_monad___rarg___lambda__4(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_catch(obj*);
obj* l_option__t_monad___rarg___lambda__5(obj*, obj*, obj*);
obj* l_option__t_lift(obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__5(obj*);
obj* l_option__t_bind__cont___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__5___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_monad___rarg(obj*);
obj* l_option__t_pure___rarg(obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__2(obj*);
obj* l_option__t_monad(obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__5(obj*);
obj* l_option__t_pure(obj*);
obj* l_option__t_monad__except___rarg(obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__7(obj*);
obj* l_option__t_has__monad__lift(obj*);
obj* l_option__t_monad___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_alternative___rarg___lambda__5(obj*, obj*, obj*);
obj* l_option__t_bind(obj*);
obj* l_option__t_fail(obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__7___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_monad__functor(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__3(obj*);
obj* l_option__t_monad__map___rarg(obj*, obj*);
obj* l_option__t_alternative___rarg(obj*);
obj* l_option__t_bind__cont___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_monad___spec__3___rarg(obj*, obj*, obj*, obj*, obj*);
extern obj* l_optional___rarg___closed__1;
obj* l_option__t_alternative___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_alternative___rarg___lambda__7(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__3(obj*);
obj* l_option__t_alternative___rarg___lambda__4(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_monad__map(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_orelse___rarg(obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont(obj*);
obj* l_option__t;
obj* l_option__t_alternative___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__1(obj*);
obj* l_option__t_lift___rarg(obj*, obj*, obj*);
obj* l_option__t_run___rarg(obj*);
obj* l_option__t_orelse___rarg___lambda__1(obj*, obj*, obj*);
obj* l_except__t_monad___rarg___lambda__8(obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__4___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_option__t_bind__cont___at_option__t_alternative___spec__6(obj*);
obj* _init_l_option__t() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_option__t_run___rarg(obj* x_0) {
_start:
{
return x_0;
}
}
obj* l_option__t_run(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_run___rarg), 1, 0);
return x_4;
}
}
obj* l_option__t_bind__cont___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_12; obj* x_15; obj* x_16; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::box(0);
x_16 = lean::apply_2(x_12, lean::box(0), x_15);
return x_16;
}
else
{
obj* x_18; obj* x_21; 
lean::dec(x_0);
x_18 = lean::cnstr_get(x_4, 0);
lean::inc(x_18);
lean::dec(x_4);
x_21 = lean::apply_1(x_3, x_18);
return x_21;
}
}
}
obj* l_option__t_bind__cont___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___main___rarg), 5, 0);
return x_2;
}
}
obj* l_option__t_bind__cont___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = l_option__t_bind__cont___main___rarg(x_0, lean::box(0), lean::box(0), x_3, x_4);
return x_7;
}
}
obj* l_option__t_bind__cont(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___rarg), 5, 0);
return x_2;
}
}
obj* l_option__t_bind___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_9; obj* x_10; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___rarg), 5, 4);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, lean::box(0));
lean::closure_set(x_9, 2, lean::box(0));
lean::closure_set(x_9, 3, x_4);
x_10 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_3, x_9);
return x_10;
}
}
obj* l_option__t_bind(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind___rarg), 5, 0);
return x_2;
}
}
obj* l_option__t_pure___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_2);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_option__t_pure(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_pure___rarg), 3, 0);
return x_2;
}
}
obj* l_option__t_monad___rarg(obj* x_0) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_monad___rarg___lambda__1), 5, 1);
lean::closure_set(x_2, 0, x_0);
lean::inc(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_monad___rarg___lambda__2), 5, 1);
lean::closure_set(x_4, 0, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_4);
lean::inc(x_0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_pure___rarg), 3, 1);
lean::closure_set(x_7, 0, x_0);
lean::inc(x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_monad___rarg___lambda__4), 5, 1);
lean::closure_set(x_9, 0, x_0);
lean::inc(x_0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_monad___rarg___lambda__7), 5, 1);
lean::closure_set(x_11, 0, x_0);
lean::inc(x_0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_monad___rarg___lambda__8), 5, 1);
lean::closure_set(x_13, 0, x_0);
x_14 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_14, 0, x_5);
lean::cnstr_set(x_14, 1, x_7);
lean::cnstr_set(x_14, 2, x_9);
lean::cnstr_set(x_14, 3, x_11);
lean::cnstr_set(x_14, 4, x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind___rarg), 5, 1);
lean::closure_set(x_15, 0, x_0);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
obj* l_option__t_monad___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; 
lean::dec(x_2);
lean::dec(x_1);
lean::inc(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_pure___rarg), 3, 2);
lean::closure_set(x_8, 0, x_0);
lean::closure_set(x_8, 1, lean::box(0));
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_9, 0, x_8);
lean::closure_set(x_9, 1, x_3);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_monad___spec__1___rarg), 5, 4);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, lean::box(0));
lean::closure_set(x_12, 2, lean::box(0));
lean::closure_set(x_12, 3, x_9);
x_13 = lean::apply_4(x_10, lean::box(0), lean::box(0), x_4, x_12);
return x_13;
}
}
obj* l_option__t_monad___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_function_const___rarg), 2, 1);
lean::closure_set(x_7, 0, x_3);
lean::inc(x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_pure___rarg), 3, 2);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, lean::box(0));
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_10, 0, x_9);
lean::closure_set(x_10, 1, x_7);
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_monad___spec__2___rarg), 5, 4);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, lean::box(0));
lean::closure_set(x_13, 2, lean::box(0));
lean::closure_set(x_13, 3, x_10);
x_14 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_4, x_13);
return x_14;
}
}
obj* l_option__t_monad___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_9; 
lean::inc(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_pure___rarg), 3, 2);
lean::closure_set(x_4, 0, x_0);
lean::closure_set(x_4, 1, lean::box(0));
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_5, 0, x_4);
lean::closure_set(x_5, 1, x_2);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_monad___spec__3___rarg), 5, 4);
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
obj* x_8; obj* x_9; obj* x_11; obj* x_12; 
lean::dec(x_2);
lean::dec(x_1);
lean::inc(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_monad___rarg___lambda__3), 3, 2);
lean::closure_set(x_8, 0, x_0);
lean::closure_set(x_8, 1, x_4);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_monad___spec__4___rarg), 5, 4);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, lean::box(0));
lean::closure_set(x_11, 2, lean::box(0));
lean::closure_set(x_11, 3, x_8);
x_12 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_3, x_11);
return x_12;
}
}
obj* l_option__t_monad___rarg___lambda__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_2);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_1);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_option__t_monad___rarg___lambda__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
lean::inc(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_monad___rarg___lambda__5), 3, 2);
lean::closure_set(x_4, 0, x_0);
lean::closure_set(x_4, 1, x_2);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_monad___spec__5___rarg), 5, 4);
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
obj* x_8; obj* x_9; obj* x_11; obj* x_12; 
lean::dec(x_2);
lean::dec(x_1);
lean::inc(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_monad___rarg___lambda__6), 3, 2);
lean::closure_set(x_8, 0, x_0);
lean::closure_set(x_8, 1, x_4);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_monad___spec__6___rarg), 5, 4);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, lean::box(0));
lean::closure_set(x_11, 2, lean::box(0));
lean::closure_set(x_11, 3, x_8);
x_12 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_3, x_11);
return x_12;
}
}
obj* l_option__t_monad___rarg___lambda__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_8; obj* x_10; obj* x_11; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_monad___rarg___lambda__8), 2, 1);
lean::closure_set(x_7, 0, x_4);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_monad___spec__7___rarg), 5, 4);
lean::closure_set(x_10, 0, x_0);
lean::closure_set(x_10, 1, lean::box(0));
lean::closure_set(x_10, 2, lean::box(0));
lean::closure_set(x_10, 3, x_7);
x_11 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_3, x_10);
return x_11;
}
}
obj* l_option__t_monad(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_monad___rarg), 1, 0);
return x_2;
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_12; obj* x_15; obj* x_16; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::box(0);
x_16 = lean::apply_2(x_12, lean::box(0), x_15);
return x_16;
}
else
{
obj* x_18; obj* x_21; 
lean::dec(x_0);
x_18 = lean::cnstr_get(x_4, 0);
lean::inc(x_18);
lean::dec(x_4);
x_21 = lean::apply_1(x_3, x_18);
return x_21;
}
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_monad___spec__1___rarg), 5, 0);
return x_2;
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_12; obj* x_15; obj* x_16; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::box(0);
x_16 = lean::apply_2(x_12, lean::box(0), x_15);
return x_16;
}
else
{
obj* x_18; obj* x_21; 
lean::dec(x_0);
x_18 = lean::cnstr_get(x_4, 0);
lean::inc(x_18);
lean::dec(x_4);
x_21 = lean::apply_1(x_3, x_18);
return x_21;
}
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__2(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_monad___spec__2___rarg), 5, 0);
return x_2;
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_12; obj* x_15; obj* x_16; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::box(0);
x_16 = lean::apply_2(x_12, lean::box(0), x_15);
return x_16;
}
else
{
obj* x_18; obj* x_21; 
lean::dec(x_0);
x_18 = lean::cnstr_get(x_4, 0);
lean::inc(x_18);
lean::dec(x_4);
x_21 = lean::apply_1(x_3, x_18);
return x_21;
}
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__3(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_monad___spec__3___rarg), 5, 0);
return x_2;
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_12; obj* x_15; obj* x_16; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::box(0);
x_16 = lean::apply_2(x_12, lean::box(0), x_15);
return x_16;
}
else
{
obj* x_18; obj* x_21; 
lean::dec(x_0);
x_18 = lean::cnstr_get(x_4, 0);
lean::inc(x_18);
lean::dec(x_4);
x_21 = lean::apply_1(x_3, x_18);
return x_21;
}
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__4(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_monad___spec__4___rarg), 5, 0);
return x_2;
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_12; obj* x_15; obj* x_16; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::box(0);
x_16 = lean::apply_2(x_12, lean::box(0), x_15);
return x_16;
}
else
{
obj* x_18; obj* x_21; 
lean::dec(x_0);
x_18 = lean::cnstr_get(x_4, 0);
lean::inc(x_18);
lean::dec(x_4);
x_21 = lean::apply_1(x_3, x_18);
return x_21;
}
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__5(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_monad___spec__5___rarg), 5, 0);
return x_2;
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_12; obj* x_15; obj* x_16; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::box(0);
x_16 = lean::apply_2(x_12, lean::box(0), x_15);
return x_16;
}
else
{
obj* x_18; obj* x_21; 
lean::dec(x_0);
x_18 = lean::cnstr_get(x_4, 0);
lean::inc(x_18);
lean::dec(x_4);
x_21 = lean::apply_1(x_3, x_18);
return x_21;
}
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__6(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_monad___spec__6___rarg), 5, 0);
return x_2;
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__7___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_12; obj* x_15; obj* x_16; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::box(0);
x_16 = lean::apply_2(x_12, lean::box(0), x_15);
return x_16;
}
else
{
obj* x_18; obj* x_21; 
lean::dec(x_0);
x_18 = lean::cnstr_get(x_4, 0);
lean::inc(x_18);
lean::dec(x_4);
x_21 = lean::apply_1(x_3, x_18);
return x_21;
}
}
}
obj* l_option__t_bind__cont___at_option__t_monad___spec__7(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_monad___spec__7___rarg), 5, 0);
return x_2;
}
}
obj* l_option__t_orelse___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; 
lean::dec(x_1);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_orelse___rarg___lambda__1), 3, 2);
lean::closure_set(x_7, 0, x_3);
lean::closure_set(x_7, 1, x_0);
x_8 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_2, x_7);
return x_8;
}
}
obj* l_option__t_orelse___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_1);
lean::dec(x_2);
return x_0;
}
else
{
obj* x_6; obj* x_9; obj* x_12; 
lean::dec(x_0);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::apply_2(x_9, lean::box(0), x_2);
return x_12;
}
}
}
obj* l_option__t_orelse(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_orelse___rarg), 4, 0);
return x_2;
}
}
obj* l_option__t_fail___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; 
lean::dec(x_1);
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
obj* l_option__t_fail(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_fail___rarg), 2, 0);
return x_2;
}
}
obj* l_option__t_alternative___rarg(obj* x_0) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_alternative___rarg___lambda__1), 5, 1);
lean::closure_set(x_2, 0, x_0);
lean::inc(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_alternative___rarg___lambda__2), 5, 1);
lean::closure_set(x_4, 0, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_4);
lean::inc(x_0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_pure___rarg), 3, 1);
lean::closure_set(x_7, 0, x_0);
lean::inc(x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_alternative___rarg___lambda__4), 5, 1);
lean::closure_set(x_9, 0, x_0);
lean::inc(x_0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_alternative___rarg___lambda__6), 5, 1);
lean::closure_set(x_11, 0, x_0);
lean::inc(x_0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_alternative___rarg___lambda__7), 5, 1);
lean::closure_set(x_13, 0, x_0);
x_14 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_14, 0, x_5);
lean::cnstr_set(x_14, 1, x_7);
lean::cnstr_set(x_14, 2, x_9);
lean::cnstr_set(x_14, 3, x_11);
lean::cnstr_set(x_14, 4, x_13);
lean::inc(x_0);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_orelse___rarg), 4, 1);
lean::closure_set(x_16, 0, x_0);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_fail___rarg), 2, 1);
lean::closure_set(x_17, 0, x_0);
x_18 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_18, 0, x_14);
lean::cnstr_set(x_18, 1, x_16);
lean::cnstr_set(x_18, 2, x_17);
return x_18;
}
}
obj* l_option__t_alternative___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; 
lean::dec(x_2);
lean::dec(x_1);
lean::inc(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_pure___rarg), 3, 2);
lean::closure_set(x_8, 0, x_0);
lean::closure_set(x_8, 1, lean::box(0));
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_9, 0, x_8);
lean::closure_set(x_9, 1, x_3);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_alternative___spec__1___rarg), 5, 4);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, lean::box(0));
lean::closure_set(x_12, 2, lean::box(0));
lean::closure_set(x_12, 3, x_9);
x_13 = lean::apply_4(x_10, lean::box(0), lean::box(0), x_4, x_12);
return x_13;
}
}
obj* l_option__t_alternative___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_function_const___rarg), 2, 1);
lean::closure_set(x_7, 0, x_3);
lean::inc(x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_pure___rarg), 3, 2);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, lean::box(0));
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_10, 0, x_9);
lean::closure_set(x_10, 1, x_7);
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_alternative___spec__2___rarg), 5, 4);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, lean::box(0));
lean::closure_set(x_13, 2, lean::box(0));
lean::closure_set(x_13, 3, x_10);
x_14 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_4, x_13);
return x_14;
}
}
obj* l_option__t_alternative___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_9; 
lean::inc(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_pure___rarg), 3, 2);
lean::closure_set(x_4, 0, x_0);
lean::closure_set(x_4, 1, lean::box(0));
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_5, 0, x_4);
lean::closure_set(x_5, 1, x_2);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_alternative___spec__3___rarg), 5, 4);
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
obj* x_8; obj* x_9; obj* x_11; obj* x_12; 
lean::dec(x_2);
lean::dec(x_1);
lean::inc(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_alternative___rarg___lambda__3), 3, 2);
lean::closure_set(x_8, 0, x_0);
lean::closure_set(x_8, 1, x_4);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_alternative___spec__4___rarg), 5, 4);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, lean::box(0));
lean::closure_set(x_11, 2, lean::box(0));
lean::closure_set(x_11, 3, x_8);
x_12 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_3, x_11);
return x_12;
}
}
obj* l_option__t_alternative___rarg___lambda__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
lean::inc(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_monad___rarg___lambda__5), 3, 2);
lean::closure_set(x_4, 0, x_0);
lean::closure_set(x_4, 1, x_2);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_alternative___spec__5___rarg), 5, 4);
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
obj* x_8; obj* x_9; obj* x_11; obj* x_12; 
lean::dec(x_2);
lean::dec(x_1);
lean::inc(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_alternative___rarg___lambda__5), 3, 2);
lean::closure_set(x_8, 0, x_0);
lean::closure_set(x_8, 1, x_4);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_alternative___spec__6___rarg), 5, 4);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, lean::box(0));
lean::closure_set(x_11, 2, lean::box(0));
lean::closure_set(x_11, 3, x_8);
x_12 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_3, x_11);
return x_12;
}
}
obj* l_option__t_alternative___rarg___lambda__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_8; obj* x_10; obj* x_11; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_monad___rarg___lambda__8), 2, 1);
lean::closure_set(x_7, 0, x_4);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_alternative___spec__7___rarg), 5, 4);
lean::closure_set(x_10, 0, x_0);
lean::closure_set(x_10, 1, lean::box(0));
lean::closure_set(x_10, 2, lean::box(0));
lean::closure_set(x_10, 3, x_7);
x_11 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_3, x_10);
return x_11;
}
}
obj* l_option__t_alternative(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_alternative___rarg), 1, 0);
return x_2;
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_12; obj* x_15; obj* x_16; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::box(0);
x_16 = lean::apply_2(x_12, lean::box(0), x_15);
return x_16;
}
else
{
obj* x_18; obj* x_21; 
lean::dec(x_0);
x_18 = lean::cnstr_get(x_4, 0);
lean::inc(x_18);
lean::dec(x_4);
x_21 = lean::apply_1(x_3, x_18);
return x_21;
}
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_alternative___spec__1___rarg), 5, 0);
return x_2;
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_12; obj* x_15; obj* x_16; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::box(0);
x_16 = lean::apply_2(x_12, lean::box(0), x_15);
return x_16;
}
else
{
obj* x_18; obj* x_21; 
lean::dec(x_0);
x_18 = lean::cnstr_get(x_4, 0);
lean::inc(x_18);
lean::dec(x_4);
x_21 = lean::apply_1(x_3, x_18);
return x_21;
}
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__2(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_alternative___spec__2___rarg), 5, 0);
return x_2;
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_12; obj* x_15; obj* x_16; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::box(0);
x_16 = lean::apply_2(x_12, lean::box(0), x_15);
return x_16;
}
else
{
obj* x_18; obj* x_21; 
lean::dec(x_0);
x_18 = lean::cnstr_get(x_4, 0);
lean::inc(x_18);
lean::dec(x_4);
x_21 = lean::apply_1(x_3, x_18);
return x_21;
}
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__3(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_alternative___spec__3___rarg), 5, 0);
return x_2;
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_12; obj* x_15; obj* x_16; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::box(0);
x_16 = lean::apply_2(x_12, lean::box(0), x_15);
return x_16;
}
else
{
obj* x_18; obj* x_21; 
lean::dec(x_0);
x_18 = lean::cnstr_get(x_4, 0);
lean::inc(x_18);
lean::dec(x_4);
x_21 = lean::apply_1(x_3, x_18);
return x_21;
}
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__4(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_alternative___spec__4___rarg), 5, 0);
return x_2;
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_12; obj* x_15; obj* x_16; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::box(0);
x_16 = lean::apply_2(x_12, lean::box(0), x_15);
return x_16;
}
else
{
obj* x_18; obj* x_21; 
lean::dec(x_0);
x_18 = lean::cnstr_get(x_4, 0);
lean::inc(x_18);
lean::dec(x_4);
x_21 = lean::apply_1(x_3, x_18);
return x_21;
}
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__5(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_alternative___spec__5___rarg), 5, 0);
return x_2;
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_12; obj* x_15; obj* x_16; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::box(0);
x_16 = lean::apply_2(x_12, lean::box(0), x_15);
return x_16;
}
else
{
obj* x_18; obj* x_21; 
lean::dec(x_0);
x_18 = lean::cnstr_get(x_4, 0);
lean::inc(x_18);
lean::dec(x_4);
x_21 = lean::apply_1(x_3, x_18);
return x_21;
}
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__6(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_alternative___spec__6___rarg), 5, 0);
return x_2;
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__7___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_12; obj* x_15; obj* x_16; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::box(0);
x_16 = lean::apply_2(x_12, lean::box(0), x_15);
return x_16;
}
else
{
obj* x_18; obj* x_21; 
lean::dec(x_0);
x_18 = lean::cnstr_get(x_4, 0);
lean::inc(x_18);
lean::dec(x_4);
x_21 = lean::apply_1(x_3, x_18);
return x_21;
}
}
}
obj* l_option__t_bind__cont___at_option__t_alternative___spec__7(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_bind__cont___at_option__t_alternative___spec__7___rarg), 5, 0);
return x_2;
}
}
obj* l_option__t_lift___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_7; obj* x_10; obj* x_13; obj* x_15; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_7, 0);
lean::inc(x_10);
lean::dec(x_7);
x_13 = l_optional___rarg___closed__1;
lean::inc(x_13);
x_15 = lean::apply_4(x_10, lean::box(0), lean::box(0), x_13, x_2);
return x_15;
}
}
obj* l_option__t_lift(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_lift___rarg), 3, 0);
return x_2;
}
}
obj* l_option__t_has__monad__lift___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_lift___rarg), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_option__t_has__monad__lift(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_has__monad__lift___rarg), 1, 0);
return x_2;
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
obj* x_10; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_monad__map___rarg), 2, 0);
return x_10;
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
obj* x_10; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_monad__functor___rarg), 2, 0);
return x_10;
}
}
obj* l_option__t_catch___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; 
lean::dec(x_1);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_catch___rarg___lambda__1), 3, 2);
lean::closure_set(x_7, 0, x_3);
lean::closure_set(x_7, 1, x_0);
x_8 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_2, x_7);
return x_8;
}
}
obj* l_option__t_catch___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; obj* x_6; 
lean::dec(x_1);
lean::dec(x_2);
x_5 = lean::box(0);
x_6 = lean::apply_1(x_0, x_5);
return x_6;
}
else
{
obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_17; obj* x_18; 
lean::dec(x_0);
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_10 = x_2;
}
x_11 = lean::cnstr_get(x_1, 0);
lean::inc(x_11);
lean::dec(x_1);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::is_scalar(x_10)) {
 x_17 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_17 = x_10;
}
lean::cnstr_set(x_17, 0, x_8);
x_18 = lean::apply_2(x_14, lean::box(0), x_17);
return x_18;
}
}
}
obj* l_option__t_catch(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_catch___rarg), 4, 0);
return x_2;
}
}
obj* l_option__t_monad__except___rarg(obj* x_0) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_monad__except___rarg___lambda__1), 3, 1);
lean::closure_set(x_2, 0, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_catch___rarg), 4, 1);
lean::closure_set(x_3, 0, x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_option__t_monad__except___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_5; obj* x_8; obj* x_11; obj* x_12; 
lean::dec(x_2);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::box(0);
x_12 = lean::apply_2(x_8, lean::box(0), x_11);
return x_12;
}
}
obj* l_option__t_monad__except(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_monad__except___rarg), 1, 0);
return x_2;
}
}
obj* l_option__t_monad__run___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::dec(x_1);
x_4 = lean::apply_2(x_0, lean::box(0), x_2);
return x_4;
}
}
obj* l_option__t_monad__run(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_option__t_monad__run___rarg), 3, 0);
return x_4;
}
}
void initialize_init_control_alternative();
void initialize_init_control_lift();
void initialize_init_control_except();
static bool _G_initialized = false;
void initialize_init_control_option() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_control_alternative();
 initialize_init_control_lift();
 initialize_init_control_except();
 l_option__t = _init_l_option__t();
}

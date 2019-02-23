// Lean compiler output
// Module: init.control.state
// Imports: init.control.alternative init.control.lift init.control.id init.control.except
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
obj* l_state__t_has__monad__lift___boxed(obj*, obj*);
obj* l_state__t_monad___rarg___lambda__8(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_monad___rarg___lambda__3(obj*, obj*, obj*);
obj* l_state__t_bind___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_monad___rarg___lambda__1(obj*, obj*, obj*);
obj* l_state__t_put___rarg___boxed(obj*, obj*, obj*);
obj* l_state__t_monad__run___boxed(obj*, obj*, obj*);
obj* l_state__t_bind___rarg___lambda__1(obj*, obj*);
obj* l_state__t_monad__run___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_monad__state__adapter__trans___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_bind(obj*, obj*);
obj* l_state__t_has__monad__lift___rarg(obj*);
obj* l_state__t_orelse___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_bind___boxed(obj*, obj*);
obj* l_state__t_monad___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_orelse(obj*, obj*, obj*);
obj* l_state__t_monad__state__runner___boxed(obj*, obj*);
obj* l_state__t_adapt(obj*, obj*, obj*, obj*, obj*);
obj* l_monad__state__adapter_adapt__state_x_27___rarg___lambda__1(obj*, obj*);
obj* l_state__t_monad__run___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_monad__functor___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_monad___boxed(obj*, obj*);
obj* l_monad__state__adapter_adapt__state_x_27___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_run_x_27___rarg___lambda__1(obj*);
obj* l_state__t_run___boxed(obj*, obj*, obj*);
obj* l_monad__state__runner__trans___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_state__t_monad___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_alternative(obj*, obj*);
obj* l_state__t_adapt___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_monad__state__adapter_adapt__state_x_27(obj*, obj*, obj*, obj*);
obj* l_monad__state__adapter_adapt__state_x_27___rarg___lambda__2___boxed(obj*, obj*, obj*);
obj* l_state__t_failure___rarg___boxed(obj*, obj*, obj*);
obj* l_monad__state__adapter__trans___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_monad__state__trans___rarg___lambda__2(obj*, obj*, obj*);
obj* l_state__t_monad___rarg___lambda__4___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_orelse___boxed(obj*, obj*, obj*);
obj* l_monad__state__adapter_adapt__state_x_27___rarg___lambda__2(obj*, obj*, obj*);
obj* l_state__t_monad__state___rarg(obj*);
obj* l_state__t_lift(obj*, obj*);
obj* l_monad__state__trans(obj*, obj*, obj*);
obj* l_monad__state__runner__trans___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_monad__state__adapter___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_run(obj*, obj*, obj*);
obj* l_state__t_monad___rarg___lambda__7(obj*, obj*, obj*, obj*);
obj* l_state__t_monad__except___boxed(obj*, obj*);
obj* l_state__t_put___rarg(obj*, obj*, obj*);
obj* l_monad__state__trans___rarg___lambda__1(obj*, obj*, obj*);
obj* l_state__t_monad__except___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_monad__state__runner(obj*, obj*);
obj* l_state__t_failure(obj*, obj*, obj*);
obj* l_state__t_orelse___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_pure___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_state__t_monad___rarg___lambda__5(obj*, obj*, obj*, obj*);
obj* l_state__t_bind___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_monad__state__adapter(obj*, obj*, obj*);
obj* l_state__t_monad__except___rarg___lambda__3(obj*, obj*, obj*, obj*, obj*);
obj* l_monad__state__adapter__trans___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_monad__except(obj*, obj*);
obj* l_state__t_run_x_27___rarg___lambda__1___boxed(obj*);
obj* l_state__t_run_x_27___rarg(obj*, obj*, obj*, obj*);
obj* l_state__t_monad___rarg___lambda__4(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_failure___rarg(obj*, obj*, obj*);
obj* l_state__t_monad__state___boxed(obj*, obj*);
obj* l_monad__state__runner__trans(obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_monad__functor(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_get___boxed(obj*, obj*);
obj* l_state__t_monad__except___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_run_x_27___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_state__t_monad__except___rarg___lambda__3___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_monad__state__runner__trans___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_monad__state__adapter_adapt__state_x_27___boxed(obj*, obj*, obj*, obj*);
obj* l_state;
obj* l_monad__state__trans___rarg(obj*, obj*);
obj* l_state__t_monad(obj*, obj*);
obj* l_state__t_modify(obj*, obj*);
obj* l_state__t_put(obj*, obj*);
obj* l_state__t_monad__except___rarg(obj*, obj*, obj*);
obj* l_state__t_run_x_27___boxed(obj*, obj*);
obj* l_monad__state__adapter__trans___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_lift___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_monad__state__adapter__trans___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_monad___rarg___lambda__9(obj*, obj*);
obj* l_state__t_monad___rarg___lambda__10___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_monad___rarg(obj*);
obj* l_state__t_monad___rarg___lambda__10(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_put___boxed(obj*, obj*);
obj* l_state__t_adapt___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_get(obj*, obj*);
obj* l_state__t_has__monad__lift(obj*, obj*);
obj* l_monad__state__runner__trans___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_monad__state__adapter___boxed(obj*, obj*, obj*);
obj* l_state__t_alternative___rarg(obj*, obj*);
obj* l_state__t_run_x_27(obj*, obj*);
obj* l_state__t_monad___rarg___lambda__8___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_monad__state__adapter___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_monad__functor___rarg(obj*, obj*, obj*);
obj* l_state__t_adapt___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_state__t_modify___rarg(obj*, obj*, obj*);
obj* l_monad__state__trans___boxed(obj*, obj*, obj*);
obj* l_state__t_monad__run(obj*, obj*, obj*);
obj* l_monad__state__adapter_adapt__state_x_27___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_lift___boxed(obj*, obj*);
obj* l_state__t_monad__state(obj*, obj*);
obj* l_monad__state__adapter__trans(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_monad__except___rarg___lambda__2(obj*, obj*, obj*);
obj* l_state__t_pure(obj*, obj*);
obj* l_state__t_monad__state__runner___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_state__t_failure___boxed(obj*, obj*, obj*);
obj* l_state__t_alternative___boxed(obj*, obj*);
obj* l_state__t_lift___rarg___lambda__1(obj*, obj*, obj*);
obj* l_state__t_pure___rarg(obj*, obj*, obj*, obj*);
obj* l_state__t_lift___rarg(obj*, obj*, obj*, obj*);
obj* l_state__t_monad___rarg___lambda__6___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_monad__state__runner___rarg(obj*, obj*, obj*, obj*);
obj* l_monad__state__runner__trans___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_run___rarg(obj*, obj*);
obj* l_state__t_get___rarg(obj*, obj*);
obj* l_state__t_monad__except___rarg___boxed(obj*, obj*, obj*);
obj* l_state__t_monad___rarg___lambda__6(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_state__t;
obj* l_state__t_pure___boxed(obj*, obj*);
obj* l_state__t_run_x_27___rarg___closed__1;
obj* l_state__t_modify___boxed(obj*, obj*);
obj* _init_l_state__t() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_state__t_run___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* l_state__t_run(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_run___rarg), 2, 0);
return x_3;
}
}
obj* l_state__t_run___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_state__t_run(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_state__t_run_x_27___rarg___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
}
obj* _init_l_state__t_run_x_27___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_run_x_27___rarg___lambda__1___boxed), 1, 0);
return x_0;
}
}
obj* l_state__t_run_x_27___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::apply_1(x_2, x_3);
x_8 = l_state__t_run_x_27___rarg___closed__1;
x_9 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_8, x_7);
return x_9;
}
}
obj* l_state__t_run_x_27(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_run_x_27___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_state__t_run_x_27___rarg___lambda__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_state__t_run_x_27___rarg___lambda__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_state__t_run_x_27___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_state__t_run_x_27___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_state__t_run_x_27___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_state__t_run_x_27(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_state() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_state__t_pure___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_2);
lean::cnstr_set(x_10, 1, x_3);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_state__t_pure(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_pure___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_state__t_pure___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_state__t_pure___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_state__t_pure___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_state__t_pure(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_state__t_bind___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_7; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::apply_2(x_0, x_2, x_4);
return x_7;
}
}
obj* l_state__t_bind___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_9; obj* x_10; obj* x_11; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::apply_1(x_3, x_5);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_bind___rarg___lambda__1), 2, 1);
lean::closure_set(x_10, 0, x_4);
x_11 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
}
obj* l_state__t_bind(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_bind___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l_state__t_bind___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_state__t_bind___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_state__t_bind___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_state__t_bind(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_state__t_monad___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_12; obj* x_15; obj* x_16; 
x_3 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_7 = x_2;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_2);
 x_7 = lean::box(0);
}
x_8 = lean::apply_1(x_0, x_3);
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
lean::dec(x_1);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
if (lean::is_scalar(x_7)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_7;
}
lean::cnstr_set(x_15, 0, x_8);
lean::cnstr_set(x_15, 1, x_5);
x_16 = lean::apply_2(x_12, lean::box(0), x_15);
return x_16;
}
}
obj* l_state__t_monad___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::apply_1(x_4, x_5);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad___rarg___lambda__1), 3, 2);
lean::closure_set(x_9, 0, x_3);
lean::closure_set(x_9, 1, x_0);
x_10 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_state__t_monad___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_9; obj* x_12; obj* x_13; 
x_3 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_5 = x_2;
} else {
 lean::inc(x_3);
 lean::dec(x_2);
 x_5 = lean::box(0);
}
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
if (lean::is_scalar(x_5)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_5;
}
lean::cnstr_set(x_12, 0, x_1);
lean::cnstr_set(x_12, 1, x_3);
x_13 = lean::apply_2(x_9, lean::box(0), x_12);
return x_13;
}
}
obj* l_state__t_monad___rarg___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::apply_1(x_4, x_5);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad___rarg___lambda__3), 3, 2);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, x_3);
x_10 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_state__t_monad___rarg___lambda__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::apply_1(x_0, x_6);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad___rarg___lambda__1), 3, 2);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_1);
x_11 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
}
obj* l_state__t_monad___rarg___lambda__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::apply_1(x_3, x_5);
lean::inc(x_6);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad___rarg___lambda__5), 4, 3);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_0);
lean::closure_set(x_10, 2, x_6);
x_11 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_10);
return x_11;
}
}
obj* l_state__t_monad___rarg___lambda__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::apply_1(x_0, x_6);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad___rarg___lambda__3), 3, 2);
lean::closure_set(x_10, 0, x_1);
lean::closure_set(x_10, 1, x_4);
x_11 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
}
obj* l_state__t_monad___rarg___lambda__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::apply_1(x_3, x_5);
lean::inc(x_6);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad___rarg___lambda__7), 4, 3);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_0);
lean::closure_set(x_10, 2, x_6);
x_11 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_10);
return x_11;
}
}
obj* l_state__t_monad___rarg___lambda__9(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; 
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
lean::dec(x_1);
x_5 = lean::apply_1(x_0, x_2);
return x_5;
}
}
obj* l_state__t_monad___rarg___lambda__10(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_9; obj* x_10; obj* x_11; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::apply_1(x_3, x_5);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad___rarg___lambda__9), 2, 1);
lean::closure_set(x_10, 0, x_4);
x_11 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
}
obj* l_state__t_monad___rarg(obj* x_0) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad___rarg___lambda__2___boxed), 6, 1);
lean::closure_set(x_2, 0, x_0);
lean::inc(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad___rarg___lambda__4___boxed), 6, 1);
lean::closure_set(x_4, 0, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_4);
lean::inc(x_0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_pure___rarg___boxed), 4, 1);
lean::closure_set(x_7, 0, x_0);
lean::inc(x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad___rarg___lambda__6___boxed), 6, 1);
lean::closure_set(x_9, 0, x_0);
lean::inc(x_0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad___rarg___lambda__8___boxed), 6, 1);
lean::closure_set(x_11, 0, x_0);
lean::inc(x_0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad___rarg___lambda__10___boxed), 6, 1);
lean::closure_set(x_13, 0, x_0);
x_14 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_14, 0, x_5);
lean::cnstr_set(x_14, 1, x_7);
lean::cnstr_set(x_14, 2, x_9);
lean::cnstr_set(x_14, 3, x_11);
lean::cnstr_set(x_14, 4, x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_bind___rarg___boxed), 6, 1);
lean::closure_set(x_15, 0, x_0);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
obj* l_state__t_monad(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad___rarg), 1, 0);
return x_2;
}
}
obj* l_state__t_monad___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_state__t_monad___rarg___lambda__2(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_state__t_monad___rarg___lambda__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_state__t_monad___rarg___lambda__4(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_state__t_monad___rarg___lambda__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_state__t_monad___rarg___lambda__6(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_state__t_monad___rarg___lambda__8___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_state__t_monad___rarg___lambda__8(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_state__t_monad___rarg___lambda__10___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_state__t_monad___rarg___lambda__10(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_state__t_monad___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_state__t_monad(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_state__t_orelse___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_9; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
lean::inc(x_4);
x_9 = lean::apply_1(x_2, x_4);
x_10 = lean::apply_1(x_3, x_4);
x_11 = lean::apply_3(x_5, lean::box(0), x_9, x_10);
return x_11;
}
}
obj* l_state__t_orelse(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_orelse___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_state__t_orelse___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_state__t_orelse___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_state__t_orelse___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_state__t_orelse(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_state__t_failure___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 2);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::apply_1(x_3, lean::box(0));
return x_6;
}
}
obj* l_state__t_failure(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_failure___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_state__t_failure___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_state__t_failure___rarg(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_state__t_failure___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_state__t_failure(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_state__t_alternative___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
lean::inc(x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad___rarg___lambda__2___boxed), 6, 1);
lean::closure_set(x_3, 0, x_0);
lean::inc(x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad___rarg___lambda__4___boxed), 6, 1);
lean::closure_set(x_5, 0, x_0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_3);
lean::cnstr_set(x_6, 1, x_5);
lean::inc(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_pure___rarg___boxed), 4, 1);
lean::closure_set(x_8, 0, x_0);
lean::inc(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad___rarg___lambda__6___boxed), 6, 1);
lean::closure_set(x_10, 0, x_0);
lean::inc(x_0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad___rarg___lambda__8___boxed), 6, 1);
lean::closure_set(x_12, 0, x_0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad___rarg___lambda__10___boxed), 6, 1);
lean::closure_set(x_13, 0, x_0);
x_14 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_14, 0, x_6);
lean::cnstr_set(x_14, 1, x_8);
lean::cnstr_set(x_14, 2, x_10);
lean::cnstr_set(x_14, 3, x_12);
lean::cnstr_set(x_14, 4, x_13);
lean::inc(x_1);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_orelse___rarg___boxed), 5, 1);
lean::closure_set(x_16, 0, x_1);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_failure___rarg___boxed), 3, 1);
lean::closure_set(x_17, 0, x_1);
x_18 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_18, 0, x_14);
lean::cnstr_set(x_18, 1, x_16);
lean::cnstr_set(x_18, 2, x_17);
return x_18;
}
}
obj* l_state__t_alternative(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_alternative___rarg), 2, 0);
return x_2;
}
}
obj* l_state__t_alternative___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_state__t_alternative(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_state__t_get___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_9; obj* x_10; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
lean::inc(x_1);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_1);
x_10 = lean::apply_2(x_5, lean::box(0), x_9);
return x_10;
}
}
obj* l_state__t_get(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_get___rarg), 2, 0);
return x_2;
}
}
obj* l_state__t_get___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_state__t_get(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_state__t_put___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; obj* x_11; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_1);
x_11 = lean::apply_2(x_6, lean::box(0), x_10);
return x_11;
}
}
obj* l_state__t_put(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_put___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_state__t_put___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_state__t_put___rarg(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_state__t_put___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_state__t_put(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_state__t_modify___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::apply_1(x_1, x_2);
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
x_12 = lean::apply_2(x_6, lean::box(0), x_11);
return x_12;
}
}
obj* l_state__t_modify(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_modify___rarg), 3, 0);
return x_2;
}
}
obj* l_state__t_modify___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_state__t_modify(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_state__t_lift___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_2);
lean::cnstr_set(x_9, 1, x_1);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
}
obj* l_state__t_lift___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_lift___rarg___lambda__1), 3, 2);
lean::closure_set(x_6, 0, x_0);
lean::closure_set(x_6, 1, x_3);
x_7 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_2, x_6);
return x_7;
}
}
obj* l_state__t_lift(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_lift___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_state__t_lift___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_state__t_lift___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_state__t_lift___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_state__t_lift(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_state__t_has__monad__lift___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_lift___rarg___boxed), 4, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_state__t_has__monad__lift(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_has__monad__lift___rarg), 1, 0);
return x_2;
}
}
obj* l_state__t_has__monad__lift___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_state__t_has__monad__lift(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_state__t_monad__functor___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::apply_1(x_1, x_2);
x_4 = lean::apply_2(x_0, lean::box(0), x_3);
return x_4;
}
}
obj* l_state__t_monad__functor(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad__functor___rarg), 3, 0);
return x_6;
}
}
obj* l_state__t_monad__functor___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_state__t_monad__functor(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
return x_6;
}
}
obj* l_state__t_adapt___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_12; obj* x_15; obj* x_16; obj* x_17; 
x_4 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_8 = x_3;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_3);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::apply_2(x_1, x_6, x_2);
if (lean::is_scalar(x_8)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_8;
}
lean::cnstr_set(x_16, 0, x_4);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::apply_2(x_12, lean::box(0), x_16);
return x_17;
}
}
obj* l_state__t_adapt___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_5 = lean::apply_1(x_1, x_4);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
x_13 = lean::apply_1(x_3, x_6);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_adapt___rarg___lambda__1), 4, 3);
lean::closure_set(x_14, 0, x_0);
lean::closure_set(x_14, 1, x_2);
lean::closure_set(x_14, 2, x_8);
x_15 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_13, x_14);
return x_15;
}
}
obj* l_state__t_adapt(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_adapt___rarg), 5, 0);
return x_5;
}
}
obj* l_state__t_adapt___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_state__t_adapt(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_state__t_monad__except___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_9; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::apply_2(x_5, lean::box(0), x_3);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_lift___rarg___lambda__1), 3, 2);
lean::closure_set(x_11, 0, x_1);
lean::closure_set(x_11, 1, x_4);
x_12 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_8, x_11);
return x_12;
}
}
obj* l_state__t_monad__except___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_2(x_0, x_2, x_1);
return x_3;
}
}
obj* l_state__t_monad__except___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_9; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
lean::inc(x_4);
x_9 = lean::apply_1(x_2, x_4);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad__except___rarg___lambda__2), 3, 2);
lean::closure_set(x_10, 0, x_3);
lean::closure_set(x_10, 1, x_4);
x_11 = lean::apply_3(x_5, lean::box(0), x_9, x_10);
return x_11;
}
}
obj* l_state__t_monad__except___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
lean::inc(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad__except___rarg___lambda__1___boxed), 5, 2);
lean::closure_set(x_4, 0, x_2);
lean::closure_set(x_4, 1, x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad__except___rarg___lambda__3___boxed), 5, 1);
lean::closure_set(x_5, 0, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* l_state__t_monad__except(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad__except___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_state__t_monad__except___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_state__t_monad__except___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_state__t_monad__except___rarg___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_state__t_monad__except___rarg___lambda__3(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_state__t_monad__except___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_state__t_monad__except___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_state__t_monad__except___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_state__t_monad__except(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_monad__state__trans___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::apply_1(x_3, x_2);
x_7 = lean::apply_2(x_1, lean::box(0), x_6);
return x_7;
}
}
obj* l_monad__state__trans___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 2);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::apply_1(x_3, x_2);
x_7 = lean::apply_2(x_1, lean::box(0), x_6);
return x_7;
}
}
obj* l_monad__state__trans___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_8; obj* x_9; obj* x_10; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
lean::inc(x_0);
x_5 = lean::apply_2(x_0, lean::box(0), x_2);
lean::inc(x_0);
lean::inc(x_1);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__state__trans___rarg___lambda__1), 3, 2);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__state__trans___rarg___lambda__2), 3, 2);
lean::closure_set(x_9, 0, x_1);
lean::closure_set(x_9, 1, x_0);
x_10 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_8);
lean::cnstr_set(x_10, 2, x_9);
return x_10;
}
}
obj* l_monad__state__trans(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__state__trans___rarg), 2, 0);
return x_3;
}
}
obj* l_monad__state__trans___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_monad__state__trans(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_state__t_monad__state___rarg(obj* x_0) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_get___rarg), 2, 1);
lean::closure_set(x_2, 0, x_0);
lean::inc(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_put___rarg___boxed), 3, 1);
lean::closure_set(x_4, 0, x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_modify___rarg), 3, 1);
lean::closure_set(x_5, 0, x_0);
x_6 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_4);
lean::cnstr_set(x_6, 2, x_5);
return x_6;
}
}
obj* l_state__t_monad__state(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad__state___rarg), 1, 0);
return x_2;
}
}
obj* l_state__t_monad__state___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_state__t_monad__state(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_monad__state__adapter_adapt__state_x_27___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::apply_1(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_monad__state__adapter_adapt__state_x_27___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_1(x_0, x_1);
return x_3;
}
}
obj* l_monad__state__adapter_adapt__state_x_27___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__state__adapter_adapt__state_x_27___rarg___lambda__1), 2, 1);
lean::closure_set(x_5, 0, x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__state__adapter_adapt__state_x_27___rarg___lambda__2___boxed), 3, 1);
lean::closure_set(x_6, 0, x_3);
x_7 = lean::apply_5(x_0, lean::box(0), lean::box(0), x_5, x_6, x_4);
return x_7;
}
}
obj* l_monad__state__adapter_adapt__state_x_27(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__state__adapter_adapt__state_x_27___rarg___boxed), 5, 0);
return x_4;
}
}
obj* l_monad__state__adapter_adapt__state_x_27___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_monad__state__adapter_adapt__state_x_27___rarg___lambda__2(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_monad__state__adapter_adapt__state_x_27___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_monad__state__adapter_adapt__state_x_27___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_monad__state__adapter_adapt__state_x_27___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_monad__state__adapter_adapt__state_x_27(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_monad__state__adapter__trans___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::apply_5(x_0, lean::box(0), lean::box(0), x_1, x_2, x_4);
return x_5;
}
}
obj* l_monad__state__adapter__trans___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__state__adapter__trans___rarg___lambda__1___boxed), 5, 3);
lean::closure_set(x_7, 0, x_1);
lean::closure_set(x_7, 1, x_4);
lean::closure_set(x_7, 2, x_5);
x_8 = lean::apply_3(x_0, lean::box(0), x_7, x_6);
return x_8;
}
}
obj* l_monad__state__adapter__trans(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__state__adapter__trans___rarg___boxed), 7, 0);
return x_6;
}
}
obj* l_monad__state__adapter__trans___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_monad__state__adapter__trans___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_monad__state__adapter__trans___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_monad__state__adapter__trans___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_2);
lean::dec(x_3);
return x_7;
}
}
obj* l_monad__state__adapter__trans___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_monad__state__adapter__trans(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
return x_6;
}
}
obj* l_state__t_monad__state__adapter___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_10; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
x_7 = lean::apply_1(x_3, x_6);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::cnstr_get(x_0, 1);
lean::inc(x_13);
x_15 = lean::apply_1(x_5, x_8);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_adapt___rarg___lambda__1), 4, 3);
lean::closure_set(x_16, 0, x_0);
lean::closure_set(x_16, 1, x_4);
lean::closure_set(x_16, 2, x_10);
x_17 = lean::apply_4(x_13, lean::box(0), lean::box(0), x_15, x_16);
return x_17;
}
}
obj* l_state__t_monad__state__adapter(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad__state__adapter___rarg___boxed), 7, 0);
return x_3;
}
}
obj* l_state__t_monad__state__adapter___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_state__t_monad__state__adapter___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_1);
lean::dec(x_2);
return x_7;
}
}
obj* l_state__t_monad__state__adapter___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_state__t_monad__state__adapter(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_state__t_monad__run___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::apply_1(x_3, x_4);
x_9 = l_state__t_run_x_27___rarg___closed__1;
x_10 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_9, x_8);
x_11 = lean::apply_2(x_1, lean::box(0), x_10);
return x_11;
}
}
obj* l_state__t_monad__run(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad__run___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_state__t_monad__run___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_state__t_monad__run___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_state__t_monad__run___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_state__t_monad__run(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_monad__state__runner__trans___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::apply_3(x_0, lean::box(0), x_3, x_1);
return x_4;
}
}
obj* l_monad__state__runner__trans___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__state__runner__trans___rarg___lambda__1___boxed), 4, 2);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
x_6 = lean::apply_3(x_0, lean::box(0), x_5, x_3);
return x_6;
}
}
obj* l_monad__state__runner__trans(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__state__runner__trans___rarg___boxed), 5, 0);
return x_5;
}
}
obj* l_monad__state__runner__trans___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_monad__state__runner__trans___rarg___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_monad__state__runner__trans___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_monad__state__runner__trans___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_monad__state__runner__trans___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_monad__state__runner__trans(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_state__t_monad__state__runner___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_10; obj* x_13; obj* x_14; obj* x_15; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_7, 0);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::apply_1(x_2, x_3);
x_14 = l_state__t_run_x_27___rarg___closed__1;
x_15 = lean::apply_4(x_10, lean::box(0), lean::box(0), x_14, x_13);
return x_15;
}
}
obj* l_state__t_monad__state__runner(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad__state__runner___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_state__t_monad__state__runner___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_state__t_monad__state__runner___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_state__t_monad__state__runner___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_state__t_monad__state__runner(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
void initialize_init_control_alternative();
void initialize_init_control_lift();
void initialize_init_control_id();
void initialize_init_control_except();
static bool _G_initialized = false;
void initialize_init_control_state() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_control_alternative();
 initialize_init_control_lift();
 initialize_init_control_id();
 initialize_init_control_except();
 l_state__t = _init_l_state__t();
lean::mark_persistent(l_state__t);
 l_state__t_run_x_27___rarg___closed__1 = _init_l_state__t_run_x_27___rarg___closed__1();
lean::mark_persistent(l_state__t_run_x_27___rarg___closed__1);
 l_state = _init_l_state();
lean::mark_persistent(l_state);
}

// Lean compiler output
// Module: init.lean.parser.rec
// Imports: init.lean.parser.parsec init.fix
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
obj* l_lean_parser_monad__rec_trans___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_recurse(obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_alternative___rarg(obj*, obj*);
obj* l_lean_parser_rec__t_run__parsec___rarg___lambda__1(obj*, obj*);
obj* l_lean_parser_rec__t_monad__functor(obj*, obj*, obj*, obj*);
extern obj* l_mjoin___rarg___closed__1;
obj* l_lean_parser_rec__t_run__parsec___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_alternative___boxed(obj*, obj*, obj*);
obj* l_lean_parser_rec__t_run__parsec___rarg___lambda__1___closed__1;
obj* l_lean_parser_rec__t_monad__except___rarg(obj*);
obj* l_lean_parser_rec__t_monad__functor___boxed(obj*, obj*, obj*, obj*);
obj* l_reader__t_lift___boxed(obj*, obj*, obj*, obj*);
obj* l_reader__t_alternative___rarg(obj*, obj*);
obj* l_lean_parser_rec__t_monad(obj*, obj*, obj*);
obj* l_lean_parser_rec__t_monad___boxed(obj*, obj*, obj*);
obj* l_lean_parser_rec__t_run__parsec(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__rec_trans(obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_monad___rarg(obj*);
obj* l_lean_parser_rec__t_lean_parser_monad__parsec___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_run__parsec___rarg(obj*, obj*, obj*);
obj* l_lean_parser_rec__t_has__monad__lift___boxed(obj*, obj*, obj*);
obj* l_lean_parser_rec__t_monad__except(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_run___rarg(obj*, obj*, obj*);
obj* l_lean_parser_rec__t_monad__functor___rarg(obj*);
obj* l_lean_parser_rec__t_run__parsec___rarg___lambda__1___boxed(obj*, obj*);
obj* l_lean_parser_rec__t_lean_parser_monad__parsec___rarg___boxed(obj*, obj*, obj*);
obj* l_fix__core___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__rec_trans___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_alternative(obj*, obj*, obj*);
obj* l_lean_parser_rec__t_lean_parser_monad__parsec___rarg(obj*, obj*, obj*);
obj* l_lean_parser_rec__t_has__monad__lift___rarg(obj*);
obj* l_lean_parser_rec__t_monad__except___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_lean_parser_monad__parsec(obj*, obj*, obj*);
obj* l_reader__t_monad__except___rarg(obj*);
obj* l_lean_parser_monad__parsec__trans___rarg(obj*, obj*, obj*);
obj* l_lean_parser_rec__t_recurse___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__rec_base(obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_run___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_recurse___rarg(obj*, obj*);
obj* l_lean_parser_rec__t_run(obj*, obj*, obj*, obj*, obj*);
obj* l_reader__t_monad__functor___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_monad__except___rarg___lambda__2(obj*, obj*, obj*);
obj* l_reader__t_monad___rarg(obj*);
obj* l_lean_parser_monad__rec_base___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_has__monad__lift(obj*, obj*, obj*);
obj* l_lean_parser_monad__rec_trans___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_recurse___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_1, x_0);
return x_2;
}
}
obj* l_lean_parser_rec__t_recurse(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_recurse___rarg), 2, 0);
return x_4;
}
}
obj* l_lean_parser_rec__t_recurse___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_rec__t_recurse(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_lean_parser_rec__t_run___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad__except___rarg___lambda__2), 3, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_fix__core___rarg___boxed), 3, 2);
lean::closure_set(x_4, 0, x_1);
lean::closure_set(x_4, 1, x_3);
x_5 = lean::apply_1(x_0, x_4);
return x_5;
}
}
obj* l_lean_parser_rec__t_run(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_run___rarg), 3, 0);
return x_5;
}
}
obj* l_lean_parser_rec__t_run___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_parser_rec__t_run(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
obj* _init_l_lean_parser_rec__t_run__parsec___rarg___lambda__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("rec_t.run_parsec: no progress");
return x_0;
}
}
obj* l_lean_parser_rec__t_run__parsec___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::box(0);
x_3 = l_lean_parser_rec__t_run__parsec___rarg___lambda__1___closed__1;
x_4 = l_mjoin___rarg___closed__1;
x_5 = l_lean_parser_monad__parsec_error___rarg(x_0, lean::box(0), x_3, x_4, x_2, x_2);
return x_5;
}
}
obj* l_lean_parser_rec__t_run__parsec___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_run__parsec___rarg___lambda__1___boxed), 2, 1);
lean::closure_set(x_3, 0, x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad__except___rarg___lambda__2), 3, 1);
lean::closure_set(x_4, 0, x_2);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_fix__core___rarg___boxed), 3, 2);
lean::closure_set(x_5, 0, x_3);
lean::closure_set(x_5, 1, x_4);
x_6 = lean::apply_1(x_1, x_5);
return x_6;
}
}
obj* l_lean_parser_rec__t_run__parsec(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_run__parsec___rarg), 3, 0);
return x_6;
}
}
obj* l_lean_parser_rec__t_run__parsec___rarg___lambda__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_rec__t_run__parsec___rarg___lambda__1(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_rec__t_run__parsec___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_parser_rec__t_run__parsec(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
return x_6;
}
}
obj* l_lean_parser_rec__t_monad___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_reader__t_monad___rarg(x_0);
return x_1;
}
}
obj* l_lean_parser_rec__t_monad(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_monad___rarg), 1, 0);
return x_3;
}
}
obj* l_lean_parser_rec__t_monad___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_rec__t_monad(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_parser_rec__t_alternative___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_reader__t_alternative___rarg(x_0, x_1);
return x_2;
}
}
obj* l_lean_parser_rec__t_alternative(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_alternative___rarg), 2, 0);
return x_3;
}
}
obj* l_lean_parser_rec__t_alternative___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_rec__t_alternative(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_parser_rec__t_has__monad__lift___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___boxed), 4, 3);
lean::closure_set(x_1, 0, lean::box(0));
lean::closure_set(x_1, 1, lean::box(0));
lean::closure_set(x_1, 2, x_0);
return x_1;
}
}
obj* l_lean_parser_rec__t_has__monad__lift(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_has__monad__lift___rarg), 1, 0);
return x_3;
}
}
obj* l_lean_parser_rec__t_has__monad__lift___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_rec__t_has__monad__lift(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_parser_rec__t_monad__except___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_reader__t_monad__except___rarg(x_0);
return x_1;
}
}
obj* l_lean_parser_rec__t_monad__except(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_monad__except___rarg), 1, 0);
return x_5;
}
}
obj* l_lean_parser_rec__t_monad__except___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_parser_rec__t_monad__except(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_lean_parser_rec__t_lean_parser_monad__parsec___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; 
lean::inc(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___boxed), 4, 3);
lean::closure_set(x_4, 0, lean::box(0));
lean::closure_set(x_4, 1, lean::box(0));
lean::closure_set(x_4, 2, x_0);
lean::inc(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_monad__functor___boxed), 6, 5);
lean::closure_set(x_6, 0, lean::box(0));
lean::closure_set(x_6, 1, lean::box(0));
lean::closure_set(x_6, 2, lean::box(0));
lean::closure_set(x_6, 3, x_0);
lean::closure_set(x_6, 4, x_0);
x_7 = l_lean_parser_monad__parsec__trans___rarg(x_4, x_6, x_2);
return x_7;
}
}
obj* l_lean_parser_rec__t_lean_parser_monad__parsec(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_lean_parser_monad__parsec___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_lean_parser_rec__t_lean_parser_monad__parsec___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_rec__t_lean_parser_monad__parsec___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_lean_parser_rec__t_lean_parser_monad__parsec___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_rec__t_lean_parser_monad__parsec(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_parser_rec__t_monad__functor___rarg(obj* x_0) {
_start:
{
obj* x_2; 
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_monad__functor___boxed), 6, 5);
lean::closure_set(x_2, 0, lean::box(0));
lean::closure_set(x_2, 1, lean::box(0));
lean::closure_set(x_2, 2, lean::box(0));
lean::closure_set(x_2, 3, x_0);
lean::closure_set(x_2, 4, x_0);
return x_2;
}
}
obj* l_lean_parser_rec__t_monad__functor(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_monad__functor___rarg), 1, 0);
return x_4;
}
}
obj* l_lean_parser_rec__t_monad__functor___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_rec__t_monad__functor(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_lean_parser_monad__rec_trans___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::apply_2(x_0, lean::box(0), x_4);
return x_5;
}
}
obj* l_lean_parser_monad__rec_trans(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__rec_trans___rarg___boxed), 4, 0);
return x_4;
}
}
obj* l_lean_parser_monad__rec_trans___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_monad__rec_trans___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_lean_parser_monad__rec_trans___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_monad__rec_trans(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_lean_parser_monad__rec_base(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_recurse___rarg), 2, 0);
return x_4;
}
}
obj* l_lean_parser_monad__rec_base___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_monad__rec_base(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* initialize_init_lean_parser_parsec(obj*);
obj* initialize_init_fix(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_parser_rec(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_parsec(w);
if (io_result_is_error(w)) return w;
w = initialize_init_fix(w);
 l_lean_parser_rec__t_run__parsec___rarg___lambda__1___closed__1 = _init_l_lean_parser_rec__t_run__parsec___rarg___lambda__1___closed__1();
lean::mark_persistent(l_lean_parser_rec__t_run__parsec___rarg___lambda__1___closed__1);
return w;
}

// Lean compiler output
// Module: init.lean.parser.rec
// Imports: init.lean.parser.parsec
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
obj* l_lean_parser_monad__parsec_error___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l___private_3693562977__run__aux(obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_recurse(obj*, obj*, obj*);
obj* l_lean_parser_rec__t_alternative___rarg(obj*, obj*);
obj* l_lean_parser_rec__t_run__parsec___rarg___lambda__1(obj*, obj*, obj*);
obj* l_lean_parser_rec__t_monad__functor(obj*, obj*, obj*, obj*);
extern obj* l_mjoin___rarg___closed__1;
obj* l_lean_parser_rec__t_run__parsec___rarg___lambda__1___closed__1;
obj* l_lean_parser_rec__t_monad__except___rarg(obj*);
obj* l_reader__t_alternative___rarg(obj*, obj*);
obj* l_lean_parser_rec__t_monad(obj*, obj*, obj*);
obj* l___private_3693562977__run__aux___main(obj*, obj*, obj*);
obj* l_reader__t_monad__functor(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_rec__t_run__parsec___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_rec__t_run__parsec(obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_run___at_lean_parser_rec__t_run__parsec___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__rec_base___rarg(obj*);
obj* l_lean_parser_monad__rec_trans(obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_monad___rarg(obj*);
obj* l_lean_parser_rec__t_recurse___rarg___lambda__1(obj*, obj*);
obj* l_lean_parser_rec__t_run__parsec___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_monad__except(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_run___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_monad__functor___rarg(obj*);
extern obj* l_lean_parser_monad__parsec_left__over___rarg___closed__1;
obj* l_lean_parser_rec__t_alternative(obj*, obj*, obj*);
obj* l_lean_parser_rec__t_lean_parser_monad__parsec___rarg(obj*, obj*, obj*);
obj* l___private_3693562977__run__aux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_has__monad__lift___rarg(obj*);
obj* l_lean_parser_rec__t_lean_parser_monad__parsec(obj*, obj*, obj*);
obj* l_reader__t_monad__except___rarg(obj*);
obj* l_lean_parser_monad__parsec__trans___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__rec_base(obj*, obj*, obj*);
obj* l_lean_parser_rec__t_run__parsec___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_recurse___rarg(obj*, obj*, obj*);
obj* l_reader__t_lift(obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_run(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_rec__t_run__parsec___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_reader__t_monad___rarg(obj*);
obj* l_lean_parser_rec__t_has__monad__lift(obj*, obj*, obj*);
obj* l___private_3693562977__run__aux___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_run___at_lean_parser_rec__t_run__parsec___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__rec_trans___rarg(obj*, obj*, obj*, obj*);
obj* _init_l_lean_parser_rec__t() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_parser_rec__t_recurse___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; obj* x_11; obj* x_12; obj* x_13; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::apply_2(x_8, lean::box(0), x_2);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_recurse___rarg___lambda__1), 2, 1);
lean::closure_set(x_12, 0, x_1);
x_13 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_11, x_12);
return x_13;
}
}
obj* l_lean_parser_rec__t_recurse___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_1, x_0);
return x_2;
}
}
obj* l_lean_parser_rec__t_recurse(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_recurse___rarg), 3, 0);
return x_6;
}
}
obj* l___private_3693562977__run__aux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_7; obj* x_8; obj* x_12; obj* x_13; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_2, x_7);
lean::dec(x_7);
lean::dec(x_2);
lean::inc(x_1);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l___private_3693562977__run__aux___main___rarg), 4, 3);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, x_1);
lean::closure_set(x_12, 2, x_8);
x_13 = lean::apply_2(x_1, x_3, x_12);
return x_13;
}
else
{
obj* x_16; 
lean::dec(x_1);
lean::dec(x_2);
x_16 = lean::apply_1(x_0, x_3);
return x_16;
}
}
}
obj* l___private_3693562977__run__aux___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l___private_3693562977__run__aux___main___rarg), 4, 0);
return x_6;
}
}
obj* l___private_3693562977__run__aux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_3693562977__run__aux___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_3693562977__run__aux(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l___private_3693562977__run__aux___rarg), 4, 0);
return x_8;
}
}
obj* l_lean_parser_rec__t_run___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l___private_3693562977__run__aux___rarg), 4, 3);
lean::closure_set(x_4, 0, x_1);
lean::closure_set(x_4, 1, x_2);
lean::closure_set(x_4, 2, x_3);
x_5 = lean::apply_1(x_0, x_4);
return x_5;
}
}
obj* l_lean_parser_rec__t_run(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_10; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_run___rarg), 4, 0);
return x_10;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_rec__t_run__parsec___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_rec__t_run__parsec___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_rec__t_run__parsec___spec__1___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_rec__t_run___at_lean_parser_rec__t_run__parsec___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l___private_3693562977__run__aux___rarg), 4, 3);
lean::closure_set(x_4, 0, x_1);
lean::closure_set(x_4, 1, x_2);
lean::closure_set(x_4, 2, x_3);
x_5 = lean::apply_1(x_0, x_4);
return x_5;
}
}
obj* l_lean_parser_rec__t_run___at_lean_parser_rec__t_run__parsec___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_10; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_run___at_lean_parser_rec__t_run__parsec___spec__2___rarg), 4, 0);
return x_10;
}
}
obj* l_lean_parser_rec__t_run__parsec___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
lean::dec(x_1);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
x_10 = l_lean_parser_monad__parsec_left__over___rarg___closed__1;
lean::inc(x_10);
x_12 = lean::apply_2(x_8, lean::box(0), x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_run__parsec___rarg___lambda__2), 5, 4);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, x_2);
lean::closure_set(x_13, 2, x_3);
lean::closure_set(x_13, 3, x_4);
x_14 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
}
obj* l_lean_parser_rec__t_run__parsec___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_11; 
lean::dec(x_2);
lean::dec(x_0);
x_5 = lean::box(0);
x_6 = l_lean_parser_rec__t_run__parsec___rarg___lambda__1___closed__1;
x_7 = l_mjoin___rarg___closed__1;
lean::inc(x_5);
lean::inc(x_7);
lean::inc(x_6);
x_11 = l_lean_parser_monad__parsec_error___at_lean_parser_rec__t_run__parsec___spec__1___rarg(x_1, lean::box(0), x_6, x_7, x_5, x_5);
return x_11;
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
obj* l_lean_parser_rec__t_run__parsec___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_12; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_run__parsec___rarg___lambda__1), 3, 2);
lean::closure_set(x_5, 0, x_0);
lean::closure_set(x_5, 1, x_1);
x_6 = lean::string_iterator_remaining(x_4);
lean::dec(x_4);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_add(x_6, x_8);
lean::dec(x_8);
lean::dec(x_6);
x_12 = l_lean_parser_rec__t_run___at_lean_parser_rec__t_run__parsec___spec__2___rarg(x_2, x_5, x_3, x_9);
return x_12;
}
}
obj* l_lean_parser_rec__t_run__parsec(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_run__parsec___rarg), 5, 0);
return x_8;
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
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_monad___rarg), 1, 0);
return x_6;
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
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_alternative___rarg), 2, 0);
return x_6;
}
}
obj* l_lean_parser_rec__t_has__monad__lift___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift), 4, 3);
lean::closure_set(x_1, 0, lean::box(0));
lean::closure_set(x_1, 1, lean::box(0));
lean::closure_set(x_1, 2, x_0);
return x_1;
}
}
obj* l_lean_parser_rec__t_has__monad__lift(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_has__monad__lift___rarg), 1, 0);
return x_6;
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
obj* x_10; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_monad__except___rarg), 1, 0);
return x_10;
}
}
obj* l_lean_parser_rec__t_lean_parser_monad__parsec___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; 
lean::dec(x_1);
lean::inc(x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift), 4, 3);
lean::closure_set(x_5, 0, lean::box(0));
lean::closure_set(x_5, 1, lean::box(0));
lean::closure_set(x_5, 2, x_0);
lean::inc(x_0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_monad__functor), 6, 5);
lean::closure_set(x_7, 0, lean::box(0));
lean::closure_set(x_7, 1, lean::box(0));
lean::closure_set(x_7, 2, lean::box(0));
lean::closure_set(x_7, 3, x_0);
lean::closure_set(x_7, 4, x_0);
x_8 = l_lean_parser_monad__parsec__trans___rarg(x_5, x_7, x_2);
return x_8;
}
}
obj* l_lean_parser_rec__t_lean_parser_monad__parsec(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_lean_parser_monad__parsec___rarg), 3, 0);
return x_6;
}
}
obj* l_lean_parser_rec__t_monad__functor___rarg(obj* x_0) {
_start:
{
obj* x_2; 
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_monad__functor), 6, 5);
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
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_monad__functor___rarg), 1, 0);
return x_8;
}
}
obj* l_lean_parser_monad__rec_trans___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; 
lean::dec(x_2);
x_5 = lean::apply_1(x_1, x_3);
x_6 = lean::apply_2(x_0, lean::box(0), x_5);
return x_6;
}
}
obj* l_lean_parser_monad__rec_trans(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__rec_trans___rarg), 4, 0);
return x_8;
}
}
obj* l_lean_parser_monad__rec_base___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_recurse___rarg), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_parser_monad__rec_base(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__rec_base___rarg), 1, 0);
return x_6;
}
}
void initialize_init_lean_parser_parsec();
static bool _G_initialized = false;
void initialize_init_lean_parser_rec() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_parser_parsec();
 l_lean_parser_rec__t = _init_l_lean_parser_rec__t();
 l_lean_parser_rec__t_run__parsec___rarg___lambda__1___closed__1 = _init_l_lean_parser_rec__t_run__parsec___rarg___lambda__1___closed__1();
}

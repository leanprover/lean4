// Lean compiler output
// Module: init.lean.parser.rec
// Imports: init.lean.parser.parsec
#include "runtime/object.h"
#include "runtime/apply.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#endif
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s6_rec__t_s11_run__parsec_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_rec__t_s11_run__parsec_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_rec__t_s11_run__parsec_s6___rarg_s11___lambda__1_s11___closed__1;
obj* _l_s9___private_3693562977__s8_run__aux(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s10_monad__rec_s4_base_s6___rarg(obj*);
obj* _l_s9_reader__t_s11_alternative_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_rec__t_s4_lean_s6_parser_s13_monad__parsec(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_rec__t_s4_lean_s6_parser_s13_monad__parsec_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s10_monad__rec_s5_trans_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_rec__t;
obj* _l_s4_lean_s6_parser_s6_rec__t_s11_run__parsec_s6___rarg_s11___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_rec__t_s11_alternative(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_rec__t_s14_monad__functor_s6___rarg(obj*);
obj* _l_s5_mjoin_s6___rarg_s11___closed__1;
obj* _l_s9___private_3693562977__s8_run__aux_s6___main(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_rec__t_s5_monad_s6___rarg(obj*);
obj* _l_s4_lean_s6_parser_s6_rec__t_s11_run__parsec(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_rec__t_s16_has__monad__lift_s6___rarg(obj*);
obj* _l_s9_reader__t_s14_monad__functor(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s9_reader__t_s5_monad_s6___rarg(obj*);
obj* _l_s9_reader__t_s4_lift(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_rec__t_s7_recurse_s6___rarg_s11___lambda__1(obj*, obj*);
obj* _l_s4_lean_s6_parser_s20_monad__parsec__trans_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_rec__t_s5_monad(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_rec__t_s11_run__parsec_s6___rarg_s11___lambda__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_rec__t_s3_run_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_rec__t_s3_run(obj*, obj*, obj*, obj*, obj*);
obj* _l_s9___private_3693562977__s8_run__aux_s6___main_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_rec__t_s7_recurse(obj*, obj*, obj*);
obj* _l_s9___private_3693562977__s8_run__aux_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* _l_s9_reader__t_s13_monad__except_s6___rarg(obj*);
obj* _l_s4_lean_s6_parser_s6_rec__t_s14_monad__functor(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_rec__t_s13_monad__except(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s10_monad__rec_s5_trans(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s6_parser_s6_rec__t_s7_recurse_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_rec__t_s11_alternative_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_rec__t_s13_monad__except_s6___rarg(obj*);
obj* _l_s4_lean_s6_parser_s6_rec__t_s16_has__monad__lift(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_rec__t_s3_run_s4___at_s4_lean_s6_parser_s6_rec__t_s11_run__parsec_s9___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_rec__t_s3_run_s4___at_s4_lean_s6_parser_s6_rec__t_s11_run__parsec_s9___spec__2_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s6_rec__t_s11_run__parsec_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s10_monad__rec_s4_base(obj*, obj*, obj*);
obj* _init__l_s4_lean_s6_parser_s6_rec__t() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _l_s4_lean_s6_parser_s6_rec__t_s7_recurse_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
x_12 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s6_rec__t_s7_recurse_s6___rarg_s11___lambda__1), 2, 1);
lean::closure_set(x_12, 0, x_1);
x_13 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_11, x_12);
return x_13;
}
}
obj* _l_s4_lean_s6_parser_s6_rec__t_s7_recurse_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1) {
{
obj* x_2; 
x_2 = lean::apply_1(x_1, x_0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s6_rec__t_s7_recurse(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s6_rec__t_s7_recurse_s6___rarg), 3, 0);
return x_6;
}
}
obj* _l_s9___private_3693562977__s8_run__aux_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_2, x_4);
lean::dec(x_4);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_9; obj* x_13; obj* x_14; 
lean::dec(x_5);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_2, x_8);
lean::dec(x_8);
lean::dec(x_2);
lean::inc(x_1);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_3693562977__s8_run__aux_s6___main_s6___rarg), 4, 3);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, x_1);
lean::closure_set(x_13, 2, x_9);
x_14 = lean::apply_2(x_1, x_3, x_13);
return x_14;
}
else
{
obj* x_18; 
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_2);
x_18 = lean::apply_1(x_0, x_3);
return x_18;
}
}
}
obj* _l_s9___private_3693562977__s8_run__aux_s6___main(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_3693562977__s8_run__aux_s6___main_s6___rarg), 4, 0);
return x_6;
}
}
obj* _l_s9___private_3693562977__s8_run__aux_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_4; 
x_4 = _l_s9___private_3693562977__s8_run__aux_s6___main_s6___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* _l_s9___private_3693562977__s8_run__aux(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_3693562977__s8_run__aux_s6___rarg), 4, 0);
return x_8;
}
}
obj* _l_s4_lean_s6_parser_s6_rec__t_s3_run_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_4; obj* x_5; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_3693562977__s8_run__aux_s6___rarg), 4, 3);
lean::closure_set(x_4, 0, x_1);
lean::closure_set(x_4, 1, x_2);
lean::closure_set(x_4, 2, x_3);
x_5 = lean::apply_1(x_0, x_4);
return x_5;
}
}
obj* _l_s4_lean_s6_parser_s6_rec__t_s3_run(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_10; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s6_rec__t_s3_run_s6___rarg), 4, 0);
return x_10;
}
}
obj* _l_s4_lean_s6_parser_s6_rec__t_s11_run__parsec_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
lean::dec(x_1);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
x_10 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_10);
x_12 = lean::apply_2(x_8, lean::box(0), x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s6_rec__t_s11_run__parsec_s6___rarg_s11___lambda__2), 5, 4);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, x_2);
lean::closure_set(x_13, 2, x_3);
lean::closure_set(x_13, 3, x_4);
x_14 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
}
obj* _l_s4_lean_s6_parser_s6_rec__t_s11_run__parsec_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_5; obj* x_6; obj* x_7; obj* x_11; 
lean::dec(x_2);
lean::dec(x_0);
x_5 = lean::alloc_cnstr(0, 0, 0);
;
x_6 = _l_s4_lean_s6_parser_s6_rec__t_s11_run__parsec_s6___rarg_s11___lambda__1_s11___closed__1;
x_7 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_5);
lean::inc(x_7);
lean::inc(x_6);
x_11 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s6_rec__t_s11_run__parsec_s9___spec__1_s6___rarg(x_1, lean::box(0), x_6, x_7, x_5, x_5);
return x_11;
}
}
obj* _init__l_s4_lean_s6_parser_s6_rec__t_s11_run__parsec_s6___rarg_s11___lambda__1_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string("rec_t.run_parsec: no progress");
return x_0;
}
}
obj* _l_s4_lean_s6_parser_s6_rec__t_s11_run__parsec_s6___rarg_s11___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_12; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s6_rec__t_s11_run__parsec_s6___rarg_s11___lambda__1), 3, 2);
lean::closure_set(x_5, 0, x_0);
lean::closure_set(x_5, 1, x_1);
x_6 = lean::string_iterator_remaining(x_4);
lean::dec(x_4);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_add(x_6, x_8);
lean::dec(x_8);
lean::dec(x_6);
x_12 = _l_s4_lean_s6_parser_s6_rec__t_s3_run_s4___at_s4_lean_s6_parser_s6_rec__t_s11_run__parsec_s9___spec__2_s6___rarg(x_2, x_5, x_3, x_9);
return x_12;
}
}
obj* _l_s4_lean_s6_parser_s6_rec__t_s11_run__parsec(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s6_rec__t_s11_run__parsec_s6___rarg), 5, 0);
return x_8;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s6_rec__t_s11_run__parsec_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s6_rec__t_s11_run__parsec_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s6_rec__t_s11_run__parsec_s9___spec__1_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s6_rec__t_s3_run_s4___at_s4_lean_s6_parser_s6_rec__t_s11_run__parsec_s9___spec__2_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_4; obj* x_5; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_3693562977__s8_run__aux_s6___rarg), 4, 3);
lean::closure_set(x_4, 0, x_1);
lean::closure_set(x_4, 1, x_2);
lean::closure_set(x_4, 2, x_3);
x_5 = lean::apply_1(x_0, x_4);
return x_5;
}
}
obj* _l_s4_lean_s6_parser_s6_rec__t_s3_run_s4___at_s4_lean_s6_parser_s6_rec__t_s11_run__parsec_s9___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_10; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s6_rec__t_s3_run_s4___at_s4_lean_s6_parser_s6_rec__t_s11_run__parsec_s9___spec__2_s6___rarg), 4, 0);
return x_10;
}
}
obj* _l_s4_lean_s6_parser_s6_rec__t_s5_monad_s6___rarg(obj* x_0) {
{
obj* x_1; 
x_1 = _l_s9_reader__t_s5_monad_s6___rarg(x_0);
return x_1;
}
}
obj* _l_s4_lean_s6_parser_s6_rec__t_s5_monad(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s6_rec__t_s5_monad_s6___rarg), 1, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s6_rec__t_s11_alternative_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; 
x_2 = _l_s9_reader__t_s11_alternative_s6___rarg(x_0, x_1);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s6_rec__t_s11_alternative(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s6_rec__t_s11_alternative_s6___rarg), 2, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s6_rec__t_s16_has__monad__lift_s6___rarg(obj* x_0) {
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_reader__t_s4_lift), 4, 3);
lean::closure_set(x_1, 0, lean::box(0));
lean::closure_set(x_1, 1, lean::box(0));
lean::closure_set(x_1, 2, x_0);
return x_1;
}
}
obj* _l_s4_lean_s6_parser_s6_rec__t_s16_has__monad__lift(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s6_rec__t_s16_has__monad__lift_s6___rarg), 1, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s6_rec__t_s13_monad__except_s6___rarg(obj* x_0) {
{
obj* x_1; 
x_1 = _l_s9_reader__t_s13_monad__except_s6___rarg(x_0);
return x_1;
}
}
obj* _l_s4_lean_s6_parser_s6_rec__t_s13_monad__except(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_10; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s6_rec__t_s13_monad__except_s6___rarg), 1, 0);
return x_10;
}
}
obj* _l_s4_lean_s6_parser_s6_rec__t_s4_lean_s6_parser_s13_monad__parsec_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_5; obj* x_7; obj* x_8; 
lean::dec(x_1);
lean::inc(x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_reader__t_s4_lift), 4, 3);
lean::closure_set(x_5, 0, lean::box(0));
lean::closure_set(x_5, 1, lean::box(0));
lean::closure_set(x_5, 2, x_0);
lean::inc(x_0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_reader__t_s14_monad__functor), 6, 5);
lean::closure_set(x_7, 0, lean::box(0));
lean::closure_set(x_7, 1, lean::box(0));
lean::closure_set(x_7, 2, lean::box(0));
lean::closure_set(x_7, 3, x_0);
lean::closure_set(x_7, 4, x_0);
x_8 = _l_s4_lean_s6_parser_s20_monad__parsec__trans_s6___rarg(x_5, x_7, x_2);
return x_8;
}
}
obj* _l_s4_lean_s6_parser_s6_rec__t_s4_lean_s6_parser_s13_monad__parsec(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s6_rec__t_s4_lean_s6_parser_s13_monad__parsec_s6___rarg), 3, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s6_rec__t_s14_monad__functor_s6___rarg(obj* x_0) {
{
obj* x_2; 
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_reader__t_s14_monad__functor), 6, 5);
lean::closure_set(x_2, 0, lean::box(0));
lean::closure_set(x_2, 1, lean::box(0));
lean::closure_set(x_2, 2, lean::box(0));
lean::closure_set(x_2, 3, x_0);
lean::closure_set(x_2, 4, x_0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s6_rec__t_s14_monad__functor(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s6_rec__t_s14_monad__functor_s6___rarg), 1, 0);
return x_8;
}
}
obj* _l_s4_lean_s6_parser_s10_monad__rec_s5_trans_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_5; obj* x_6; 
lean::dec(x_2);
x_5 = lean::apply_1(x_1, x_3);
x_6 = lean::apply_2(x_0, lean::box(0), x_5);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s10_monad__rec_s5_trans(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s10_monad__rec_s5_trans_s6___rarg), 4, 0);
return x_8;
}
}
obj* _l_s4_lean_s6_parser_s10_monad__rec_s4_base_s6___rarg(obj* x_0) {
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s6_rec__t_s7_recurse_s6___rarg), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _l_s4_lean_s6_parser_s10_monad__rec_s4_base(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s10_monad__rec_s4_base_s6___rarg), 1, 0);
return x_6;
}
}
void _l_initialize__l_s4_init_s4_lean_s6_parser_s6_parsec();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_lean_s6_parser_s3_rec() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_lean_s6_parser_s6_parsec();
 _l_s4_lean_s6_parser_s6_rec__t = _init__l_s4_lean_s6_parser_s6_rec__t();
 _l_s4_lean_s6_parser_s6_rec__t_s11_run__parsec_s6___rarg_s11___lambda__1_s11___closed__1 = _init__l_s4_lean_s6_parser_s6_rec__t_s11_run__parsec_s6___rarg_s11___lambda__1_s11___closed__1();
}

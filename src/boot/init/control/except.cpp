// Lean compiler output
// Module: init.control.except
// Imports: init.control.alternative init.control.lift init.data.to_string init.control.monad_fail
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#endif
obj* _l_s9_except__t_s5_adapt_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s6_except_s9_has__repr(obj*, obj*);
obj* _l_s9_except__t_s14_monad__functor_s6___rarg(obj*, obj*);
obj* _l_s9_except__t_s5_monad_s6___rarg_s11___lambda__3(obj*, obj*, obj*);
obj* _l_s9_except__t_s16_has__monad__lift(obj*, obj*);
obj* _l_s6_except_s10_to__string_s6___rarg(obj*, obj*, obj*);
obj* _l_s9_except__t_s11_monad__fail_s6___rarg(obj*, obj*, obj*);
obj* _l_s8_function_s4_comp_s6___rarg(obj*, obj*, obj*);
obj* _l_s13_monad__except_s10_orelse_x27_s6___rarg_s7___boxed(obj*, obj*, obj*, obj*, obj*);
obj* _l_s13_monad__except_s12_lift__except_s6___main(obj*, obj*, obj*);
obj* _l_s6_except_s5_catch(obj*, obj*);
obj* _l_s9_except__t_s5_monad_s6___rarg_s11___lambda__8(obj*, obj*);
obj* _l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__6_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s6_except_s5_monad_s11___lambda__3(obj*, obj*, obj*, obj*);
obj* _l_s9_except__t_s3_run(obj*, obj*, obj*);
unsigned char _l_s6_except_s8_to__bool_s6___main_s6___rarg(obj*);
obj* _l_s9_except__t_s22_monad__except__adapter(obj*, obj*, obj*);
obj* _l_s13_monad__except_s10_orelse_x27_s6___rarg_s11___lambda__2_s7___boxed(obj*, obj*, obj*, obj*, obj*);
obj* _l_s6_except_s4_repr(obj*, obj*);
obj* _l_s6_except_s15_has__to__string(obj*, obj*);
obj* _l_s9_except__t_s5_catch_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s6_except_s10_map__error(obj*, obj*, obj*);
obj* _l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__4(obj*, obj*);
obj* _l_s9_except__t_s5_catch(obj*, obj*);
obj* _l_s29_monad__except__adapter__trans(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s9_except__t_s6_return_s6___rarg(obj*, obj*, obj*);
obj* _l_s6_except_s5_monad_s11___lambda__4(obj*, obj*, obj*, obj*);
obj* _l_s9_except__t_s5_catch_s6___rarg_s11___lambda__1(obj*, obj*, obj*);
obj* _l_s6_except_s4_repr_s6___rarg(obj*, obj*, obj*);
obj* _l_s13_monad__except_s12_lift__except_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s6_except_s6_return(obj*, obj*);
obj* _l_s9_except__t;
obj* _l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__7_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s9_except__t_s5_monad(obj*, obj*);
obj* _l_s6_except_s8_to__bool_s6___main(obj*, obj*);
obj* _l_s9_except__t_s4_bind(obj*, obj*);
obj* _l_s6_except_s3_map_s6___main(obj*, obj*, obj*);
obj* _l_s6_except_s8_to__bool(obj*, obj*);
obj* _l_s8_function_s5_const_s6___rarg(obj*, obj*);
obj* _l_s6_except_s5_monad_s11___lambda__2(obj*, obj*, obj*, obj*);
obj* _l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__7(obj*, obj*);
obj* _l_s6_except_s3_map_s6___main_s6___rarg(obj*, obj*);
obj* _l_s9_except__t_s14_monad__functor(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s6_except_s3_map(obj*, obj*, obj*);
obj* _l_s13_monad__except_s10_orelse_x27(obj*, obj*);
obj* _l_s9_except__t_s5_monad_s6___rarg_s11___lambda__5(obj*, obj*, obj*);
obj* _l_s9_except__t_s13_monad__except(obj*, obj*);
obj* _l_s13_monad__except_s6_orelse_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s6_except_s5_monad_s11___closed__1;
obj* _l_s6_except_s13_monad__except_s11___lambda__1(obj*, obj*);
obj* _l_s9_except__t_s2_mk_s6___rarg(obj*);
obj* _l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s6_except_s9_has__repr_s6___rarg(obj*, obj*);
obj* _l_s6_except_s13_monad__except_s11___closed__1;
obj* _l_s6_except_s4_repr_s6___main(obj*, obj*);
obj* _l_s9_except__t_s10_bind__cont_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s6_except_s8_to__bool_s6___main_s6___rarg_s7___boxed(obj*);
obj* _l_s6_except_s10_map__error_s6___main(obj*, obj*, obj*);
obj* _l_s9_except__t_s4_bind_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s6_except_s10_to__option_s6___rarg(obj*);
obj* _l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__4_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s9_except__t_s5_adapt(obj*, obj*);
obj* _l_s9_except__t_s22_monad__except__adapter_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s9_except__t_s13_monad__except_s6___rarg(obj*);
obj* _l_s6_except_s15_has__to__string_s6___rarg(obj*, obj*);
obj* _l_s9_except__t_s10_monad__run(obj*, obj*, obj*);
obj* _l_s9_except__t_s4_lift_s6___rarg_s11___lambda__1(obj*);
obj* _l_s13_monad__except_s10_orelse_x27_s6___rarg_s11___lambda__1_s7___boxed(obj*, obj*, obj*, obj*);
obj* _l_s6_except_s5_catch_s6___rarg(obj*, obj*);
obj* _l_s9_except__t_s3_run_s6___rarg(obj*);
obj* _l_s13_monad__except_s6_orelse(obj*, obj*);
obj* _l_s6_except_s10_to__option(obj*, obj*);
obj* _l_s9_except__t_s5_monad_s6___rarg_s11___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* _l_s13_monad__except_s10_orelse_x27_s6___rarg(obj*, obj*, obj*, obj*, unsigned char);
obj* _l_s6_except_s10_to__string_s6___main(obj*, obj*);
obj* _l_s9_except__t_s5_monad_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* _l_s6_except_s10_to__string_s6___main_s6___rarg_s11___closed__1;
obj* _l_s6_except_s10_to__option_s6___main_s6___rarg(obj*);
obj* _l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__6(obj*, obj*);
obj* _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
obj* _l_s6_except_s13_monad__except(obj*);
obj* _l_s9_except__t_s10_bind__cont(obj*, obj*);
obj* _l_s6_except_s4_bind(obj*, obj*, obj*);
obj* _l_s13_monad__except_s10_orelse_x27_s6___rarg_s11___lambda__1(obj*, unsigned char, obj*, obj*);
obj* _l_s9_except__t_s11_monad__fail(obj*);
obj* _l_s6_except_s4_bind_s6___rarg(obj*, obj*);
obj* _l_s9_except__t_s16_has__monad__lift_s6___rarg(obj*);
obj* _l_s9_except__t_s5_monad_s6___rarg_s11___lambda__4(obj*, obj*, obj*, obj*, obj*);
obj* _l_s6_except_s10_to__string_s6___main_s6___rarg_s11___closed__2;
obj* _l_s6_except_s5_monad(obj*);
obj* _l_s6_except_s10_to__string_s6___main_s6___rarg(obj*, obj*, obj*);
obj* _l_s9_except__t_s13_monad__except_s6___rarg_s11___lambda__1(obj*, obj*, obj*);
obj* _l_s9_except__t_s5_monad_s6___rarg_s11___lambda__7(obj*, obj*, obj*, obj*, obj*);
obj* _l_s9_except__t_s6_return(obj*, obj*);
obj* _l_s6_except_s10_map__error_s6___main_s6___rarg(obj*, obj*);
obj* _l_s9_except__t_s10_monad__run_s6___rarg(obj*, obj*, obj*);
obj* _l_s6_except_s6_return_s6___rarg(obj*);
obj* _l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__5(obj*, obj*);
obj* _l_s6_except_s10_map__error_s6___rarg(obj*, obj*);
obj* _l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__3_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s13_monad__except_s12_lift__except_s6___main_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__3(obj*, obj*);
obj* _l_s29_monad__except__adapter__trans_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s6_except_s4_repr_s6___main_s6___rarg(obj*, obj*, obj*);
obj* _l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__5_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s9_except__t_s10_bind__cont_s6___main_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s6_except_s10_to__string(obj*, obj*);
obj* _l_s9_except__t_s5_monad_s6___rarg_s11___lambda__9(obj*, obj*, obj*, obj*, obj*);
obj* _l_s9_except__t_s2_mk(obj*, obj*, obj*);
obj* _l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__2_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s6_except_s10_to__option_s6___main(obj*, obj*);
unsigned char _l_s6_except_s8_to__bool_s6___rarg(obj*);
obj* _l_s13_monad__except_s10_orelse_x27_s6___rarg_s11___lambda__2(obj*, unsigned char, obj*, obj*, obj*);
obj* _l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__1(obj*, obj*);
obj* _l_s9_except__t_s21_except__t__of__except_s6___rarg(obj*, obj*, obj*);
obj* _l_s13_monad__except_s12_lift__except(obj*, obj*, obj*);
obj* _l_s9_except__t_s5_monad_s6___rarg_s11___lambda__6(obj*, obj*, obj*);
obj* _l_s9_except__t_s4_lift_s6___rarg(obj*, obj*, obj*);
obj* _l_s9_except__t_s10_bind__cont_s6___main(obj*, obj*);
obj* _l_s6_except_s8_to__bool_s6___rarg_s7___boxed(obj*);
obj* _l_s6_except_s5_monad_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s9_except__t_s5_monad_s6___rarg(obj*);
obj* _l_s6_except_s3_map_s6___rarg(obj*, obj*);
obj* _l_s24_monad__functor__t__trans_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s9_except__t_s21_except__t__of__except(obj*, obj*);
obj* _l_s6_except_s5_monad_s11___lambda__5(obj*, obj*, obj*, obj*);
obj* _l_s9_except__t_s4_lift_s6___rarg_s11___closed__1;
obj* _l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__2(obj*, obj*);
obj* _l_s9_except__t_s4_lift(obj*, obj*);
obj* _l_s6_except_s10_to__string_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{

if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_7 = lean::apply_1(x_0, x_4);
x_8 = _l_s6_except_s10_to__string_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_8);
x_10 = lean::string_append(x_8, x_7);
lean::dec(x_7);
x_12 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
x_13 = lean::string_append(x_10, x_12);
return x_13;
}
else
{
obj* x_15; obj* x_18; obj* x_19; obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_0);
x_15 = lean::cnstr_get(x_2, 0);
lean::inc(x_15);
lean::dec(x_2);
x_18 = lean::apply_1(x_1, x_15);
x_19 = _l_s6_except_s10_to__string_s6___main_s6___rarg_s11___closed__2;
lean::inc(x_19);
x_21 = lean::string_append(x_19, x_18);
lean::dec(x_18);
x_23 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
x_24 = lean::string_append(x_21, x_23);
return x_24;
}
}
}
obj* _init__l_s6_except_s10_to__string_s6___main_s6___rarg_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string("(error ");
return x_0;
}
}
obj* _init__l_s6_except_s10_to__string_s6___main_s6___rarg_s11___closed__2() {
{
obj* x_0; 
x_0 = lean::mk_string("(ok ");
return x_0;
}
}
obj* _l_s6_except_s10_to__string_s6___main(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_except_s10_to__string_s6___main_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s6_except_s10_to__string_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; 
x_3 = _l_s6_except_s10_to__string_s6___main_s6___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s6_except_s10_to__string(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_except_s10_to__string_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s6_except_s4_repr_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{

if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_7 = lean::apply_1(x_0, x_4);
x_8 = _l_s6_except_s10_to__string_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_8);
x_10 = lean::string_append(x_8, x_7);
lean::dec(x_7);
x_12 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
x_13 = lean::string_append(x_10, x_12);
return x_13;
}
else
{
obj* x_15; obj* x_18; obj* x_19; obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_0);
x_15 = lean::cnstr_get(x_2, 0);
lean::inc(x_15);
lean::dec(x_2);
x_18 = lean::apply_1(x_1, x_15);
x_19 = _l_s6_except_s10_to__string_s6___main_s6___rarg_s11___closed__2;
lean::inc(x_19);
x_21 = lean::string_append(x_19, x_18);
lean::dec(x_18);
x_23 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
x_24 = lean::string_append(x_21, x_23);
return x_24;
}
}
}
obj* _l_s6_except_s4_repr_s6___main(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_except_s4_repr_s6___main_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s6_except_s4_repr_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; 
x_3 = _l_s6_except_s4_repr_s6___main_s6___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s6_except_s4_repr(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_except_s4_repr_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s6_except_s15_has__to__string_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_except_s10_to__string_s6___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* _l_s6_except_s15_has__to__string(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_except_s15_has__to__string_s6___rarg), 2, 0);
return x_4;
}
}
obj* _l_s6_except_s9_has__repr_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_except_s4_repr_s6___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* _l_s6_except_s9_has__repr(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_except_s9_has__repr_s6___rarg), 2, 0);
return x_4;
}
}
obj* _l_s6_except_s6_return_s6___rarg(obj* x_0) {
{
obj* x_1; 
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _l_s6_except_s6_return(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_except_s6_return_s6___rarg), 1, 0);
return x_4;
}
}
obj* _l_s6_except_s3_map_s6___main_s6___rarg(obj* x_0, obj* x_1) {
{

if (lean::obj_tag(x_1) == 0)
{
obj* x_3; obj* x_5; obj* x_6; 
lean::dec(x_0);
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_5 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_5 = x_1;
}
if (lean::is_scalar(x_5)) {
 x_6 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_6 = x_5;
}
lean::cnstr_set(x_6, 0, x_3);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_9 = x_1;
}
x_10 = lean::apply_1(x_0, x_7);
if (lean::is_scalar(x_9)) {
 x_11 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_11 = x_9;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
}
obj* _l_s6_except_s3_map_s6___main(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_except_s3_map_s6___main_s6___rarg), 2, 0);
return x_6;
}
}
obj* _l_s6_except_s3_map_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; 
x_2 = _l_s6_except_s3_map_s6___main_s6___rarg(x_0, x_1);
return x_2;
}
}
obj* _l_s6_except_s3_map(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_except_s3_map_s6___rarg), 2, 0);
return x_6;
}
}
obj* _l_s6_except_s10_map__error_s6___main_s6___rarg(obj* x_0, obj* x_1) {
{

if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_4 = x_1;
}
x_5 = lean::apply_1(x_0, x_2);
if (lean::is_scalar(x_4)) {
 x_6 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_6 = x_4;
}
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
else
{
obj* x_8; obj* x_10; obj* x_11; 
lean::dec(x_0);
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_10 = x_1;
}
if (lean::is_scalar(x_10)) {
 x_11 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_11 = x_10;
}
lean::cnstr_set(x_11, 0, x_8);
return x_11;
}
}
}
obj* _l_s6_except_s10_map__error_s6___main(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_except_s10_map__error_s6___main_s6___rarg), 2, 0);
return x_6;
}
}
obj* _l_s6_except_s10_map__error_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; 
x_2 = _l_s6_except_s10_map__error_s6___main_s6___rarg(x_0, x_1);
return x_2;
}
}
obj* _l_s6_except_s10_map__error(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_except_s10_map__error_s6___rarg), 2, 0);
return x_6;
}
}
obj* _l_s6_except_s4_bind_s6___rarg(obj* x_0, obj* x_1) {
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_5; obj* x_6; 
lean::dec(x_1);
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_5 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_5 = x_0;
}
if (lean::is_scalar(x_5)) {
 x_6 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_6 = x_5;
}
lean::cnstr_set(x_6, 0, x_3);
return x_6;
}
else
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::apply_1(x_1, x_7);
return x_10;
}
}
}
obj* _l_s6_except_s4_bind(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_except_s4_bind_s6___rarg), 2, 0);
return x_6;
}
}
unsigned char _l_s6_except_s8_to__bool_s6___main_s6___rarg(obj* x_0) {
{

if (lean::obj_tag(x_0) == 0)
{
unsigned char x_2; 
lean::dec(x_0);
x_2 = 0;
return x_2;
}
else
{
unsigned char x_4; 
lean::dec(x_0);
x_4 = 1;
return x_4;
}
}
}
obj* _l_s6_except_s8_to__bool_s6___main(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_except_s8_to__bool_s6___main_s6___rarg_s7___boxed), 1, 0);
return x_4;
}
}
obj* _l_s6_except_s8_to__bool_s6___main_s6___rarg_s7___boxed(obj* x_0) {
{
unsigned char x_1; obj* x_2; 
x_1 = _l_s6_except_s8_to__bool_s6___main_s6___rarg(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
unsigned char _l_s6_except_s8_to__bool_s6___rarg(obj* x_0) {
{
unsigned char x_1; 
x_1 = _l_s6_except_s8_to__bool_s6___main_s6___rarg(x_0);
return x_1;
}
}
obj* _l_s6_except_s8_to__bool(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_except_s8_to__bool_s6___rarg_s7___boxed), 1, 0);
return x_4;
}
}
obj* _l_s6_except_s8_to__bool_s6___rarg_s7___boxed(obj* x_0) {
{
unsigned char x_1; obj* x_2; 
x_1 = _l_s6_except_s8_to__bool_s6___rarg(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
obj* _l_s6_except_s10_to__option_s6___main_s6___rarg(obj* x_0) {
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_cnstr(0, 0, 0);
;
return x_2;
}
else
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_3);
return x_6;
}
}
}
obj* _l_s6_except_s10_to__option_s6___main(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_except_s10_to__option_s6___main_s6___rarg), 1, 0);
return x_4;
}
}
obj* _l_s6_except_s10_to__option_s6___rarg(obj* x_0) {
{
obj* x_1; 
x_1 = _l_s6_except_s10_to__option_s6___main_s6___rarg(x_0);
return x_1;
}
}
obj* _l_s6_except_s10_to__option(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_except_s10_to__option_s6___rarg), 1, 0);
return x_4;
}
}
obj* _l_s6_except_s5_catch_s6___rarg(obj* x_0, obj* x_1) {
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_2; obj* x_5; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::apply_1(x_1, x_2);
return x_5;
}
else
{

lean::dec(x_1);
return x_0;
}
}
}
obj* _l_s6_except_s5_catch(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_except_s5_catch_s6___rarg), 2, 0);
return x_4;
}
}
obj* _l_s6_except_s5_monad(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = _l_s6_except_s5_monad_s11___closed__1;
lean::inc(x_2);
return x_2;
}
}
obj* _init__l_s6_except_s5_monad_s11___closed__1() {
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_except_s5_monad_s11___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_except_s5_monad_s11___lambda__2), 4, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_except_s6_return), 2, 1);
lean::closure_set(x_3, 0, lean::box(0));
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_except_s5_monad_s11___lambda__3), 4, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_except_s5_monad_s11___lambda__4), 4, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_except_s5_monad_s11___lambda__5), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_2);
lean::cnstr_set(x_7, 1, x_3);
lean::cnstr_set(x_7, 2, x_4);
lean::cnstr_set(x_7, 3, x_5);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_except_s4_bind), 3, 1);
lean::closure_set(x_8, 0, lean::box(0));
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* _l_s6_except_s5_monad_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{

lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_3) == 0)
{
obj* x_7; obj* x_9; obj* x_10; 
lean::dec(x_2);
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_9 = x_3;
}
if (lean::is_scalar(x_9)) {
 x_10 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_10 = x_9;
}
lean::cnstr_set(x_10, 0, x_7);
return x_10;
}
else
{
obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_11 = lean::cnstr_get(x_3, 0);
lean::inc(x_11);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_13 = x_3;
}
x_14 = lean::apply_1(x_2, x_11);
if (lean::is_scalar(x_13)) {
 x_15 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_15 = x_13;
}
lean::cnstr_set(x_15, 0, x_14);
return x_15;
}
}
}
obj* _l_s6_except_s5_monad_s11___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{

lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_3) == 0)
{
obj* x_7; obj* x_9; obj* x_10; 
lean::dec(x_2);
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_9 = x_3;
}
if (lean::is_scalar(x_9)) {
 x_10 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_10 = x_9;
}
lean::cnstr_set(x_10, 0, x_7);
return x_10;
}
else
{
obj* x_11; obj* x_12; 
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_11 = x_3;
}
if (lean::is_scalar(x_11)) {
 x_12 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_12 = x_11;
}
lean::cnstr_set(x_12, 0, x_2);
return x_12;
}
}
}
obj* _l_s6_except_s5_monad_s11___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{

lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_7; obj* x_9; obj* x_10; 
lean::dec(x_3);
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_9 = x_2;
}
if (lean::is_scalar(x_9)) {
 x_10 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_10 = x_9;
}
lean::cnstr_set(x_10, 0, x_7);
return x_10;
}
else
{
obj* x_11; obj* x_13; 
x_11 = lean::cnstr_get(x_2, 0);
lean::inc(x_11);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_13 = x_2;
}
if (lean::obj_tag(x_3) == 0)
{
obj* x_15; obj* x_18; 
lean::dec(x_11);
x_15 = lean::cnstr_get(x_3, 0);
lean::inc(x_15);
lean::dec(x_3);
if (lean::is_scalar(x_13)) {
 x_18 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_18 = x_13;
}
lean::cnstr_set(x_18, 0, x_15);
return x_18;
}
else
{
obj* x_19; obj* x_22; obj* x_23; 
x_19 = lean::cnstr_get(x_3, 0);
lean::inc(x_19);
lean::dec(x_3);
x_22 = lean::apply_1(x_11, x_19);
if (lean::is_scalar(x_13)) {
 x_23 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_23 = x_13;
}
lean::cnstr_set(x_23, 0, x_22);
return x_23;
}
}
}
}
obj* _l_s6_except_s5_monad_s11___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{

lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_7; obj* x_9; obj* x_10; 
lean::dec(x_3);
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_9 = x_2;
}
if (lean::is_scalar(x_9)) {
 x_10 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_10 = x_9;
}
lean::cnstr_set(x_10, 0, x_7);
return x_10;
}
else
{
obj* x_11; obj* x_13; 
x_11 = lean::cnstr_get(x_2, 0);
lean::inc(x_11);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_13 = x_2;
}
if (lean::obj_tag(x_3) == 0)
{
obj* x_15; obj* x_18; 
lean::dec(x_11);
x_15 = lean::cnstr_get(x_3, 0);
lean::inc(x_15);
lean::dec(x_3);
if (lean::is_scalar(x_13)) {
 x_18 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_18 = x_13;
}
lean::cnstr_set(x_18, 0, x_15);
return x_18;
}
else
{
obj* x_20; 
lean::dec(x_3);
if (lean::is_scalar(x_13)) {
 x_20 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_20 = x_13;
}
lean::cnstr_set(x_20, 0, x_11);
return x_20;
}
}
}
}
obj* _l_s6_except_s5_monad_s11___lambda__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{

lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_7; obj* x_9; obj* x_10; 
lean::dec(x_3);
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_9 = x_2;
}
if (lean::is_scalar(x_9)) {
 x_10 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_10 = x_9;
}
lean::cnstr_set(x_10, 0, x_7);
return x_10;
}
else
{

lean::dec(x_2);
return x_3;
}
}
}
obj* _init__l_s9_except__t() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _l_s9_except__t_s2_mk_s6___rarg(obj* x_0) {
{

return x_0;
}
}
obj* _l_s9_except__t_s2_mk(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s2_mk_s6___rarg), 1, 0);
return x_6;
}
}
obj* _l_s9_except__t_s3_run_s6___rarg(obj* x_0) {
{

return x_0;
}
}
obj* _l_s9_except__t_s3_run(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s3_run_s6___rarg), 1, 0);
return x_6;
}
}
obj* _l_s9_except__t_s6_return_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* _l_s9_except__t_s6_return(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s6_return_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s9_except__t_s10_bind__cont_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{

lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_17; obj* x_18; 
lean::dec(x_3);
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_10 = x_4;
}
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::is_scalar(x_10)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_10;
}
lean::cnstr_set(x_17, 0, x_8);
x_18 = lean::apply_2(x_14, lean::box(0), x_17);
return x_18;
}
else
{
obj* x_20; obj* x_23; 
lean::dec(x_0);
x_20 = lean::cnstr_get(x_4, 0);
lean::inc(x_20);
lean::dec(x_4);
x_23 = lean::apply_1(x_3, x_20);
return x_23;
}
}
}
obj* _l_s9_except__t_s10_bind__cont_s6___main(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s10_bind__cont_s6___main_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s9_except__t_s10_bind__cont_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_7; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = _l_s9_except__t_s10_bind__cont_s6___main_s6___rarg(x_0, lean::box(0), lean::box(0), x_3, x_4);
return x_7;
}
}
obj* _l_s9_except__t_s10_bind__cont(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s10_bind__cont_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s9_except__t_s4_bind_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_7; obj* x_9; obj* x_10; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s10_bind__cont_s6___rarg), 5, 4);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, lean::box(0));
lean::closure_set(x_9, 2, lean::box(0));
lean::closure_set(x_9, 3, x_4);
x_10 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_3, x_9);
return x_10;
}
}
obj* _l_s9_except__t_s4_bind(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s4_bind_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s9_except__t_s4_lift_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
x_13 = _l_s9_except__t_s4_lift_s6___rarg_s11___closed__1;
lean::inc(x_13);
x_15 = lean::apply_4(x_10, lean::box(0), lean::box(0), x_13, x_2);
return x_15;
}
}
obj* _init__l_s9_except__t_s4_lift_s6___rarg_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s4_lift_s6___rarg_s11___lambda__1), 1, 0);
return x_0;
}
}
obj* _l_s9_except__t_s4_lift_s6___rarg_s11___lambda__1(obj* x_0) {
{
obj* x_1; 
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _l_s9_except__t_s4_lift(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s4_lift_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s9_except__t_s21_except__t__of__except_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_4; obj* x_7; obj* x_10; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::apply_2(x_7, lean::box(0), x_2);
return x_10;
}
}
obj* _l_s9_except__t_s21_except__t__of__except(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s21_except__t__of__except_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s9_except__t_s16_has__monad__lift_s6___rarg(obj* x_0) {
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s4_lift_s6___rarg), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _l_s9_except__t_s16_has__monad__lift(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s16_has__monad__lift_s6___rarg), 1, 0);
return x_4;
}
}
obj* _l_s9_except__t_s5_catch_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_5; obj* x_7; obj* x_8; 
lean::dec(x_1);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s5_catch_s6___rarg_s11___lambda__1), 3, 2);
lean::closure_set(x_7, 0, x_3);
lean::closure_set(x_7, 1, x_0);
x_8 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_2, x_7);
return x_8;
}
}
obj* _l_s9_except__t_s5_catch_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
{

if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_7; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_7 = lean::apply_1(x_0, x_4);
return x_7;
}
else
{
obj* x_9; obj* x_12; obj* x_15; 
lean::dec(x_0);
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
lean::dec(x_1);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::apply_2(x_12, lean::box(0), x_2);
return x_15;
}
}
}
obj* _l_s9_except__t_s5_catch(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s5_catch_s6___rarg), 4, 0);
return x_4;
}
}
obj* _l_s9_except__t_s14_monad__functor_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; 
x_2 = lean::apply_2(x_0, lean::box(0), x_1);
return x_2;
}
}
obj* _l_s9_except__t_s14_monad__functor(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_12; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s14_monad__functor_s6___rarg), 2, 0);
return x_12;
}
}
obj* _l_s9_except__t_s5_monad_s6___rarg(obj* x_0) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s5_monad_s6___rarg_s11___lambda__1), 5, 1);
lean::closure_set(x_2, 0, x_0);
lean::inc(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s5_monad_s6___rarg_s11___lambda__2), 5, 1);
lean::closure_set(x_4, 0, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_4);
lean::inc(x_0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s6_return_s6___rarg), 3, 1);
lean::closure_set(x_7, 0, x_0);
lean::inc(x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s5_monad_s6___rarg_s11___lambda__4), 5, 1);
lean::closure_set(x_9, 0, x_0);
lean::inc(x_0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s5_monad_s6___rarg_s11___lambda__7), 5, 1);
lean::closure_set(x_11, 0, x_0);
lean::inc(x_0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s5_monad_s6___rarg_s11___lambda__9), 5, 1);
lean::closure_set(x_13, 0, x_0);
x_14 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_14, 0, x_5);
lean::cnstr_set(x_14, 1, x_7);
lean::cnstr_set(x_14, 2, x_9);
lean::cnstr_set(x_14, 3, x_11);
lean::cnstr_set(x_14, 4, x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s4_bind_s6___rarg), 5, 1);
lean::closure_set(x_15, 0, x_0);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
obj* _l_s9_except__t_s5_monad_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; 
lean::dec(x_2);
lean::dec(x_1);
lean::inc(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s6_return_s6___rarg), 3, 2);
lean::closure_set(x_8, 0, x_0);
lean::closure_set(x_8, 1, lean::box(0));
x_9 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s4_comp_s6___rarg), 3, 2);
lean::closure_set(x_9, 0, x_8);
lean::closure_set(x_9, 1, x_3);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__1_s6___rarg), 5, 4);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, lean::box(0));
lean::closure_set(x_12, 2, lean::box(0));
lean::closure_set(x_12, 3, x_9);
x_13 = lean::apply_4(x_10, lean::box(0), lean::box(0), x_4, x_12);
return x_13;
}
}
obj* _l_s9_except__t_s5_monad_s6___rarg_s11___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s5_const_s6___rarg), 2, 1);
lean::closure_set(x_7, 0, x_3);
lean::inc(x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s6_return_s6___rarg), 3, 2);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, lean::box(0));
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s4_comp_s6___rarg), 3, 2);
lean::closure_set(x_10, 0, x_9);
lean::closure_set(x_10, 1, x_7);
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__2_s6___rarg), 5, 4);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, lean::box(0));
lean::closure_set(x_13, 2, lean::box(0));
lean::closure_set(x_13, 3, x_10);
x_14 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_4, x_13);
return x_14;
}
}
obj* _l_s9_except__t_s5_monad_s6___rarg_s11___lambda__3(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_9; 
lean::inc(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s6_return_s6___rarg), 3, 2);
lean::closure_set(x_4, 0, x_0);
lean::closure_set(x_4, 1, lean::box(0));
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s4_comp_s6___rarg), 3, 2);
lean::closure_set(x_5, 0, x_4);
lean::closure_set(x_5, 1, x_2);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__3_s6___rarg), 5, 4);
lean::closure_set(x_8, 0, x_0);
lean::closure_set(x_8, 1, lean::box(0));
lean::closure_set(x_8, 2, lean::box(0));
lean::closure_set(x_8, 3, x_5);
x_9 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_1, x_8);
return x_9;
}
}
obj* _l_s9_except__t_s5_monad_s6___rarg_s11___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_8; obj* x_9; obj* x_11; obj* x_12; 
lean::dec(x_2);
lean::dec(x_1);
lean::inc(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s5_monad_s6___rarg_s11___lambda__3), 3, 2);
lean::closure_set(x_8, 0, x_0);
lean::closure_set(x_8, 1, x_4);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__4_s6___rarg), 5, 4);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, lean::box(0));
lean::closure_set(x_11, 2, lean::box(0));
lean::closure_set(x_11, 3, x_8);
x_12 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_3, x_11);
return x_12;
}
}
obj* _l_s9_except__t_s5_monad_s6___rarg_s11___lambda__5(obj* x_0, obj* x_1, obj* x_2) {
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
obj* _l_s9_except__t_s5_monad_s6___rarg_s11___lambda__6(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
lean::inc(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s5_monad_s6___rarg_s11___lambda__5), 3, 2);
lean::closure_set(x_4, 0, x_0);
lean::closure_set(x_4, 1, x_2);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__5_s6___rarg), 5, 4);
lean::closure_set(x_7, 0, x_0);
lean::closure_set(x_7, 1, lean::box(0));
lean::closure_set(x_7, 2, lean::box(0));
lean::closure_set(x_7, 3, x_4);
x_8 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_1, x_7);
return x_8;
}
}
obj* _l_s9_except__t_s5_monad_s6___rarg_s11___lambda__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_8; obj* x_9; obj* x_11; obj* x_12; 
lean::dec(x_2);
lean::dec(x_1);
lean::inc(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s5_monad_s6___rarg_s11___lambda__6), 3, 2);
lean::closure_set(x_8, 0, x_0);
lean::closure_set(x_8, 1, x_4);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__6_s6___rarg), 5, 4);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, lean::box(0));
lean::closure_set(x_11, 2, lean::box(0));
lean::closure_set(x_11, 3, x_8);
x_12 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_3, x_11);
return x_12;
}
}
obj* _l_s9_except__t_s5_monad_s6___rarg_s11___lambda__8(obj* x_0, obj* x_1) {
{

lean::dec(x_1);
return x_0;
}
}
obj* _l_s9_except__t_s5_monad_s6___rarg_s11___lambda__9(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_7; obj* x_8; obj* x_10; obj* x_11; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s5_monad_s6___rarg_s11___lambda__8), 2, 1);
lean::closure_set(x_7, 0, x_4);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__7_s6___rarg), 5, 4);
lean::closure_set(x_10, 0, x_0);
lean::closure_set(x_10, 1, lean::box(0));
lean::closure_set(x_10, 2, lean::box(0));
lean::closure_set(x_10, 3, x_7);
x_11 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_3, x_10);
return x_11;
}
}
obj* _l_s9_except__t_s5_monad(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s5_monad_s6___rarg), 1, 0);
return x_4;
}
}
obj* _l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{

lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_17; obj* x_18; 
lean::dec(x_3);
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_10 = x_4;
}
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::is_scalar(x_10)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_10;
}
lean::cnstr_set(x_17, 0, x_8);
x_18 = lean::apply_2(x_14, lean::box(0), x_17);
return x_18;
}
else
{
obj* x_20; obj* x_23; 
lean::dec(x_0);
x_20 = lean::cnstr_get(x_4, 0);
lean::inc(x_20);
lean::dec(x_4);
x_23 = lean::apply_1(x_3, x_20);
return x_23;
}
}
}
obj* _l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__1(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__1_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__2_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{

lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_17; obj* x_18; 
lean::dec(x_3);
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_10 = x_4;
}
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::is_scalar(x_10)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_10;
}
lean::cnstr_set(x_17, 0, x_8);
x_18 = lean::apply_2(x_14, lean::box(0), x_17);
return x_18;
}
else
{
obj* x_20; obj* x_23; 
lean::dec(x_0);
x_20 = lean::cnstr_get(x_4, 0);
lean::inc(x_20);
lean::dec(x_4);
x_23 = lean::apply_1(x_3, x_20);
return x_23;
}
}
}
obj* _l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__2(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__2_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__3_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{

lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_17; obj* x_18; 
lean::dec(x_3);
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_10 = x_4;
}
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::is_scalar(x_10)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_10;
}
lean::cnstr_set(x_17, 0, x_8);
x_18 = lean::apply_2(x_14, lean::box(0), x_17);
return x_18;
}
else
{
obj* x_20; obj* x_23; 
lean::dec(x_0);
x_20 = lean::cnstr_get(x_4, 0);
lean::inc(x_20);
lean::dec(x_4);
x_23 = lean::apply_1(x_3, x_20);
return x_23;
}
}
}
obj* _l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__3(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__3_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__4_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{

lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_17; obj* x_18; 
lean::dec(x_3);
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_10 = x_4;
}
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::is_scalar(x_10)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_10;
}
lean::cnstr_set(x_17, 0, x_8);
x_18 = lean::apply_2(x_14, lean::box(0), x_17);
return x_18;
}
else
{
obj* x_20; obj* x_23; 
lean::dec(x_0);
x_20 = lean::cnstr_get(x_4, 0);
lean::inc(x_20);
lean::dec(x_4);
x_23 = lean::apply_1(x_3, x_20);
return x_23;
}
}
}
obj* _l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__4(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__4_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__5_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{

lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_17; obj* x_18; 
lean::dec(x_3);
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_10 = x_4;
}
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::is_scalar(x_10)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_10;
}
lean::cnstr_set(x_17, 0, x_8);
x_18 = lean::apply_2(x_14, lean::box(0), x_17);
return x_18;
}
else
{
obj* x_20; obj* x_23; 
lean::dec(x_0);
x_20 = lean::cnstr_get(x_4, 0);
lean::inc(x_20);
lean::dec(x_4);
x_23 = lean::apply_1(x_3, x_20);
return x_23;
}
}
}
obj* _l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__5(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__5_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__6_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{

lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_17; obj* x_18; 
lean::dec(x_3);
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_10 = x_4;
}
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::is_scalar(x_10)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_10;
}
lean::cnstr_set(x_17, 0, x_8);
x_18 = lean::apply_2(x_14, lean::box(0), x_17);
return x_18;
}
else
{
obj* x_20; obj* x_23; 
lean::dec(x_0);
x_20 = lean::cnstr_get(x_4, 0);
lean::inc(x_20);
lean::dec(x_4);
x_23 = lean::apply_1(x_3, x_20);
return x_23;
}
}
}
obj* _l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__6(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__6_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__7_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{

lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_17; obj* x_18; 
lean::dec(x_3);
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_10 = x_4;
}
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::is_scalar(x_10)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_10;
}
lean::cnstr_set(x_17, 0, x_8);
x_18 = lean::apply_2(x_14, lean::box(0), x_17);
return x_18;
}
else
{
obj* x_20; obj* x_23; 
lean::dec(x_0);
x_20 = lean::cnstr_get(x_4, 0);
lean::inc(x_20);
lean::dec(x_4);
x_23 = lean::apply_1(x_3, x_20);
return x_23;
}
}
}
obj* _l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__7(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s10_bind__cont_s4___at_s9_except__t_s5_monad_s9___spec__7_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s9_except__t_s5_adapt_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_7; obj* x_10; obj* x_13; obj* x_16; obj* x_17; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_7, 0);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
lean::dec(x_10);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_except_s10_map__error_s6___rarg), 2, 1);
lean::closure_set(x_16, 0, x_3);
x_17 = lean::apply_4(x_13, lean::box(0), lean::box(0), x_16, x_4);
return x_17;
}
}
obj* _l_s9_except__t_s5_adapt(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s5_adapt_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s13_monad__except_s6_orelse_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_5; obj* x_8; obj* x_9; 
lean::dec(x_1);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s5_monad_s6___rarg_s11___lambda__8), 2, 1);
lean::closure_set(x_8, 0, x_3);
x_9 = lean::apply_3(x_5, lean::box(0), x_2, x_8);
return x_9;
}
}
obj* _l_s13_monad__except_s6_orelse(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_monad__except_s6_orelse_s6___rarg), 4, 0);
return x_4;
}
}
obj* _l_s13_monad__except_s10_orelse_x27_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, unsigned char x_4) {
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::box(x_4);
lean::inc(x_6);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_monad__except_s10_orelse_x27_s6___rarg_s11___lambda__2_s7___boxed), 5, 4);
lean::closure_set(x_10, 0, x_0);
lean::closure_set(x_10, 1, x_8);
lean::closure_set(x_10, 2, x_6);
lean::closure_set(x_10, 3, x_3);
x_11 = lean::apply_3(x_6, lean::box(0), x_2, x_10);
return x_11;
}
}
obj* _l_s13_monad__except_s10_orelse_x27_s6___rarg_s11___lambda__1(obj* x_0, unsigned char x_1, obj* x_2, obj* x_3) {
{
obj* x_4; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
if (x_1 == 0)
{
obj* x_8; 
lean::dec(x_2);
x_8 = lean::apply_2(x_4, lean::box(0), x_3);
return x_8;
}
else
{
obj* x_10; 
lean::dec(x_3);
x_10 = lean::apply_2(x_4, lean::box(0), x_2);
return x_10;
}
}
}
obj* _l_s13_monad__except_s10_orelse_x27_s6___rarg_s11___lambda__2(obj* x_0, unsigned char x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::box(x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_monad__except_s10_orelse_x27_s6___rarg_s11___lambda__1_s7___boxed), 4, 3);
lean::closure_set(x_6, 0, x_0);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::apply_3(x_2, lean::box(0), x_3, x_6);
return x_7;
}
}
obj* _l_s13_monad__except_s10_orelse_x27(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_monad__except_s10_orelse_x27_s6___rarg_s7___boxed), 5, 0);
return x_4;
}
}
obj* _l_s13_monad__except_s10_orelse_x27_s6___rarg_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
unsigned char x_5; obj* x_6; 
x_5 = lean::unbox(x_4);
x_6 = _l_s13_monad__except_s10_orelse_x27_s6___rarg(x_0, x_1, x_2, x_3, x_5);
return x_6;
}
}
obj* _l_s13_monad__except_s10_orelse_x27_s6___rarg_s11___lambda__1_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
unsigned char x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = _l_s13_monad__except_s10_orelse_x27_s6___rarg_s11___lambda__1(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* _l_s13_monad__except_s10_orelse_x27_s6___rarg_s11___lambda__2_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
unsigned char x_5; obj* x_6; 
x_5 = lean::unbox(x_1);
x_6 = _l_s13_monad__except_s10_orelse_x27_s6___rarg_s11___lambda__2(x_0, x_5, x_2, x_3, x_4);
return x_6;
}
}
obj* _l_s13_monad__except_s12_lift__except_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{

lean::dec(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; obj* x_10; obj* x_13; obj* x_14; 
lean::dec(x_2);
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::apply_1(x_1, x_7);
x_14 = lean::apply_2(x_10, lean::box(0), x_13);
return x_14;
}
else
{
obj* x_17; obj* x_20; obj* x_23; obj* x_26; 
lean::dec(x_0);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_4, 0);
lean::inc(x_17);
lean::dec(x_4);
x_20 = lean::cnstr_get(x_2, 0);
lean::inc(x_20);
lean::dec(x_2);
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
lean::dec(x_20);
x_26 = lean::apply_2(x_23, lean::box(0), x_17);
return x_26;
}
}
}
obj* _l_s13_monad__except_s12_lift__except_s6___main(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_monad__except_s12_lift__except_s6___main_s6___rarg), 5, 0);
return x_6;
}
}
obj* _l_s13_monad__except_s12_lift__except_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_6; 
lean::dec(x_3);
x_6 = _l_s13_monad__except_s12_lift__except_s6___main_s6___rarg(x_0, x_1, x_2, lean::box(0), x_4);
return x_6;
}
}
obj* _l_s13_monad__except_s12_lift__except(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_monad__except_s12_lift__except_s6___rarg), 5, 0);
return x_6;
}
}
obj* _l_s9_except__t_s13_monad__except_s6___rarg(obj* x_0) {
{
obj* x_2; obj* x_3; obj* x_4; 
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s13_monad__except_s6___rarg_s11___lambda__1), 3, 1);
lean::closure_set(x_2, 0, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s5_catch_s6___rarg), 4, 1);
lean::closure_set(x_3, 0, x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* _l_s9_except__t_s13_monad__except_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_4; obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_10, 0, x_2);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s9_except__t_s13_monad__except(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s13_monad__except_s6___rarg), 1, 0);
return x_4;
}
}
obj* _l_s6_except_s13_monad__except(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = _l_s6_except_s13_monad__except_s11___closed__1;
lean::inc(x_2);
return x_2;
}
}
obj* _init__l_s6_except_s13_monad__except_s11___closed__1() {
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_except_s5_catch), 2, 1);
lean::closure_set(x_0, 0, lean::box(0));
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_except_s13_monad__except_s11___lambda__1), 2, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
return x_2;
}
}
obj* _l_s6_except_s13_monad__except_s11___lambda__1(obj* x_0, obj* x_1) {
{
obj* x_3; 
lean::dec(x_0);
x_3 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_3, 0, x_1);
return x_3;
}
}
obj* _l_s29_monad__except__adapter__trans_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_6; obj* x_7; 
lean::dec(x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s24_monad__functor__t__trans_s6___rarg_s11___lambda__1), 4, 2);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_3);
x_7 = lean::apply_3(x_0, lean::box(0), x_6, x_4);
return x_7;
}
}
obj* _l_s29_monad__except__adapter__trans(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_12; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(_l_s29_monad__except__adapter__trans_s6___rarg), 5, 0);
return x_12;
}
}
obj* _l_s9_except__t_s22_monad__except__adapter_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_5; obj* x_8; obj* x_11; obj* x_14; obj* x_15; 
lean::dec(x_1);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
lean::dec(x_8);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_except_s10_map__error_s6___rarg), 2, 1);
lean::closure_set(x_14, 0, x_2);
x_15 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_14, x_3);
return x_15;
}
}
obj* _l_s9_except__t_s22_monad__except__adapter(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s22_monad__except__adapter_s6___rarg), 4, 0);
return x_6;
}
}
obj* _l_s9_except__t_s10_monad__run_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_4; 
lean::dec(x_1);
x_4 = lean::apply_2(x_0, lean::box(0), x_2);
return x_4;
}
}
obj* _l_s9_except__t_s10_monad__run(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s10_monad__run_s6___rarg), 3, 0);
return x_6;
}
}
obj* _l_s9_except__t_s11_monad__fail_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_4; obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_10, 0, x_2);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s9_except__t_s11_monad__fail(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s11_monad__fail_s6___rarg), 3, 0);
return x_2;
}
}
void _l_initialize__l_s4_init_s7_control_s11_alternative();
void _l_initialize__l_s4_init_s7_control_s4_lift();
void _l_initialize__l_s4_init_s4_data_s10_to__string();
void _l_initialize__l_s4_init_s7_control_s11_monad__fail();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s7_control_s6_except() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s7_control_s11_alternative();
 _l_initialize__l_s4_init_s7_control_s4_lift();
 _l_initialize__l_s4_init_s4_data_s10_to__string();
 _l_initialize__l_s4_init_s7_control_s11_monad__fail();
 _l_s6_except_s10_to__string_s6___main_s6___rarg_s11___closed__1 = _init__l_s6_except_s10_to__string_s6___main_s6___rarg_s11___closed__1();
 _l_s6_except_s10_to__string_s6___main_s6___rarg_s11___closed__2 = _init__l_s6_except_s10_to__string_s6___main_s6___rarg_s11___closed__2();
 _l_s6_except_s5_monad_s11___closed__1 = _init__l_s6_except_s5_monad_s11___closed__1();
 _l_s9_except__t = _init__l_s9_except__t();
 _l_s9_except__t_s4_lift_s6___rarg_s11___closed__1 = _init__l_s9_except__t_s4_lift_s6___rarg_s11___closed__1();
 _l_s6_except_s13_monad__except_s11___closed__1 = _init__l_s6_except_s13_monad__except_s11___closed__1();
}

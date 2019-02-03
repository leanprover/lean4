// Lean compiler output
// Module: init.control.coroutine
// Imports: init.control.monad init.wf init.control.reader
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* _l_s9_coroutine_s6_resume_s6___rarg(obj*, obj*);
obj* _l_s8_function_s4_comp_s6___rarg(obj*, obj*, obj*);
obj* _l_s9_coroutine_s13_monad__reader_s6___rarg(obj*);
obj* _l_s9_except__t_s5_monad_s6___rarg_s11___lambda__8(obj*, obj*);
obj* _l_s9_coroutine_s5_monad_s11___closed__1;
obj* _l_s9_coroutine_s5_yield_s6___rarg_s11___lambda__1(obj*);
obj* _l_s9_coroutine_s5_monad_s11___lambda__4(obj*, obj*, obj*, obj*);
obj* _l_s9_coroutine_s5_monad_s11___lambda__5(obj*, obj*, obj*);
obj* _l_s9_coroutine_s5_monad_s11___lambda__8(obj*, obj*, obj*, obj*);
obj* _l_s9_coroutine_s5_adapt(obj*, obj*, obj*);
obj* _l_s9_coroutine_s13_monad__reader(obj*, obj*);
obj* _l_s9_coroutine_s4_bind_s6___rarg(obj*, obj*);
obj* _l_s9_coroutine_s5_yield_s6___rarg_s11___lambda__1_s11___closed__1;
obj* _l_s8_function_s5_const_s6___rarg(obj*, obj*);
obj* _l_s9_coroutine_s4_pipe(obj*, obj*, obj*, obj*);
obj* _l_s9_coroutine_s4_pure(obj*, obj*, obj*);
obj* _l_s9_coroutine_s5_monad_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s9___private_3144039831__s11_finish__aux_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s9_coroutine_s5_monad_s11___lambda__2(obj*, obj*, obj*, obj*);
obj* _l_s9_coroutine_s4_read(obj*, obj*);
obj* _l_s9_coroutine_s4_bind_s6___main(obj*, obj*, obj*, obj*);
obj* _l_s23_monad__coroutine__trans(obj*, obj*, obj*, obj*);
obj* _l_s9_coroutine_s5_yield_s6___rarg_s11___closed__1;
obj* _l_s9_coroutine_s4_pipe_s6___main(obj*, obj*, obj*, obj*);
obj* _l_s9_coroutine_s4_bind(obj*, obj*, obj*, obj*);
obj* _l_s9___private_3144039831__s11_finish__aux(obj*, obj*, obj*);
obj* _l_s9_coroutine_s6_finish(obj*, obj*, obj*);
obj* _l_s9_coroutine_s5_adapt_s6___rarg(obj*, obj*, obj*);
obj* _l_s9_coroutine_s5_monad(obj*, obj*);
obj* _l_s9_coroutine_s4_bind_s6___main_s6___rarg(obj*, obj*, obj*);
obj* _l_s9_coroutine_s6_resume_s6___main(obj*, obj*, obj*);
obj* _l_s9___private_3144039831__s11_finish__aux_s6___main_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s23_monad__coroutine__trans_s6___rarg(obj*, obj*, obj*);
obj* _l_s9_coroutine_s16_monad__coroutine(obj*, obj*);
obj* _l_s4_list_s7_reverse_s6___rarg(obj*);
obj* _l_s9_coroutine_s6_finish_s6___rarg(obj*, obj*, obj*);
obj* _l_s9_coroutine_s5_monad_s11___lambda__6(obj*, obj*);
obj* _l_s9_coroutine_s5_monad_s11___lambda__1_s11___closed__1;
obj* _l_s9_coroutine_s4_pipe_s6___rarg(obj*, obj*);
obj* _l_s17_coroutine__result;
obj* _l_s9_coroutine_s4_pure_s6___rarg(obj*, obj*);
obj* _l_s9___private_3144039831__s11_finish__aux_s6___main(obj*, obj*, obj*);
obj* _l_s9_coroutine_s4_pipe_s6___main_s6___rarg(obj*, obj*, obj*);
obj* _l_s9_coroutine_s6_resume(obj*, obj*, obj*);
obj* _l_s9_coroutine_s4_read_s6___rarg(obj*);
obj* _l_s9_coroutine_s5_yield_s6___rarg(obj*, obj*);
obj* _l_s9_coroutine_s5_yield(obj*, obj*);
obj* _l_s9_coroutine_s5_monad_s11___lambda__7(obj*, obj*, obj*, obj*);
obj* _l_s9_coroutine_s6_resume_s6___main_s6___rarg(obj*, obj*);
obj* _l_s9_coroutine_s5_monad_s11___lambda__3(obj*, obj*);
obj* _init__l_s17_coroutine__result(){
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _l_s9_coroutine_s6_resume_s6___main_s6___rarg(obj* x_0, obj* x_1){
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* _l_s9_coroutine_s6_resume_s6___main(obj* x_0, obj* x_1, obj* x_2){
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s6_resume_s6___main_s6___rarg), 2, 0);
return x_6;
}
}
obj* _l_s9_coroutine_s6_resume_s6___rarg(obj* x_0, obj* x_1){
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* _l_s9_coroutine_s6_resume(obj* x_0, obj* x_1, obj* x_2){
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s6_resume_s6___rarg), 2, 0);
return x_6;
}
}
obj* _l_s9_coroutine_s4_pure_s6___rarg(obj* x_0, obj* x_1){
_start:
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_3, 0, x_0);
return x_3;
}
}
obj* _l_s9_coroutine_s4_pure(obj* x_0, obj* x_1, obj* x_2){
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s4_pure_s6___rarg), 2, 0);
return x_6;
}
}
obj* _l_s9_coroutine_s4_read_s6___rarg(obj* x_0){
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _l_s9_coroutine_s4_read(obj* x_0, obj* x_1){
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s4_read_s6___rarg), 1, 0);
return x_4;
}
}
obj* _l_s9_coroutine_s5_adapt_s6___rarg(obj* x_0, obj* x_1, obj* x_2){
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::apply_1(x_0, x_2);
x_4 = lean::apply_1(x_1, x_3);
return x_4;
}
}
obj* _l_s9_coroutine_s5_adapt(obj* x_0, obj* x_1, obj* x_2){
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s5_adapt_s6___rarg), 3, 0);
return x_6;
}
}
obj* _l_s9_coroutine_s5_yield_s6___rarg(obj* x_0, obj* x_1){
_start:
{
obj* x_3; obj* x_5; 
lean::dec(x_1);
x_3 = _l_s9_coroutine_s5_yield_s6___rarg_s11___closed__1;
lean::inc(x_3);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_3);
return x_5;
}
}
obj* _init__l_s9_coroutine_s5_yield_s6___rarg_s11___closed__1(){
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s5_yield_s6___rarg_s11___lambda__1), 1, 0);
return x_0;
}
}
obj* _l_s9_coroutine_s5_yield_s6___rarg_s11___lambda__1(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = _l_s9_coroutine_s5_yield_s6___rarg_s11___lambda__1_s11___closed__1;
lean::inc(x_2);
return x_2;
}
}
obj* _init__l_s9_coroutine_s5_yield_s6___rarg_s11___lambda__1_s11___closed__1(){
_start:
{
unsigned char x_0; obj* x_1; obj* x_2; 
x_0 = 0;
x_1 = lean::box(x_0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _l_s9_coroutine_s5_yield(obj* x_0, obj* x_1){
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s5_yield_s6___rarg), 2, 0);
return x_4;
}
}
obj* _l_s9_coroutine_s4_bind_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2){
_start:
{
obj* x_4; 
lean::inc(x_2);
x_4 = lean::apply_1(x_0, x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_8; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_8 = lean::apply_2(x_1, x_5, x_2);
return x_8;
}
else
{
obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_2);
x_10 = lean::cnstr_get(x_4, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_4, 1);
lean::inc(x_12);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 x_14 = x_4;
}
x_15 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s4_bind_s6___main_s6___rarg), 3, 2);
lean::closure_set(x_15, 0, x_12);
lean::closure_set(x_15, 1, x_1);
if (lean::is_scalar(x_14)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_14;
}
lean::cnstr_set(x_16, 0, x_10);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
}
obj* _l_s9_coroutine_s4_bind_s6___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3){
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s4_bind_s6___main_s6___rarg), 3, 0);
return x_8;
}
}
obj* _l_s9_coroutine_s4_bind_s6___rarg(obj* x_0, obj* x_1){
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s4_bind_s6___main_s6___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* _l_s9_coroutine_s4_bind(obj* x_0, obj* x_1, obj* x_2, obj* x_3){
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s4_bind_s6___rarg), 2, 0);
return x_8;
}
}
obj* _l_s9_coroutine_s4_pipe_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2){
_start:
{
obj* x_3; 
x_3 = lean::apply_1(x_0, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_7; obj* x_8; 
lean::dec(x_1);
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_7 = x_3;
}
if (lean::is_scalar(x_7)) {
 x_8 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_8 = x_7;
}
lean::cnstr_set(x_8, 0, x_5);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_13; obj* x_14; 
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_3, 1);
lean::inc(x_11);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_13 = x_3;
}
x_14 = lean::apply_1(x_1, x_9);
if (lean::obj_tag(x_14) == 0)
{
obj* x_17; obj* x_19; obj* x_20; 
lean::dec(x_11);
lean::dec(x_13);
x_17 = lean::cnstr_get(x_14, 0);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_19 = x_14;
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_17);
return x_20;
}
else
{
obj* x_21; obj* x_23; obj* x_26; obj* x_27; 
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_14, 1);
lean::inc(x_23);
lean::dec(x_14);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s4_pipe_s6___main_s6___rarg), 3, 2);
lean::closure_set(x_26, 0, x_11);
lean::closure_set(x_26, 1, x_23);
if (lean::is_scalar(x_13)) {
 x_27 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_27 = x_13;
}
lean::cnstr_set(x_27, 0, x_21);
lean::cnstr_set(x_27, 1, x_26);
return x_27;
}
}
}
}
obj* _l_s9_coroutine_s4_pipe_s6___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3){
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s4_pipe_s6___main_s6___rarg), 3, 0);
return x_8;
}
}
obj* _l_s9_coroutine_s4_pipe_s6___rarg(obj* x_0, obj* x_1){
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s4_pipe_s6___main_s6___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* _l_s9_coroutine_s4_pipe(obj* x_0, obj* x_1, obj* x_2, obj* x_3){
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s4_pipe_s6___rarg), 2, 0);
return x_8;
}
}
obj* _l_s9___private_3144039831__s11_finish__aux_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3){
_start:
{
obj* x_4; 
x_4 = lean::apply_1(x_1, x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_9; obj* x_10; 
lean::dec(x_0);
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::dec(x_4);
x_9 = _l_s4_list_s7_reverse_s6___rarg(x_3);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_6);
return x_10;
}
else
{
obj* x_11; obj* x_13; obj* x_18; obj* x_19; obj* x_20; 
x_11 = lean::cnstr_get(x_4, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_4, 1);
lean::inc(x_13);
lean::dec(x_4);
lean::inc(x_11);
lean::inc(x_0);
x_18 = lean::apply_1(x_0, x_11);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_11);
lean::cnstr_set(x_19, 1, x_3);
x_20 = _l_s9___private_3144039831__s11_finish__aux_s6___main_s6___rarg(x_0, x_13, x_18, x_19);
x_1 = x_13;
x_2 = x_18;
x_3 = x_19;
goto _start;
}
}
}
obj* _l_s9___private_3144039831__s11_finish__aux_s6___main(obj* x_0, obj* x_1, obj* x_2){
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_3144039831__s11_finish__aux_s6___main_s6___rarg), 4, 0);
return x_6;
}
}
obj* _l_s9___private_3144039831__s11_finish__aux_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3){
_start:
{
obj* x_4; 
x_4 = _l_s9___private_3144039831__s11_finish__aux_s6___main_s6___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* _l_s9___private_3144039831__s11_finish__aux(obj* x_0, obj* x_1, obj* x_2){
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_3144039831__s11_finish__aux_s6___rarg), 4, 0);
return x_6;
}
}
obj* _l_s9_coroutine_s6_finish_s6___rarg(obj* x_0, obj* x_1, obj* x_2){
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_cnstr(0, 0, 0);
;
x_4 = _l_s9___private_3144039831__s11_finish__aux_s6___main_s6___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* _l_s9_coroutine_s6_finish(obj* x_0, obj* x_1, obj* x_2){
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s6_finish_s6___rarg), 3, 0);
return x_6;
}
}
obj* _l_s9_coroutine_s5_monad(obj* x_0, obj* x_1){
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = _l_s9_coroutine_s5_monad_s11___closed__1;
lean::inc(x_4);
return x_4;
}
}
obj* _init__l_s9_coroutine_s5_monad_s11___closed__1(){
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s5_monad_s11___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s5_monad_s11___lambda__2), 4, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s4_pure), 3, 2);
lean::closure_set(x_3, 0, lean::box(0));
lean::closure_set(x_3, 1, lean::box(0));
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s5_monad_s11___lambda__4), 4, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s5_monad_s11___lambda__7), 4, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s5_monad_s11___lambda__8), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_2);
lean::cnstr_set(x_7, 1, x_3);
lean::cnstr_set(x_7, 2, x_4);
lean::cnstr_set(x_7, 3, x_5);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s4_bind), 4, 2);
lean::closure_set(x_8, 0, lean::box(0));
lean::closure_set(x_8, 1, lean::box(0));
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* _l_s9_coroutine_s5_monad_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3){
_start:
{
obj* x_6; obj* x_8; obj* x_9; 
lean::dec(x_1);
lean::dec(x_0);
x_6 = _l_s9_coroutine_s5_monad_s11___lambda__1_s11___closed__1;
lean::inc(x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s4_comp_s6___rarg), 3, 2);
lean::closure_set(x_8, 0, x_6);
lean::closure_set(x_8, 1, x_2);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s4_bind_s6___main_s6___rarg), 3, 2);
lean::closure_set(x_9, 0, x_3);
lean::closure_set(x_9, 1, x_8);
return x_9;
}
}
obj* _init__l_s9_coroutine_s5_monad_s11___lambda__1_s11___closed__1(){
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s4_pure_s6___rarg), 2, 0);
return x_0;
}
}
obj* _l_s9_coroutine_s5_monad_s11___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3){
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_10; 
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s5_const_s6___rarg), 2, 1);
lean::closure_set(x_6, 0, x_2);
x_7 = _l_s9_coroutine_s5_monad_s11___lambda__1_s11___closed__1;
lean::inc(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s4_comp_s6___rarg), 3, 2);
lean::closure_set(x_9, 0, x_7);
lean::closure_set(x_9, 1, x_6);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s4_bind_s6___main_s6___rarg), 3, 2);
lean::closure_set(x_10, 0, x_3);
lean::closure_set(x_10, 1, x_9);
return x_10;
}
}
obj* _l_s9_coroutine_s5_monad_s11___lambda__3(obj* x_0, obj* x_1){
_start:
{
obj* x_2; obj* x_4; obj* x_5; 
x_2 = _l_s9_coroutine_s5_monad_s11___lambda__1_s11___closed__1;
lean::inc(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s4_comp_s6___rarg), 3, 2);
lean::closure_set(x_4, 0, x_2);
lean::closure_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s4_bind_s6___main_s6___rarg), 3, 2);
lean::closure_set(x_5, 0, x_0);
lean::closure_set(x_5, 1, x_4);
return x_5;
}
}
obj* _l_s9_coroutine_s5_monad_s11___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3){
_start:
{
obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s5_monad_s11___lambda__3), 2, 1);
lean::closure_set(x_6, 0, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s4_bind_s6___main_s6___rarg), 3, 2);
lean::closure_set(x_7, 0, x_2);
lean::closure_set(x_7, 1, x_6);
return x_7;
}
}
obj* _l_s9_coroutine_s5_monad_s11___lambda__5(obj* x_0, obj* x_1, obj* x_2){
_start:
{
obj* x_5; 
lean::dec(x_2);
lean::dec(x_1);
x_5 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_5, 0, x_0);
return x_5;
}
}
obj* _l_s9_coroutine_s5_monad_s11___lambda__6(obj* x_0, obj* x_1){
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s5_monad_s11___lambda__5), 3, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s4_bind_s6___main_s6___rarg), 3, 2);
lean::closure_set(x_3, 0, x_0);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* _l_s9_coroutine_s5_monad_s11___lambda__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3){
_start:
{
obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s5_monad_s11___lambda__6), 2, 1);
lean::closure_set(x_6, 0, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s4_bind_s6___main_s6___rarg), 3, 2);
lean::closure_set(x_7, 0, x_2);
lean::closure_set(x_7, 1, x_6);
return x_7;
}
}
obj* _l_s9_coroutine_s5_monad_s11___lambda__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3){
_start:
{
obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s5_monad_s6___rarg_s11___lambda__8), 2, 1);
lean::closure_set(x_6, 0, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s4_bind_s6___main_s6___rarg), 3, 2);
lean::closure_set(x_7, 0, x_2);
lean::closure_set(x_7, 1, x_6);
return x_7;
}
}
obj* _l_s9_coroutine_s13_monad__reader_s6___rarg(obj* x_0){
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _l_s9_coroutine_s13_monad__reader(obj* x_0, obj* x_1){
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s13_monad__reader_s6___rarg), 1, 0);
return x_4;
}
}
obj* _l_s9_coroutine_s16_monad__coroutine(obj* x_0, obj* x_1){
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_coroutine_s5_yield_s6___rarg), 2, 0);
return x_4;
}
}
obj* _l_s23_monad__coroutine__trans_s6___rarg(obj* x_0, obj* x_1, obj* x_2){
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::apply_1(x_1, x_2);
x_4 = lean::apply_2(x_0, lean::box(0), x_3);
return x_4;
}
}
obj* _l_s23_monad__coroutine__trans(obj* x_0, obj* x_1, obj* x_2, obj* x_3){
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s23_monad__coroutine__trans_s6___rarg), 3, 0);
return x_8;
}
}
void _l_initialize__l_s4_init_s7_control_s5_monad();
void _l_initialize__l_s4_init_s2_wf();
void _l_initialize__l_s4_init_s7_control_s6_reader();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s7_control_s9_coroutine() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s7_control_s5_monad();
 _l_initialize__l_s4_init_s2_wf();
 _l_initialize__l_s4_init_s7_control_s6_reader();
 _l_s17_coroutine__result = _init__l_s17_coroutine__result();
 _l_s9_coroutine_s5_yield_s6___rarg_s11___closed__1 = _init__l_s9_coroutine_s5_yield_s6___rarg_s11___closed__1();
 _l_s9_coroutine_s5_yield_s6___rarg_s11___lambda__1_s11___closed__1 = _init__l_s9_coroutine_s5_yield_s6___rarg_s11___lambda__1_s11___closed__1();
 _l_s9_coroutine_s5_monad_s11___closed__1 = _init__l_s9_coroutine_s5_monad_s11___closed__1();
 _l_s9_coroutine_s5_monad_s11___lambda__1_s11___closed__1 = _init__l_s9_coroutine_s5_monad_s11___lambda__1_s11___closed__1();
}

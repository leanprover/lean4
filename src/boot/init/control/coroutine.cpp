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
obj* l_coroutine_resume___rarg(obj*, obj*);
obj* l_function_comp___rarg(obj*, obj*, obj*);
obj* l_coroutine_monad__reader___rarg(obj*);
obj* l_except__t_monad___rarg___lambda__8(obj*, obj*);
obj* l_coroutine_monad___closed__1;
obj* l_coroutine_yield___rarg___lambda__1(obj*);
obj* l_coroutine_monad___lambda__4(obj*, obj*, obj*, obj*);
obj* l_coroutine_monad___lambda__5(obj*, obj*, obj*);
obj* l_coroutine_monad___lambda__8(obj*, obj*, obj*, obj*);
obj* l_coroutine_adapt(obj*, obj*, obj*);
obj* l_coroutine_monad__reader(obj*, obj*);
obj* l_coroutine_bind___rarg(obj*, obj*);
obj* l_coroutine_yield___rarg___lambda__1___closed__1;
obj* l_function_const___rarg(obj*, obj*);
obj* l_coroutine_pipe(obj*, obj*, obj*, obj*);
obj* l_coroutine_pure(obj*, obj*, obj*);
obj* l_coroutine_monad___lambda__1(obj*, obj*, obj*, obj*);
obj* l___private_3144039831__finish__aux___rarg(obj*, obj*, obj*, obj*);
obj* l_coroutine_monad___lambda__2(obj*, obj*, obj*, obj*);
obj* l_coroutine_read(obj*, obj*);
obj* l_coroutine_bind___main(obj*, obj*, obj*, obj*);
obj* l_monad__coroutine__trans(obj*, obj*, obj*, obj*);
obj* l_coroutine_yield___rarg___closed__1;
obj* l_coroutine_pipe___main(obj*, obj*, obj*, obj*);
obj* l_coroutine_bind(obj*, obj*, obj*, obj*);
obj* l___private_3144039831__finish__aux(obj*, obj*, obj*);
obj* l_coroutine_finish(obj*, obj*, obj*);
obj* l_coroutine_adapt___rarg(obj*, obj*, obj*);
obj* l_coroutine_monad(obj*, obj*);
obj* l_coroutine_bind___main___rarg(obj*, obj*, obj*);
obj* l_coroutine_resume___main(obj*, obj*, obj*);
obj* l___private_3144039831__finish__aux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_monad__coroutine__trans___rarg(obj*, obj*, obj*);
obj* l_coroutine_monad__coroutine(obj*, obj*);
obj* l_list_reverse___rarg(obj*);
obj* l_coroutine_finish___rarg(obj*, obj*, obj*);
obj* l_coroutine_monad___lambda__6(obj*, obj*);
obj* l_coroutine_monad___lambda__1___closed__1;
obj* l_coroutine_pipe___rarg(obj*, obj*);
obj* l_coroutine__result;
obj* l_coroutine_pure___rarg(obj*, obj*);
obj* l___private_3144039831__finish__aux___main(obj*, obj*, obj*);
obj* l_coroutine_pipe___main___rarg(obj*, obj*, obj*);
obj* l_coroutine_resume(obj*, obj*, obj*);
obj* l_coroutine_read___rarg(obj*);
obj* l_coroutine_yield___rarg(obj*, obj*);
obj* l_coroutine_yield(obj*, obj*);
obj* l_coroutine_monad___lambda__7(obj*, obj*, obj*, obj*);
obj* l_coroutine_resume___main___rarg(obj*, obj*);
obj* l_coroutine_monad___lambda__3(obj*, obj*);
obj* _init_l_coroutine__result() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_coroutine_resume___main___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* l_coroutine_resume___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_resume___main___rarg), 2, 0);
return x_6;
}
}
obj* l_coroutine_resume___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* l_coroutine_resume(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_resume___rarg), 2, 0);
return x_6;
}
}
obj* l_coroutine_pure___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_3, 0, x_0);
return x_3;
}
}
obj* l_coroutine_pure(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_pure___rarg), 2, 0);
return x_6;
}
}
obj* l_coroutine_read___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_coroutine_read(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_read___rarg), 1, 0);
return x_4;
}
}
obj* l_coroutine_adapt___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::apply_1(x_0, x_2);
x_4 = lean::apply_1(x_1, x_3);
return x_4;
}
}
obj* l_coroutine_adapt(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_adapt___rarg), 3, 0);
return x_6;
}
}
obj* l_coroutine_yield___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_5; 
lean::dec(x_1);
x_3 = l_coroutine_yield___rarg___closed__1;
lean::inc(x_3);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_3);
return x_5;
}
}
obj* _init_l_coroutine_yield___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_yield___rarg___lambda__1), 1, 0);
return x_0;
}
}
obj* l_coroutine_yield___rarg___lambda__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = l_coroutine_yield___rarg___lambda__1___closed__1;
lean::inc(x_2);
return x_2;
}
}
obj* _init_l_coroutine_yield___rarg___lambda__1___closed__1() {
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
obj* l_coroutine_yield(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_yield___rarg), 2, 0);
return x_4;
}
}
obj* l_coroutine_bind___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
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
obj* l_coroutine_bind___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 0);
return x_8;
}
}
obj* l_coroutine_bind___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_coroutine_bind(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___rarg), 2, 0);
return x_8;
}
}
obj* l_coroutine_pipe___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_pipe___main___rarg), 3, 2);
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
obj* l_coroutine_pipe___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_pipe___main___rarg), 3, 0);
return x_8;
}
}
obj* l_coroutine_pipe___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_pipe___main___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_coroutine_pipe(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_pipe___rarg), 2, 0);
return x_8;
}
}
obj* l___private_3144039831__finish__aux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
x_9 = l_list_reverse___rarg(x_3);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_6);
return x_10;
}
else
{
obj* x_11; obj* x_13; obj* x_18; obj* x_19; 
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
x_1 = x_13;
x_2 = x_18;
x_3 = x_19;
goto _start;
}
}
}
obj* l___private_3144039831__finish__aux___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l___private_3144039831__finish__aux___main___rarg), 4, 0);
return x_6;
}
}
obj* l___private_3144039831__finish__aux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_3144039831__finish__aux___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_3144039831__finish__aux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l___private_3144039831__finish__aux___rarg), 4, 0);
return x_6;
}
}
obj* l_coroutine_finish___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_cnstr(0, 0, 0);
;
x_4 = l___private_3144039831__finish__aux___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_coroutine_finish(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_finish___rarg), 3, 0);
return x_6;
}
}
obj* l_coroutine_monad(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = l_coroutine_monad___closed__1;
lean::inc(x_4);
return x_4;
}
}
obj* _init_l_coroutine_monad___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_monad___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_monad___lambda__2), 4, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_pure), 3, 2);
lean::closure_set(x_3, 0, lean::box(0));
lean::closure_set(x_3, 1, lean::box(0));
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_monad___lambda__4), 4, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_monad___lambda__7), 4, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_monad___lambda__8), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_2);
lean::cnstr_set(x_7, 1, x_3);
lean::cnstr_set(x_7, 2, x_4);
lean::cnstr_set(x_7, 3, x_5);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind), 4, 2);
lean::closure_set(x_8, 0, lean::box(0));
lean::closure_set(x_8, 1, lean::box(0));
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* l_coroutine_monad___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; 
lean::dec(x_1);
lean::dec(x_0);
x_6 = l_coroutine_monad___lambda__1___closed__1;
lean::inc(x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_8, 0, x_6);
lean::closure_set(x_8, 1, x_2);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_9, 0, x_3);
lean::closure_set(x_9, 1, x_8);
return x_9;
}
}
obj* _init_l_coroutine_monad___lambda__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_pure___rarg), 2, 0);
return x_0;
}
}
obj* l_coroutine_monad___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_10; 
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_function_const___rarg), 2, 1);
lean::closure_set(x_6, 0, x_2);
x_7 = l_coroutine_monad___lambda__1___closed__1;
lean::inc(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_9, 0, x_7);
lean::closure_set(x_9, 1, x_6);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_10, 0, x_3);
lean::closure_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_coroutine_monad___lambda__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; 
x_2 = l_coroutine_monad___lambda__1___closed__1;
lean::inc(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_4, 0, x_2);
lean::closure_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_5, 0, x_0);
lean::closure_set(x_5, 1, x_4);
return x_5;
}
}
obj* l_coroutine_monad___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_monad___lambda__3), 2, 1);
lean::closure_set(x_6, 0, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_7, 0, x_2);
lean::closure_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_coroutine_monad___lambda__5(obj* x_0, obj* x_1, obj* x_2) {
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
obj* l_coroutine_monad___lambda__6(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_monad___lambda__5), 3, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_3, 0, x_0);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_coroutine_monad___lambda__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_monad___lambda__6), 2, 1);
lean::closure_set(x_6, 0, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_7, 0, x_2);
lean::closure_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_coroutine_monad___lambda__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_monad___rarg___lambda__8), 2, 1);
lean::closure_set(x_6, 0, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_7, 0, x_2);
lean::closure_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_coroutine_monad__reader___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_coroutine_monad__reader(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_monad__reader___rarg), 1, 0);
return x_4;
}
}
obj* l_coroutine_monad__coroutine(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_yield___rarg), 2, 0);
return x_4;
}
}
obj* l_monad__coroutine__trans___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::apply_1(x_1, x_2);
x_4 = lean::apply_2(x_0, lean::box(0), x_3);
return x_4;
}
}
obj* l_monad__coroutine__trans(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__coroutine__trans___rarg), 3, 0);
return x_8;
}
}
void initialize_init_control_monad();
void initialize_init_wf();
void initialize_init_control_reader();
static bool _G_initialized = false;
void initialize_init_control_coroutine() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_control_monad();
 initialize_init_wf();
 initialize_init_control_reader();
 l_coroutine__result = _init_l_coroutine__result();
 l_coroutine_yield___rarg___closed__1 = _init_l_coroutine_yield___rarg___closed__1();
 l_coroutine_yield___rarg___lambda__1___closed__1 = _init_l_coroutine_yield___rarg___lambda__1___closed__1();
 l_coroutine_monad___closed__1 = _init_l_coroutine_monad___closed__1();
 l_coroutine_monad___lambda__1___closed__1 = _init_l_coroutine_monad___lambda__1___closed__1();
}

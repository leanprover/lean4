// Lean compiler output
// Module: Init.System.Promise
// Imports: Init.System.IO
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_IO_Promise_resultD___rarg___lambda__1(lean_object*, lean_object*);
lean_object* lean_io_promise_new(lean_object*);
LEAN_EXPORT lean_object* l_IO_Promise_result_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Promise_result_x21(lean_object*);
LEAN_EXPORT lean_object* l_IO_Promise_isResolved___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Promise_result(lean_object*);
LEAN_EXPORT lean_object* l_IO_Promise_isResolved___rarg(lean_object*, lean_object*);
lean_object* lean_option_get_or_block(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_Promise_0__IO_PromisePointed;
LEAN_EXPORT lean_object* l_IO_Promise_resolve___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Promise_new___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
LEAN_EXPORT lean_object* l_IO_Promise_isResolved(lean_object*);
extern lean_object* l_Task_Priority_default;
static lean_object* l_IO_Promise_result_x21___rarg___closed__1;
LEAN_EXPORT lean_object* l_IO_Promise_result___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_Promise_0__IO_Option_getOrBlock_x21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Promise_resultD___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Promise_resultD___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Promise_result_x21___rarg___boxed(lean_object*);
lean_object* lean_io_get_task_state(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Promise_result_x21___rarg(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_Promise_resultD___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Promise_result___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_Promise_resultD(lean_object*);
static lean_object* _init_l___private_Init_System_Promise_0__IO_PromisePointed() {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_IO_Promise_new___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_promise_new(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_resolve___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_promise_resolve(x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_result_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_promise_result_opt(x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_Promise_0__IO_Option_getOrBlock_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_option_get_or_block(x_3);
return x_4;
}
}
static lean_object* _init_l_IO_Promise_result_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_System_Promise_0__IO_Option_getOrBlock_x21___boxed), 3, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_result_x21___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = lean_io_promise_result_opt(x_1);
x_3 = l_IO_Promise_result_x21___rarg___closed__1;
x_4 = l_Task_Priority_default;
x_5 = 1;
x_6 = lean_task_map(x_3, x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_result_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_Promise_result_x21___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_result_x21___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_Promise_result_x21___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_result___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_Promise_result_x21___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_result(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_Promise_result___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_result___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_Promise_result___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_resultD___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_IO_Promise_resultD___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_3 = lean_alloc_closure((void*)(l_IO_Promise_resultD___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_io_promise_result_opt(x_1);
x_5 = l_Task_Priority_default;
x_6 = 1;
x_7 = lean_task_map(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_resultD(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_Promise_resultD___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_resultD___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Promise_resultD___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_resultD___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Promise_resultD___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_isResolved___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_io_promise_result_opt(x_1);
x_4 = lean_io_get_task_state(x_3, x_2);
lean_dec(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 2)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = 1;
x_9 = lean_box(x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_5);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_4, 0);
lean_dec(x_15);
x_16 = 0;
x_17 = lean_box(x_16);
lean_ctor_set(x_4, 0, x_17);
return x_4;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_dec(x_4);
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
return x_4;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_4, 0);
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_4);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Promise_isResolved(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_Promise_isResolved___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_isResolved___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Promise_isResolved___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_System_Promise(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_System_Promise_0__IO_PromisePointed = _init_l___private_Init_System_Promise_0__IO_PromisePointed();
l_IO_Promise_result_x21___rarg___closed__1 = _init_l_IO_Promise_result_x21___rarg___closed__1();
lean_mark_persistent(l_IO_Promise_result_x21___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

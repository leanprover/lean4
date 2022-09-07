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
static lean_object* l___private_Init_System_Promise_0__IO_PromiseImpl___closed__1;
lean_object* lean_io_promise_resolve(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_promise_new(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_Promise_0__IO_PromiseImpl(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_Promise_0__IO_Promise_resultImpl___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_Promise_0__IO_Promise_resultImpl___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_Promise_0__IO_Promise_resultImpl(lean_object*);
LEAN_EXPORT lean_object* l_IO_Promise_resolve___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Promise_new___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Init_System_Promise_0__IO_PromiseImpl___closed__1() {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l___private_Init_System_Promise_0__IO_PromiseImpl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_System_Promise_0__IO_PromiseImpl___closed__1;
return x_2;
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
LEAN_EXPORT lean_object* l___private_Init_System_Promise_0__IO_Promise_resultImpl___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_Promise_0__IO_Promise_resultImpl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_System_Promise_0__IO_Promise_resultImpl___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_Promise_0__IO_Promise_resultImpl___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_System_Promise_0__IO_Promise_resultImpl___rarg(x_1);
lean_dec(x_1);
return x_2;
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
l___private_Init_System_Promise_0__IO_PromiseImpl___closed__1 = _init_l___private_Init_System_Promise_0__IO_PromiseImpl___closed__1();
lean_mark_persistent(l___private_Init_System_Promise_0__IO_PromiseImpl___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Init.System.Promise
// Imports: public import Init.System.IO
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
lean_object* lean_io_promise_new();
LEAN_EXPORT lean_object* l_IO_Promise_isResolved___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Promise_result_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Promise_result_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Promise_result_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* lean_option_get_or_block(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_Promise_0__IO_PromisePointed;
LEAN_EXPORT lean_object* l_IO_Promise_resolve___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Promise_result_x21___redArg___lam__0(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Promise_new___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
LEAN_EXPORT uint8_t l_IO_Promise_isResolved___redArg(lean_object*);
LEAN_EXPORT uint8_t l_IO_Promise_isResolved(lean_object*, lean_object*);
static lean_object* l_IO_Promise_result_x21___redArg___closed__0;
LEAN_EXPORT lean_object* l_IO_Promise_isResolved___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Promise_result_x21___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_Promise_0__IO_Option_getOrBlock_x21___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_io_get_task_state(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
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
x_4 = lean_io_promise_new();
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_resolve___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_promise_resolve(x_2, x_3);
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
LEAN_EXPORT lean_object* l_IO_Promise_result_x21___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_option_get_or_block(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_Promise_result_x21___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_Promise_result_x21___redArg___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_result_x21___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_IO_Promise_result_x21___redArg___closed__0;
x_3 = lean_io_promise_result_opt(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = 1;
x_6 = lean_task_map(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_result_x21___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_Promise_result_x21___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_result_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Promise_result_x21___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_result_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Promise_result_x21(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_IO_Promise_isResolved___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_io_promise_result_opt(x_1);
x_4 = lean_io_get_task_state(x_3);
lean_dec_ref(x_3);
if (x_4 == 2)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_IO_Promise_isResolved___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_IO_Promise_isResolved___redArg(x_1);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_IO_Promise_isResolved(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_IO_Promise_isResolved___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_isResolved___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_IO_Promise_isResolved(x_1, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_System_Promise(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_System_Promise_0__IO_PromisePointed = _init_l___private_Init_System_Promise_0__IO_PromisePointed();
l_IO_Promise_result_x21___redArg___closed__0 = _init_l_IO_Promise_result_x21___redArg___closed__0();
lean_mark_persistent(l_IO_Promise_result_x21___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

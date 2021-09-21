// Lean compiler output
// Module: Std.Data.Stack
// Imports: Init
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_Stack_vals___default(lean_object*);
LEAN_EXPORT lean_object* l_Std_Stack_push(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_Stack_peek_x21___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Stack_peek_x3f(lean_object*);
LEAN_EXPORT uint8_t l_Std_Stack_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Stack_empty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Stack_push___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Stack_isEmpty___rarg___boxed(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Stack_pop___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Stack_modify(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___rarg(lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Stack_peek_x21(lean_object*);
LEAN_EXPORT lean_object* l_Std_Stack_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Stack_modify___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Stack_vals___default___closed__1;
LEAN_EXPORT lean_object* l_Std_Stack_peek_x3f___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Stack_pop___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Stack_peek_x3f___rarg___boxed(lean_object*);
lean_object* l_Array_get_x3f___rarg(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
LEAN_EXPORT lean_object* l_Std_Stack_peek_x21___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Stack_pop(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* _init_l_Std_Stack_vals___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Stack_vals___default(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Stack_vals___default___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Stack_empty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Stack_vals___default___closed__1;
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_Stack_isEmpty___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Array_isEmpty___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Stack_isEmpty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Stack_isEmpty___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Stack_isEmpty___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Stack_isEmpty___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Stack_push___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Stack_push(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Stack_push___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Stack_peek_x3f___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Array_isEmpty___rarg(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_3, x_4);
lean_dec(x_3);
x_6 = l_Array_get_x3f___rarg(x_1, x_5);
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_Stack_peek_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Stack_peek_x3f___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Stack_peek_x3f___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Stack_peek_x3f___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Stack_peek_x21___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_back___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Stack_peek_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Stack_peek_x21___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Stack_peek_x21___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Stack_peek_x21___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Stack_pop___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_array_pop(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Stack_pop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Stack_pop___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Stack_pop___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Stack_pop(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Stack_modify___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_4, x_5);
x_7 = lean_nat_dec_lt(x_6, x_4);
lean_dec(x_4);
if (x_7 == 0)
{
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_fget(x_2, x_6);
x_9 = lean_array_fset(x_2, x_6, x_1);
x_10 = lean_apply_1(x_3, x_8);
x_11 = lean_array_fset(x_9, x_6, x_10);
lean_dec(x_6);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_Stack_modify(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Stack_modify___rarg), 3, 0);
return x_2;
}
}
lean_object* initialize_Init(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Stack(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Stack_vals___default___closed__1 = _init_l_Std_Stack_vals___default___closed__1();
lean_mark_persistent(l_Std_Stack_vals___default___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

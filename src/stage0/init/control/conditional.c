// Lean compiler output
// Module: init.control.conditional
// Imports: init.control.monad init.data.option.basic
#include "runtime/lean.h"
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
lean_object* l_bool___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_andM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_bool___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_orM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_bool(lean_object*, lean_object*);
lean_object* l_Bool_HasToBool;
lean_object* l_notM___boxed(lean_object*);
lean_object* l_orM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Option_HasToBool___closed__1;
extern lean_object* l_liftRefl___closed__1;
lean_object* l_notM___rarg___closed__1;
lean_object* l_Option_toBool___rarg___boxed(lean_object*);
lean_object* l_andM___boxed(lean_object*, lean_object*);
lean_object* l_andM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Option_HasToBool(lean_object*);
lean_object* l_notM(lean_object*);
lean_object* l_notM___rarg(lean_object*, lean_object*);
lean_object* l_notM___rarg___lambda__1___boxed(lean_object*);
lean_object* l_andM(lean_object*, lean_object*);
lean_object* l_orM(lean_object*, lean_object*);
uint8_t l_notM___rarg___lambda__1(uint8_t);
lean_object* l_andM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_orM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_orM___boxed(lean_object*, lean_object*);
lean_object* _init_l_Bool_HasToBool() {
_start:
{
lean_object* x_1; 
x_1 = l_liftRefl___closed__1;
return x_1;
}
}
lean_object* _init_l_Option_HasToBool___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Option_toBool___rarg___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Option_HasToBool(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Option_HasToBool___closed__1;
return x_2;
}
}
lean_object* l_bool___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_inc(x_3);
return x_3;
}
}
}
lean_object* l_bool(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_bool___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_bool___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_bool___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_orM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_4);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_4);
return x_9;
}
}
}
lean_object* l_orM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_orM___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_4);
lean_closure_set(x_6, 2, x_1);
x_7 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_3, x_6);
return x_7;
}
}
lean_object* l_orM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_orM___rarg), 4, 0);
return x_3;
}
}
lean_object* l_orM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_orM___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_orM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_orM(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_andM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_4);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_4);
return x_9;
}
else
{
lean_dec(x_4);
lean_dec(x_2);
lean_inc(x_3);
return x_3;
}
}
}
lean_object* l_andM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_andM___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_4);
x_7 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_3, x_6);
return x_7;
}
}
lean_object* l_andM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_andM___rarg), 4, 0);
return x_3;
}
}
lean_object* l_andM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_andM___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_andM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_andM(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
uint8_t l_notM___rarg___lambda__1(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* _init_l_notM___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_notM___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l_notM___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_notM___rarg___closed__1;
x_6 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_2);
return x_6;
}
}
lean_object* l_notM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_notM___rarg), 2, 0);
return x_2;
}
}
lean_object* l_notM___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_notM___rarg___lambda__1(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_notM___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_notM(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_init_control_monad(lean_object*);
lean_object* initialize_init_data_option_basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_init_control_conditional(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_init_control_monad(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_option_basic(w);
if (lean_io_result_is_error(w)) return w;
l_Bool_HasToBool = _init_l_Bool_HasToBool();
lean_mark_persistent(l_Bool_HasToBool);
l_Option_HasToBool___closed__1 = _init_l_Option_HasToBool___closed__1();
lean_mark_persistent(l_Option_HasToBool___closed__1);
l_notM___rarg___closed__1 = _init_l_notM___rarg___closed__1();
lean_mark_persistent(l_notM___rarg___closed__1);
return w;
}
#ifdef __cplusplus
}
#endif

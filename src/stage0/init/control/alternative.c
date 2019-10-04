// Lean compiler output
// Module: Init.Control.Alternative
// Imports: Init.Core Init.Control.Applicative
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
lean_object* l_guard___boxed(lean_object*);
lean_object* l_guardb___rarg___boxed(lean_object*, lean_object*);
lean_object* l_alternativeHasOrelse___rarg(lean_object*);
lean_object* l_failure___boxed(lean_object*);
lean_object* l_guard(lean_object*);
lean_object* l_assert___rarg(lean_object*, lean_object*, uint8_t);
lean_object* l_optional___rarg___lambda__1(lean_object*);
lean_object* l_guard___rarg(lean_object*, lean_object*, uint8_t);
lean_object* l_assert___boxed(lean_object*);
lean_object* l_assert(lean_object*);
lean_object* l_optional___boxed(lean_object*);
lean_object* l_guard___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_assert___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_guardb___boxed(lean_object*);
lean_object* l_optional___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_failure___rarg(lean_object*, lean_object*);
lean_object* l_failure(lean_object*);
lean_object* l_guardb(lean_object*);
lean_object* l_optional(lean_object*);
lean_object* l_optional___rarg___closed__1;
lean_object* l_alternativeHasOrelse(lean_object*, lean_object*);
lean_object* l_guardb___rarg(lean_object*, uint8_t);
lean_object* l_alternativeHasOrelse___boxed(lean_object*, lean_object*);
lean_object* l_alternativeHasOrelse___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_apply_1(x_2, lean_box(0));
return x_3;
}
}
lean_object* l_alternativeHasOrelse(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_alternativeHasOrelse___rarg), 1, 0);
return x_3;
}
}
lean_object* l_alternativeHasOrelse___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_alternativeHasOrelse(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_failure___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_3, lean_box(0));
return x_4;
}
}
lean_object* l_failure(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_failure___rarg), 2, 0);
return x_2;
}
}
lean_object* l_failure___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_failure(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_guard___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_4, lean_box(0));
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
return x_9;
}
}
}
lean_object* l_guard(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_guard___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_guard___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_guard___rarg(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l_guard___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_guard(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_assert___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_4, lean_box(0));
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_2(x_7, lean_box(0), lean_box(0));
return x_8;
}
}
}
lean_object* l_assert(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_assert___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_assert___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_assert___rarg(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l_assert___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_assert(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_guardb___rarg(lean_object* x_1, uint8_t x_2) {
_start:
{
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_3, lean_box(0));
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = lean_apply_2(x_6, lean_box(0), x_7);
return x_8;
}
}
}
lean_object* l_guardb(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_guardb___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_guardb___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_guardb___rarg(x_1, x_3);
return x_4;
}
}
lean_object* l_guardb___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_guardb(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_optional___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_optional___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_optional___rarg___lambda__1), 1, 0);
return x_1;
}
}
lean_object* l_optional___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_optional___rarg___closed__1;
x_9 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_3);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_apply_2(x_10, lean_box(0), x_11);
x_13 = lean_apply_3(x_4, lean_box(0), x_9, x_12);
return x_13;
}
}
lean_object* l_optional(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_optional___rarg), 3, 0);
return x_2;
}
}
lean_object* l_optional___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_optional(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Core(lean_object*);
lean_object* initialize_Init_Control_Applicative(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Control_Alternative(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Core(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Control_Applicative(w);
if (lean_io_result_is_error(w)) return w;
l_optional___rarg___closed__1 = _init_l_optional___rarg___closed__1();
lean_mark_persistent(l_optional___rarg___closed__1);
return w;
}
#ifdef __cplusplus
}
#endif

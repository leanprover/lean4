// Lean compiler output
// Module: Init.Control.Monad
// Imports: Init.Control.Applicative
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
lean_object* l_whenM___rarg___lambda__1(lean_object*, lean_object*, uint8_t);
lean_object* l_whenM(lean_object*);
lean_object* l_whenM___boxed(lean_object*);
lean_object* l_condM___rarg___lambda__1(lean_object*, lean_object*, uint8_t);
lean_object* l_whenM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_unlessM___boxed(lean_object*);
extern lean_object* l_Nat_HasOfNat___closed__1;
lean_object* l_unlessM___rarg___lambda__1(lean_object*, lean_object*, uint8_t);
lean_object* l_monadInhabited_x27___rarg(lean_object*);
lean_object* l_unlessM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_condM(lean_object*);
lean_object* l_unlessM(lean_object*);
lean_object* l_whenM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_condM___boxed(lean_object*);
lean_object* l_condM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mcomp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_monadInhabited_x27___boxed(lean_object*, lean_object*);
lean_object* l_mcomp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mcomp___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_condM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_joinM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_monadInhabited(lean_object*, lean_object*);
lean_object* l_joinM(lean_object*);
lean_object* l_monadInhabited___boxed(lean_object*, lean_object*);
lean_object* l_joinM___boxed(lean_object*);
lean_object* l_unlessM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_monadInhabited_x27(lean_object*, lean_object*);
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
lean_object* l_mcomp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_1(x_2, x_4);
x_6 = lean_apply_4(x_1, lean_box(0), lean_box(0), x_5, x_3);
return x_6;
}
}
lean_object* l_mcomp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_mcomp___rarg), 4, 0);
return x_5;
}
}
lean_object* l_mcomp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_mcomp(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_monadInhabited_x27___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_apply_1(x_3, lean_box(0));
return x_4;
}
}
lean_object* l_monadInhabited_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_monadInhabited_x27___rarg), 1, 0);
return x_3;
}
}
lean_object* l_monadInhabited_x27___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_monadInhabited_x27(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_monadInhabited___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_apply_2(x_4, lean_box(0), x_2);
return x_5;
}
}
lean_object* l_monadInhabited(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_monadInhabited___rarg), 2, 0);
return x_3;
}
}
lean_object* l_monadInhabited___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_monadInhabited(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_joinM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Nat_HasOfNat___closed__1;
x_6 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_3, x_5);
return x_6;
}
}
lean_object* l_joinM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_joinM___rarg), 3, 0);
return x_2;
}
}
lean_object* l_joinM___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_joinM(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_condM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
if (x_3 == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
lean_object* l_condM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_closure((void*)(l_condM___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_4);
x_8 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_3, x_7);
return x_8;
}
}
lean_object* l_condM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_condM___rarg), 5, 0);
return x_2;
}
}
lean_object* l_condM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_condM___rarg___lambda__1(x_1, x_2, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_condM___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_condM(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_whenM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
else
{
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
}
}
lean_object* l_whenM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l_whenM___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_2, x_5);
return x_6;
}
}
lean_object* l_whenM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_whenM___rarg), 3, 0);
return x_2;
}
}
lean_object* l_whenM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_whenM___rarg___lambda__1(x_1, x_2, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_whenM___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_whenM(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_unlessM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
if (x_3 == 0)
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
}
}
lean_object* l_unlessM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l_unlessM___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_1);
x_6 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_2, x_5);
return x_6;
}
}
lean_object* l_unlessM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_unlessM___rarg), 3, 0);
return x_2;
}
}
lean_object* l_unlessM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_unlessM___rarg___lambda__1(x_1, x_2, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_unlessM___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_unlessM(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Control_Applicative(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Control_Monad(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Applicative(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

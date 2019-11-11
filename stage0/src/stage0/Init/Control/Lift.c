// Lean compiler output
// Module: Init.Control.Lift
// Imports: Init.Coe Init.Control.Monad
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
lean_object* l_hasMonadLiftToHasCoe___elambda__1___rarg(lean_object*, lean_object*);
lean_object* l_hasMonadLiftToHasCoe___elambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_monadFunctorTTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_hasMonadLiftTRefl___rarg(lean_object*);
lean_object* l_hasMonadLiftToHasCoe___boxed(lean_object*, lean_object*);
lean_object* l_hasMonadLiftTRefl___rarg___boxed(lean_object*);
lean_object* l_monadFunctorTTrans___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_monadFunctorTRefl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_hasMonadLiftTTrans___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_hasMonadLiftTRefl___boxed(lean_object*, lean_object*);
lean_object* l_monadFunctorTRefl___rarg(lean_object*, lean_object*);
lean_object* l_hasMonadLiftToHasCoe___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_monadFunctorTRefl(lean_object*, lean_object*, lean_object*);
lean_object* l_hasMonadLiftTRefl(lean_object*, lean_object*);
lean_object* l_hasMonadLiftTTrans(lean_object*, lean_object*, lean_object*);
lean_object* l_hasMonadLiftToHasCoe(lean_object*, lean_object*);
lean_object* l_hasMonadLiftTTrans___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_monadFunctorTTrans___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_hasMonadLiftToHasCoe___rarg(lean_object*, lean_object*);
lean_object* l_monadFunctorTTrans___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_hasMonadLiftToHasCoe___elambda__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
lean_object* l_hasMonadLiftToHasCoe___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_hasMonadLiftToHasCoe___elambda__1___rarg), 2, 0);
return x_4;
}
}
lean_object* l_hasMonadLiftToHasCoe___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_hasMonadLiftToHasCoe___elambda__1___rarg), 2, 1);
lean_closure_set(x_3, 0, x_1);
return x_3;
}
}
lean_object* l_hasMonadLiftToHasCoe(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_hasMonadLiftToHasCoe___rarg), 2, 0);
return x_3;
}
}
lean_object* l_hasMonadLiftToHasCoe___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_hasMonadLiftToHasCoe___elambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_hasMonadLiftToHasCoe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_hasMonadLiftToHasCoe(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_hasMonadLiftTTrans___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_hasMonadLiftTTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_hasMonadLiftTTrans___rarg), 4, 0);
return x_4;
}
}
lean_object* l_hasMonadLiftTTrans___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_hasMonadLiftTTrans(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_hasMonadLiftTRefl___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_hasMonadLiftTRefl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_hasMonadLiftTRefl___rarg___boxed), 1, 0);
return x_3;
}
}
lean_object* l_hasMonadLiftTRefl___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_hasMonadLiftTRefl___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_hasMonadLiftTRefl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_hasMonadLiftTRefl(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_monadFunctorTTrans___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, lean_box(0), x_2, x_4);
return x_5;
}
}
lean_object* l_monadFunctorTTrans___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_monadFunctorTTrans___rarg___lambda__1), 4, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_3(x_2, lean_box(0), x_6, x_5);
return x_7;
}
}
lean_object* l_monadFunctorTTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_monadFunctorTTrans___rarg), 5, 0);
return x_7;
}
}
lean_object* l_monadFunctorTTrans___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_monadFunctorTTrans(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_monadFunctorTRefl___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
lean_object* l_monadFunctorTRefl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_monadFunctorTRefl___rarg), 2, 0);
return x_4;
}
}
lean_object* l_monadFunctorTRefl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_monadFunctorTRefl(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init_Coe(lean_object*);
lean_object* initialize_Init_Control_Monad(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Control_Lift(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Coe(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Monad(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

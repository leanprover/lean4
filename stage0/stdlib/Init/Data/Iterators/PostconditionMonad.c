// Lean compiler output
// Module: Init.Data.Iterators.PostconditionMonad
// Imports: Init.Control.Lawful.Basic Init.Data.Subtype Init.PropLemmas
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
static lean_object* l_Std_Iterators_PostconditionT_lift___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_Iterators_instFunctorPostconditionT___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftWithProperty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___rarg___lambda__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_pbind(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_bind___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___rarg___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_lift(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_lift___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftMap(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_bind___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_run___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_lift___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instFunctorPostconditionT(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_pure(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_lift___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___rarg___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftMap___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_pbind___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_run(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftWithProperty___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instFunctorPostconditionT___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftWithProperty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instFunctorPostconditionT___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_pure___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instFunctorPostconditionT___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___rarg___lambda__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_bind(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_map(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_map___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_lift___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Std_Iterators_PostconditionT_lift___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_lift___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_lift___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Std_Iterators_PostconditionT_lift___rarg___closed__1;
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_lift(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_lift___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_lift___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Iterators_PostconditionT_lift___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_pure___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_pure(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_pure___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftWithProperty___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftWithProperty(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_liftWithProperty___rarg___boxed), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftWithProperty___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Iterators_PostconditionT_liftWithProperty___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_map___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_map(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_map___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_bind___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_1(x_2, x_3);
x_8 = l_Std_Iterators_PostconditionT_lift___rarg___closed__1;
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_bind___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_bind___rarg___lambda__1), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_bind(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_bind___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_pbind___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_bind___rarg___lambda__1), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_pbind(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_pbind___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftMap___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftMap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_liftMap___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_run___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Std_Iterators_PostconditionT_lift___rarg___closed__1;
x_8 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_run___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instFunctorPostconditionT___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instFunctorPostconditionT___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_closure((void*)(l_Std_Iterators_instFunctorPostconditionT___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_7, 0, x_4);
x_8 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instFunctorPostconditionT___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_map___rarg), 5, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_Std_Iterators_instFunctorPostconditionT___rarg___lambda__2), 5, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instFunctorPostconditionT(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Iterators_instFunctorPostconditionT___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instFunctorPostconditionT___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Iterators_instFunctorPostconditionT___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_4, lean_box(0), x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
lean_inc(x_4);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_3, x_6);
x_8 = l_Std_Iterators_PostconditionT_lift___rarg___closed__1;
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_closure((void*)(l_Std_Iterators_instMonadPostconditionT___rarg___lambda__2), 3, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_6);
x_9 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_2(x_6, lean_box(0), x_2);
x_8 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_2, x_7);
x_9 = l_Std_Iterators_PostconditionT_lift___rarg___closed__1;
lean_inc(x_6);
x_10 = lean_alloc_closure((void*)(l_Std_Iterators_instMonadPostconditionT___rarg___lambda__4___boxed), 5, 4);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_5);
lean_closure_set(x_10, 2, x_6);
lean_closure_set(x_10, 3, x_9);
x_11 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_8, x_10);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___rarg___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Std_Iterators_instMonadPostconditionT___rarg___lambda__5), 5, 4);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_7);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_8);
x_10 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___rarg___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
x_7 = l_Std_Iterators_PostconditionT_lift___rarg___closed__1;
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___rarg___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_closure((void*)(l_Std_Iterators_instMonadPostconditionT___rarg___lambda__7___boxed), 3, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_6);
x_9 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_inc(x_3);
x_4 = l_Std_Iterators_instFunctorPostconditionT___rarg(x_3);
lean_inc(x_2);
x_5 = lean_alloc_closure((void*)(l_Std_Iterators_instMonadPostconditionT___rarg___lambda__1), 3, 1);
lean_closure_set(x_5, 0, x_2);
lean_inc(x_3);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Std_Iterators_instMonadPostconditionT___rarg___lambda__3), 6, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_3);
lean_inc(x_3);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Std_Iterators_instMonadPostconditionT___rarg___lambda__6), 7, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_2);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Std_Iterators_instMonadPostconditionT___rarg___lambda__8), 6, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_3);
x_9 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set(x_9, 4, x_8);
x_10 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_bind___rarg), 5, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Iterators_instMonadPostconditionT___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Iterators_instMonadPostconditionT___rarg___lambda__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___rarg___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Iterators_instMonadPostconditionT___rarg___lambda__7(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* initialize_Init_Control_Lawful_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Subtype(uint8_t builtin, lean_object*);
lean_object* initialize_Init_PropLemmas(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_PostconditionMonad(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Lawful_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Subtype(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_PropLemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Iterators_PostconditionT_lift___rarg___closed__1 = _init_l_Std_Iterators_PostconditionT_lift___rarg___closed__1();
lean_mark_persistent(l_Std_Iterators_PostconditionT_lift___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

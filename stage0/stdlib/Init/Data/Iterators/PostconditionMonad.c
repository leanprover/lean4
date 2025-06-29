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
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftWithProperty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftWithProperty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_bind___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_lift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_pbind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_lift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instFunctorPostconditionT___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instFunctorPostconditionT___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instFunctorPostconditionT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_pure(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_run___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_pure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftMap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_bind___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_bind___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_lift___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftWithProperty(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Iterators_PostconditionT_pbind___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftWithProperty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instFunctorPostconditionT___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_pbind___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_lift___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_map___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_run___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_bind___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_map___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instFunctorPostconditionT___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_lift___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_lift___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_lift___redArg___lam__0___boxed), 1, 0);
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_lift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_lift___redArg___lam__0___boxed), 1, 0);
x_7 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_lift___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Iterators_PostconditionT_lift___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_pure___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_pure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftWithProperty___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftWithProperty(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftWithProperty___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Iterators_PostconditionT_liftWithProperty___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftWithProperty___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Iterators_PostconditionT_liftWithProperty(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_map___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_map___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_map___redArg___lam__0), 2, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_map(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_map___redArg___lam__0), 2, 1);
lean_closure_set(x_8, 0, x_5);
x_9 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_bind___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_bind___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_4);
x_7 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_bind___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_bind___redArg___lam__0___boxed), 1, 0);
x_8 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_bind___redArg___lam__1), 4, 3);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_3);
lean_closure_set(x_8, 2, x_7);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_bind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_bind___redArg___lam__0___boxed), 1, 0);
x_11 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_bind___redArg___lam__1), 4, 3);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_6);
lean_closure_set(x_11, 2, x_10);
x_12 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_5, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_bind___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Iterators_PostconditionT_bind___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Iterators_PostconditionT_pbind___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_bind___redArg___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_pbind___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Std_Iterators_PostconditionT_pbind___redArg___closed__0;
x_8 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_bind___redArg___lam__1), 4, 3);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_3);
lean_closure_set(x_8, 2, x_7);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_pbind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Std_Iterators_PostconditionT_pbind___redArg___closed__0;
x_11 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_bind___redArg___lam__1), 4, 3);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_6);
lean_closure_set(x_11, 2, x_10);
x_12 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_5, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftMap___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_7 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_map___redArg___lam__0), 2, 1);
lean_closure_set(x_7, 0, x_2);
x_8 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_liftMap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_map___redArg___lam__0), 2, 1);
lean_closure_set(x_10, 0, x_5);
x_11 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_10, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_run___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_run___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_run___redArg___lam__0___boxed), 1, 0);
x_7 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_run___redArg___lam__0___boxed), 1, 0);
x_9 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_run___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Iterators_PostconditionT_run___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instFunctorPostconditionT___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instFunctorPostconditionT___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_closure((void*)(l_Std_Iterators_instFunctorPostconditionT___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_7, 0, x_4);
x_8 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instFunctorPostconditionT___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_Std_Iterators_instFunctorPostconditionT___redArg___lam__1), 5, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_map), 6, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instFunctorPostconditionT(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Iterators_instFunctorPostconditionT___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instFunctorPostconditionT___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Iterators_instFunctorPostconditionT___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Std_Iterators_instMonadPostconditionT___redArg___lam__4___boxed), 4, 3);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
lean_closure_set(x_8, 2, x_2);
x_9 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_apply_2(x_1, lean_box(0), x_2);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Std_Iterators_instMonadPostconditionT___redArg___lam__1___boxed), 5, 4);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_7);
lean_closure_set(x_9, 2, x_8);
lean_closure_set(x_9, 3, x_3);
x_10 = lean_box(0);
x_11 = lean_apply_1(x_4, x_10);
x_12 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_11, x_9);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_6, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_4);
x_10 = lean_alloc_closure((void*)(l_Std_Iterators_instMonadPostconditionT___redArg___lam__2), 7, 6);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_9);
lean_closure_set(x_10, 4, x_4);
lean_closure_set(x_10, 5, x_5);
x_11 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_closure((void*)(l_Std_Iterators_instMonadPostconditionT___redArg___lam__5), 2, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_2, x_7);
lean_inc(x_5);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_8);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_3, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Std_Iterators_instMonadPostconditionT___redArg___lam__6), 4, 3);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
lean_closure_set(x_8, 2, x_2);
x_9 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 4);
lean_dec(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_dec(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_dec(x_9);
x_10 = l_Std_Iterators_PostconditionT_pbind___redArg___closed__0;
lean_inc(x_3);
lean_inc(x_5);
x_11 = lean_alloc_closure((void*)(l_Std_Iterators_instMonadPostconditionT___redArg___lam__0), 7, 3);
lean_closure_set(x_11, 0, x_5);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_3);
lean_inc(x_3);
lean_inc(x_6);
lean_inc(x_5);
x_12 = lean_alloc_closure((void*)(l_Std_Iterators_instMonadPostconditionT___redArg___lam__3), 9, 5);
lean_closure_set(x_12, 0, x_5);
lean_closure_set(x_12, 1, x_6);
lean_closure_set(x_12, 2, x_10);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_10);
lean_inc(x_5);
x_13 = lean_alloc_closure((void*)(l_Std_Iterators_instMonadPostconditionT___redArg___lam__7), 7, 3);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_3);
x_14 = l_Std_Iterators_instFunctorPostconditionT___redArg(x_5);
x_15 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_pure), 4, 2);
lean_closure_set(x_15, 0, lean_box(0));
lean_closure_set(x_15, 1, x_6);
lean_ctor_set(x_2, 4, x_11);
lean_ctor_set(x_2, 3, x_12);
lean_ctor_set(x_2, 2, x_13);
lean_ctor_set(x_2, 1, x_15);
lean_ctor_set(x_2, 0, x_14);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_bind), 6, 2);
lean_closure_set(x_16, 0, lean_box(0));
lean_closure_set(x_16, 1, x_1);
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_1, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_1, 0);
lean_dec(x_19);
lean_ctor_set(x_1, 1, x_16);
return x_1;
}
else
{
lean_object* x_20; 
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
x_23 = l_Std_Iterators_PostconditionT_pbind___redArg___closed__0;
lean_inc(x_3);
lean_inc(x_21);
x_24 = lean_alloc_closure((void*)(l_Std_Iterators_instMonadPostconditionT___redArg___lam__0), 7, 3);
lean_closure_set(x_24, 0, x_21);
lean_closure_set(x_24, 1, x_23);
lean_closure_set(x_24, 2, x_3);
lean_inc(x_3);
lean_inc(x_22);
lean_inc(x_21);
x_25 = lean_alloc_closure((void*)(l_Std_Iterators_instMonadPostconditionT___redArg___lam__3), 9, 5);
lean_closure_set(x_25, 0, x_21);
lean_closure_set(x_25, 1, x_22);
lean_closure_set(x_25, 2, x_23);
lean_closure_set(x_25, 3, x_3);
lean_closure_set(x_25, 4, x_23);
lean_inc(x_21);
x_26 = lean_alloc_closure((void*)(l_Std_Iterators_instMonadPostconditionT___redArg___lam__7), 7, 3);
lean_closure_set(x_26, 0, x_21);
lean_closure_set(x_26, 1, x_23);
lean_closure_set(x_26, 2, x_3);
x_27 = l_Std_Iterators_instFunctorPostconditionT___redArg(x_21);
x_28 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_pure), 4, 2);
lean_closure_set(x_28, 0, lean_box(0));
lean_closure_set(x_28, 1, x_22);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_24);
lean_inc(x_1);
x_30 = lean_alloc_closure((void*)(l_Std_Iterators_PostconditionT_bind), 6, 2);
lean_closure_set(x_30, 0, lean_box(0));
lean_closure_set(x_30, 1, x_1);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_31 = x_1;
} else {
 lean_dec_ref(x_1);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Iterators_instMonadPostconditionT___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Iterators_instMonadPostconditionT___redArg___lam__4(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instMonadPostconditionT___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Iterators_instMonadPostconditionT___redArg___lam__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
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
l_Std_Iterators_PostconditionT_pbind___redArg___closed__0 = _init_l_Std_Iterators_PostconditionT_pbind___redArg___closed__0();
lean_mark_persistent(l_Std_Iterators_PostconditionT_pbind___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

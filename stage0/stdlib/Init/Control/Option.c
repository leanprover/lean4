// Lean compiler output
// Module: Init.Control.Option
// Imports: Init.Data.Option.Basic Init.Control.Basic Init.Control.Except
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
LEAN_EXPORT lean_object* l_OptionT_instMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_run___redArg(lean_object*);
LEAN_EXPORT lean_object* l_OptionT_orElse___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOf___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_mk(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_orElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_bind___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_run(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_fail(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_orElse___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_tryCatch___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOf___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_lift___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOfUnit___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_OptionT_mk___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonadLift___redArg(lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_tryCatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_pure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToBoolOption(lean_object*);
LEAN_EXPORT lean_object* l_OptionT_mk___redArg(lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_lift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_fail___redArg(lean_object*);
static lean_object* l_instToBoolOption___closed__0;
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonadLift(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOfUnit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instInhabitedOfPure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonadFunctor(lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_pure(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_run___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_mk___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instAlternative___redArg(lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOfUnit___redArg(lean_object*);
LEAN_EXPORT lean_object* l_OptionT_run___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOfUnit___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOf___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_lift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_tryCatch___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instInhabitedOfPure___redArg(lean_object*);
lean_object* l_Option_isSome___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_bind___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OptionT_instAlternative(lean_object*, lean_object*);
static lean_object* _init_l_instToBoolOption___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Option_isSome___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToBoolOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToBoolOption___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_OptionT_run___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_OptionT_run(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_OptionT_run___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_OptionT_run___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_OptionT_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_OptionT_run(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_OptionT_mk___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_OptionT_mk(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_OptionT_mk___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_OptionT_mk___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_OptionT_mk___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_OptionT_mk(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_OptionT_bind___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_OptionT_bind___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_closure((void*)(l_OptionT_bind___redArg___lam__0), 3, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_3);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_OptionT_bind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_closure((void*)(l_OptionT_bind___redArg___lam__0), 3, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_6);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_5, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_OptionT_pure___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_OptionT_pure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
x_8 = lean_apply_2(x_6, lean_box(0), x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_apply_1(x_2, x_6);
lean_ctor_set(x_3, 0, x_7);
x_8 = lean_apply_2(x_1, lean_box(0), x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_apply_1(x_2, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_apply_2(x_1, lean_box(0), x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__0), 3, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_4);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_5, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_2);
x_7 = lean_apply_2(x_1, lean_box(0), x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = lean_apply_2(x_1, lean_box(0), x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__2), 3, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_4);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_5, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_apply_1(x_2, x_6);
lean_ctor_set(x_3, 0, x_7);
x_8 = lean_apply_2(x_1, lean_box(0), x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_apply_1(x_2, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_apply_2(x_1, lean_box(0), x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__4), 3, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_2, x_9);
x_11 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_10, x_8);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__5), 4, 3);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_5);
lean_closure_set(x_9, 2, x_7);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_4, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
else
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__7), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_2, x_7);
x_9 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__8), 4, 3);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_5);
lean_closure_set(x_9, 2, x_7);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_4, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg___lam__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__10), 3, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_5);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_4, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(x_2, 0, x_1);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(x_3, 0, x_1);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(x_4, 0, x_1);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(x_5, 0, x_1);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, x_1);
x_9 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_4);
lean_ctor_set(x_9, 3, x_5);
lean_ctor_set(x_9, 4, x_6);
x_10 = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(x_10, 0, lean_box(0));
lean_closure_set(x_10, 1, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonad(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_2);
x_3 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(x_3, 0, x_2);
lean_inc(x_2);
x_4 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(x_4, 0, x_2);
lean_inc(x_2);
x_5 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(x_5, 0, x_2);
lean_inc(x_2);
x_6 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(x_6, 0, x_2);
lean_inc(x_2);
x_7 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(x_7, 0, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_inc(x_2);
x_9 = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(x_9, 0, lean_box(0));
lean_closure_set(x_9, 1, x_2);
x_10 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_5);
lean_ctor_set(x_10, 3, x_6);
lean_ctor_set(x_10, 4, x_7);
x_11 = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(x_11, 0, lean_box(0));
lean_closure_set(x_11, 1, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_OptionT_instInhabitedOfPure___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_OptionT_instInhabitedOfPure(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_OptionT_instInhabitedOfPure___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_OptionT_orElse___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = lean_apply_2(x_2, lean_box(0), x_3);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_OptionT_orElse___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_closure((void*)(l_OptionT_orElse___redArg___lam__0), 3, 2);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_6);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_OptionT_orElse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_closure((void*)(l_OptionT_orElse___redArg___lam__0), 3, 2);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_8);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_4, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_OptionT_fail___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_2(x_3, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_OptionT_fail(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
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
LEAN_EXPORT lean_object* l_OptionT_instAlternative___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(x_2, 0, x_1);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(x_3, 0, x_1);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(x_4, 0, x_1);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(x_5, 0, x_1);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, x_1);
x_9 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_4);
lean_ctor_set(x_9, 3, x_5);
lean_ctor_set(x_9, 4, x_6);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_OptionT_fail), 3, 2);
lean_closure_set(x_10, 0, lean_box(0));
lean_closure_set(x_10, 1, x_1);
x_11 = lean_alloc_closure((void*)(l_OptionT_orElse), 5, 2);
lean_closure_set(x_11, 0, lean_box(0));
lean_closure_set(x_11, 1, x_1);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_OptionT_instAlternative(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_OptionT_instAlternative___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_OptionT_lift___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_OptionT_lift___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_closure((void*)(l_OptionT_lift___redArg___lam__0), 2, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_OptionT_lift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_closure((void*)(l_OptionT_lift___redArg___lam__0), 2, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_4, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadLift___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadLift(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadFunctor___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_2, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadFunctor(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_OptionT_instMonadFunctor___lam__0), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_OptionT_tryCatch___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = lean_apply_2(x_2, lean_box(0), x_3);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_OptionT_tryCatch___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_closure((void*)(l_OptionT_tryCatch___redArg___lam__0), 3, 2);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_6);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_OptionT_tryCatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_closure((void*)(l_OptionT_tryCatch___redArg___lam__0), 3, 2);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_8);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_4, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOfUnit___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
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
}
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOfUnit___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_OptionT_instMonadExceptOfUnit___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_OptionT_tryCatch), 5, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOfUnit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_OptionT_instMonadExceptOfUnit___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOfUnit___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_OptionT_instMonadExceptOfUnit___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOf___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_4, lean_box(0), x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOf___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_3(x_5, lean_box(0), x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOf___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_OptionT_instMonadExceptOf___redArg___lam__0), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_OptionT_instMonadExceptOf___redArg___lam__1), 4, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_OptionT_instMonadExceptOf(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_OptionT_instMonadExceptOf___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_1(x_4, x_2);
x_9 = lean_alloc_closure((void*)(l_OptionT_lift___redArg___lam__0), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_alloc_closure((void*)(l_instMonadControlOptionTOfMonad___redArg___lam__0___boxed), 2, 0);
x_3 = lean_alloc_closure((void*)(l_instMonadControlOptionTOfMonad___redArg___lam__2), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = lean_alloc_closure((void*)(l_instMonadControlOptionTOfMonad___redArg___lam__1___boxed), 2, 0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instMonadControlOptionTOfMonad___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instMonadControlOptionTOfMonad___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instMonadControlOptionTOfMonad___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instMonadControlOptionTOfMonad___redArg___lam__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Init_Data_Option_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Control_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Control_Except(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Control_Option(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Option_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Except(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instToBoolOption___closed__0 = _init_l_instToBoolOption___closed__0();
lean_mark_persistent(l_instToBoolOption___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

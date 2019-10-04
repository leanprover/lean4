// Lean compiler output
// Module: Init.Control.Reader
// Imports: Init.Control.Lift Init.Control.Id Init.Control.Alternative Init.Control.Except
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
lean_object* l_ReaderT_Monad___rarg___lambda__7(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_map___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_HasMonadLift(lean_object*, lean_object*);
lean_object* l_ReaderT_Monad___rarg___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Monad___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_MonadRun(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Monad(lean_object*, lean_object*);
lean_object* l_ReaderT_HasMonadLift___rarg(lean_object*);
lean_object* l_ReaderT_lift___rarg(lean_object*, lean_object*);
lean_object* l_ReaderT_pure(lean_object*, lean_object*);
lean_object* l_monadReaderTrans(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_failure(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_MonadReader___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_MonadExcept___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_MonadStateRunner___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_map___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_adapt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_run(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_lift(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_MonadExcept___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_MonadReaderAdapter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_failure___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_monadReaderRunnerTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_MonadReaderAdapter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_monadReaderTrans___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read(lean_object*, lean_object*);
lean_object* l_ReaderT_MonadStateRunner(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_monadReaderTrans___rarg(lean_object*, lean_object*);
lean_object* l_ReaderT_Monad___rarg___lambda__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_run___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Alternative___boxed(lean_object*, lean_object*);
lean_object* l_monadReaderAdapterTrans___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_adapt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read___rarg(lean_object*, lean_object*);
lean_object* l_ReaderT_pure___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_monadReaderAdapterTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_lift___rarg___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_failure___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Monad___rarg___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Monad___rarg(lean_object*);
lean_object* l_ReaderT_bind(lean_object*, lean_object*);
lean_object* l_ReaderT_Monad___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_HasMonadLift___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_MonadExcept___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_monadReaderRunnerTrans___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_MonadRun___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_monadReaderRunnerTrans___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_orelse___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_MonadFunctor___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_map(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_MonadRun___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_MonadStateRunner___rarg(lean_object*, lean_object*);
lean_object* l_ReaderT_MonadFunctor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Monad___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Monad___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Monad___rarg___lambda__4(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_MonadReaderAdapter___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Function_const___rarg___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_orelse(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_MonadExcept___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_MonadFunctor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_MonadExcept___rarg(lean_object*);
lean_object* l_ReaderT_failure___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Monad___boxed(lean_object*, lean_object*);
lean_object* l_monadReaderAdapterTrans___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_monadReaderRunnerTrans___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Monad___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_adapt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Alternative___rarg(lean_object*, lean_object*);
lean_object* l_ReaderT_MonadExcept(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_MonadReader___rarg(lean_object*);
lean_object* l_ReaderT_MonadReader(lean_object*, lean_object*);
lean_object* l_ReaderT_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Alternative(lean_object*, lean_object*);
lean_object* l_ReaderT_orelse___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_monadFunctorTTrans___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_run___rarg(lean_object*, lean_object*);
lean_object* l_ReaderT_read___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_run___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_ReaderT_run(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_ReaderT_run___rarg), 2, 0);
return x_4;
}
}
lean_object* l_ReaderT_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ReaderT_run(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_ReaderT_read___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_ReaderT_read(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_read___rarg), 2, 0);
return x_3;
}
}
lean_object* l_ReaderT_read___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ReaderT_read(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_ReaderT_pure___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_2(x_6, lean_box(0), x_3);
return x_7;
}
}
lean_object* l_ReaderT_pure(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_pure___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_ReaderT_pure___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_ReaderT_pure___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_ReaderT_pure___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ReaderT_pure(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_ReaderT_bind___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
lean_object* l_ReaderT_bind___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_6);
x_8 = lean_apply_1(x_4, x_6);
x_9 = lean_alloc_closure((void*)(l_ReaderT_bind___rarg___lambda__1), 3, 2);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_6);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_ReaderT_bind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___rarg), 6, 0);
return x_3;
}
}
lean_object* l_ReaderT_bind___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ReaderT_bind(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_ReaderT_map___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_1(x_5, x_6);
x_11 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_4, x_10);
return x_11;
}
}
lean_object* l_ReaderT_map(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_map___rarg), 6, 0);
return x_3;
}
}
lean_object* l_ReaderT_map___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ReaderT_map(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_ReaderT_Monad___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_alloc_closure((void*)(l_Function_const___rarg___boxed), 2, 1);
lean_closure_set(x_7, 0, x_4);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_1(x_5, x_6);
x_12 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_7, x_11);
return x_12;
}
}
lean_object* l_ReaderT_Monad___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_1(x_2, x_3);
x_9 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_4, x_8);
return x_9;
}
}
lean_object* l_ReaderT_Monad___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
x_8 = lean_apply_1(x_4, x_6);
x_9 = lean_alloc_closure((void*)(l_ReaderT_Monad___rarg___lambda__2), 4, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_5);
lean_closure_set(x_9, 2, x_6);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_ReaderT_Monad___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_2(x_5, lean_box(0), x_2);
return x_6;
}
}
lean_object* l_ReaderT_Monad___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_apply_1(x_1, x_2);
x_7 = lean_alloc_closure((void*)(l_ReaderT_Monad___rarg___lambda__4___boxed), 3, 2);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
lean_object* l_ReaderT_Monad___rarg___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
x_8 = lean_apply_1(x_4, x_6);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_ReaderT_Monad___rarg___lambda__5), 5, 4);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_6);
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, x_7);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_ReaderT_Monad___rarg___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_2);
return x_4;
}
}
lean_object* l_ReaderT_Monad___rarg___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_6);
x_8 = lean_apply_1(x_4, x_6);
x_9 = lean_alloc_closure((void*)(l_ReaderT_Monad___rarg___lambda__7___boxed), 3, 2);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_6);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_ReaderT_Monad___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_ReaderT_map___rarg), 6, 1);
lean_closure_set(x_2, 0, x_1);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_ReaderT_Monad___rarg___lambda__1), 6, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_ReaderT_pure___rarg___boxed), 4, 1);
lean_closure_set(x_5, 0, x_1);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_ReaderT_Monad___rarg___lambda__3), 6, 1);
lean_closure_set(x_6, 0, x_1);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_ReaderT_Monad___rarg___lambda__6), 6, 1);
lean_closure_set(x_7, 0, x_1);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_ReaderT_Monad___rarg___lambda__8), 6, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set(x_9, 4, x_8);
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___rarg), 6, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
lean_object* l_ReaderT_Monad(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_Monad___rarg), 1, 0);
return x_3;
}
}
lean_object* l_ReaderT_Monad___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ReaderT_Monad___rarg___lambda__4(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_ReaderT_Monad___rarg___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ReaderT_Monad___rarg___lambda__7(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_ReaderT_Monad___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ReaderT_Monad(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_ReaderT_lift___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_ReaderT_lift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_ReaderT_lift___rarg___boxed), 2, 0);
return x_5;
}
}
lean_object* l_ReaderT_lift___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ReaderT_lift___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_ReaderT_lift___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_ReaderT_lift(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_ReaderT_HasMonadLift___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_lift___boxed), 4, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
lean_object* l_ReaderT_HasMonadLift(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_HasMonadLift___rarg), 1, 0);
return x_3;
}
}
lean_object* l_ReaderT_HasMonadLift___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ReaderT_HasMonadLift(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_ReaderT_MonadFunctor___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_ReaderT_MonadFunctor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_ReaderT_MonadFunctor___rarg), 3, 0);
return x_7;
}
}
lean_object* l_ReaderT_MonadFunctor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_ReaderT_MonadFunctor(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_ReaderT_adapt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
lean_object* l_ReaderT_adapt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_ReaderT_adapt___rarg), 3, 0);
return x_7;
}
}
lean_object* l_ReaderT_adapt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_ReaderT_adapt(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_ReaderT_orelse___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec(x_1);
lean_inc(x_5);
x_7 = lean_apply_1(x_3, x_5);
x_8 = lean_apply_1(x_4, x_5);
x_9 = lean_apply_3(x_6, lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_ReaderT_orelse(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_ReaderT_orelse___rarg), 5, 0);
return x_4;
}
}
lean_object* l_ReaderT_orelse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ReaderT_orelse(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_ReaderT_failure___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_4, lean_box(0));
return x_5;
}
}
lean_object* l_ReaderT_failure(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_ReaderT_failure___rarg___boxed), 3, 0);
return x_4;
}
}
lean_object* l_ReaderT_failure___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ReaderT_failure___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_ReaderT_failure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ReaderT_failure(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_ReaderT_Alternative___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_ReaderT_Monad___rarg(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
lean_inc(x_2);
x_5 = lean_alloc_closure((void*)(l_ReaderT_failure___rarg___boxed), 3, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = lean_alloc_closure((void*)(l_ReaderT_orelse___rarg), 5, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
lean_object* l_ReaderT_Alternative(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_Alternative___rarg), 2, 0);
return x_3;
}
}
lean_object* l_ReaderT_Alternative___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ReaderT_Alternative(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_ReaderT_MonadExcept___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_5, lean_box(0), x_3);
return x_6;
}
}
lean_object* l_ReaderT_MonadExcept___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
lean_inc(x_5);
x_7 = lean_apply_1(x_3, x_5);
x_8 = lean_alloc_closure((void*)(l_ReaderT_bind___rarg___lambda__1), 3, 2);
lean_closure_set(x_8, 0, x_4);
lean_closure_set(x_8, 1, x_5);
x_9 = lean_apply_3(x_6, lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_ReaderT_MonadExcept___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_ReaderT_MonadExcept___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_ReaderT_MonadExcept___rarg___lambda__2), 5, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l_ReaderT_MonadExcept(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_ReaderT_MonadExcept___rarg), 1, 0);
return x_6;
}
}
lean_object* l_ReaderT_MonadExcept___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_ReaderT_MonadExcept___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_ReaderT_MonadExcept___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_ReaderT_MonadExcept(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_monadReaderTrans___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
lean_object* l_monadReaderTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_monadReaderTrans___rarg), 2, 0);
return x_4;
}
}
lean_object* l_monadReaderTrans___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_monadReaderTrans(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_ReaderT_MonadReader___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_read___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_ReaderT_MonadReader(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_MonadReader___rarg), 1, 0);
return x_3;
}
}
lean_object* l_ReaderT_MonadReader___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ReaderT_MonadReader(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_monadReaderAdapterTrans___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_monadFunctorTTrans___rarg___lambda__1), 4, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_3(x_1, lean_box(0), x_6, x_5);
return x_7;
}
}
lean_object* l_monadReaderAdapterTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_monadReaderAdapterTrans___rarg), 5, 0);
return x_7;
}
}
lean_object* l_monadReaderAdapterTrans___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_monadReaderAdapterTrans(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_ReaderT_MonadReaderAdapter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
lean_object* l_ReaderT_MonadReaderAdapter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_ReaderT_MonadReaderAdapter___rarg), 3, 0);
return x_6;
}
}
lean_object* l_ReaderT_MonadReaderAdapter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_ReaderT_MonadReaderAdapter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_ReaderT_MonadRun___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_1(x_3, x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_ReaderT_MonadRun(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_ReaderT_MonadRun___rarg), 4, 0);
return x_4;
}
}
lean_object* l_ReaderT_MonadRun___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ReaderT_MonadRun(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_monadReaderRunnerTrans___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, lean_box(0), x_4, x_2);
return x_5;
}
}
lean_object* l_monadReaderRunnerTrans___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_monadReaderRunnerTrans___rarg___lambda__1), 4, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_apply_3(x_1, lean_box(0), x_6, x_4);
return x_7;
}
}
lean_object* l_monadReaderRunnerTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_monadReaderRunnerTrans___rarg), 5, 0);
return x_6;
}
}
lean_object* l_monadReaderRunnerTrans___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_monadReaderRunnerTrans(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_ReaderT_MonadStateRunner___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_ReaderT_MonadStateRunner(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_ReaderT_MonadStateRunner___rarg), 2, 0);
return x_5;
}
}
lean_object* l_ReaderT_MonadStateRunner___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_ReaderT_MonadStateRunner(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Init_Control_Lift(lean_object*);
lean_object* initialize_Init_Control_Id(lean_object*);
lean_object* initialize_Init_Control_Alternative(lean_object*);
lean_object* initialize_Init_Control_Except(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Control_Reader(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Control_Lift(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Control_Id(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Control_Alternative(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Control_Except(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif

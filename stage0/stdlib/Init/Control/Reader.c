// Lean compiler output
// Module: Init.Control.Reader
// Imports: Init.Control.MonadControl Init.Control.Id Init.Control.Alternative Init.Control.Except
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
lean_object* l_ReaderT_Init_Control_Reader___instance__4(lean_object*, lean_object*);
lean_object* l_withTheReader(lean_object*, lean_object*);
lean_object* l_Init_Control_Reader___instance__7___rarg(lean_object*);
lean_object* l_ReaderT_tryFinally___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_lift(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Id_Init_Control_Id___instance__1___closed__5;
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_map___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_run(lean_object*, lean_object*, lean_object*);
lean_object* l_Init_Control_Reader___instance__9___rarg(lean_object*);
lean_object* l_ReaderT_lift___rarg___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__3___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__2___rarg(lean_object*, lean_object*);
lean_object* l_ReaderT_failure(lean_object*, lean_object*);
lean_object* l_readThe___rarg___boxed(lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__3___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_adapt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__9___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Init_Control_Reader___instance__13___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Init_Control_Reader___instance__11(lean_object*, lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Function_const___rarg___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__6___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_failure___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_withTheReader___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__6___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__5___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Init_Control_Reader___instance__10___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Init_Control_Reader___instance__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Init_Control_Reader___instance__7___rarg___boxed(lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind(lean_object*, lean_object*);
lean_object* l_Init_Control_Reader___instance__1___rarg(lean_object*, lean_object*);
lean_object* l_ReaderT_read___rarg(lean_object*, lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_run___rarg(lean_object*, lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__3___rarg(lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__6___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__3(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__9(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_orelse___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Init_Control_Reader___instance__8___rarg(lean_object*, lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_readThe(lean_object*, lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_orelse(lean_object*, lean_object*);
lean_object* l_ReaderT_tryFinally(lean_object*, lean_object*);
lean_object* l_ReaderT_read(lean_object*, lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__3___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Init_Control_Reader___instance__1(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__6___rarg(lean_object*, lean_object*);
lean_object* l_Init_Control_Reader___instance__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_adapt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_failure___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__2___rarg___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__6(lean_object*, lean_object*);
lean_object* l_Init_Control_Reader___instance__8(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_map(lean_object*, lean_object*);
lean_object* l_Init_Control_Reader___instance__10___closed__1;
lean_object* l_Init_Control_Reader___instance__9(lean_object*, lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_adapt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Init_Control_Reader___instance__10___closed__2;
lean_object* l_Init_Control_Reader___instance__10(lean_object*, lean_object*);
lean_object* l_Init_Control_Reader___instance__7(lean_object*, lean_object*);
lean_object* l_Init_Control_Reader___instance__12___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure(lean_object*, lean_object*);
lean_object* l_ReaderT_lift___rarg(lean_object*, lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg(lean_object*);
lean_object* l_Init_Control_Reader___instance__12___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Init_Control_Reader___instance__3___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Init_Control_Reader___instance__12(lean_object*, lean_object*, lean_object*);
lean_object* l_Init_Control_Reader___instance__13(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Init_Control_Reader___instance__10___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Init_Control_Reader___instance__11___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_tryFinally___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_readThe___rarg(lean_object*);
lean_object* l_Init_Control_Reader___instance__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Init_Control_Reader___instance__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Init_Control_Reader___instance__1___rarg___boxed), 2, 0);
return x_4;
}
}
lean_object* l_Init_Control_Reader___instance__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Init_Control_Reader___instance__1___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
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
lean_object* l_ReaderT_lift___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_ReaderT_lift(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_ReaderT_lift___rarg___boxed), 2, 0);
return x_4;
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
lean_object* l_ReaderT_Init_Control_Reader___instance__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_ReaderT_Init_Control_Reader___instance__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_ReaderT_Init_Control_Reader___instance__2___rarg___boxed), 2, 0);
return x_4;
}
}
lean_object* l_ReaderT_Init_Control_Reader___instance__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ReaderT_Init_Control_Reader___instance__2___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_ReaderT_Init_Control_Reader___instance__3___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_ReaderT_Init_Control_Reader___instance__3___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
lean_object* l_ReaderT_Init_Control_Reader___instance__3___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_5);
x_6 = lean_apply_1(x_3, x_5);
x_7 = lean_alloc_closure((void*)(l_ReaderT_Init_Control_Reader___instance__3___rarg___lambda__2), 3, 2);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_3(x_8, lean_box(0), x_6, x_7);
return x_9;
}
}
lean_object* l_ReaderT_Init_Control_Reader___instance__3___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_ReaderT_Init_Control_Reader___instance__3___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_ReaderT_Init_Control_Reader___instance__3___rarg___lambda__3), 5, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l_ReaderT_Init_Control_Reader___instance__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_ReaderT_Init_Control_Reader___instance__3___rarg), 1, 0);
return x_4;
}
}
lean_object* l_ReaderT_Init_Control_Reader___instance__3___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_ReaderT_Init_Control_Reader___instance__3___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
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
lean_object* l_ReaderT_orelse(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_orelse___rarg), 5, 0);
return x_3;
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
lean_object* l_ReaderT_failure(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_failure___rarg___boxed), 3, 0);
return x_3;
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
lean_object* l_ReaderT_bind___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_6);
x_8 = lean_apply_1(x_4, x_6);
x_9 = lean_alloc_closure((void*)(l_ReaderT_Init_Control_Reader___instance__3___rarg___lambda__2), 3, 2);
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
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
x_8 = lean_apply_1(x_4, x_6);
x_9 = lean_alloc_closure((void*)(l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__4), 4, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_5);
lean_closure_set(x_9, 2, x_6);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_apply_1(x_1, x_2);
x_7 = lean_alloc_closure((void*)(l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__6___boxed), 3, 2);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
x_7 = lean_apply_1(x_3, x_5);
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__7), 5, 4);
lean_closure_set(x_8, 0, x_4);
lean_closure_set(x_8, 1, x_5);
lean_closure_set(x_8, 2, x_1);
lean_closure_set(x_8, 3, x_6);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_2);
return x_4;
}
}
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
lean_inc(x_5);
x_7 = lean_apply_1(x_3, x_5);
x_8 = lean_alloc_closure((void*)(l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__9___boxed), 3, 2);
lean_closure_set(x_8, 0, x_4);
lean_closure_set(x_8, 1, x_5);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_6);
x_8 = lean_apply_1(x_4, x_6);
x_9 = lean_alloc_closure((void*)(l_ReaderT_Init_Control_Reader___instance__3___rarg___lambda__2), 3, 2);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_6);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__1), 6, 1);
lean_closure_set(x_2, 0, x_1);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__2), 6, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__3___boxed), 4, 1);
lean_closure_set(x_5, 0, x_1);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__5), 6, 1);
lean_closure_set(x_6, 0, x_1);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__8), 5, 1);
lean_closure_set(x_7, 0, x_1);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__10), 5, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set(x_9, 4, x_8);
x_10 = lean_alloc_closure((void*)(l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__11), 6, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
lean_object* l_ReaderT_Init_Control_Reader___instance__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_Init_Control_Reader___instance__4___rarg), 1, 0);
return x_3;
}
}
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__6(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__9(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_ReaderT_Init_Control_Reader___instance__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_ReaderT_Init_Control_Reader___instance__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_ReaderT_Init_Control_Reader___instance__5___rarg), 3, 0);
return x_5;
}
}
lean_object* l_ReaderT_Init_Control_Reader___instance__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_ReaderT_Init_Control_Reader___instance__5(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
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
lean_object* l_ReaderT_adapt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_ReaderT_adapt___rarg), 3, 0);
return x_6;
}
}
lean_object* l_ReaderT_adapt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_ReaderT_adapt(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_ReaderT_Init_Control_Reader___instance__6___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_ReaderT_Init_Control_Reader___instance__6___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_ReaderT_Init_Control_Reader___instance__6___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_ReaderT_Init_Control_Reader___instance__4___rarg(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
lean_inc(x_2);
x_5 = lean_alloc_closure((void*)(l_ReaderT_Init_Control_Reader___instance__6___rarg___lambda__1___boxed), 3, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = lean_alloc_closure((void*)(l_ReaderT_Init_Control_Reader___instance__6___rarg___lambda__2), 5, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
lean_object* l_ReaderT_Init_Control_Reader___instance__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_Init_Control_Reader___instance__6___rarg), 2, 0);
return x_3;
}
}
lean_object* l_ReaderT_Init_Control_Reader___instance__6___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ReaderT_Init_Control_Reader___instance__6___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_readThe___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_readThe(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_readThe___rarg___boxed), 1, 0);
return x_3;
}
}
lean_object* l_readThe___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_readThe___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Init_Control_Reader___instance__7___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Init_Control_Reader___instance__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Init_Control_Reader___instance__7___rarg___boxed), 1, 0);
return x_3;
}
}
lean_object* l_Init_Control_Reader___instance__7___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Init_Control_Reader___instance__7___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Init_Control_Reader___instance__8___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_2, lean_box(0), x_1);
return x_3;
}
}
lean_object* l_Init_Control_Reader___instance__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Init_Control_Reader___instance__8___rarg), 2, 0);
return x_4;
}
}
lean_object* l_Init_Control_Reader___instance__9___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_read___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Init_Control_Reader___instance__9(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Init_Control_Reader___instance__9___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Init_Control_Reader___instance__10___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
}
lean_object* l_Init_Control_Reader___instance__10___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Init_Control_Reader___instance__10___lambda__1), 3, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Init_Control_Reader___instance__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Init_Control_Reader___instance__10___lambda__2), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Init_Control_Reader___instance__10___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Init_Control_Reader___instance__10___closed__1;
x_2 = l_Id_Init_Control_Id___instance__1___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Init_Control_Reader___instance__10(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Init_Control_Reader___instance__10___closed__2;
return x_3;
}
}
lean_object* l_ReaderT_tryFinally___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_7);
x_8 = lean_apply_1(x_5, x_7);
x_9 = lean_alloc_closure((void*)(l_ReaderT_Init_Control_Reader___instance__3___rarg___lambda__2), 3, 2);
lean_closure_set(x_9, 0, x_6);
lean_closure_set(x_9, 1, x_7);
x_10 = lean_apply_4(x_1, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_ReaderT_tryFinally(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___rarg___boxed), 7, 0);
return x_3;
}
}
lean_object* l_ReaderT_tryFinally___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_ReaderT_tryFinally___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_withTheReader___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, lean_box(0), x_3, x_4);
return x_5;
}
}
lean_object* l_withTheReader(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_withTheReader___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Init_Control_Reader___instance__11___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, lean_box(0), x_3, x_4);
return x_5;
}
}
lean_object* l_Init_Control_Reader___instance__11(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Init_Control_Reader___instance__11___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Init_Control_Reader___instance__12___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, lean_box(0), x_2, x_4);
return x_5;
}
}
lean_object* l_Init_Control_Reader___instance__12___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Init_Control_Reader___instance__12___rarg___lambda__1), 4, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_3(x_2, lean_box(0), x_6, x_5);
return x_7;
}
}
lean_object* l_Init_Control_Reader___instance__12(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Init_Control_Reader___instance__12___rarg), 5, 0);
return x_4;
}
}
lean_object* l_Init_Control_Reader___instance__13___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
lean_object* l_Init_Control_Reader___instance__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Init_Control_Reader___instance__13___rarg), 3, 0);
return x_5;
}
}
lean_object* l_Init_Control_Reader___instance__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Init_Control_Reader___instance__13(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* initialize_Init_Control_MonadControl(lean_object*);
lean_object* initialize_Init_Control_Id(lean_object*);
lean_object* initialize_Init_Control_Alternative(lean_object*);
lean_object* initialize_Init_Control_Except(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Control_Reader(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_MonadControl(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Id(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Alternative(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Except(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Init_Control_Reader___instance__10___closed__1 = _init_l_Init_Control_Reader___instance__10___closed__1();
lean_mark_persistent(l_Init_Control_Reader___instance__10___closed__1);
l_Init_Control_Reader___instance__10___closed__2 = _init_l_Init_Control_Reader___instance__10___closed__2();
lean_mark_persistent(l_Init_Control_Reader___instance__10___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

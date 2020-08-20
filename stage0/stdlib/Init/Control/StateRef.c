// Lean compiler output
// Module: Init.Control.StateRef
// Imports: Init.System.IO Init.Control.State
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
lean_object* l_StateRefT_MonadStateOf(lean_object*, lean_object*);
lean_object* l_StateRefT_MonadStateOf___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_MonadIO___rarg(lean_object*);
lean_object* l_StateRefT_set___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_lift___rarg(lean_object*, lean_object*);
lean_object* l_StateRefT_MonadStateOf___rarg___boxed(lean_object*, lean_object*);
lean_object* l_StateRefT_set(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_run_x27(lean_object*, lean_object*);
lean_object* l_StateRefT_set___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_run___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Monad___rarg(lean_object*);
lean_object* l_StateRefT_run___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_Ref_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_MonadExceptOf(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_MonadFunctor___rarg(lean_object*, lean_object*);
lean_object* l_StateRefT_modifyGet(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_get___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_run_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_Monad(lean_object*, lean_object*);
lean_object* l_StateRefT_get(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_run___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_run(lean_object*, lean_object*);
lean_object* l_StateRefT_modifyGet___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_get___rarg(lean_object*, lean_object*);
lean_object* l_StateRefT_lift___rarg___boxed(lean_object*, lean_object*);
lean_object* l_StateRefT_Monad___rarg(lean_object*);
lean_object* l_StateRefT_HasMonadLift___rarg(lean_object*, lean_object*);
lean_object* l_ReaderT_MonadExceptOf___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_MonadFunctor(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_MonadIO(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_HasMonadLift(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_MonadExceptOf___rarg(lean_object*);
lean_object* l_StateRefT_HasMonadLift___rarg___boxed(lean_object*, lean_object*);
lean_object* l_StateRefT_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_lift(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_monadIO___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_MonadExceptOf___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_MonadFunctor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_run_x27___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_IO_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_modifyGet___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_MonadIO___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_Ref_modifyGetUnsafe___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_MonadStateOf___rarg(lean_object*, lean_object*);
lean_object* l_StateRefT_run___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_StateRefT_run___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_closure((void*)(l_IO_Prim_Ref_get___boxed), 3, 2);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, x_1);
x_7 = lean_apply_2(x_2, lean_box(0), x_6);
x_8 = lean_alloc_closure((void*)(l_StateRefT_run___rarg___lambda__1), 3, 2);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_5);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_StateRefT_run___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_5);
x_6 = lean_apply_1(x_1, x_5);
lean_inc(x_4);
x_7 = lean_alloc_closure((void*)(l_StateRefT_run___rarg___lambda__2), 5, 4);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_3);
lean_closure_set(x_7, 3, x_4);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
lean_object* l_StateRefT_run___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_IO_Prim_mkRef___boxed), 3, 2);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, x_5);
lean_inc(x_2);
x_8 = lean_apply_2(x_2, lean_box(0), x_7);
lean_inc(x_6);
x_9 = lean_alloc_closure((void*)(l_StateRefT_run___rarg___lambda__3), 5, 4);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, x_6);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_StateRefT_run(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_StateRefT_run___rarg), 5, 0);
return x_3;
}
}
lean_object* l_StateRefT_run_x27___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_2(x_5, lean_box(0), x_3);
return x_6;
}
}
lean_object* l_StateRefT_run_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_IO_Prim_mkRef___boxed), 3, 2);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, x_5);
lean_inc(x_2);
x_8 = lean_apply_2(x_2, lean_box(0), x_7);
lean_inc(x_6);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_StateRefT_run___rarg___lambda__3), 5, 4);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, x_6);
lean_inc(x_6);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
x_11 = lean_alloc_closure((void*)(l_StateRefT_run_x27___rarg___lambda__1), 2, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
lean_object* l_StateRefT_run_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_StateRefT_run_x27___rarg), 5, 0);
return x_3;
}
}
lean_object* l_StateRefT_lift___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_StateRefT_lift(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_StateRefT_lift___rarg___boxed), 2, 0);
return x_4;
}
}
lean_object* l_StateRefT_lift___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_StateRefT_lift___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_StateRefT_Monad___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ReaderT_Monad___rarg(x_1);
return x_2;
}
}
lean_object* l_StateRefT_Monad(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_StateRefT_Monad___rarg), 1, 0);
return x_3;
}
}
lean_object* l_StateRefT_HasMonadLift___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_StateRefT_HasMonadLift(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_StateRefT_HasMonadLift___rarg___boxed), 2, 0);
return x_4;
}
}
lean_object* l_StateRefT_HasMonadLift___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_StateRefT_HasMonadLift___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_StateRefT_MonadIO___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_monadIO___rarg___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_StateRefT_MonadIO(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_StateRefT_MonadIO___rarg), 1, 0);
return x_4;
}
}
lean_object* l_StateRefT_MonadIO___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_StateRefT_MonadIO(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_StateRefT_MonadFunctor___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_MonadFunctor___boxed), 6, 5);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, lean_box(0));
lean_closure_set(x_3, 3, x_1);
lean_closure_set(x_3, 4, x_2);
return x_3;
}
}
lean_object* l_StateRefT_MonadFunctor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_StateRefT_MonadFunctor___rarg), 2, 0);
return x_4;
}
}
lean_object* l_StateRefT_get___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_IO_Prim_Ref_get___boxed), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_StateRefT_get(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_StateRefT_get___rarg), 2, 0);
return x_4;
}
}
lean_object* l_StateRefT_get___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_StateRefT_get(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_StateRefT_set___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_IO_Prim_Ref_set___boxed), 4, 3);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, x_3);
lean_closure_set(x_4, 2, x_2);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_StateRefT_set(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_StateRefT_set___rarg), 3, 0);
return x_4;
}
}
lean_object* l_StateRefT_set___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_StateRefT_set(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_StateRefT_modifyGet___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_IO_Prim_Ref_modifyGetUnsafe___rarg___boxed), 3, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_StateRefT_modifyGet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_StateRefT_modifyGet___rarg), 3, 0);
return x_5;
}
}
lean_object* l_StateRefT_modifyGet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_StateRefT_modifyGet(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_StateRefT_MonadStateOf___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_IO_Prim_Ref_modifyGetUnsafe___rarg___boxed), 3, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_StateRefT_MonadStateOf___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_StateRefT_get___rarg), 2, 1);
lean_closure_set(x_3, 0, x_1);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_StateRefT_set___rarg), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_alloc_closure((void*)(l_StateRefT_MonadStateOf___rarg___lambda__1), 4, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
return x_6;
}
}
lean_object* l_StateRefT_MonadStateOf(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_StateRefT_MonadStateOf___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_StateRefT_MonadStateOf___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_StateRefT_MonadStateOf___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_StateRefT_MonadExceptOf___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_ReaderT_MonadExceptOf___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_ReaderT_MonadExceptOf___rarg___lambda__2), 5, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l_StateRefT_MonadExceptOf(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_StateRefT_MonadExceptOf___rarg), 1, 0);
return x_4;
}
}
lean_object* initialize_Init_System_IO(lean_object*);
lean_object* initialize_Init_Control_State(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Control_StateRef(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_State(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

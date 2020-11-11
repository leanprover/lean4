// Lean compiler output
// Module: Init.Control.MonadControl
// Imports: Init.Control.MonadLift
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
lean_object* l_Init_Control_MonadControl___instance__1___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Init_Control_MonadControl___instance__2___rarg(lean_object*);
lean_object* l_control___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_controlAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_controlAt(lean_object*, lean_object*);
lean_object* l_Init_Control_MonadControl___instance__2___rarg___lambda__2(lean_object*, lean_object*);
lean_object* l_Init_Control_MonadControl___instance__2___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Init_Control_MonadControl___instance__1___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Init_Control_MonadControl___instance__2___rarg___closed__1;
lean_object* l_Init_Prelude___instance__37___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Init_Control_MonadControl___instance__1___rarg___lambda__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Init_Control_MonadControl___instance__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Init_Control_MonadControl___instance__2___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Init_Control_MonadControl___instance__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Init_Control_MonadControl___instance__2___rarg___lambda__2___closed__1;
lean_object* l_Init_Control_MonadControl___instance__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Init_Control_MonadControl___instance__1___rarg(lean_object*, lean_object*);
lean_object* l_Init_Control_MonadControl___instance__2(lean_object*);
lean_object* l_control(lean_object*, lean_object*);
lean_object* l_Init_Control_MonadControl___instance__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Init_Control_MonadControl___instance__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Init_Control_MonadControl___instance__1___rarg___lambda__1), 4, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
lean_object* l_Init_Control_MonadControl___instance__1___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_closure((void*)(l_Init_Control_MonadControl___instance__1___rarg___lambda__2), 3, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_2);
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Init_Control_MonadControl___instance__1___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_closure((void*)(l_Init_Control_MonadControl___instance__1___rarg___lambda__3), 3, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Init_Control_MonadControl___instance__1___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_apply_2(x_6, lean_box(0), x_4);
x_8 = lean_apply_2(x_5, lean_box(0), x_7);
return x_8;
}
}
lean_object* l_Init_Control_MonadControl___instance__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
lean_inc(x_2);
x_3 = lean_alloc_closure((void*)(l_Init_Control_MonadControl___instance__1___rarg___lambda__4), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
x_4 = lean_alloc_closure((void*)(l_Init_Control_MonadControl___instance__1___rarg___lambda__5), 4, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
lean_object* l_Init_Control_MonadControl___instance__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Init_Control_MonadControl___instance__1___rarg), 2, 0);
return x_4;
}
}
lean_object* l_Init_Control_MonadControl___instance__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Init_Control_MonadControl___instance__2___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Init_Control_MonadControl___instance__2___rarg___lambda__1___boxed), 2, 0);
return x_1;
}
}
lean_object* l_Init_Control_MonadControl___instance__2___rarg___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Init_Control_MonadControl___instance__2___rarg___lambda__2___closed__1;
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Init_Control_MonadControl___instance__2___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Init_Control_MonadControl___instance__2___rarg___lambda__2), 2, 0);
return x_1;
}
}
lean_object* l_Init_Control_MonadControl___instance__2___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Init_Prelude___instance__37___rarg___lambda__1), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Init_Control_MonadControl___instance__2___rarg___closed__1;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Init_Control_MonadControl___instance__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Init_Control_MonadControl___instance__2___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Init_Control_MonadControl___instance__2___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Init_Control_MonadControl___instance__2___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_controlAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_apply_2(x_5, lean_box(0), x_4);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_7, lean_box(0));
x_9 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_6, x_8);
return x_9;
}
}
lean_object* l_controlAt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_controlAt___rarg), 4, 0);
return x_3;
}
}
lean_object* l_control___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_apply_2(x_5, lean_box(0), x_4);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_7, lean_box(0));
x_9 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_6, x_8);
return x_9;
}
}
lean_object* l_control(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_control___rarg), 4, 0);
return x_3;
}
}
lean_object* initialize_Init_Control_MonadLift(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Control_MonadControl(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_MonadLift(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Init_Control_MonadControl___instance__2___rarg___lambda__2___closed__1 = _init_l_Init_Control_MonadControl___instance__2___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Init_Control_MonadControl___instance__2___rarg___lambda__2___closed__1);
l_Init_Control_MonadControl___instance__2___rarg___closed__1 = _init_l_Init_Control_MonadControl___instance__2___rarg___closed__1();
lean_mark_persistent(l_Init_Control_MonadControl___instance__2___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

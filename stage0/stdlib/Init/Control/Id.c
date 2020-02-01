// Lean compiler output
// Module: Init.Control.Id
// Imports: Init.Control.Lift
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
lean_object* l_Id_bind___rarg(lean_object*, lean_object*);
lean_object* l_Id_map___rarg(lean_object*, lean_object*);
lean_object* l_Id_bind(lean_object*, lean_object*);
lean_object* l_Id_monad___closed__6;
lean_object* l_Id_monad___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_monad___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_run(lean_object*);
lean_object* l_Id_monad;
lean_object* l_Id_monad___closed__8;
lean_object* l_Id_monad___closed__3;
lean_object* l_Id_pure___rarg___boxed(lean_object*);
lean_object* l_Id_monad___closed__1;
lean_object* l_Id_run___rarg___boxed(lean_object*);
lean_object* l_Id_monad___closed__4;
lean_object* l_Id_map(lean_object*, lean_object*);
lean_object* l_Id_monad___closed__7;
lean_object* l_Id_pure___rarg(lean_object*);
lean_object* l_Id_monad___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_monad___closed__2;
lean_object* l_Id_pure(lean_object*);
lean_object* l_Id_monad___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_monad___closed__5;
lean_object* l_Id_hasBind;
lean_object* l_Id_MonadRun;
lean_object* l_Id_MonadRun___closed__1;
lean_object* l_Id_hasBind___closed__1;
lean_object* l_Id_run___rarg(lean_object*);
lean_object* l_Id_monad___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_pure___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Id_pure(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Id_pure___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_Id_pure___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Id_pure___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Id_bind___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
}
}
lean_object* l_Id_bind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Id_bind___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Id_map___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_Id_map(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Id_map___rarg), 2, 0);
return x_3;
}
}
lean_object* _init_l_Id_hasBind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_bind), 2, 0);
return x_1;
}
}
lean_object* _init_l_Id_hasBind() {
_start:
{
lean_object* x_1; 
x_1 = l_Id_hasBind___closed__1;
return x_1;
}
}
lean_object* l_Id_monad___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_3);
return x_3;
}
}
lean_object* l_Id_monad___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
lean_object* l_Id_monad___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
lean_object* _init_l_Id_monad___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_map), 2, 0);
return x_1;
}
}
lean_object* _init_l_Id_monad___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_monad___lambda__1___boxed), 4, 0);
return x_1;
}
}
lean_object* _init_l_Id_monad___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Id_monad___closed__1;
x_2 = l_Id_monad___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Id_monad___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_pure), 1, 0);
return x_1;
}
}
lean_object* _init_l_Id_monad___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_monad___lambda__2), 4, 0);
return x_1;
}
}
lean_object* _init_l_Id_monad___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_monad___lambda__3___boxed), 4, 0);
return x_1;
}
}
lean_object* _init_l_Id_monad___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Id_monad___closed__3;
x_2 = l_Id_monad___closed__4;
x_3 = l_Id_monad___closed__5;
x_4 = l_Id_monad___closed__2;
x_5 = l_Id_monad___closed__6;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
lean_object* _init_l_Id_monad___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Id_monad___closed__7;
x_2 = l_Id_hasBind___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Id_monad() {
_start:
{
lean_object* x_1; 
x_1 = l_Id_monad___closed__8;
return x_1;
}
}
lean_object* l_Id_monad___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Id_monad___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Id_monad___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Id_monad___lambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Id_run___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Id_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Id_run___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_Id_run___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Id_run___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Id_MonadRun___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_run), 1, 0);
return x_1;
}
}
lean_object* _init_l_Id_MonadRun() {
_start:
{
lean_object* x_1; 
x_1 = l_Id_MonadRun___closed__1;
return x_1;
}
}
lean_object* initialize_Init_Control_Lift(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Control_Id(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Lift(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Id_hasBind___closed__1 = _init_l_Id_hasBind___closed__1();
lean_mark_persistent(l_Id_hasBind___closed__1);
l_Id_hasBind = _init_l_Id_hasBind();
lean_mark_persistent(l_Id_hasBind);
l_Id_monad___closed__1 = _init_l_Id_monad___closed__1();
lean_mark_persistent(l_Id_monad___closed__1);
l_Id_monad___closed__2 = _init_l_Id_monad___closed__2();
lean_mark_persistent(l_Id_monad___closed__2);
l_Id_monad___closed__3 = _init_l_Id_monad___closed__3();
lean_mark_persistent(l_Id_monad___closed__3);
l_Id_monad___closed__4 = _init_l_Id_monad___closed__4();
lean_mark_persistent(l_Id_monad___closed__4);
l_Id_monad___closed__5 = _init_l_Id_monad___closed__5();
lean_mark_persistent(l_Id_monad___closed__5);
l_Id_monad___closed__6 = _init_l_Id_monad___closed__6();
lean_mark_persistent(l_Id_monad___closed__6);
l_Id_monad___closed__7 = _init_l_Id_monad___closed__7();
lean_mark_persistent(l_Id_monad___closed__7);
l_Id_monad___closed__8 = _init_l_Id_monad___closed__8();
lean_mark_persistent(l_Id_monad___closed__8);
l_Id_monad = _init_l_Id_monad();
lean_mark_persistent(l_Id_monad);
l_Id_MonadRun___closed__1 = _init_l_Id_MonadRun___closed__1();
lean_mark_persistent(l_Id_MonadRun___closed__1);
l_Id_MonadRun = _init_l_Id_MonadRun();
lean_mark_persistent(l_Id_MonadRun);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

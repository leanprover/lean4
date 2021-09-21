// Lean compiler output
// Module: Init.Control.Reader
// Imports: Init.Control.Basic Init.Control.Id Init.Control.Except
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
LEAN_EXPORT lean_object* l_ReaderT_tryFinally___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlReaderT___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_failure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_tryFinally___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_orElse___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlReaderT___lambda__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeReaderT___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_failure___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_instMonadControlReaderT___closed__3;
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeReaderT___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlReaderT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlReaderT___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_instMonadControlReaderT___closed__2;
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeReaderT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_tryFinally(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_orElse___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_failure___rarg(lean_object*, lean_object*);
static lean_object* l_instMonadControlReaderT___closed__1;
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeReaderT___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_orElse(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlReaderT___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_orElse___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeReaderT___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_tryFinally___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_orElse___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_apply_2(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ReaderT_orElse___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_4);
x_5 = lean_apply_1(x_2, x_4);
x_6 = lean_alloc_closure((void*)(l_ReaderT_orElse___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_3(x_7, lean_box(0), x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_ReaderT_orElse(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_ReaderT_orElse___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ReaderT_orElse___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ReaderT_orElse___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ReaderT_failure___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_3, lean_box(0));
return x_4;
}
}
LEAN_EXPORT lean_object* l_ReaderT_failure(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_ReaderT_failure___rarg___boxed), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ReaderT_failure___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ReaderT_failure___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeReaderT___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeReaderT___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_5);
x_6 = lean_apply_1(x_3, x_5);
x_7 = lean_alloc_closure((void*)(l_ReaderT_orElse___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_3(x_8, lean_box(0), x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeReaderT___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_ReaderT_instMonadReaderT___rarg(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_ReaderT_instAlternativeReaderT___rarg___lambda__1___boxed), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_alloc_closure((void*)(l_ReaderT_instAlternativeReaderT___rarg___lambda__2), 5, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeReaderT(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_instAlternativeReaderT___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeReaderT___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ReaderT_instAlternativeReaderT___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instMonadControlReaderT___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instMonadControlReaderT___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_instMonadControlReaderT___lambda__1), 3, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instMonadControlReaderT___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_instMonadControlReaderT___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadControlReaderT___lambda__2), 3, 0);
return x_1;
}
}
static lean_object* _init_l_instMonadControlReaderT___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadControlReaderT___lambda__3___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_instMonadControlReaderT___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_instMonadControlReaderT___closed__1;
x_2 = l_instMonadControlReaderT___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instMonadControlReaderT(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instMonadControlReaderT___closed__3;
return x_3;
}
}
LEAN_EXPORT lean_object* l_instMonadControlReaderT___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_instMonadControlReaderT___lambda__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ReaderT_tryFinally___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ReaderT_tryFinally___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_7);
x_8 = lean_apply_1(x_5, x_7);
x_9 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___rarg___lambda__1), 3, 2);
lean_closure_set(x_9, 0, x_6);
lean_closure_set(x_9, 1, x_7);
x_10 = lean_apply_4(x_1, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_ReaderT_tryFinally(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___rarg___boxed), 7, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ReaderT_tryFinally___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_ReaderT_tryFinally___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* initialize_Init_Control_Basic(lean_object*);
lean_object* initialize_Init_Control_Id(lean_object*);
lean_object* initialize_Init_Control_Except(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Control_Reader(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Id(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Except(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instMonadControlReaderT___closed__1 = _init_l_instMonadControlReaderT___closed__1();
lean_mark_persistent(l_instMonadControlReaderT___closed__1);
l_instMonadControlReaderT___closed__2 = _init_l_instMonadControlReaderT___closed__2();
lean_mark_persistent(l_instMonadControlReaderT___closed__2);
l_instMonadControlReaderT___closed__3 = _init_l_instMonadControlReaderT___closed__3();
lean_mark_persistent(l_instMonadControlReaderT___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

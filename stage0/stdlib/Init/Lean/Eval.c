// Lean compiler output
// Module: Init.Lean.Eval
// Imports: Init.Control.Reader Init.System.IO Init.Lean.Environment
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
lean_object* l_Lean_MetaIO_monadIO___closed__3;
extern lean_object* l_EIO_Monad___closed__1;
lean_object* l_Lean_MetaIO_getOptions(lean_object*, lean_object*);
lean_object* l_Lean_MetaIO_monadIO___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_IO_MonadIO;
lean_object* l_ReaderT_monadIO___rarg(lean_object*, lean_object*);
lean_object* l_Lean_MetaIO_monadIO;
lean_object* l_Lean_MetaHasEvalOfHasEval(lean_object*);
lean_object* l_Lean_MetaIO_getEnv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MetaHasEvalOfHasEval___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetaIO_monadIO___closed__1;
lean_object* l_Lean_MetaIO_monadIO___closed__2;
lean_object* l_Lean_MetaHasEvalOfHasEval___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetaIO_metaHasEval(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetaIO_monadIO___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetaIO_getOptions___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MetaIO_getEnv(lean_object*, lean_object*);
lean_object* l_Lean_MetaHasEvalOfHasEval___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_2(x_1, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_MetaHasEvalOfHasEval(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MetaHasEvalOfHasEval___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_MetaHasEvalOfHasEval___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_MetaHasEvalOfHasEval___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_MetaIO_getEnv(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_MetaIO_getEnv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MetaIO_getEnv(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_MetaIO_getOptions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_MetaIO_getOptions___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MetaIO_getOptions(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_MetaIO_metaHasEval(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
x_6 = lean_apply_2(x_3, x_5, x_4);
return x_6;
}
}
lean_object* l_Lean_MetaIO_monadIO___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_MetaIO_monadIO___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_EIO_Monad___closed__1;
x_2 = l_IO_MonadIO;
x_3 = l_ReaderT_monadIO___rarg(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_MetaIO_monadIO___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MetaIO_monadIO___lambda__1___boxed), 4, 0);
return x_1;
}
}
lean_object* _init_l_Lean_MetaIO_monadIO___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lean_MetaIO_monadIO___closed__1;
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_dec(x_3);
x_4 = l_Lean_MetaIO_monadIO___closed__2;
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_MetaIO_monadIO___closed__2;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
lean_object* _init_l_Lean_MetaIO_monadIO() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MetaIO_monadIO___closed__3;
return x_1;
}
}
lean_object* l_Lean_MetaIO_monadIO___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MetaIO_monadIO___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* initialize_Init_Control_Reader(lean_object*);
lean_object* initialize_Init_System_IO(lean_object*);
lean_object* initialize_Init_Lean_Environment(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Eval(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Reader(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IO(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_MetaIO_monadIO___closed__1 = _init_l_Lean_MetaIO_monadIO___closed__1();
lean_mark_persistent(l_Lean_MetaIO_monadIO___closed__1);
l_Lean_MetaIO_monadIO___closed__2 = _init_l_Lean_MetaIO_monadIO___closed__2();
lean_mark_persistent(l_Lean_MetaIO_monadIO___closed__2);
l_Lean_MetaIO_monadIO___closed__3 = _init_l_Lean_MetaIO_monadIO___closed__3();
lean_mark_persistent(l_Lean_MetaIO_monadIO___closed__3);
l_Lean_MetaIO_monadIO = _init_l_Lean_MetaIO_monadIO();
lean_mark_persistent(l_Lean_MetaIO_monadIO);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

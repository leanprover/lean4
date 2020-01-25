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
lean_object* l_Lean_MetaIO_getOptions(lean_object*, lean_object*);
lean_object* l_Lean_MetaIO_monadIO(lean_object*);
lean_object* l_Lean_MetaIO_monadIO___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetaIO_monadIO___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetaHasEvalOfHasEval(lean_object*);
lean_object* l_Lean_MetaIO_getEnv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MetaHasEvalOfHasEval___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetaHasEvalOfHasEval___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetaIO_metaHasEval(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_MetaIO_monadIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
}
lean_object* l_Lean_MetaIO_monadIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MetaIO_monadIO___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_MetaIO_monadIO___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MetaIO_monadIO___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

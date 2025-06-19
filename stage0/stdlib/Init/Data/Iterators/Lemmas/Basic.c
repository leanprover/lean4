// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Basic
// Imports: Init.Data.Iterators.Basic
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
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_inductSteps___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_inductSteps___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_inductSkips___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_inductSkips___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_inductSteps___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_inductSteps___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_inductSteps(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_inductSkips(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_inductSteps___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Iterators_Iter_inductSteps___rarg(x_1, lean_box(0), lean_box(0), x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_inductSteps___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Iterators_Iter_inductSteps___rarg(x_1, lean_box(0), lean_box(0), x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_inductSteps___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_4);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Std_Iterators_Iter_inductSteps___rarg___lambda__1___boxed), 5, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
lean_inc(x_4);
x_7 = lean_alloc_closure((void*)(l_Std_Iterators_Iter_inductSteps___rarg___lambda__2), 4, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_4);
x_8 = lean_apply_3(x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_inductSteps(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Iterators_Iter_inductSteps___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_inductSteps___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Iterators_Iter_inductSteps___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_inductSkips___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Iterators_Iter_inductSkips___rarg(x_1, lean_box(0), lean_box(0), x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_inductSkips___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_4);
x_6 = lean_alloc_closure((void*)(l_Std_Iterators_Iter_inductSkips___rarg___lambda__1), 4, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_2(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_inductSkips(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Iterators_Iter_inductSkips___rarg), 5, 0);
return x_3;
}
}
lean_object* initialize_Init_Data_Iterators_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Lemmas_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

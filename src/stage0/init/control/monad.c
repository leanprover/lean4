// Lean compiler output
// Module: init.control.monad
// Imports: init.control.applicative
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
lean_object* l_mcomp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_monadInhabited_x27___rarg(lean_object*);
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
lean_object* l_monadInhabited(lean_object*, lean_object*);
lean_object* l_mcomp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_monadInhabited_x27___boxed(lean_object*, lean_object*);
lean_object* l_mcomp___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_monadInhabited___boxed(lean_object*, lean_object*);
lean_object* l_monadInhabited_x27(lean_object*, lean_object*);
lean_object* l_mcomp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_1(x_2, x_4);
x_6 = lean_apply_4(x_1, lean_box(0), lean_box(0), x_5, x_3);
return x_6;
}
}
lean_object* l_mcomp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_mcomp___rarg), 4, 0);
return x_5;
}
}
lean_object* l_mcomp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_mcomp(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_monadInhabited_x27___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_apply_1(x_3, lean_box(0));
return x_4;
}
}
lean_object* l_monadInhabited_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_monadInhabited_x27___rarg), 1, 0);
return x_3;
}
}
lean_object* l_monadInhabited_x27___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_monadInhabited_x27(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_monadInhabited___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_monadInhabited(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_monadInhabited___rarg), 2, 0);
return x_3;
}
}
lean_object* l_monadInhabited___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_monadInhabited(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_init_control_applicative(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_init_control_monad(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_init_control_applicative(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif

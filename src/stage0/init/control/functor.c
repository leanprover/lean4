// Lean compiler output
// Module: Init.Control.Functor
// Imports: Init.Core
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
lean_object* l_Functor_mapRev___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Functor_mapConstRev___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Functor_mapConstRev(lean_object*);
lean_object* l_Functor_mapRev(lean_object*);
lean_object* l_Functor_mapConstRev___boxed(lean_object*);
lean_object* l_Functor_mapRev___boxed(lean_object*);
lean_object* l_Functor_mapConstRev___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_5, x_4);
return x_7;
}
}
lean_object* l_Functor_mapConstRev(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Functor_mapConstRev___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Functor_mapConstRev___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Functor_mapConstRev(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Functor_mapRev___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_5, x_4);
return x_7;
}
}
lean_object* l_Functor_mapRev(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Functor_mapRev___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Functor_mapRev___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Functor_mapRev(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Core(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Control_Functor(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Core(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif

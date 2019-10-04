// Lean compiler output
// Module: Init.Control.Monadfail
// Imports: Init.Control.Lift Init.Data.String.Basic
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
lean_object* l_monadFailLift(lean_object*, lean_object*);
lean_object* l_matchFailed(lean_object*, lean_object*);
lean_object* l_matchFailed___boxed(lean_object*, lean_object*);
lean_object* l_monadFailLift___boxed(lean_object*, lean_object*);
lean_object* l_monadFailLift___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_matchFailed___rarg___closed__1;
lean_object* l_matchFailed___rarg(lean_object*);
lean_object* l_monadFailLift___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* _init_l_matchFailed___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("match failed");
return x_1;
}
}
lean_object* l_matchFailed___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_matchFailed___rarg___closed__1;
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
lean_object* l_matchFailed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_matchFailed___rarg), 1, 0);
return x_3;
}
}
lean_object* l_matchFailed___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_matchFailed(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_monadFailLift___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_monadFailLift(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_monadFailLift___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_monadFailLift___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_monadFailLift___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_monadFailLift___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_monadFailLift(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init_Control_Lift(lean_object*);
lean_object* initialize_Init_Data_String_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Control_Monadfail(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Control_Lift(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_String_Basic(w);
if (lean_io_result_is_error(w)) return w;
l_matchFailed___rarg___closed__1 = _init_l_matchFailed___rarg___closed__1();
lean_mark_persistent(l_matchFailed___rarg___closed__1);
return w;
}
#ifdef __cplusplus
}
#endif

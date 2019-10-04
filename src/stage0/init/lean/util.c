// Lean compiler output
// Module: Init.Lean.Util
// Imports: Init.System.IO Init.Lean.Position
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
lean_object* l_Lean_profileit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_lean_profileit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_profileitPure(lean_object*);
lean_object* l_Lean_profileitPure___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_profileitPure___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_lazyPure___rarg(lean_object*, lean_object*);
lean_object* l_Lean_profileit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_lean_profileit(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_profileitPure___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_IO_lazyPure___rarg), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_lean_profileit(lean_box(0), x_1, x_2, x_5, x_4);
return x_6;
}
}
lean_object* l_Lean_profileitPure(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_profileitPure___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_profileitPure___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_profileitPure___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Init_System_IO(lean_object*);
lean_object* initialize_Init_Lean_Position(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Util(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_System_IO(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Position(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif

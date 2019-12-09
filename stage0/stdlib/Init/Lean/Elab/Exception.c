// Lean compiler output
// Module: Init.Lean.Elab.Exception
// Imports: Init.Lean.Meta
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
lean_object* l_Lean_Elab_Exception_inhabited;
lean_object* l_Lean_Elab_str2ex(lean_object*);
lean_object* _init_l_Lean_Elab_Exception_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(5);
return x_1;
}
}
lean_object* l_Lean_Elab_str2ex(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* initialize_Init_Lean_Meta(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elab_Exception(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Meta(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Exception_inhabited = _init_l_Lean_Elab_Exception_inhabited();
lean_mark_persistent(l_Lean_Elab_Exception_inhabited);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

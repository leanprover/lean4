// Lean compiler output
// Module: init.lean.typeclass.basic
// Imports: init.lean.environment
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
lean_object* l_Lean_TypeClass_synth__command___closed__1;
lean_object* l_Lean_TypeClass_synth__command___closed__2;
lean_object* lean_typeclass_synth_command(lean_object*, lean_object*);
lean_object* _init_l_Lean_TypeClass_synth__command___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("not implemented yet");
return x_1;
}
}
lean_object* _init_l_Lean_TypeClass_synth__command___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_TypeClass_synth__command___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* lean_typeclass_synth_command(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_dec(x_2);
lean_dec(x_1);
x_3 = l_Lean_TypeClass_synth__command___closed__2;
return x_3;
}
}
lean_object* initialize_init_lean_environment(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_init_lean_typeclass_basic(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_environment(w);
if (lean_io_result_is_error(w)) return w;
l_Lean_TypeClass_synth__command___closed__1 = _init_l_Lean_TypeClass_synth__command___closed__1();
lean_mark_persistent(l_Lean_TypeClass_synth__command___closed__1);
l_Lean_TypeClass_synth__command___closed__2 = _init_l_Lean_TypeClass_synth__command___closed__2();
lean_mark_persistent(l_Lean_TypeClass_synth__command___closed__2);
return w;
}
#ifdef __cplusplus
}
#endif

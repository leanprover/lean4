// Lean compiler output
// Module: Init.Lean.Elab.Tactic.Induction
// Imports: Init.Lean.Elab.Tactic.Basic
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
lean_object* l_Lean_Elab_Tactic_evalInduction___closed__1;
lean_object* l_Lean_Elab_Tactic_evalInduction___closed__2;
extern lean_object* l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3;
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__3;
lean_object* l_Lean_Elab_Tactic_focus___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__1;
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalInduction___closed__3;
extern lean_object* l_Lean_Parser_Tactic_induction___elambda__1___closed__2;
lean_object* l_Lean_Elab_Tactic_evalInduction(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_addBuiltinTactic(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* _init_l_Lean_Elab_Tactic_evalInduction___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("WIP ");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalInduction___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalInduction___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalInduction___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalInduction___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_evalInduction(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = l_Lean_Elab_Tactic_evalInduction___closed__3;
x_6 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_throwError___rarg), 4, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
x_8 = l_Lean_Elab_Tactic_focus___rarg(x_1, x_7, x_2, x_3);
return x_8;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalInduction");
return x_1;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3;
x_2 = l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInduction), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Tactic_induction___elambda__1___closed__2;
x_3 = l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__2;
x_4 = l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__3;
x_5 = l_Lean_Elab_Tactic_addBuiltinTactic(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init_Lean_Elab_Tactic_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elab_Tactic_Induction(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Elab_Tactic_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalInduction___closed__1 = _init_l_Lean_Elab_Tactic_evalInduction___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalInduction___closed__1);
l_Lean_Elab_Tactic_evalInduction___closed__2 = _init_l_Lean_Elab_Tactic_evalInduction___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalInduction___closed__2);
l_Lean_Elab_Tactic_evalInduction___closed__3 = _init_l_Lean_Elab_Tactic_evalInduction___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalInduction___closed__3);
l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__1 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__1();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__1);
l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__2 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__2();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__2);
l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__3 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__3();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__3);
res = l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

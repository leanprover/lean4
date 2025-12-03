// Lean compiler output
// Module: Lean.Elab.Command.Scope
// Imports: public import Lean.Parser.Term
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
static lean_object* l_Lean_Elab_Command_instInhabitedScope_default___closed__0;
static lean_object* l_Lean_Elab_Command_instInhabitedScope_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_Array_empty(lean_object*);
static lean_object* l_Lean_Elab_Command_instInhabitedScope_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instInhabitedScope;
static lean_object* _init_l_Lean_Elab_Command_instInhabitedScope_default___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedScope_default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedScope_default___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 0;
x_2 = l_Lean_Elab_Command_instInhabitedScope_default___closed__1;
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = l_Lean_Elab_Command_instInhabitedScope_default___closed__0;
x_6 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_4);
lean_ctor_set(x_6, 5, x_2);
lean_ctor_set(x_6, 6, x_2);
lean_ctor_set(x_6, 7, x_4);
lean_ctor_set(x_6, 8, x_4);
lean_ctor_set(x_6, 9, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*10, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*10 + 1, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*10 + 2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedScope_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instInhabitedScope_default___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedScope() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instInhabitedScope_default;
return x_1;
}
}
lean_object* initialize_Lean_Parser_Term(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Command_Scope(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_instInhabitedScope_default___closed__0 = _init_l_Lean_Elab_Command_instInhabitedScope_default___closed__0();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedScope_default___closed__0);
l_Lean_Elab_Command_instInhabitedScope_default___closed__1 = _init_l_Lean_Elab_Command_instInhabitedScope_default___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedScope_default___closed__1);
l_Lean_Elab_Command_instInhabitedScope_default___closed__2 = _init_l_Lean_Elab_Command_instInhabitedScope_default___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedScope_default___closed__2);
l_Lean_Elab_Command_instInhabitedScope_default = _init_l_Lean_Elab_Command_instInhabitedScope_default();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedScope_default);
l_Lean_Elab_Command_instInhabitedScope = _init_l_Lean_Elab_Command_instInhabitedScope();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedScope);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

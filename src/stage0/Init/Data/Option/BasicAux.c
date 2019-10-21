// Lean compiler output
// Module: Init.Data.Option.BasicAux
// Imports: Init.Data.Option.Basic Init.Util
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
lean_object* l_Option_get_x21___rarg(lean_object*, lean_object*);
lean_object* l_Option_get_x21(lean_object*);
lean_object* l_Option_get_x21___rarg___closed__2;
lean_object* l_Option_get_x21___rarg___closed__1;
lean_object* l_Option_get_x21___rarg___boxed(lean_object*, lean_object*);
lean_object* l_panicWithPos___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* _init_l_Option_get_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Data.Option.BasicAux");
return x_1;
}
}
lean_object* _init_l_Option_get_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("value is none");
return x_1;
}
}
lean_object* l_Option_get_x21___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Option_get_x21___rarg___closed__1;
x_4 = lean_unsigned_to_nat(16u);
x_5 = lean_unsigned_to_nat(12u);
x_6 = l_Option_get_x21___rarg___closed__2;
x_7 = l_panicWithPos___rarg(x_1, x_3, x_4, x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
return x_8;
}
}
}
lean_object* l_Option_get_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_get_x21___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Option_get_x21___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Option_get_x21___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Init_Data_Option_Basic(lean_object*);
lean_object* initialize_Init_Util(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_Option_BasicAux(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Option_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Option_get_x21___rarg___closed__1 = _init_l_Option_get_x21___rarg___closed__1();
lean_mark_persistent(l_Option_get_x21___rarg___closed__1);
l_Option_get_x21___rarg___closed__2 = _init_l_Option_get_x21___rarg___closed__2();
lean_mark_persistent(l_Option_get_x21___rarg___closed__2);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

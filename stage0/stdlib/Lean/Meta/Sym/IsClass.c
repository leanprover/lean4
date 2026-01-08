// Lean compiler output
// Module: Lean.Meta.Sym.IsClass
// Imports: public import Lean.Meta.Sym.SymM
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_IsClass_0__Lean_Meta_Sym_isClass_x3f_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isClass_x3f(lean_object*, lean_object*);
uint8_t lean_is_class(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_IsClass_0__Lean_Meta_Sym_isClass_x3f_go(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 4:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec_ref(x_2);
lean_inc(x_3);
x_4 = lean_is_class(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_3);
return x_6;
}
}
case 5:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_2);
x_2 = x_7;
goto _start;
}
case 7:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_9);
lean_dec_ref(x_2);
x_2 = x_9;
goto _start;
}
case 8:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_11);
lean_dec_ref(x_2);
x_2 = x_11;
goto _start;
}
case 10:
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_13);
lean_dec_ref(x_2);
x_2 = x_13;
goto _start;
}
default: 
{
lean_object* x_15; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_15 = lean_box(0);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isClass_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Sym_IsClass_0__Lean_Meta_Sym_isClass_x3f_go(x_1, x_2);
return x_3;
}
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_IsClass(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

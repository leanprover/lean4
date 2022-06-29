// Lean compiler output
// Module: Lean.Elab.RecAppSyntax
// Imports: Init Lean.Expr
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
lean_object* lean_name_mk_string(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__1;
static lean_object* l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__2;
LEAN_EXPORT lean_object* l_Lean_getRecAppSyntax_x3f(lean_object*);
lean_object* l_Lean_mkMData(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRecAppSyntax_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkRecAppWithSyntax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey;
extern lean_object* l_Lean_KVMap_empty;
lean_object* l_Lean_KVMap_insertCore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_findCore(lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_recApp", 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRecAppWithSyntax(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = l_Lean_KVMap_empty;
x_5 = l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey;
x_6 = l_Lean_KVMap_insertCore(x_4, x_5, x_3);
x_7 = l_Lean_mkMData(x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getRecAppSyntax_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 10)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey;
x_4 = l_Lean_KVMap_findCore(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_7) == 5)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; 
lean_free_object(x_4);
lean_dec(x_7);
x_9 = lean_box(0);
return x_9;
}
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
if (lean_obj_tag(x_10) == 5)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_10);
x_13 = lean_box(0);
return x_13;
}
}
}
}
else
{
lean_object* x_14; 
x_14 = lean_box(0);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRecAppSyntax_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_getRecAppSyntax_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_RecAppSyntax(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__1 = _init_l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__1();
lean_mark_persistent(l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__1);
l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__2 = _init_l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__2();
lean_mark_persistent(l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__2);
l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey = _init_l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey();
lean_mark_persistent(l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

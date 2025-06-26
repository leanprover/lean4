// Lean compiler output
// Module: Init.Data.Option.BasicAux
// Imports: Init.Data.Option.Basic Init.Util
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
static lean_object* l_Option_get_x21___redArg___closed__1;
lean_object* l_panic___redArg(lean_object*, lean_object*);
static lean_object* l_Option_get_x21___redArg___closed__2;
LEAN_EXPORT lean_object* l_Option_get_x21(lean_object*, lean_object*, lean_object*);
static lean_object* l_Option_get_x21___redArg___closed__0;
LEAN_EXPORT lean_object* l_Option_get_x21___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_get_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_get_x21___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Option_get_x21___redArg___closed__3;
static lean_object* _init_l_Option_get_x21___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Option_get_x21___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Option.get!", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Option_get_x21___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value is none", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Option_get_x21___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Option_get_x21___redArg___closed__2;
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(21u);
x_4 = l_Option_get_x21___redArg___closed__1;
x_5 = l_Option_get_x21___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Option_get_x21___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Option_get_x21___redArg___closed__3;
x_4 = l_panic___redArg(x_1, x_3);
return x_4;
}
else
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Option_get_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Option_get_x21___redArg___closed__3;
x_5 = l_panic___redArg(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Option_get_x21___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Option_get_x21___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_get_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Option_get_x21(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* initialize_Init_Data_Option_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Option_BasicAux(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Option_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Option_get_x21___redArg___closed__0 = _init_l_Option_get_x21___redArg___closed__0();
lean_mark_persistent(l_Option_get_x21___redArg___closed__0);
l_Option_get_x21___redArg___closed__1 = _init_l_Option_get_x21___redArg___closed__1();
lean_mark_persistent(l_Option_get_x21___redArg___closed__1);
l_Option_get_x21___redArg___closed__2 = _init_l_Option_get_x21___redArg___closed__2();
lean_mark_persistent(l_Option_get_x21___redArg___closed__2);
l_Option_get_x21___redArg___closed__3 = _init_l_Option_get_x21___redArg___closed__3();
lean_mark_persistent(l_Option_get_x21___redArg___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

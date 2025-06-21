// Lean compiler output
// Module: Lean.Compiler.Options
// Imports: Lean.Util.Trace Lean.Data.Options
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
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5_(lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__2;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__5;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__3;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_compiler_check;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__8;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__6;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__4;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__7;
lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_5____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("check", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__1;
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type check code after each compiler step (this is useful for debugging purses)", 78, 78);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__1;
x_3 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__4;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__6;
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__7;
x_3 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__1;
x_4 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__3;
x_3 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__5;
x_4 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__8;
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_5____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Lean_Util_Trace(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Options(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_Options(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_Trace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Options(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__1 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__1();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__1);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__2 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__2();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__2);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__3 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__3();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__3);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__4 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__4();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__4);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__5 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__5();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__5);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__6 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__6();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__6);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__7 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__7();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__7);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__8 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__8();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5____closed__8);
if (builtin) {res = l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_5_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_compiler_check = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_compiler_check);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

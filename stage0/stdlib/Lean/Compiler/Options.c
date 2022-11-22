// Lean compiler output
// Module: Lean.Compiler.Options
// Imports: Init Lean.Util.Trace Lean.Data.Options
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6_(lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__4;
lean_object* l_Lean_Option_register___at_Std_Format_initFn____x40_Lean_Data_Format___hyg_95____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__1;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__6;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__8;
LEAN_EXPORT lean_object* l_Lean_Compiler_compiler_check;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__7;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__5;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__3;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__2;
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("compiler", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("check", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__1;
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("type check code after each compiler step (this is useful for debugging purses)", 78);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__1;
x_3 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__4;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Compiler", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__6;
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__7;
x_3 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__1;
x_4 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__3;
x_3 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__5;
x_4 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__8;
x_5 = l_Lean_Option_register___at_Std_Format_initFn____x40_Lean_Data_Format___hyg_95____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Trace(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Options(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_Options(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Trace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Options(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__1 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__1();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__1);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__2 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__2();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__2);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__3 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__3();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__3);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__4 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__4();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__4);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__5 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__5();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__5);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__6 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__6();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__6);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__7 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__7();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__7);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__8 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__8();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6____closed__8);
if (builtin) {res = l_Lean_Compiler_initFn____x40_Lean_Compiler_Options___hyg_6_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_compiler_check = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_compiler_check);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

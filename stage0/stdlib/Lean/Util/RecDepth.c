// Lean compiler output
// Module: Lean.Util.RecDepth
// Imports: Lean.Data.Options
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
extern lean_object* l_Lean_defaultMaxRecDepth;
static lean_object* l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__4;
static lean_object* l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__7;
LEAN_EXPORT lean_object* l_Lean_maxRecDepth;
LEAN_EXPORT lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__5;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__3;
LEAN_EXPORT lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__1;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__6;
static lean_object* l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__2;
LEAN_EXPORT lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_5);
lean_inc(x_7);
lean_inc(x_6);
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_inc(x_1);
x_10 = lean_register_option(x_1, x_9, x_4);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_inc(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
lean_inc(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maximum recursion depth for many Lean procedures", 48, 48);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_defaultMaxRecDepth;
x_2 = l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__3;
x_3 = l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__6;
x_2 = l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__5;
x_4 = l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__7;
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Lean_Data_Options(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_RecDepth(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Options(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__1 = _init_l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__1);
l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__2 = _init_l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__2);
l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__3 = _init_l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__3);
l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__4 = _init_l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__4);
l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__5 = _init_l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__5);
l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__6 = _init_l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__6();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__6);
l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__7 = _init_l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__7();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5____closed__7);
if (builtin) {res = l_Lean_initFn____x40_Lean_Util_RecDepth___hyg_5_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_maxRecDepth = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_maxRecDepth);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

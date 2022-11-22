// Lean compiler output
// Module: Lean.Linter.Basic
// Imports: Init Lean.Data.Options
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
static lean_object* l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__4;
LEAN_EXPORT lean_object* l_Lean_Linter_linter_all;
static lean_object* l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__1;
static lean_object* l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__6;
static lean_object* l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__2;
LEAN_EXPORT lean_object* l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6_(lean_object*);
static lean_object* l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__8;
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterAll(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_register___at_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__7;
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
static lean_object* l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__5;
static lean_object* l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__3;
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterAll___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterValue___boxed(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_findCore(lean_object*, lean_object*);
static lean_object* l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__9;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_alloc_ctor(1, 0, 1);
x_9 = lean_unbox(x_5);
lean_ctor_set_uint8(x_8, 0, x_9);
lean_inc(x_7);
lean_inc(x_6);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_6);
lean_ctor_set(x_10, 3, x_7);
lean_inc(x_1);
x_11 = lean_register_option(x_1, x_10, x_4);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_inc(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
static lean_object* _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("linter", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("all", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__1;
x_2 = l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("enable all linters", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__4;
x_3 = l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__5;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Linter", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__7;
x_2 = l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__8;
x_3 = l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__1;
x_4 = l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__3;
x_3 = l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__6;
x_4 = l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__9;
x_5 = l_Lean_Option_register___at_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterAll(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Linter_linter_all;
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Lean_KVMap_findCore(x_1, x_4);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
return x_2;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 1)
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_6, 0);
lean_dec(x_6);
return x_7;
}
else
{
lean_dec(x_6);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterAll___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Linter_getLinterAll(x_1, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterValue(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Linter_getLinterAll(x_2, x_5);
x_7 = l_Lean_KVMap_findCore(x_2, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_7) == 0)
{
return x_6;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec(x_8);
return x_9;
}
else
{
lean_dec(x_8);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterValue___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Linter_getLinterValue(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Options(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Options(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__1 = _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__1();
lean_mark_persistent(l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__1);
l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__2 = _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__2();
lean_mark_persistent(l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__2);
l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__3 = _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__3();
lean_mark_persistent(l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__3);
l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__4 = _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__4();
lean_mark_persistent(l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__4);
l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__5 = _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__5();
lean_mark_persistent(l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__5);
l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__6 = _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__6();
lean_mark_persistent(l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__6);
l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__7 = _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__7();
lean_mark_persistent(l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__7);
l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__8 = _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__8();
lean_mark_persistent(l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__8);
l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__9 = _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__9();
lean_mark_persistent(l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6____closed__9);
if (builtin) {res = l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_6_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_all = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_all);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Lean.Linter.Basic
// Imports: Lean.Data.Options Lean.Log
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
static lean_object* l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__8;
static lean_object* l_Lean_Linter_logLint___rarg___closed__3;
static lean_object* l_Lean_Linter_logLint___rarg___closed__4;
static lean_object* l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__2;
LEAN_EXPORT lean_object* l_Lean_Linter_linter_all;
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
static lean_object* l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__1;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterValue___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5_(lean_object*);
static lean_object* l_Lean_Linter_logLint___rarg___closed__5;
static lean_object* l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__5;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint(lean_object*);
static lean_object* l_Lean_Linter_logLint___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf(lean_object*);
static lean_object* l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__4;
static lean_object* l_Lean_Linter_logLint___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterAll___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterAll(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Linter_logLint___rarg___closed__7;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_logAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
static lean_object* l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__6;
lean_object* l_Lean_KVMap_findCore(lean_object*, lean_object*);
static lean_object* l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__7;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Linter_logLint___rarg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__9;
lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_5____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("linter", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("all", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__1;
x_2 = l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("enable all linters", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__4;
x_3 = l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__5;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Linter", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__7;
x_2 = l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__8;
x_3 = l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__1;
x_4 = l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__3;
x_3 = l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__6;
x_4 = l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__9;
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_5____spec__1(x_2, x_3, x_4, x_1);
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
static lean_object* _init_l_Lean_Linter_logLint___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("note: this linter can be disabled with `set_option ", 51, 51);
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_logLint___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Linter_logLint___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Linter_logLint___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" false`", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_logLint___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Linter_logLint___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Linter_logLint___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Linter_logLint___rarg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_logLint___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Linter_logLint___rarg___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_dec(x_10);
lean_inc(x_9);
x_11 = l_Lean_MessageData_ofName(x_9);
x_12 = l_Lean_Linter_logLint___rarg___closed__2;
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_11);
lean_ctor_set(x_5, 0, x_12);
x_13 = l_Lean_Linter_logLint___rarg___closed__4;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Linter_logLint___rarg___closed__5;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
x_17 = l_Lean_Linter_logLint___rarg___closed__7;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
x_21 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_21, 0, x_9);
lean_ctor_set(x_21, 1, x_20);
x_22 = 1;
x_23 = 0;
x_24 = l_Lean_logAt___rarg(x_1, x_2, x_3, x_4, x_6, x_21, x_22, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; 
x_25 = lean_ctor_get(x_5, 0);
lean_inc(x_25);
lean_dec(x_5);
lean_inc(x_25);
x_26 = l_Lean_MessageData_ofName(x_25);
x_27 = l_Lean_Linter_logLint___rarg___closed__2;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_Linter_logLint___rarg___closed__4;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Linter_logLint___rarg___closed__5;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_7);
x_33 = l_Lean_Linter_logLint___rarg___closed__7;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
x_37 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_37, 0, x_25);
lean_ctor_set(x_37, 1, x_36);
x_38 = 1;
x_39 = 0;
x_40 = l_Lean_logAt___rarg(x_1, x_2, x_3, x_4, x_6, x_37, x_38, x_39);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Linter_logLint___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
lean_inc(x_1);
x_9 = l_Lean_Linter_getLinterValue(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = lean_apply_2(x_11, lean_box(0), x_12);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_Linter_logLint___rarg(x_2, x_3, x_4, x_5, x_1, x_6, x_7);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_4);
x_9 = lean_alloc_closure((void*)(l_Lean_Linter_logLintIf___rarg___lambda__1___boxed), 8, 7);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, x_3);
lean_closure_set(x_9, 4, x_4);
lean_closure_set(x_9, 5, x_6);
lean_closure_set(x_9, 6, x_7);
x_10 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_4, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Linter_logLintIf___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Linter_logLintIf___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
return x_9;
}
}
lean_object* initialize_Lean_Data_Options(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Log(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Options(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__1 = _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__1();
lean_mark_persistent(l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__1);
l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__2 = _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__2();
lean_mark_persistent(l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__2);
l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__3 = _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__3();
lean_mark_persistent(l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__3);
l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__4 = _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__4();
lean_mark_persistent(l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__4);
l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__5 = _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__5();
lean_mark_persistent(l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__5);
l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__6 = _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__6();
lean_mark_persistent(l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__6);
l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__7 = _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__7();
lean_mark_persistent(l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__7);
l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__8 = _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__8();
lean_mark_persistent(l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__8);
l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__9 = _init_l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__9();
lean_mark_persistent(l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5____closed__9);
if (builtin) {res = l_Lean_Linter_initFn____x40_Lean_Linter_Basic___hyg_5_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_all = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_all);
lean_dec_ref(res);
}l_Lean_Linter_logLint___rarg___closed__1 = _init_l_Lean_Linter_logLint___rarg___closed__1();
lean_mark_persistent(l_Lean_Linter_logLint___rarg___closed__1);
l_Lean_Linter_logLint___rarg___closed__2 = _init_l_Lean_Linter_logLint___rarg___closed__2();
lean_mark_persistent(l_Lean_Linter_logLint___rarg___closed__2);
l_Lean_Linter_logLint___rarg___closed__3 = _init_l_Lean_Linter_logLint___rarg___closed__3();
lean_mark_persistent(l_Lean_Linter_logLint___rarg___closed__3);
l_Lean_Linter_logLint___rarg___closed__4 = _init_l_Lean_Linter_logLint___rarg___closed__4();
lean_mark_persistent(l_Lean_Linter_logLint___rarg___closed__4);
l_Lean_Linter_logLint___rarg___closed__5 = _init_l_Lean_Linter_logLint___rarg___closed__5();
lean_mark_persistent(l_Lean_Linter_logLint___rarg___closed__5);
l_Lean_Linter_logLint___rarg___closed__6 = _init_l_Lean_Linter_logLint___rarg___closed__6();
lean_mark_persistent(l_Lean_Linter_logLint___rarg___closed__6);
l_Lean_Linter_logLint___rarg___closed__7 = _init_l_Lean_Linter_logLint___rarg___closed__7();
lean_mark_persistent(l_Lean_Linter_logLint___rarg___closed__7);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Init.Lean.Compiler.IR.CtorLayout
// Imports: Init.Lean.Environment Init.Lean.Compiler.IR.Format
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
lean_object* l_Lean_IR_CtorFieldInfo_format___closed__7;
lean_object* l_Lean_IR_CtorFieldInfo_format___closed__6;
lean_object* l_Lean_fmt___at_Lean_IR_CtorFieldInfo_format___spec__1(lean_object*);
lean_object* l_Lean_IR_CtorFieldInfo_format___closed__5;
lean_object* l_Lean_fmt___at_Lean_Level_LevelToFormat_Result_format___main___spec__1(lean_object*);
lean_object* l_Lean_IR_CtorFieldInfo_Lean_HasFormat___closed__1;
lean_object* l_Lean_IR_CtorFieldInfo_format(lean_object*);
lean_object* l_Lean_IR_CtorFieldInfo_format___closed__3;
lean_object* l_Lean_IR_CtorFieldInfo_format___closed__1;
lean_object* l_Lean_IR_CtorFieldInfo_format___closed__8;
lean_object* l_Lean_IR_CtorFieldInfo_format___closed__9;
lean_object* l_Lean_fmt___at_Lean_IR_CtorFieldInfo_format___spec__1___boxed(lean_object*);
lean_object* l_Lean_IR_CtorFieldInfo_format___closed__4;
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__2;
lean_object* l_Lean_IR_CtorFieldInfo_format___closed__2;
lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main(lean_object*);
lean_object* l_Lean_IR_getCtorLayout___boxed(lean_object*, lean_object*);
lean_object* lean_ir_get_ctor_layout(lean_object*, lean_object*);
lean_object* l_Lean_IR_CtorFieldInfo_Lean_HasFormat;
extern lean_object* l___private_Init_Lean_Compiler_IR_Format_1__formatArg___closed__2;
lean_object* l_Lean_fmt___at_Lean_IR_CtorFieldInfo_format___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("obj@");
return x_1;
}
}
lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_CtorFieldInfo_format___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("usize@");
return x_1;
}
}
lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_CtorFieldInfo_format___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("scalar#");
return x_1;
}
}
lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_CtorFieldInfo_format___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("@");
return x_1;
}
}
lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_CtorFieldInfo_format___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Util_1__mkPanicMessage___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_IR_CtorFieldInfo_format(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Compiler_IR_Format_1__formatArg___closed__2;
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_fmt___at_Lean_Level_LevelToFormat_Result_format___main___spec__1(x_3);
x_5 = 0;
x_6 = l_Lean_IR_CtorFieldInfo_format___closed__2;
x_7 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set_uint8(x_7, sizeof(void*)*2, x_5);
return x_7;
}
case 2:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_fmt___at_Lean_Level_LevelToFormat_Result_format___main___spec__1(x_8);
x_10 = 0;
x_11 = l_Lean_IR_CtorFieldInfo_format___closed__4;
x_12 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_10);
return x_12;
}
default: 
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l_Lean_fmt___at_Lean_Level_LevelToFormat_Result_format___main___spec__1(x_13);
x_17 = 0;
x_18 = l_Lean_IR_CtorFieldInfo_format___closed__6;
x_19 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_17);
x_20 = l_Lean_IR_CtorFieldInfo_format___closed__8;
x_21 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*2, x_17);
x_22 = l_Lean_fmt___at_Lean_Level_LevelToFormat_Result_format___main___spec__1(x_14);
x_23 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_17);
x_24 = l_Lean_IR_CtorFieldInfo_format___closed__9;
x_25 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_17);
x_26 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main(x_15);
lean_dec(x_15);
x_27 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_17);
return x_27;
}
}
}
}
lean_object* l_Lean_fmt___at_Lean_IR_CtorFieldInfo_format___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_fmt___at_Lean_IR_CtorFieldInfo_format___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_CtorFieldInfo_Lean_HasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_CtorFieldInfo_format), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_CtorFieldInfo_Lean_HasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_CtorFieldInfo_Lean_HasFormat___closed__1;
return x_1;
}
}
lean_object* l_Lean_IR_getCtorLayout___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ir_get_ctor_layout(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init_Lean_Environment(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_Format(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Compiler_IR_CtorLayout(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_Format(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_CtorFieldInfo_format___closed__1 = _init_l_Lean_IR_CtorFieldInfo_format___closed__1();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__1);
l_Lean_IR_CtorFieldInfo_format___closed__2 = _init_l_Lean_IR_CtorFieldInfo_format___closed__2();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__2);
l_Lean_IR_CtorFieldInfo_format___closed__3 = _init_l_Lean_IR_CtorFieldInfo_format___closed__3();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__3);
l_Lean_IR_CtorFieldInfo_format___closed__4 = _init_l_Lean_IR_CtorFieldInfo_format___closed__4();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__4);
l_Lean_IR_CtorFieldInfo_format___closed__5 = _init_l_Lean_IR_CtorFieldInfo_format___closed__5();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__5);
l_Lean_IR_CtorFieldInfo_format___closed__6 = _init_l_Lean_IR_CtorFieldInfo_format___closed__6();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__6);
l_Lean_IR_CtorFieldInfo_format___closed__7 = _init_l_Lean_IR_CtorFieldInfo_format___closed__7();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__7);
l_Lean_IR_CtorFieldInfo_format___closed__8 = _init_l_Lean_IR_CtorFieldInfo_format___closed__8();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__8);
l_Lean_IR_CtorFieldInfo_format___closed__9 = _init_l_Lean_IR_CtorFieldInfo_format___closed__9();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__9);
l_Lean_IR_CtorFieldInfo_Lean_HasFormat___closed__1 = _init_l_Lean_IR_CtorFieldInfo_Lean_HasFormat___closed__1();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_Lean_HasFormat___closed__1);
l_Lean_IR_CtorFieldInfo_Lean_HasFormat = _init_l_Lean_IR_CtorFieldInfo_Lean_HasFormat();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_Lean_HasFormat);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

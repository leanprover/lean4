// Lean compiler output
// Module: Lean.Compiler.IR.CtorLayout
// Imports: Init Lean.Environment Lean.Compiler.IR.Format
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
lean_object* l_Lean_IR_CtorFieldInfo_format___closed__7;
lean_object* l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(lean_object*);
extern lean_object* l_Std_Format_join___closed__1;
lean_object* l_Lean_IR_CtorFieldInfo_format_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_CtorFieldInfo_format___closed__6;
lean_object* l_Std_fmt___at_Lean_IR_CtorFieldInfo_format___spec__1(lean_object*);
extern lean_object* l___private_Lean_Syntax_0__Lean_Syntax_formatInfo___closed__1;
lean_object* l_Lean_IR_CtorFieldInfo_format___closed__5;
extern lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__2;
lean_object* l_Lean_IR_CtorFieldInfo_format(lean_object*);
lean_object* l_Lean_IR_CtorFieldInfo_format___closed__3;
lean_object* l_Lean_IR_CtorFieldInfo_format___closed__1;
lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(lean_object*);
lean_object* l_Lean_IR_CtorFieldInfo_format___closed__4;
lean_object* l_Lean_IR_CtorFieldInfo_instToFormatCtorFieldInfo___closed__1;
lean_object* l_Lean_IR_CtorFieldInfo_format___closed__2;
lean_object* l_Lean_IR_getCtorLayout___boxed(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_NotationExtra___hyg_3476____closed__44;
lean_object* lean_ir_get_ctor_layout(lean_object*, lean_object*);
lean_object* l_Lean_IR_CtorFieldInfo_instToFormatCtorFieldInfo;
lean_object* l_Lean_IR_CtorFieldInfo_format_match__1(lean_object*);
lean_object* l_Lean_IR_CtorFieldInfo_format_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_1(x_4, x_10);
return x_11;
}
default: 
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_apply_3(x_5, x_12, x_13, x_14);
return x_15;
}
}
}
}
lean_object* l_Lean_IR_CtorFieldInfo_format_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_CtorFieldInfo_format_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Std_fmt___at_Lean_IR_CtorFieldInfo_format___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("obj@");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_CtorFieldInfo_format___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("usize@");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_CtorFieldInfo_format___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("scalar#");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_CtorFieldInfo_format___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_myMacro____x40_Init_NotationExtra___hyg_3476____closed__44;
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
x_2 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__2;
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_3);
x_5 = l_Lean_IR_CtorFieldInfo_format___closed__2;
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = l_Std_Format_join___closed__1;
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
case 2:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_9);
x_11 = l_Lean_IR_CtorFieldInfo_format___closed__4;
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Std_Format_join___closed__1;
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
default: 
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_15);
x_19 = l_Lean_IR_CtorFieldInfo_format___closed__6;
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_IR_CtorFieldInfo_format___closed__7;
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_16);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l___private_Lean_Syntax_0__Lean_Syntax_formatInfo___closed__1;
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_17);
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Std_Format_join___closed__1;
x_30 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_instToFormatCtorFieldInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_CtorFieldInfo_format), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_instToFormatCtorFieldInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_CtorFieldInfo_instToFormatCtorFieldInfo___closed__1;
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
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Environment(lean_object*);
lean_object* initialize_Lean_Compiler_IR_Format(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Compiler_IR_CtorLayout(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Format(lean_io_mk_world());
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
l_Lean_IR_CtorFieldInfo_instToFormatCtorFieldInfo___closed__1 = _init_l_Lean_IR_CtorFieldInfo_instToFormatCtorFieldInfo___closed__1();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_instToFormatCtorFieldInfo___closed__1);
l_Lean_IR_CtorFieldInfo_instToFormatCtorFieldInfo = _init_l_Lean_IR_CtorFieldInfo_instToFormatCtorFieldInfo();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_instToFormatCtorFieldInfo);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

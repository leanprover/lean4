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
lean_object* l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(lean_object*);
extern lean_object* l___private_Lean_Compiler_IR_Format_1__formatArg___closed__2;
lean_object* l_Lean_IR_CtorFieldInfo_format___closed__6;
lean_object* l_Lean_fmt___at_Lean_IR_CtorFieldInfo_format___spec__1(lean_object*);
extern lean_object* l___private_Lean_Syntax_6__formatInfo___closed__1;
lean_object* l_Lean_IR_CtorFieldInfo_format___closed__5;
lean_object* l_Lean_IR_CtorFieldInfo_Lean_HasFormat___closed__1;
lean_object* l_Lean_IR_CtorFieldInfo_format(lean_object*);
lean_object* l_Lean_IR_CtorFieldInfo_format___closed__3;
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___main(lean_object*);
lean_object* l_Lean_IR_CtorFieldInfo_format___closed__1;
lean_object* l_Lean_IR_CtorFieldInfo_format___closed__8;
lean_object* l_Lean_fmt___at_Lean_IR_CtorFieldInfo_format___spec__1___boxed(lean_object*);
lean_object* l_Lean_IR_CtorFieldInfo_format___closed__4;
lean_object* l_Lean_IR_CtorFieldInfo_format___closed__2;
lean_object* l_Lean_IR_getCtorLayout___boxed(lean_object*, lean_object*);
lean_object* lean_ir_get_ctor_layout(lean_object*, lean_object*);
lean_object* l_Lean_IR_CtorFieldInfo_Lean_HasFormat;
lean_object* l_Lean_fmt___at_Lean_IR_CtorFieldInfo_format___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main(x_1);
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
lean_object* x_1; 
x_1 = lean_mk_string("@");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_CtorFieldInfo_format___closed__7;
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
x_2 = l___private_Lean_Compiler_IR_Format_1__formatArg___closed__2;
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_3);
x_5 = l_Lean_IR_CtorFieldInfo_format___closed__2;
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
case 2:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_7);
x_9 = l_Lean_IR_CtorFieldInfo_format___closed__4;
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
default: 
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_11);
x_15 = l_Lean_IR_CtorFieldInfo_format___closed__6;
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_IR_CtorFieldInfo_format___closed__8;
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_12);
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l___private_Lean_Syntax_6__formatInfo___closed__1;
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main(x_13);
lean_dec(x_13);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
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
static lean_object* _init_l_Lean_IR_CtorFieldInfo_Lean_HasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_CtorFieldInfo_format), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_Lean_HasFormat() {
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
l_Lean_IR_CtorFieldInfo_format___closed__8 = _init_l_Lean_IR_CtorFieldInfo_format___closed__8();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__8);
l_Lean_IR_CtorFieldInfo_Lean_HasFormat___closed__1 = _init_l_Lean_IR_CtorFieldInfo_Lean_HasFormat___closed__1();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_Lean_HasFormat___closed__1);
l_Lean_IR_CtorFieldInfo_Lean_HasFormat = _init_l_Lean_IR_CtorFieldInfo_Lean_HasFormat();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_Lean_HasFormat);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

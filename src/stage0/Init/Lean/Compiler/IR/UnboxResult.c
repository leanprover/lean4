// Lean compiler output
// Module: Init.Lean.Compiler.IR.UnboxResult
// Imports: Init.Lean.Format Init.Lean.Compiler.IR.Basic Init.Lean.Compiler.IR.CtorLayout
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
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr___closed__3;
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__3;
extern lean_object* l_Lean_TagAttribute_Inhabited___closed__3;
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr___closed__1;
uint8_t l_Lean_IR_UnboxResult_hasUnboxAttr(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__1;
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__5;
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__7;
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__6;
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr___closed__2;
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__4;
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__2;
lean_object* l_Lean_IR_UnboxResult_unboxAttr;
lean_object* l_Lean_IR_UnboxResult_hasUnboxAttr___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr___closed__4;
lean_object* _init_l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown declaration");
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("constant must be an inductive type");
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("recursive inductive datatypes are not supported");
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_environment_find(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__2;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*5);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__5;
return x_8;
}
else
{
lean_object* x_9; 
x_9 = l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__7;
return x_9;
}
}
else
{
lean_object* x_10; 
lean_dec(x_5);
x_10 = l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__4;
return x_10;
}
}
}
}
lean_object* _init_l_Lean_IR_UnboxResult_mkUnboxAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unbox");
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnboxResult_mkUnboxAttr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_UnboxResult_mkUnboxAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_UnboxResult_mkUnboxAttr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("compiler tries to unbox result values if their types are tagged with `[unbox]`");
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnboxResult_mkUnboxAttr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1), 2, 0);
return x_1;
}
}
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_IR_UnboxResult_mkUnboxAttr___closed__2;
x_3 = l_Lean_IR_UnboxResult_mkUnboxAttr___closed__3;
x_4 = l_Lean_IR_UnboxResult_mkUnboxAttr___closed__4;
x_5 = l_Lean_registerTagAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
uint8_t l_Lean_IR_UnboxResult_hasUnboxAttr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_IR_UnboxResult_unboxAttr;
x_4 = l_Lean_TagAttribute_hasTag(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_Lean_IR_UnboxResult_hasUnboxAttr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_UnboxResult_hasUnboxAttr(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Init_Lean_Format(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_Basic(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_CtorLayout(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Compiler_IR_UnboxResult(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Format(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Compiler_IR_Basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Compiler_IR_CtorLayout(w);
if (lean_io_result_is_error(w)) return w;
l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__1 = _init_l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__1();
lean_mark_persistent(l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__1);
l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__2 = _init_l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__2();
lean_mark_persistent(l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__2);
l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__3 = _init_l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__3();
lean_mark_persistent(l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__3);
l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__4 = _init_l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__4();
lean_mark_persistent(l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__4);
l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__5 = _init_l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__5();
lean_mark_persistent(l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__5);
l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__6 = _init_l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__6();
lean_mark_persistent(l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__6);
l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__7 = _init_l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__7();
lean_mark_persistent(l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__7);
l_Lean_IR_UnboxResult_mkUnboxAttr___closed__1 = _init_l_Lean_IR_UnboxResult_mkUnboxAttr___closed__1();
lean_mark_persistent(l_Lean_IR_UnboxResult_mkUnboxAttr___closed__1);
l_Lean_IR_UnboxResult_mkUnboxAttr___closed__2 = _init_l_Lean_IR_UnboxResult_mkUnboxAttr___closed__2();
lean_mark_persistent(l_Lean_IR_UnboxResult_mkUnboxAttr___closed__2);
l_Lean_IR_UnboxResult_mkUnboxAttr___closed__3 = _init_l_Lean_IR_UnboxResult_mkUnboxAttr___closed__3();
lean_mark_persistent(l_Lean_IR_UnboxResult_mkUnboxAttr___closed__3);
l_Lean_IR_UnboxResult_mkUnboxAttr___closed__4 = _init_l_Lean_IR_UnboxResult_mkUnboxAttr___closed__4();
lean_mark_persistent(l_Lean_IR_UnboxResult_mkUnboxAttr___closed__4);
w = l_Lean_IR_UnboxResult_mkUnboxAttr(w);
if (lean_io_result_is_error(w)) return w;
l_Lean_IR_UnboxResult_unboxAttr = lean_io_result_get_value(w);
lean_mark_persistent(l_Lean_IR_UnboxResult_unboxAttr);
return w;
}
#ifdef __cplusplus
}
#endif

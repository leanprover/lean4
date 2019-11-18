// Lean compiler output
// Module: Init.Lean.EqnCompiler.MatchPattern
// Imports: Init.Lean.Attributes
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
uint8_t lean_has_match_pattern_attribute(lean_object*, lean_object*);
lean_object* l_Lean_EqnCompiler_matchPatternAttr;
lean_object* l_Lean_EqnCompiler_mkMatchPatternAttr___closed__3;
extern lean_object* l_Lean_TagAttribute_Inhabited___closed__3;
lean_object* l_Lean_EqnCompiler_mkMatchPatternAttr(lean_object*);
lean_object* l_Lean_EqnCompiler_mkMatchPatternAttr___lambda__1___closed__1;
lean_object* l_Lean_EqnCompiler_mkMatchPatternAttr___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_EqnCompiler_hasMatchPatternAttribute___boxed(lean_object*, lean_object*);
lean_object* l_Lean_EqnCompiler_mkMatchPatternAttr___closed__4;
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EqnCompiler_mkMatchPatternAttr___closed__1;
lean_object* l_Lean_EqnCompiler_mkMatchPatternAttr___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_EqnCompiler_mkMatchPatternAttr___closed__2;
lean_object* _init_l_Lean_EqnCompiler_mkMatchPatternAttr___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_EqnCompiler_mkMatchPatternAttr___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EqnCompiler_mkMatchPatternAttr___lambda__1___closed__1;
return x_3;
}
}
lean_object* _init_l_Lean_EqnCompiler_mkMatchPatternAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matchPattern");
return x_1;
}
}
lean_object* _init_l_Lean_EqnCompiler_mkMatchPatternAttr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_EqnCompiler_mkMatchPatternAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_EqnCompiler_mkMatchPatternAttr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mark that a definition can be used in a pattern (remark: the dependent pattern matching compiler will unfold the definition)");
return x_1;
}
}
lean_object* _init_l_Lean_EqnCompiler_mkMatchPatternAttr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EqnCompiler_mkMatchPatternAttr___lambda__1___boxed), 2, 0);
return x_1;
}
}
lean_object* l_Lean_EqnCompiler_mkMatchPatternAttr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_EqnCompiler_mkMatchPatternAttr___closed__2;
x_3 = l_Lean_EqnCompiler_mkMatchPatternAttr___closed__3;
x_4 = l_Lean_EqnCompiler_mkMatchPatternAttr___closed__4;
x_5 = l_Lean_registerTagAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_EqnCompiler_mkMatchPatternAttr___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EqnCompiler_mkMatchPatternAttr___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
uint8_t lean_has_match_pattern_attribute(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_EqnCompiler_matchPatternAttr;
x_4 = l_Lean_TagAttribute_hasTag(x_3, x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_EqnCompiler_hasMatchPatternAttribute___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_has_match_pattern_attribute(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Init_Lean_Attributes(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_EqnCompiler_MatchPattern(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Attributes(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_EqnCompiler_mkMatchPatternAttr___lambda__1___closed__1 = _init_l_Lean_EqnCompiler_mkMatchPatternAttr___lambda__1___closed__1();
lean_mark_persistent(l_Lean_EqnCompiler_mkMatchPatternAttr___lambda__1___closed__1);
l_Lean_EqnCompiler_mkMatchPatternAttr___closed__1 = _init_l_Lean_EqnCompiler_mkMatchPatternAttr___closed__1();
lean_mark_persistent(l_Lean_EqnCompiler_mkMatchPatternAttr___closed__1);
l_Lean_EqnCompiler_mkMatchPatternAttr___closed__2 = _init_l_Lean_EqnCompiler_mkMatchPatternAttr___closed__2();
lean_mark_persistent(l_Lean_EqnCompiler_mkMatchPatternAttr___closed__2);
l_Lean_EqnCompiler_mkMatchPatternAttr___closed__3 = _init_l_Lean_EqnCompiler_mkMatchPatternAttr___closed__3();
lean_mark_persistent(l_Lean_EqnCompiler_mkMatchPatternAttr___closed__3);
l_Lean_EqnCompiler_mkMatchPatternAttr___closed__4 = _init_l_Lean_EqnCompiler_mkMatchPatternAttr___closed__4();
lean_mark_persistent(l_Lean_EqnCompiler_mkMatchPatternAttr___closed__4);
res = l_Lean_EqnCompiler_mkMatchPatternAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_EqnCompiler_matchPatternAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_EqnCompiler_matchPatternAttr);
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

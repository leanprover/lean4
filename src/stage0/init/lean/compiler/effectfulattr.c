// Lean compiler output
// Module: init.lean.compiler.effectfulattr
// Imports: init.lean.environment init.lean.attributes
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
extern lean_object* l_Lean_TagAttribute_Inhabited___closed__3;
lean_object* l_Lean_mkEffectfulAttr___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_effectfulAttr;
lean_object* l_Lean_mkEffectfulAttr___closed__1;
lean_object* l_Lean_mkEffectfulAttr___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkEffectfulAttr(lean_object*);
lean_object* l_Lean_mkEffectfulAttr___closed__4;
lean_object* l_Lean_mkEffectfulAttr___closed__3;
lean_object* l_Lean_mkEffectfulAttr___closed__2;
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_hasEffectfulAttribute___boxed(lean_object*, lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
uint8_t lean_has_effectful_attribute(lean_object*, lean_object*);
lean_object* l_Lean_mkEffectfulAttr___lambda__1___closed__1;
lean_object* _init_l_Lean_mkEffectfulAttr___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_mkEffectfulAttr___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkEffectfulAttr___lambda__1___closed__1;
return x_3;
}
}
lean_object* _init_l_Lean_mkEffectfulAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("effectful");
return x_1;
}
}
lean_object* _init_l_Lean_mkEffectfulAttr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkEffectfulAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_mkEffectfulAttr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mark that a declaration has implicit effects, and the compiler should avoid optimizations such as common subexpression elimination and closed term extraction");
return x_1;
}
}
lean_object* _init_l_Lean_mkEffectfulAttr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_mkEffectfulAttr___lambda__1___boxed), 2, 0);
return x_1;
}
}
lean_object* l_Lean_mkEffectfulAttr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_mkEffectfulAttr___closed__2;
x_3 = l_Lean_mkEffectfulAttr___closed__3;
x_4 = l_Lean_mkEffectfulAttr___closed__4;
x_5 = l_Lean_registerTagAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_mkEffectfulAttr___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkEffectfulAttr___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
uint8_t lean_has_effectful_attribute(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_effectfulAttr;
x_4 = l_Lean_TagAttribute_hasTag(x_3, x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_hasEffectfulAttribute___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_has_effectful_attribute(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_init_lean_environment(lean_object*);
lean_object* initialize_init_lean_attributes(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_init_lean_compiler_effectfulattr(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_environment(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_attributes(w);
if (lean_io_result_is_error(w)) return w;
l_Lean_mkEffectfulAttr___lambda__1___closed__1 = _init_l_Lean_mkEffectfulAttr___lambda__1___closed__1();
lean_mark_persistent(l_Lean_mkEffectfulAttr___lambda__1___closed__1);
l_Lean_mkEffectfulAttr___closed__1 = _init_l_Lean_mkEffectfulAttr___closed__1();
lean_mark_persistent(l_Lean_mkEffectfulAttr___closed__1);
l_Lean_mkEffectfulAttr___closed__2 = _init_l_Lean_mkEffectfulAttr___closed__2();
lean_mark_persistent(l_Lean_mkEffectfulAttr___closed__2);
l_Lean_mkEffectfulAttr___closed__3 = _init_l_Lean_mkEffectfulAttr___closed__3();
lean_mark_persistent(l_Lean_mkEffectfulAttr___closed__3);
l_Lean_mkEffectfulAttr___closed__4 = _init_l_Lean_mkEffectfulAttr___closed__4();
lean_mark_persistent(l_Lean_mkEffectfulAttr___closed__4);
w = l_Lean_mkEffectfulAttr(w);
if (lean_io_result_is_error(w)) return w;
l_Lean_effectfulAttr = lean_io_result_get_value(w);
lean_mark_persistent(l_Lean_effectfulAttr);
return w;
}
#ifdef __cplusplus
}
#endif

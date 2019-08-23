// Lean compiler output
// Module: init.lean.eqncompiler.matchpattern
// Imports: init.lean.attributes
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
extern "C" {
uint8 lean_has_match_pattern_attribute(obj*, obj*);
obj* l_Lean_EqnCompiler_matchPatternAttr;
obj* l_Lean_EqnCompiler_mkMatchPatternAttr___closed__3;
extern obj* l_Lean_TagAttribute_Inhabited___closed__3;
obj* l_Lean_EqnCompiler_mkMatchPatternAttr(obj*);
obj* l_Lean_EqnCompiler_mkMatchPatternAttr___lambda__1___closed__1;
obj* l_Lean_EqnCompiler_mkMatchPatternAttr___lambda__1___boxed(obj*, obj*);
obj* l_Lean_registerTagAttribute(obj*, obj*, obj*, obj*);
obj* l_Lean_EqnCompiler_hasMatchPatternAttribute___boxed(obj*, obj*);
obj* l_Lean_EqnCompiler_mkMatchPatternAttr___closed__4;
obj* lean_name_mk_string(obj*, obj*);
uint8 l_Lean_TagAttribute_hasTag(obj*, obj*, obj*);
obj* l_Lean_EqnCompiler_mkMatchPatternAttr___closed__1;
obj* l_Lean_EqnCompiler_mkMatchPatternAttr___lambda__1(obj*, obj*);
obj* l_Lean_EqnCompiler_mkMatchPatternAttr___closed__2;
obj* _init_l_Lean_EqnCompiler_mkMatchPatternAttr___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_EqnCompiler_mkMatchPatternAttr___lambda__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_EqnCompiler_mkMatchPatternAttr___lambda__1___closed__1;
return x_3;
}
}
obj* _init_l_Lean_EqnCompiler_mkMatchPatternAttr___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("matchPattern");
return x_1;
}
}
obj* _init_l_Lean_EqnCompiler_mkMatchPatternAttr___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_EqnCompiler_mkMatchPatternAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_EqnCompiler_mkMatchPatternAttr___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("mark that a definition can be used in a pattern (remark: the dependent pattern matching compiler will unfold the definition)");
return x_1;
}
}
obj* _init_l_Lean_EqnCompiler_mkMatchPatternAttr___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_EqnCompiler_mkMatchPatternAttr___lambda__1___boxed), 2, 0);
return x_1;
}
}
obj* l_Lean_EqnCompiler_mkMatchPatternAttr(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_EqnCompiler_mkMatchPatternAttr___closed__2;
x_3 = l_Lean_EqnCompiler_mkMatchPatternAttr___closed__3;
x_4 = l_Lean_EqnCompiler_mkMatchPatternAttr___closed__4;
x_5 = l_Lean_registerTagAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l_Lean_EqnCompiler_mkMatchPatternAttr___lambda__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_EqnCompiler_mkMatchPatternAttr___lambda__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
uint8 lean_has_match_pattern_attribute(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = l_Lean_EqnCompiler_matchPatternAttr;
x_4 = l_Lean_TagAttribute_hasTag(x_3, x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_EqnCompiler_hasMatchPatternAttribute___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean_has_match_pattern_attribute(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* initialize_init_lean_attributes(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_eqncompiler_matchpattern(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_attributes(w);
if (lean::io_result_is_error(w)) return w;
l_Lean_EqnCompiler_mkMatchPatternAttr___lambda__1___closed__1 = _init_l_Lean_EqnCompiler_mkMatchPatternAttr___lambda__1___closed__1();
lean::mark_persistent(l_Lean_EqnCompiler_mkMatchPatternAttr___lambda__1___closed__1);
l_Lean_EqnCompiler_mkMatchPatternAttr___closed__1 = _init_l_Lean_EqnCompiler_mkMatchPatternAttr___closed__1();
lean::mark_persistent(l_Lean_EqnCompiler_mkMatchPatternAttr___closed__1);
l_Lean_EqnCompiler_mkMatchPatternAttr___closed__2 = _init_l_Lean_EqnCompiler_mkMatchPatternAttr___closed__2();
lean::mark_persistent(l_Lean_EqnCompiler_mkMatchPatternAttr___closed__2);
l_Lean_EqnCompiler_mkMatchPatternAttr___closed__3 = _init_l_Lean_EqnCompiler_mkMatchPatternAttr___closed__3();
lean::mark_persistent(l_Lean_EqnCompiler_mkMatchPatternAttr___closed__3);
l_Lean_EqnCompiler_mkMatchPatternAttr___closed__4 = _init_l_Lean_EqnCompiler_mkMatchPatternAttr___closed__4();
lean::mark_persistent(l_Lean_EqnCompiler_mkMatchPatternAttr___closed__4);
w = l_Lean_EqnCompiler_mkMatchPatternAttr(w);
if (lean::io_result_is_error(w)) return w;
l_Lean_EqnCompiler_matchPatternAttr = lean::io_result_get_value(w);
lean::mark_persistent(l_Lean_EqnCompiler_matchPatternAttr);
return w;
}
}

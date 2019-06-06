// Lean compiler output
// Module: init.lean.compiler.attributes
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
obj* l_Lean_mkMacroInlineAttribute___closed__1;
obj* l_Lean_mkInlineIfReduceAttribute___closed__2;
obj* l_Lean_AttributeImpl_inhabited___lambda__4___boxed(obj*, obj*, obj*);
obj* l_Lean_mkNoInlineAttribute___closed__1;
obj* l_Lean_mkInlineAttribute___closed__3;
obj* l_Lean_AttributeImpl_inhabited___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__1___boxed(obj*);
obj* l_Lean_macroInlineAttribute;
obj* l_Lean_inlineIfReduceAttribute;
obj* l_Lean_mkMacroInlineAttribute___closed__2;
obj* l_Lean_mkNoInlineAttribute___closed__2;
obj* l_Lean_mkInlineIfReduceAttribute(obj*);
obj* l_Array_mkEmpty(obj*, obj*);
obj* l_Lean_registerTagAttribute(obj*, obj*, obj*, obj*);
obj* l_Lean_mkInlineIfReduceAttribute___closed__1;
obj* l_Lean_AttributeImpl_inhabited___lambda__5(obj*, obj*);
obj* l_Lean_AttributeImpl_inhabited___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_ExceptT_Monad___rarg___lambda__8___boxed(obj*, obj*);
obj* l_Lean_mkInlineAttribute___closed__2;
obj* l_Lean_mkMacroInlineAttribute(obj*);
obj* l_Lean_inlineAttribute;
obj* l___private_init_lean_compiler_attributes_1__checkIsDefinition___closed__3;
namespace lean {
obj* environment_find_core(obj*, obj*);
}
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__2___boxed(obj*);
obj* l_Lean_noInlineAttribute;
obj* l_Lean_mkInlineAttribute(obj*);
obj* l_Lean_mkNoInlineAttribute(obj*);
obj* l_Lean_AttributeImpl_inhabited___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_mkInlineAttribute___closed__1;
obj* l___private_init_lean_compiler_attributes_1__checkIsDefinition(obj*, obj*);
obj* l___private_init_lean_compiler_attributes_1__checkIsDefinition___closed__2;
obj* l___private_init_lean_compiler_attributes_1__checkIsDefinition___closed__1;
obj* _init_l___private_init_lean_compiler_attributes_1__checkIsDefinition___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("unknow declaration");
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_attributes_1__checkIsDefinition___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("declaration is not a definition");
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_attributes_1__checkIsDefinition___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_attributes_1__checkIsDefinition(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::environment_find_core(x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_attributes_1__checkIsDefinition___closed__1;
return x_4;
}
else
{
obj* x_5; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
lean::dec(x_3);
if (lean::obj_tag(x_5) == 1)
{
obj* x_6; 
lean::dec(x_5);
x_6 = l___private_init_lean_compiler_attributes_1__checkIsDefinition___closed__3;
return x_6;
}
else
{
obj* x_7; 
lean::dec(x_5);
x_7 = l___private_init_lean_compiler_attributes_1__checkIsDefinition___closed__2;
return x_7;
}
}
}
}
obj* _init_l_Lean_mkInlineAttribute___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("inline");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_mkInlineAttribute___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("mark definition to always be inlined");
return x_1;
}
}
obj* _init_l_Lean_mkInlineAttribute___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_attributes_1__checkIsDefinition), 2, 0);
return x_1;
}
}
obj* l_Lean_mkInlineAttribute(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_mkInlineAttribute___closed__1;
x_3 = l_Lean_mkInlineAttribute___closed__2;
x_4 = l_Lean_mkInlineAttribute___closed__3;
x_5 = l_Lean_registerTagAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_mkInlineIfReduceAttribute___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("inlineIfReduce");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_mkInlineIfReduceAttribute___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("mark definition to be inlined when resultant term after reduction is not a `cases_on` application.");
return x_1;
}
}
obj* l_Lean_mkInlineIfReduceAttribute(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_mkInlineIfReduceAttribute___closed__1;
x_3 = l_Lean_mkInlineIfReduceAttribute___closed__2;
x_4 = l_Lean_mkInlineAttribute___closed__3;
x_5 = l_Lean_registerTagAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_mkNoInlineAttribute___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("noinline");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_mkNoInlineAttribute___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("mark definition to never be inlined");
return x_1;
}
}
obj* l_Lean_mkNoInlineAttribute(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_mkNoInlineAttribute___closed__1;
x_3 = l_Lean_mkNoInlineAttribute___closed__2;
x_4 = l_Lean_mkInlineAttribute___closed__3;
x_5 = l_Lean_registerTagAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_mkMacroInlineAttribute___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("macroInline");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_mkMacroInlineAttribute___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("mark definition to always be inlined before ANF conversion");
return x_1;
}
}
obj* l_Lean_mkMacroInlineAttribute(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_mkMacroInlineAttribute___closed__1;
x_3 = l_Lean_mkMacroInlineAttribute___closed__2;
x_4 = l_Lean_mkInlineAttribute___closed__3;
x_5 = l_Lean_registerTagAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* initialize_init_lean_attributes(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_attributes(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_attributes(w);
if (io_result_is_error(w)) return w;
l___private_init_lean_compiler_attributes_1__checkIsDefinition___closed__1 = _init_l___private_init_lean_compiler_attributes_1__checkIsDefinition___closed__1();
lean::mark_persistent(l___private_init_lean_compiler_attributes_1__checkIsDefinition___closed__1);
l___private_init_lean_compiler_attributes_1__checkIsDefinition___closed__2 = _init_l___private_init_lean_compiler_attributes_1__checkIsDefinition___closed__2();
lean::mark_persistent(l___private_init_lean_compiler_attributes_1__checkIsDefinition___closed__2);
l___private_init_lean_compiler_attributes_1__checkIsDefinition___closed__3 = _init_l___private_init_lean_compiler_attributes_1__checkIsDefinition___closed__3();
lean::mark_persistent(l___private_init_lean_compiler_attributes_1__checkIsDefinition___closed__3);
l_Lean_mkInlineAttribute___closed__1 = _init_l_Lean_mkInlineAttribute___closed__1();
lean::mark_persistent(l_Lean_mkInlineAttribute___closed__1);
l_Lean_mkInlineAttribute___closed__2 = _init_l_Lean_mkInlineAttribute___closed__2();
lean::mark_persistent(l_Lean_mkInlineAttribute___closed__2);
l_Lean_mkInlineAttribute___closed__3 = _init_l_Lean_mkInlineAttribute___closed__3();
lean::mark_persistent(l_Lean_mkInlineAttribute___closed__3);
w = l_Lean_mkInlineAttribute(w);
if (io_result_is_error(w)) return w;
l_Lean_inlineAttribute = io_result_get_value(w);
lean::mark_persistent(l_Lean_inlineAttribute);
l_Lean_mkInlineIfReduceAttribute___closed__1 = _init_l_Lean_mkInlineIfReduceAttribute___closed__1();
lean::mark_persistent(l_Lean_mkInlineIfReduceAttribute___closed__1);
l_Lean_mkInlineIfReduceAttribute___closed__2 = _init_l_Lean_mkInlineIfReduceAttribute___closed__2();
lean::mark_persistent(l_Lean_mkInlineIfReduceAttribute___closed__2);
w = l_Lean_mkInlineIfReduceAttribute(w);
if (io_result_is_error(w)) return w;
l_Lean_inlineIfReduceAttribute = io_result_get_value(w);
lean::mark_persistent(l_Lean_inlineIfReduceAttribute);
l_Lean_mkNoInlineAttribute___closed__1 = _init_l_Lean_mkNoInlineAttribute___closed__1();
lean::mark_persistent(l_Lean_mkNoInlineAttribute___closed__1);
l_Lean_mkNoInlineAttribute___closed__2 = _init_l_Lean_mkNoInlineAttribute___closed__2();
lean::mark_persistent(l_Lean_mkNoInlineAttribute___closed__2);
w = l_Lean_mkNoInlineAttribute(w);
if (io_result_is_error(w)) return w;
l_Lean_noInlineAttribute = io_result_get_value(w);
lean::mark_persistent(l_Lean_noInlineAttribute);
l_Lean_mkMacroInlineAttribute___closed__1 = _init_l_Lean_mkMacroInlineAttribute___closed__1();
lean::mark_persistent(l_Lean_mkMacroInlineAttribute___closed__1);
l_Lean_mkMacroInlineAttribute___closed__2 = _init_l_Lean_mkMacroInlineAttribute___closed__2();
lean::mark_persistent(l_Lean_mkMacroInlineAttribute___closed__2);
w = l_Lean_mkMacroInlineAttribute(w);
if (io_result_is_error(w)) return w;
l_Lean_macroInlineAttribute = io_result_get_value(w);
lean::mark_persistent(l_Lean_macroInlineAttribute);
return w;
}

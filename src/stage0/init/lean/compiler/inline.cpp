// Lean compiler output
// Module: init.lean.compiler.inline
// Imports: init.lean.attributes init.lean.compiler.util
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
obj* l_Lean_Compiler_mkInlineIfReduceAttribute___closed__1;
obj* l_Lean_Compiler_hasInlineIfReduceAttribure___boxed(obj*, obj*);
obj* l_Lean_Compiler_mkMacroInlineAttribute___closed__2;
obj* l_Lean_AttributeImpl_inhabited___lambda__4___boxed(obj*, obj*, obj*);
obj* l_Lean_Compiler_mkNoInlineAttribute(obj*);
obj* l_Lean_Compiler_mkMacroInlineAttribute(obj*);
obj* l_Lean_AttributeImpl_inhabited___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__1___boxed(obj*);
obj* l___private_init_lean_compiler_inline_2__hasInlineAttrAux___main___boxed(obj*, obj*, obj*);
obj* l_Lean_Compiler_noInlineAttribute;
obj* l_Lean_Compiler_mkInlineAttribute___closed__1;
obj* l___private_init_lean_compiler_inline_2__hasInlineAttrAux___boxed(obj*, obj*, obj*);
uint8 l_Lean_Compiler_isEagerLambdaLiftingName___main(obj*);
obj* l_Lean_Compiler_inlineAttribute;
obj* l_Lean_Compiler_inlineIfReduceAttribute;
obj* l_Array_mkEmpty(obj*, obj*);
namespace lean {
uint8 has_macro_inline_attribute_core(obj*, obj*);
}
obj* l_Lean_registerTagAttribute(obj*, obj*, obj*, obj*);
obj* l_Lean_AttributeImpl_inhabited___lambda__5(obj*, obj*);
obj* l_Lean_Compiler_mkInlineAttribute(obj*);
namespace lean {
uint8 has_inline_if_reduce_attribute_core(obj*, obj*);
}
obj* l___private_init_lean_compiler_inline_1__checkIsDefinition___closed__1;
obj* l_Lean_Compiler_hasInlineAttribure___boxed(obj*, obj*);
namespace lean {
uint8 has_noinline_attribute_core(obj*, obj*);
}
obj* l_Lean_Compiler_mkInlineAttribute___closed__2;
obj* l_Lean_AttributeImpl_inhabited___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_inline_1__checkIsDefinition___closed__2;
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Compiler_hasNoInlineAttribure___boxed(obj*, obj*);
uint8 l___private_init_lean_compiler_inline_2__hasInlineAttrAux(obj*, obj*, obj*);
obj* l_ExceptT_Monad___rarg___lambda__8___boxed(obj*, obj*);
obj* l_Lean_Compiler_hasMacroInlineAttribure___boxed(obj*, obj*);
obj* l___private_init_lean_compiler_inline_1__checkIsDefinition___closed__3;
uint8 l_Lean_TagAttribute_hasTag(obj*, obj*, obj*);
obj* l_Lean_Compiler_macroInlineAttribute;
obj* l___private_init_lean_compiler_inline_1__checkIsDefinition(obj*, obj*);
namespace lean {
obj* environment_find_core(obj*, obj*);
}
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__2___boxed(obj*);
obj* l_Lean_Compiler_mkMacroInlineAttribute___closed__1;
obj* l_Lean_Name_getPrefix___main(obj*);
obj* l_Lean_Compiler_mkInlineIfReduceAttribute(obj*);
obj* l_Lean_Compiler_mkInlineAttribute___closed__3;
obj* l_Lean_Compiler_mkNoInlineAttribute___closed__2;
obj* l_Lean_AttributeImpl_inhabited___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Compiler_mkNoInlineAttribute___closed__1;
uint8 l_Lean_Name_isInternal___main(obj*);
uint8 l___private_init_lean_compiler_inline_2__hasInlineAttrAux___main(obj*, obj*, obj*);
obj* l_Lean_Compiler_mkInlineIfReduceAttribute___closed__2;
namespace lean {
uint8 has_inline_attribute_core(obj*, obj*);
}
obj* _init_l___private_init_lean_compiler_inline_1__checkIsDefinition___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("unknow declaration");
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_inline_1__checkIsDefinition___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("declaration is not a definition");
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_inline_1__checkIsDefinition___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_inline_1__checkIsDefinition(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::environment_find_core(x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_inline_1__checkIsDefinition___closed__1;
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
x_6 = l___private_init_lean_compiler_inline_1__checkIsDefinition___closed__3;
return x_6;
}
else
{
obj* x_7; 
lean::dec(x_5);
x_7 = l___private_init_lean_compiler_inline_1__checkIsDefinition___closed__2;
return x_7;
}
}
}
}
obj* _init_l_Lean_Compiler_mkInlineAttribute___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("inline");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Compiler_mkInlineAttribute___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("mark definition to always be inlined");
return x_1;
}
}
obj* _init_l_Lean_Compiler_mkInlineAttribute___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_inline_1__checkIsDefinition), 2, 0);
return x_1;
}
}
obj* l_Lean_Compiler_mkInlineAttribute(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Compiler_mkInlineAttribute___closed__1;
x_3 = l_Lean_Compiler_mkInlineAttribute___closed__2;
x_4 = l_Lean_Compiler_mkInlineAttribute___closed__3;
x_5 = l_Lean_registerTagAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Compiler_mkInlineIfReduceAttribute___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("inlineIfReduce");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Compiler_mkInlineIfReduceAttribute___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("mark definition to be inlined when resultant term after reduction is not a `cases_on` application.");
return x_1;
}
}
obj* l_Lean_Compiler_mkInlineIfReduceAttribute(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Compiler_mkInlineIfReduceAttribute___closed__1;
x_3 = l_Lean_Compiler_mkInlineIfReduceAttribute___closed__2;
x_4 = l_Lean_Compiler_mkInlineAttribute___closed__3;
x_5 = l_Lean_registerTagAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Compiler_mkNoInlineAttribute___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("noinline");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Compiler_mkNoInlineAttribute___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("mark definition to never be inlined");
return x_1;
}
}
obj* l_Lean_Compiler_mkNoInlineAttribute(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Compiler_mkNoInlineAttribute___closed__1;
x_3 = l_Lean_Compiler_mkNoInlineAttribute___closed__2;
x_4 = l_Lean_Compiler_mkInlineAttribute___closed__3;
x_5 = l_Lean_registerTagAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Compiler_mkMacroInlineAttribute___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("macroInline");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Compiler_mkMacroInlineAttribute___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("mark definition to always be inlined before ANF conversion");
return x_1;
}
}
obj* l_Lean_Compiler_mkMacroInlineAttribute(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Compiler_mkMacroInlineAttribute___closed__1;
x_3 = l_Lean_Compiler_mkMacroInlineAttribute___closed__2;
x_4 = l_Lean_Compiler_mkInlineAttribute___closed__3;
x_5 = l_Lean_registerTagAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
uint8 l___private_init_lean_compiler_inline_2__hasInlineAttrAux___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_Lean_Compiler_isEagerLambdaLiftingName___main(x_3);
if (x_4 == 0)
{
uint8 x_5; 
lean::inc(x_2);
x_5 = l_Lean_TagAttribute_hasTag(x_2, x_1, x_3);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = l_Lean_Name_isInternal___main(x_3);
if (x_6 == 0)
{
uint8 x_7; 
lean::dec(x_3);
lean::dec(x_2);
x_7 = 0;
return x_7;
}
else
{
obj* x_8; 
x_8 = l_Lean_Name_getPrefix___main(x_3);
lean::dec(x_3);
x_3 = x_8;
goto _start;
}
}
else
{
uint8 x_10; 
lean::dec(x_3);
lean::dec(x_2);
x_10 = 1;
return x_10;
}
}
else
{
uint8 x_11; 
lean::dec(x_3);
lean::dec(x_2);
x_11 = 0;
return x_11;
}
}
}
obj* l___private_init_lean_compiler_inline_2__hasInlineAttrAux___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l___private_init_lean_compiler_inline_2__hasInlineAttrAux___main(x_1, x_2, x_3);
lean::dec(x_1);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l___private_init_lean_compiler_inline_2__hasInlineAttrAux(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l___private_init_lean_compiler_inline_2__hasInlineAttrAux___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_lean_compiler_inline_2__hasInlineAttrAux___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l___private_init_lean_compiler_inline_2__hasInlineAttrAux(x_1, x_2, x_3);
lean::dec(x_1);
x_5 = lean::box(x_4);
return x_5;
}
}
namespace lean {
uint8 has_inline_attribute_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = l_Lean_Compiler_inlineAttribute;
x_4 = l___private_init_lean_compiler_inline_2__hasInlineAttrAux___main(x_1, x_3, x_2);
lean::dec(x_1);
return x_4;
}
}
}
obj* l_Lean_Compiler_hasInlineAttribure___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::has_inline_attribute_core(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
namespace lean {
uint8 has_inline_if_reduce_attribute_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = l_Lean_Compiler_inlineIfReduceAttribute;
x_4 = l___private_init_lean_compiler_inline_2__hasInlineAttrAux___main(x_1, x_3, x_2);
lean::dec(x_1);
return x_4;
}
}
}
obj* l_Lean_Compiler_hasInlineIfReduceAttribure___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::has_inline_if_reduce_attribute_core(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
namespace lean {
uint8 has_noinline_attribute_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = l_Lean_Compiler_noInlineAttribute;
x_4 = l___private_init_lean_compiler_inline_2__hasInlineAttrAux___main(x_1, x_3, x_2);
lean::dec(x_1);
return x_4;
}
}
}
obj* l_Lean_Compiler_hasNoInlineAttribure___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::has_noinline_attribute_core(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
namespace lean {
uint8 has_macro_inline_attribute_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = l_Lean_Compiler_macroInlineAttribute;
x_4 = l___private_init_lean_compiler_inline_2__hasInlineAttrAux___main(x_1, x_3, x_2);
lean::dec(x_1);
return x_4;
}
}
}
obj* l_Lean_Compiler_hasMacroInlineAttribure___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::has_macro_inline_attribute_core(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* initialize_init_lean_attributes(obj*);
obj* initialize_init_lean_compiler_util(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_inline(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_attributes(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_util(w);
if (io_result_is_error(w)) return w;
l___private_init_lean_compiler_inline_1__checkIsDefinition___closed__1 = _init_l___private_init_lean_compiler_inline_1__checkIsDefinition___closed__1();
lean::mark_persistent(l___private_init_lean_compiler_inline_1__checkIsDefinition___closed__1);
l___private_init_lean_compiler_inline_1__checkIsDefinition___closed__2 = _init_l___private_init_lean_compiler_inline_1__checkIsDefinition___closed__2();
lean::mark_persistent(l___private_init_lean_compiler_inline_1__checkIsDefinition___closed__2);
l___private_init_lean_compiler_inline_1__checkIsDefinition___closed__3 = _init_l___private_init_lean_compiler_inline_1__checkIsDefinition___closed__3();
lean::mark_persistent(l___private_init_lean_compiler_inline_1__checkIsDefinition___closed__3);
l_Lean_Compiler_mkInlineAttribute___closed__1 = _init_l_Lean_Compiler_mkInlineAttribute___closed__1();
lean::mark_persistent(l_Lean_Compiler_mkInlineAttribute___closed__1);
l_Lean_Compiler_mkInlineAttribute___closed__2 = _init_l_Lean_Compiler_mkInlineAttribute___closed__2();
lean::mark_persistent(l_Lean_Compiler_mkInlineAttribute___closed__2);
l_Lean_Compiler_mkInlineAttribute___closed__3 = _init_l_Lean_Compiler_mkInlineAttribute___closed__3();
lean::mark_persistent(l_Lean_Compiler_mkInlineAttribute___closed__3);
w = l_Lean_Compiler_mkInlineAttribute(w);
if (io_result_is_error(w)) return w;
l_Lean_Compiler_inlineAttribute = io_result_get_value(w);
lean::mark_persistent(l_Lean_Compiler_inlineAttribute);
l_Lean_Compiler_mkInlineIfReduceAttribute___closed__1 = _init_l_Lean_Compiler_mkInlineIfReduceAttribute___closed__1();
lean::mark_persistent(l_Lean_Compiler_mkInlineIfReduceAttribute___closed__1);
l_Lean_Compiler_mkInlineIfReduceAttribute___closed__2 = _init_l_Lean_Compiler_mkInlineIfReduceAttribute___closed__2();
lean::mark_persistent(l_Lean_Compiler_mkInlineIfReduceAttribute___closed__2);
w = l_Lean_Compiler_mkInlineIfReduceAttribute(w);
if (io_result_is_error(w)) return w;
l_Lean_Compiler_inlineIfReduceAttribute = io_result_get_value(w);
lean::mark_persistent(l_Lean_Compiler_inlineIfReduceAttribute);
l_Lean_Compiler_mkNoInlineAttribute___closed__1 = _init_l_Lean_Compiler_mkNoInlineAttribute___closed__1();
lean::mark_persistent(l_Lean_Compiler_mkNoInlineAttribute___closed__1);
l_Lean_Compiler_mkNoInlineAttribute___closed__2 = _init_l_Lean_Compiler_mkNoInlineAttribute___closed__2();
lean::mark_persistent(l_Lean_Compiler_mkNoInlineAttribute___closed__2);
w = l_Lean_Compiler_mkNoInlineAttribute(w);
if (io_result_is_error(w)) return w;
l_Lean_Compiler_noInlineAttribute = io_result_get_value(w);
lean::mark_persistent(l_Lean_Compiler_noInlineAttribute);
l_Lean_Compiler_mkMacroInlineAttribute___closed__1 = _init_l_Lean_Compiler_mkMacroInlineAttribute___closed__1();
lean::mark_persistent(l_Lean_Compiler_mkMacroInlineAttribute___closed__1);
l_Lean_Compiler_mkMacroInlineAttribute___closed__2 = _init_l_Lean_Compiler_mkMacroInlineAttribute___closed__2();
lean::mark_persistent(l_Lean_Compiler_mkMacroInlineAttribute___closed__2);
w = l_Lean_Compiler_mkMacroInlineAttribute(w);
if (io_result_is_error(w)) return w;
l_Lean_Compiler_macroInlineAttribute = io_result_get_value(w);
lean::mark_persistent(l_Lean_Compiler_macroInlineAttribute);
return w;
}

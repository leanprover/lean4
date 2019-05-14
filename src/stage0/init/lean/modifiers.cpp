// Lean compiler output
// Module: init.lean.modifiers
// Imports: init.lean.environment
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
extern obj* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
namespace lean {
obj* add_protected_core(obj*, obj*);
}
obj* l_List_toArrayAux___main___rarg(obj*, obj*);
obj* l_Lean_mkProtectedExtension___lambda__1(uint8, obj*, obj*);
obj* l_List_redLength___main___rarg(obj*);
obj* l_Lean_isProtected___boxed(obj*, obj*);
obj* l_Lean_mkProtectedExtension___closed__2;
obj* l_Lean_protectedExt___elambda__1(obj*);
uint8 l_Lean_NameSet_contains(obj*, obj*);
obj* l_RBNode_insert___at_Lean_NameSet_insert___spec__1(obj*, obj*, obj*);
obj* l_Lean_PersistentEnvExtension_getState___rarg(obj*, obj*);
obj* l_Lean_mkProtectedExtension___closed__1;
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_protectedExt;
obj* l_Lean_mkProtectedExtension___lambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_protectedExt___elambda__2___rarg(obj*, obj*);
obj* l_Lean_protectedExt___elambda__2(uint8);
obj* l_Lean_PersistentEnvExtension_addEntry___rarg(obj*, obj*, obj*);
namespace lean {
uint8 is_protected_core(obj*, obj*);
}
obj* l_Lean_mkProtectedExtension(obj*);
obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg(obj*, obj*, obj*, obj*, obj*, uint8, obj*);
obj* l_Lean_protectedExt___elambda__2___boxed(obj*);
obj* l_Lean_protectedExt___elambda__2___rarg___boxed(obj*, obj*);
obj* l_Lean_mkProtectedExtension___lambda__1(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
obj* _init_l_Lean_mkProtectedExtension___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("protected");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_mkProtectedExtension___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_mkProtectedExtension___lambda__1___boxed), 3, 0);
return x_0;
}
}
obj* l_Lean_mkProtectedExtension(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; uint8 x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = l_Lean_mkProtectedExtension___closed__1;
x_3 = lean::box(0);
x_4 = l_Lean_mkProtectedExtension___closed__2;
x_5 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
x_6 = 0;
x_7 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg(x_2, x_1, x_3, x_4, x_5, x_6, x_0);
return x_7;
}
}
obj* l_Lean_mkProtectedExtension___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_Lean_mkProtectedExtension___lambda__1(x_3, x_1, x_2);
return x_4;
}
}
obj* l_Lean_protectedExt___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_1 = l_List_redLength___main___rarg(x_0);
x_2 = lean::mk_empty_array(x_1);
lean::dec(x_1);
x_4 = l_List_toArrayAux___main___rarg(x_0, x_2);
return x_4;
}
}
obj* l_Lean_protectedExt___elambda__2___rarg(obj* x_0, obj* x_1) {
_start:
{
lean::inc(x_0);
return x_0;
}
}
obj* l_Lean_protectedExt___elambda__2(uint8 x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_protectedExt___elambda__2___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_Lean_protectedExt___elambda__2___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_protectedExt___elambda__2___rarg(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_protectedExt___elambda__2___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_Lean_protectedExt___elambda__2(x_1);
return x_2;
}
}
namespace lean {
obj* add_protected_core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_protectedExt;
x_3 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_2, x_0, x_1);
return x_3;
}
}
}
namespace lean {
uint8 is_protected_core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; uint8 x_5; 
x_2 = l_Lean_protectedExt;
x_3 = l_Lean_PersistentEnvExtension_getState___rarg(x_2, x_0);
lean::dec(x_0);
x_5 = l_Lean_NameSet_contains(x_3, x_1);
lean::dec(x_1);
return x_5;
}
}
}
obj* l_Lean_isProtected___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::is_protected_core(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* initialize_init_lean_environment(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_modifiers(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_environment(w);
if (io_result_is_error(w)) return w;
 l_Lean_mkProtectedExtension___closed__1 = _init_l_Lean_mkProtectedExtension___closed__1();
lean::mark_persistent(l_Lean_mkProtectedExtension___closed__1);
 l_Lean_mkProtectedExtension___closed__2 = _init_l_Lean_mkProtectedExtension___closed__2();
lean::mark_persistent(l_Lean_mkProtectedExtension___closed__2);
w = l_Lean_mkProtectedExtension(w);
if (io_result_is_error(w)) return w;
 l_Lean_protectedExt = io_result_get_value(w);
lean::mark_persistent(l_Lean_protectedExt);
return w;
}

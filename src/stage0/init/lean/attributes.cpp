// Lean compiler output
// Module: init.lean.attributes
// Imports: init.lean.environment init.lean.parser.syntax
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
extern obj* l_Array_empty___closed__1;
obj* l_List_foldl___main___at_Lean_Environment_toValidNamespace___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Environment_getNamespaces___boxed(obj*);
obj* l_Lean_scopeManagerExt___elambda__1(obj*);
obj* l_Lean_Environment_getNamespaces(obj*);
obj* l_Lean_Environment_getScopeHeader(obj*);
obj* l_List_toArrayAux___main___rarg(obj*, obj*);
obj* l_Lean_SimplePersistentEnvExtension_getState___rarg(obj*, obj*);
obj* l_Lean_scopeManagerExt;
obj* l_Lean_ScopeManagerState_Inhabited;
obj* l_List_redLength___main___rarg(obj*);
obj* l_Lean_Environment_getNamespace(obj*);
obj* l_Array_mkEmpty(obj*, obj*);
obj* l_Lean_regScopeManagerExtension___lambda__1(obj*, obj*);
uint8 l_Lean_NameSet_contains(obj*, obj*);
obj* l_Lean_regScopeManagerExtension___lambda__2___closed__1;
obj* l_Lean_Environment_getScopeHeader___boxed(obj*);
obj* l_RBNode_insert___at_Lean_NameSet_insert___spec__1(obj*, obj*, obj*);
obj* l_Lean_regScopeManagerExtension___lambda__2___boxed(obj*);
obj* l_Lean_regScopeManagerExtension(obj*);
obj* l_Array_miterateAux___main___at_Lean_regScopeManagerExtension___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_mkStateFromImportedEntries___at_Lean_regScopeManagerExtension___spec__1___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_regScopeManagerExtension___spec__3(obj*, obj*, obj*, obj*);
obj* l_Lean_scopeManagerExt___elambda__3___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_regScopeManagerExtension___spec__3___boxed(obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_Environment_getNamespace___boxed(obj*);
obj* l_Array_fget(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_registerSimplePersistentEnvExtension___rarg(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Array_miterateAux___main___at_Lean_regScopeManagerExtension___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_mkStateFromImportedEntries___at_Lean_regScopeManagerExtension___spec__1(obj*, obj*);
obj* l_Lean_regScopeManagerExtension___lambda__2(obj*);
obj* l_Lean_scopeManagerExt___elambda__2___boxed(obj*);
obj* l_Lean_scopeManagerExt___elambda__4___boxed(obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_Environment_toValidNamespace___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_ScopeManagerState_saveNamespace(obj*, obj*);
obj* l_Lean_regScopeManagerExtension___closed__1;
obj* l_Lean_scopeManagerExt___elambda__3(obj*, obj*);
obj* l_Lean_scopeManagerExt___elambda__1___boxed(obj*);
obj* l_Array_size(obj*, obj*);
obj* l_Lean_scopeManagerExt___elambda__2(obj*);
obj* l_Lean_Name_append___main(obj*, obj*);
obj* l_Lean_Environment_toValidNamespace(obj*, obj*);
obj* l_Lean_scopeManagerExt___elambda__4(obj*, obj*, obj*);
obj* l_Lean_regScopeManagerExtension___lambda__3(obj*);
obj* l_Lean_Environment_toValidNamespace___boxed(obj*, obj*);
obj* _init_l_Lean_ScopeManagerState_Inhabited() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
lean::cnstr_set(x_3, 2, x_2);
lean::cnstr_set(x_3, 3, x_2);
return x_3;
}
}
obj* l_Lean_ScopeManagerState_saveNamespace(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::box(0);
x_6 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_4, x_2, x_5);
lean::cnstr_set(x_1, 0, x_6);
return x_1;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_7 = lean::cnstr_get(x_1, 0);
x_8 = lean::cnstr_get(x_1, 1);
x_9 = lean::cnstr_get(x_1, 2);
x_10 = lean::cnstr_get(x_1, 3);
lean::inc(x_10);
lean::inc(x_9);
lean::inc(x_8);
lean::inc(x_7);
lean::dec(x_1);
x_11 = lean::box(0);
x_12 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_7, x_2, x_11);
x_13 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_8);
lean::cnstr_set(x_13, 2, x_9);
lean::cnstr_set(x_13, 3, x_10);
return x_13;
}
}
}
obj* l_Array_miterateAux___main___at_Lean_regScopeManagerExtension___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
return x_4;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::array_fget(x_2, x_3);
x_8 = l_Lean_ScopeManagerState_saveNamespace(x_4, x_7);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_add(x_3, x_9);
lean::dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_Lean_regScopeManagerExtension___spec__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
return x_4;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::array_fget(x_2, x_3);
x_8 = lean::mk_nat_obj(0u);
x_9 = l_Array_miterateAux___main___at_Lean_regScopeManagerExtension___spec__2(x_7, x_7, x_8, x_4);
lean::dec(x_7);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_3, x_10);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_9;
goto _start;
}
}
}
obj* l_Lean_mkStateFromImportedEntries___at_Lean_regScopeManagerExtension___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l_Array_miterateAux___main___at_Lean_regScopeManagerExtension___spec__3(x_2, x_2, x_3, x_1);
return x_4;
}
}
obj* l_Lean_regScopeManagerExtension___lambda__1(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::box(0);
x_6 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_4, x_2, x_5);
lean::cnstr_set(x_1, 0, x_6);
return x_1;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_7 = lean::cnstr_get(x_1, 0);
x_8 = lean::cnstr_get(x_1, 1);
x_9 = lean::cnstr_get(x_1, 2);
x_10 = lean::cnstr_get(x_1, 3);
lean::inc(x_10);
lean::inc(x_9);
lean::inc(x_8);
lean::inc(x_7);
lean::dec(x_1);
x_11 = lean::box(0);
x_12 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_7, x_2, x_11);
x_13 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_8);
lean::cnstr_set(x_13, 2, x_9);
lean::cnstr_set(x_13, 3, x_10);
return x_13;
}
}
}
obj* _init_l_Lean_regScopeManagerExtension___lambda__2___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
lean::cnstr_set(x_3, 2, x_2);
lean::cnstr_set(x_3, 3, x_2);
return x_3;
}
}
obj* l_Lean_regScopeManagerExtension___lambda__2(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::mk_nat_obj(0u);
x_3 = l_Lean_regScopeManagerExtension___lambda__2___closed__1;
x_4 = l_Array_miterateAux___main___at_Lean_regScopeManagerExtension___spec__3(x_1, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_regScopeManagerExtension___lambda__3(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_List_redLength___main___rarg(x_1);
x_3 = lean::mk_empty_array(x_2);
lean::dec(x_2);
x_4 = l_List_toArrayAux___main___rarg(x_1, x_3);
return x_4;
}
}
obj* _init_l_Lean_regScopeManagerExtension___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = lean::mk_string("scopes");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_regScopeManagerExtension___lambda__1), 2, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_regScopeManagerExtension___lambda__2___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_regScopeManagerExtension___lambda__3), 1, 0);
x_7 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_4);
lean::cnstr_set(x_7, 2, x_5);
lean::cnstr_set(x_7, 3, x_6);
return x_7;
}
}
obj* l_Lean_regScopeManagerExtension(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_regScopeManagerExtension___closed__1;
x_3 = l_Lean_registerSimplePersistentEnvExtension___rarg(x_2, x_1);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Lean_regScopeManagerExtension___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_regScopeManagerExtension___spec__2(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Array_miterateAux___main___at_Lean_regScopeManagerExtension___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_regScopeManagerExtension___spec__3(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_mkStateFromImportedEntries___at_Lean_regScopeManagerExtension___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_mkStateFromImportedEntries___at_Lean_regScopeManagerExtension___spec__1(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_regScopeManagerExtension___lambda__2___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_regScopeManagerExtension___lambda__2(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_scopeManagerExt___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
}
obj* l_Lean_scopeManagerExt___elambda__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_empty___closed__1;
return x_2;
}
}
obj* l_Lean_scopeManagerExt___elambda__3(obj* x_1, obj* x_2) {
_start:
{
lean::inc(x_1);
return x_1;
}
}
obj* l_Lean_scopeManagerExt___elambda__4(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
}
obj* l_Lean_scopeManagerExt___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_scopeManagerExt___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_scopeManagerExt___elambda__2___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_scopeManagerExt___elambda__2(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_scopeManagerExt___elambda__3___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_scopeManagerExt___elambda__3(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_scopeManagerExt___elambda__4___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_scopeManagerExt___elambda__4(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_Environment_getNamespaces(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_scopeManagerExt;
x_3 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_2, x_1);
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_Environment_getNamespaces___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Environment_getNamespaces(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Environment_getNamespace(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Environment_getNamespaces(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
return x_4;
}
}
}
obj* l_Lean_Environment_getNamespace___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Environment_getNamespace(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Environment_getScopeHeader(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_scopeManagerExt;
x_3 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_2, x_1);
x_4 = lean::cnstr_get(x_3, 2);
lean::inc(x_4);
lean::dec(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; 
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::dec(x_4);
return x_6;
}
}
}
obj* l_Lean_Environment_getScopeHeader___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Environment_getScopeHeader(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_foldl___main___at_Lean_Environment_toValidNamespace___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
lean::dec(x_1);
return x_3;
}
else
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_5 = lean::cnstr_get(x_4, 0);
x_6 = lean::cnstr_get(x_4, 1);
lean::inc(x_1);
x_7 = l_Lean_Name_append___main(x_5, x_1);
x_8 = l_Lean_NameSet_contains(x_2, x_7);
if (x_8 == 0)
{
lean::dec(x_7);
x_4 = x_6;
goto _start;
}
else
{
obj* x_10; 
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_7);
x_3 = x_10;
x_4 = x_6;
goto _start;
}
}
else
{
obj* x_12; 
x_12 = lean::cnstr_get(x_4, 1);
x_4 = x_12;
goto _start;
}
}
}
}
obj* l_Lean_Environment_toValidNamespace(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = l_Lean_scopeManagerExt;
x_4 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_3, x_1);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = l_Lean_NameSet_contains(x_5, x_2);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::box(0);
x_8 = lean::cnstr_get(x_4, 1);
lean::inc(x_8);
lean::dec(x_4);
x_9 = l_List_foldl___main___at_Lean_Environment_toValidNamespace___spec__1(x_2, x_5, x_7, x_8);
lean::dec(x_8);
lean::dec(x_5);
return x_9;
}
else
{
obj* x_10; 
lean::dec(x_5);
lean::dec(x_4);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_2);
return x_10;
}
}
}
obj* l_List_foldl___main___at_Lean_Environment_toValidNamespace___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_foldl___main___at_Lean_Environment_toValidNamespace___spec__1(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Environment_toValidNamespace___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Environment_toValidNamespace(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* initialize_init_lean_environment(obj*);
obj* initialize_init_lean_parser_syntax(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_attributes(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_environment(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_syntax(w);
if (io_result_is_error(w)) return w;
l_Lean_ScopeManagerState_Inhabited = _init_l_Lean_ScopeManagerState_Inhabited();
lean::mark_persistent(l_Lean_ScopeManagerState_Inhabited);
l_Lean_regScopeManagerExtension___lambda__2___closed__1 = _init_l_Lean_regScopeManagerExtension___lambda__2___closed__1();
lean::mark_persistent(l_Lean_regScopeManagerExtension___lambda__2___closed__1);
l_Lean_regScopeManagerExtension___closed__1 = _init_l_Lean_regScopeManagerExtension___closed__1();
lean::mark_persistent(l_Lean_regScopeManagerExtension___closed__1);
w = l_Lean_regScopeManagerExtension(w);
if (io_result_is_error(w)) return w;
l_Lean_scopeManagerExt = io_result_get_value(w);
lean::mark_persistent(l_Lean_scopeManagerExt);
return w;
}

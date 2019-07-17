// Lean compiler output
// Module: init.lean.scopes
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
obj* l_Lean_scopeManagerExt___closed__6;
obj* l_Lean_scopeManagerExt___closed__4;
extern obj* l_Array_empty___closed__1;
obj* l_List_foldl___main___at_Lean_Environment_toValidNamespace___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_regScopeManagerExtension___closed__4;
obj* l_Lean_scopeManagerExt___lambda__1___boxed(obj*);
obj* l_Lean_scopeManagerExt___closed__3;
obj* l_Lean_Environment_popScopeCore___lambda__1(obj*);
obj* l_Lean_scopeManagerExt___elambda__1(obj*);
namespace lean {
uint8 has_open_scopes_core(obj*);
}
obj* l_Lean_Environment_popScopeCore___closed__1;
obj* l_Lean_Environment_pushScopeCore___lambda__1(obj*, obj*, uint8, obj*);
namespace lean {
obj* get_namespaces_core(obj*);
}
uint8 l_List_isEmpty___main___rarg(obj*);
namespace lean {
obj* get_scope_header_core(obj*);
}
obj* l_List_toArrayAux___main___rarg(obj*, obj*);
obj* l_Lean_SimplePersistentEnvExtension_getState___rarg(obj*, obj*);
obj* l_Lean_scopeManagerExt;
obj* l_Lean_ScopeManagerState_Inhabited;
obj* l_List_redLength___main___rarg(obj*);
obj* l_Lean_Environment_registerNamespaceAux(obj*, obj*);
namespace lean {
obj* get_namespace_core(obj*);
}
obj* l_Lean_scopeManagerExt___closed__8;
obj* l_Array_mkEmpty(obj*, obj*);
obj* l_Lean_SimplePersistentEnvExtension_modifyState___rarg(obj*, obj*, obj*);
obj* l_Lean_regScopeManagerExtension___lambda__1(obj*, obj*);
obj* l_Lean_scopeManagerExt___closed__2;
obj* l_Thunk_mk(obj*, obj*);
uint8 l_Lean_NameSet_contains(obj*, obj*);
obj* l_Lean_Environment_inSection___boxed(obj*);
obj* l_Lean_scopeManagerExt___lambda__1___closed__1;
obj* l_RBNode_insert___at_Lean_NameSet_insert___spec__1(obj*, obj*, obj*);
obj* l_Lean_regScopeManagerExtension___lambda__2___boxed(obj*);
obj* l_Lean_regScopeManagerExtension(obj*);
obj* l_Array_miterateAux___main___at_Lean_regScopeManagerExtension___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Environment_getNamespaceSet(obj*);
obj* l_Lean_mkStateFromImportedEntries___at_Lean_regScopeManagerExtension___spec__1___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_regScopeManagerExtension___spec__3(obj*, obj*, obj*, obj*);
obj* l_Lean_scopeManagerExt___elambda__3___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_regScopeManagerExtension___spec__3___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_scopeManagerExt___lambda__1(obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Array_fget(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_registerSimplePersistentEnvExtension___rarg(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
namespace lean {
uint8 is_namespace_core(obj*, obj*);
}
obj* l_Lean_regScopeManagerExtension___closed__5;
obj* l_Array_miterateAux___main___at_Lean_regScopeManagerExtension___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_scopeManagerExt___closed__7;
obj* l_Lean_mkStateFromImportedEntries___at_Lean_regScopeManagerExtension___spec__1(obj*, obj*);
namespace lean {
obj* register_namespace_core(obj*, obj*);
}
obj* l_Lean_regScopeManagerExtension___lambda__2(obj*);
obj* l_Lean_scopeManagerExt___elambda__2___boxed(obj*);
obj* l_Lean_regScopeManagerExtension___closed__3;
obj* l_Lean_regScopeManagerExtension___closed__6;
obj* l_Lean_scopeManagerExt___elambda__4___boxed(obj*);
obj* l_List_foldl___main___at_Lean_Environment_toValidNamespace___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_ScopeManagerState_saveNamespace(obj*, obj*);
obj* l_Lean_scopeManagerExt___elambda__4___closed__2;
obj* l_Lean_regScopeManagerExtension___closed__1;
obj* l_Lean_Environment_popScopeCore(obj*);
obj* l_Lean_Environment_getNamespaceSet___boxed(obj*);
obj* l_Lean_PersistentEnvExtension_addEntry___rarg(obj*, obj*, obj*);
obj* l_Lean_scopeManagerExt___closed__1;
obj* l_Lean_scopeManagerExt___elambda__3(obj*, obj*);
obj* l_Lean_scopeManagerExt___elambda__4___closed__1;
obj* l_Lean_ScopeManagerState_Inhabited___closed__1;
obj* l_Lean_scopeManagerExt___elambda__1___boxed(obj*);
obj* l_Array_size(obj*, obj*);
obj* l_Lean_Environment_registerNamespace___main(obj*, obj*);
obj* l_Lean_regScopeManagerExtension___closed__2;
obj* l_List_tail___main___rarg(obj*);
obj* l_Lean_Environment_pushScopeCore___boxed(obj*, obj*, obj*);
obj* l_Lean_scopeManagerExt___elambda__2(obj*);
namespace lean {
uint8 in_section_core(obj*);
}
obj* l_Lean_scopeManagerExt___closed__5;
obj* l_Lean_Environment_pushScopeCore(obj*, obj*, uint8);
obj* l_Lean_Environment_isNamespace___boxed(obj*, obj*);
obj* l_Lean_Environment_hasOpenScopes___boxed(obj*);
obj* l_Lean_Name_append___main(obj*, obj*);
obj* l_Lean_Environment_pushScopeCore___lambda__1___boxed(obj*, obj*, obj*, obj*);
namespace lean {
obj* to_valid_namespace_core(obj*, obj*);
}
obj* l_Lean_scopeManagerExt___elambda__4(obj*);
obj* l_Lean_regScopeManagerExtension___lambda__3(obj*);
obj* _init_l_Lean_ScopeManagerState_Inhabited___closed__1() {
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
obj* _init_l_Lean_ScopeManagerState_Inhabited() {
_start:
{
obj* x_1; 
x_1 = l_Lean_ScopeManagerState_Inhabited___closed__1;
return x_1;
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
obj* l_Lean_regScopeManagerExtension___lambda__2(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::mk_nat_obj(0u);
x_3 = l_Lean_ScopeManagerState_Inhabited___closed__1;
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
obj* x_1; 
x_1 = lean::mk_string("scopes");
return x_1;
}
}
obj* _init_l_Lean_regScopeManagerExtension___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_regScopeManagerExtension___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_regScopeManagerExtension___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_regScopeManagerExtension___lambda__1), 2, 0);
return x_1;
}
}
obj* _init_l_Lean_regScopeManagerExtension___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_regScopeManagerExtension___lambda__2___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_regScopeManagerExtension___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_regScopeManagerExtension___lambda__3), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_regScopeManagerExtension___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_regScopeManagerExtension___closed__2;
x_2 = l_Lean_regScopeManagerExtension___closed__3;
x_3 = l_Lean_regScopeManagerExtension___closed__4;
x_4 = l_Lean_regScopeManagerExtension___closed__5;
x_5 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_4);
return x_5;
}
}
obj* l_Lean_regScopeManagerExtension(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_regScopeManagerExtension___closed__6;
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
obj* _init_l_Lean_scopeManagerExt___elambda__4___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_1);
lean::cnstr_set(x_3, 3, x_1);
return x_3;
}
}
obj* _init_l_Lean_scopeManagerExt___elambda__4___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_scopeManagerExt___elambda__4___closed__1;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_scopeManagerExt___elambda__4(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_scopeManagerExt___elambda__4___closed__2;
return x_2;
}
}
obj* _init_l_Lean_scopeManagerExt___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_scopeManagerExt___elambda__4___closed__2;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_scopeManagerExt___lambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_scopeManagerExt___lambda__1___closed__1;
return x_2;
}
}
obj* _init_l_Lean_scopeManagerExt___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_scopeManagerExt___lambda__1___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_scopeManagerExt___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_scopeManagerExt___closed__1;
x_2 = lean::mk_thunk(x_1);
return x_2;
}
}
obj* _init_l_Lean_scopeManagerExt___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_nat_obj(0u);
x_2 = l_Lean_scopeManagerExt___closed__2;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_scopeManagerExt___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_scopeManagerExt___elambda__4___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_scopeManagerExt___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_scopeManagerExt___elambda__3___boxed), 2, 0);
return x_1;
}
}
obj* _init_l_Lean_scopeManagerExt___closed__6() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_scopeManagerExt___elambda__2___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_scopeManagerExt___closed__7() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_scopeManagerExt___elambda__1___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_scopeManagerExt___closed__8() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = l_Lean_scopeManagerExt___closed__3;
x_2 = lean::box(0);
x_3 = l_Lean_scopeManagerExt___closed__4;
x_4 = l_Lean_scopeManagerExt___closed__5;
x_5 = l_Lean_scopeManagerExt___closed__6;
x_6 = l_Lean_scopeManagerExt___closed__7;
x_7 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_7, 0, x_1);
lean::cnstr_set(x_7, 1, x_2);
lean::cnstr_set(x_7, 2, x_3);
lean::cnstr_set(x_7, 3, x_4);
lean::cnstr_set(x_7, 4, x_5);
lean::cnstr_set(x_7, 5, x_6);
return x_7;
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
obj* l_Lean_scopeManagerExt___elambda__4___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_scopeManagerExt___elambda__4(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_scopeManagerExt___lambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_scopeManagerExt___lambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
namespace lean {
obj* get_namespaces_core(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_scopeManagerExt;
x_3 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_2, x_1);
lean::dec(x_1);
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
lean::dec(x_3);
return x_4;
}
}
}
obj* l_Lean_Environment_getNamespaceSet(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_scopeManagerExt;
x_3 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_2, x_1);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_Environment_getNamespaceSet___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Environment_getNamespaceSet(x_1);
lean::dec(x_1);
return x_2;
}
}
namespace lean {
uint8 is_namespace_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = l_Lean_Environment_getNamespaceSet(x_1);
lean::dec(x_1);
x_4 = l_Lean_NameSet_contains(x_3, x_2);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
}
obj* l_Lean_Environment_isNamespace___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::is_namespace_core(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
namespace lean {
uint8 in_section_core(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_scopeManagerExt;
x_3 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_2, x_1);
lean::dec(x_1);
x_4 = lean::cnstr_get(x_3, 3);
lean::inc(x_4);
lean::dec(x_3);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
else
{
obj* x_6; uint8 x_7; 
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::dec(x_4);
x_7 = lean::unbox(x_6);
lean::dec(x_6);
if (x_7 == 0)
{
uint8 x_8; 
x_8 = 1;
return x_8;
}
else
{
uint8 x_9; 
x_9 = 0;
return x_9;
}
}
}
}
}
obj* l_Lean_Environment_inSection___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::in_section_core(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
namespace lean {
uint8 has_open_scopes_core(obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::get_namespaces_core(x_1);
x_3 = l_List_isEmpty___main___rarg(x_2);
lean::dec(x_2);
if (x_3 == 0)
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
}
}
}
obj* l_Lean_Environment_hasOpenScopes___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::has_open_scopes_core(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
namespace lean {
obj* get_namespace_core(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::get_namespaces_core(x_1);
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
}
namespace lean {
obj* get_scope_header_core(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_scopeManagerExt;
x_3 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_2, x_1);
lean::dec(x_1);
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
namespace lean {
obj* to_valid_namespace_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = l_Lean_scopeManagerExt;
x_4 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_3, x_1);
lean::dec(x_1);
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
obj* l_Lean_Environment_registerNamespaceAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = l_Lean_Environment_getNamespaceSet(x_1);
x_4 = l_Lean_NameSet_contains(x_3, x_2);
lean::dec(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = l_Lean_scopeManagerExt;
x_6 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_5, x_1, x_2);
return x_6;
}
else
{
lean::dec(x_2);
return x_1;
}
}
}
obj* l_Lean_Environment_registerNamespace___main(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 1)
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = l_Lean_Environment_registerNamespaceAux(x_1, x_2);
x_1 = x_4;
x_2 = x_3;
goto _start;
}
else
{
lean::dec(x_2);
return x_1;
}
}
}
namespace lean {
obj* register_namespace_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Environment_registerNamespace___main(x_1, x_2);
return x_3;
}
}
}
obj* l_Lean_Environment_pushScopeCore___lambda__1(obj* x_1, obj* x_2, uint8 x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_6 = lean::cnstr_get(x_4, 1);
x_7 = lean::cnstr_get(x_4, 2);
x_8 = lean::cnstr_get(x_4, 3);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_6);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_2);
lean::cnstr_set(x_10, 1, x_7);
x_11 = lean::box(x_3);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_8);
lean::cnstr_set(x_4, 3, x_12);
lean::cnstr_set(x_4, 2, x_10);
lean::cnstr_set(x_4, 1, x_9);
return x_4;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_13 = lean::cnstr_get(x_4, 0);
x_14 = lean::cnstr_get(x_4, 1);
x_15 = lean::cnstr_get(x_4, 2);
x_16 = lean::cnstr_get(x_4, 3);
lean::inc(x_16);
lean::inc(x_15);
lean::inc(x_14);
lean::inc(x_13);
lean::dec(x_4);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_1);
lean::cnstr_set(x_17, 1, x_14);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_2);
lean::cnstr_set(x_18, 1, x_15);
x_19 = lean::box(x_3);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_16);
x_21 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_21, 0, x_13);
lean::cnstr_set(x_21, 1, x_17);
lean::cnstr_set(x_21, 2, x_18);
lean::cnstr_set(x_21, 3, x_20);
return x_21;
}
}
}
obj* l_Lean_Environment_pushScopeCore(obj* x_1, obj* x_2, uint8 x_3) {
_start:
{
obj* x_4; 
lean::inc(x_1);
x_4 = lean::get_namespace_core(x_1);
if (x_3 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::inc(x_4);
x_5 = l_Lean_Environment_registerNamespaceAux(x_1, x_4);
x_6 = lean::box(x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Environment_pushScopeCore___lambda__1___boxed), 4, 3);
lean::closure_set(x_7, 0, x_4);
lean::closure_set(x_7, 1, x_2);
lean::closure_set(x_7, 2, x_6);
x_8 = l_Lean_scopeManagerExt;
x_9 = l_Lean_SimplePersistentEnvExtension_modifyState___rarg(x_8, x_5, x_7);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
lean::inc(x_2);
x_10 = l_Lean_Name_append___main(x_4, x_2);
lean::dec(x_4);
lean::inc(x_10);
x_11 = l_Lean_Environment_registerNamespaceAux(x_1, x_10);
x_12 = lean::box(x_3);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Environment_pushScopeCore___lambda__1___boxed), 4, 3);
lean::closure_set(x_13, 0, x_10);
lean::closure_set(x_13, 1, x_2);
lean::closure_set(x_13, 2, x_12);
x_14 = l_Lean_scopeManagerExt;
x_15 = l_Lean_SimplePersistentEnvExtension_modifyState___rarg(x_14, x_11, x_13);
return x_15;
}
}
}
obj* l_Lean_Environment_pushScopeCore___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_3);
lean::dec(x_3);
x_6 = l_Lean_Environment_pushScopeCore___lambda__1(x_1, x_2, x_5, x_4);
return x_6;
}
}
obj* l_Lean_Environment_pushScopeCore___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_3);
lean::dec(x_3);
x_5 = l_Lean_Environment_pushScopeCore(x_1, x_2, x_4);
return x_5;
}
}
obj* l_Lean_Environment_popScopeCore___lambda__1(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::cnstr_get(x_1, 2);
x_5 = lean::cnstr_get(x_1, 3);
x_6 = l_List_tail___main___rarg(x_3);
lean::dec(x_3);
x_7 = l_List_tail___main___rarg(x_4);
lean::dec(x_4);
x_8 = l_List_tail___main___rarg(x_5);
lean::dec(x_5);
lean::cnstr_set(x_1, 3, x_8);
lean::cnstr_set(x_1, 2, x_7);
lean::cnstr_set(x_1, 1, x_6);
return x_1;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_9 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_11 = lean::cnstr_get(x_1, 2);
x_12 = lean::cnstr_get(x_1, 3);
lean::inc(x_12);
lean::inc(x_11);
lean::inc(x_10);
lean::inc(x_9);
lean::dec(x_1);
x_13 = l_List_tail___main___rarg(x_10);
lean::dec(x_10);
x_14 = l_List_tail___main___rarg(x_11);
lean::dec(x_11);
x_15 = l_List_tail___main___rarg(x_12);
lean::dec(x_12);
x_16 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_16, 0, x_9);
lean::cnstr_set(x_16, 1, x_13);
lean::cnstr_set(x_16, 2, x_14);
lean::cnstr_set(x_16, 3, x_15);
return x_16;
}
}
}
obj* _init_l_Lean_Environment_popScopeCore___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Environment_popScopeCore___lambda__1), 1, 0);
return x_1;
}
}
obj* l_Lean_Environment_popScopeCore(obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
lean::inc(x_1);
x_2 = lean::get_namespaces_core(x_1);
x_3 = l_List_isEmpty___main___rarg(x_2);
lean::dec(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_scopeManagerExt;
x_5 = l_Lean_Environment_popScopeCore___closed__1;
x_6 = l_Lean_SimplePersistentEnvExtension_modifyState___rarg(x_4, x_1, x_5);
return x_6;
}
else
{
return x_1;
}
}
}
obj* initialize_init_lean_environment(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_scopes(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_environment(w);
if (io_result_is_error(w)) return w;
l_Lean_ScopeManagerState_Inhabited___closed__1 = _init_l_Lean_ScopeManagerState_Inhabited___closed__1();
lean::mark_persistent(l_Lean_ScopeManagerState_Inhabited___closed__1);
l_Lean_ScopeManagerState_Inhabited = _init_l_Lean_ScopeManagerState_Inhabited();
lean::mark_persistent(l_Lean_ScopeManagerState_Inhabited);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "ScopeManagerState"), "Inhabited"), l_Lean_ScopeManagerState_Inhabited);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "ScopeManagerState"), "saveNamespace"), 2, l_Lean_ScopeManagerState_saveNamespace);
l_Lean_regScopeManagerExtension___closed__1 = _init_l_Lean_regScopeManagerExtension___closed__1();
lean::mark_persistent(l_Lean_regScopeManagerExtension___closed__1);
l_Lean_regScopeManagerExtension___closed__2 = _init_l_Lean_regScopeManagerExtension___closed__2();
lean::mark_persistent(l_Lean_regScopeManagerExtension___closed__2);
l_Lean_regScopeManagerExtension___closed__3 = _init_l_Lean_regScopeManagerExtension___closed__3();
lean::mark_persistent(l_Lean_regScopeManagerExtension___closed__3);
l_Lean_regScopeManagerExtension___closed__4 = _init_l_Lean_regScopeManagerExtension___closed__4();
lean::mark_persistent(l_Lean_regScopeManagerExtension___closed__4);
l_Lean_regScopeManagerExtension___closed__5 = _init_l_Lean_regScopeManagerExtension___closed__5();
lean::mark_persistent(l_Lean_regScopeManagerExtension___closed__5);
l_Lean_regScopeManagerExtension___closed__6 = _init_l_Lean_regScopeManagerExtension___closed__6();
lean::mark_persistent(l_Lean_regScopeManagerExtension___closed__6);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "regScopeManagerExtension"), 1, l_Lean_regScopeManagerExtension);
l_Lean_scopeManagerExt___elambda__4___closed__1 = _init_l_Lean_scopeManagerExt___elambda__4___closed__1();
lean::mark_persistent(l_Lean_scopeManagerExt___elambda__4___closed__1);
l_Lean_scopeManagerExt___elambda__4___closed__2 = _init_l_Lean_scopeManagerExt___elambda__4___closed__2();
lean::mark_persistent(l_Lean_scopeManagerExt___elambda__4___closed__2);
l_Lean_scopeManagerExt___lambda__1___closed__1 = _init_l_Lean_scopeManagerExt___lambda__1___closed__1();
lean::mark_persistent(l_Lean_scopeManagerExt___lambda__1___closed__1);
l_Lean_scopeManagerExt___closed__1 = _init_l_Lean_scopeManagerExt___closed__1();
lean::mark_persistent(l_Lean_scopeManagerExt___closed__1);
l_Lean_scopeManagerExt___closed__2 = _init_l_Lean_scopeManagerExt___closed__2();
lean::mark_persistent(l_Lean_scopeManagerExt___closed__2);
l_Lean_scopeManagerExt___closed__3 = _init_l_Lean_scopeManagerExt___closed__3();
lean::mark_persistent(l_Lean_scopeManagerExt___closed__3);
l_Lean_scopeManagerExt___closed__4 = _init_l_Lean_scopeManagerExt___closed__4();
lean::mark_persistent(l_Lean_scopeManagerExt___closed__4);
l_Lean_scopeManagerExt___closed__5 = _init_l_Lean_scopeManagerExt___closed__5();
lean::mark_persistent(l_Lean_scopeManagerExt___closed__5);
l_Lean_scopeManagerExt___closed__6 = _init_l_Lean_scopeManagerExt___closed__6();
lean::mark_persistent(l_Lean_scopeManagerExt___closed__6);
l_Lean_scopeManagerExt___closed__7 = _init_l_Lean_scopeManagerExt___closed__7();
lean::mark_persistent(l_Lean_scopeManagerExt___closed__7);
l_Lean_scopeManagerExt___closed__8 = _init_l_Lean_scopeManagerExt___closed__8();
lean::mark_persistent(l_Lean_scopeManagerExt___closed__8);
w = l_Lean_regScopeManagerExtension(w);
if (io_result_is_error(w)) return w;
l_Lean_scopeManagerExt = io_result_get_value(w);
lean::mark_persistent(l_Lean_scopeManagerExt);
lean::register_constant(lean::mk_const_name(lean::mk_const_name("Lean"), "scopeManagerExt"), l_Lean_scopeManagerExt);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Environment"), "getNamespaces"), 1, lean::get_namespaces_core);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Environment"), "getNamespaceSet"), 1, l_Lean_Environment_getNamespaceSet___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Environment"), "isNamespace"), 2, l_Lean_Environment_isNamespace___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Environment"), "inSection"), 1, l_Lean_Environment_inSection___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Environment"), "hasOpenScopes"), 1, l_Lean_Environment_hasOpenScopes___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Environment"), "getNamespace"), 1, lean::get_namespace_core);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Environment"), "getScopeHeader"), 1, lean::get_scope_header_core);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Environment"), "toValidNamespace"), 2, lean::to_valid_namespace_core);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Environment"), "registerNamespaceAux"), 2, l_Lean_Environment_registerNamespaceAux);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Environment"), "registerNamespace"), 2, lean::register_namespace_core);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Environment"), "pushScopeCore"), 3, l_Lean_Environment_pushScopeCore___boxed);
l_Lean_Environment_popScopeCore___closed__1 = _init_l_Lean_Environment_popScopeCore___closed__1();
lean::mark_persistent(l_Lean_Environment_popScopeCore___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Environment"), "popScopeCore"), 1, l_Lean_Environment_popScopeCore);
return w;
}

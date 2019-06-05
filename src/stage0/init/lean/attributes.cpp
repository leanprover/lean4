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
obj* l_AssocList_mfoldl___main___at_Lean_Environment_getAttributeNames___spec__1(obj*, obj*);
obj* l_Lean_attributeArrayRef;
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
extern obj* l_Array_empty___closed__1;
obj* l_Lean_mkAttributeArrayRef(obj*);
obj* l_Lean_Environment_isAttribute___boxed(obj*);
obj* l_Lean_Environment_addScopedAttribute(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mkArray(obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_Environment_toValidNamespace___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_HashMapImp_expand___at_Lean_registerAttribute___spec__4(obj*, obj*);
obj* l_Lean_Environment_activateScopedAttributes(obj*, obj*, obj*);
obj* l_Lean_Environment_popScopeCore___lambda__1(obj*);
obj* l_Lean_scopeManagerExt___elambda__1(obj*);
uint8 l_Lean_Environment_hasOpenScopes(obj*);
uint8 l_HashMapImp_contains___at_Lean_registerAttribute___spec__1(obj*, obj*);
obj* l_Lean_Environment_popScopeCore___closed__1;
obj* l_Lean_Environment_getAttributeNames(obj*);
obj* l_Lean_registerAttribute(obj*, obj*);
obj* l_Lean_Environment_pushScopeCore___lambda__1(obj*, obj*, uint8, obj*);
obj* l_HashMapImp_contains___at_Lean_registerAttribute___spec__1___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_Environment_popScope___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_registerAttribute___closed__2;
namespace lean {
obj* get_namespaces_core(obj*);
}
uint8 l_List_isEmpty___main___rarg(obj*);
obj* l_HashMapImp_find___at_Lean_Environment_getAttributeImpl___spec__1(obj*, obj*);
obj* l_HashMapImp_insert___at_Lean_registerAttribute___spec__3(obj*, obj*, obj*);
obj* l_Lean_Environment_getAttributeImpl___boxed(obj*);
namespace lean {
obj* get_scope_header_core(obj*);
}
obj* l_List_toArrayAux___main___rarg(obj*, obj*);
obj* l_AssocList_find___main___at_Lean_Environment_getAttributeImpl___spec__2(obj*, obj*);
obj* l_Array_uget(obj*, obj*, usize, obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l_Lean_SimplePersistentEnvExtension_getState___rarg(obj*, obj*);
obj* l_Lean_scopeManagerExt;
obj* l_AssocList_mfoldl___main___at_Lean_registerAttribute___spec__6(obj*, obj*);
obj* l_Array_uset(obj*, obj*, usize, obj*, obj*);
obj* l_Lean_ScopeManagerState_Inhabited;
obj* l_List_redLength___main___rarg(obj*);
obj* l_Lean_Environment_registerNamespaceAux(obj*, obj*);
obj* l_IO_Prim_Ref_set(obj*, obj*, obj*, obj*);
namespace lean {
obj* get_namespace_core(obj*);
}
extern "C" obj* lean_io_initializing(obj*);
obj* l_Lean_Environment_getAttributeImpl(obj*);
obj* l_Array_mkEmpty(obj*, obj*);
obj* l_Lean_SimplePersistentEnvExtension_modifyState___rarg(obj*, obj*, obj*);
obj* l_Lean_regScopeManagerExtension___lambda__1(obj*, obj*);
namespace lean {
obj* push_scope_core(obj*, obj*, uint8, obj*);
}
obj* l_Lean_Environment_isAttribute___rarg___boxed(obj*, obj*);
obj* l_Lean_Environment_activateScopedAttribute(obj*, obj*, obj*, obj*);
uint8 l_Lean_NameSet_contains(obj*, obj*);
obj* l_Lean_regScopeManagerExtension___lambda__2___closed__1;
obj* l_Lean_Environment_inSection___boxed(obj*);
obj* l_RBNode_insert___at_Lean_NameSet_insert___spec__1(obj*, obj*, obj*);
obj* l_Lean_regScopeManagerExtension___lambda__2___boxed(obj*);
obj* l_Lean_regScopeManagerExtension(obj*);
extern "C" usize lean_name_hash_usize(obj*);
obj* l_Array_miterateAux___main___at_Lean_regScopeManagerExtension___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Environment_getNamespaceSet(obj*);
extern obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
obj* l_Lean_mkStateFromImportedEntries___at_Lean_regScopeManagerExtension___spec__1___boxed(obj*, obj*);
obj* l_Lean_Environment_pushScope___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_regScopeManagerExtension___spec__3(obj*, obj*, obj*, obj*);
obj* l_Lean_scopeManagerExt___elambda__3___boxed(obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Array_miterateAux___main___at_Lean_regScopeManagerExtension___spec__3___boxed(obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_mkHashMap___at_Lean_mkAttributeMapRef___spec__1(obj*);
obj* l_AssocList_find___main___at_Lean_Environment_getAttributeImpl___spec__2___boxed(obj*, obj*);
extern obj* l_Char_HasRepr___closed__1;
obj* l_Lean_mkAttributeMapRef(obj*);
obj* l_Array_fget(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_registerSimplePersistentEnvExtension___rarg(obj*, obj*);
obj* l_Lean_Environment_addAttribute___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_AssocList_contains___main___at_Lean_registerAttribute___spec__2(obj*, obj*);
obj* l_Lean_Environment_getAttributeNames___rarg(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_Environment_addAttribute(obj*, obj*, obj*, obj*, uint8, obj*);
namespace lean {
uint8 is_namespace_core(obj*, obj*);
}
obj* l_Array_miterateAux___main___at_Lean_Environment_activateScopedAttributes___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Environment_eraseAttribute(obj*, obj*, obj*, uint8, obj*);
obj* l_Array_push(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_Environment_popScope___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_AssocList_mfoldl___main___at_Lean_Environment_getAttributeNames___spec__1___boxed(obj*, obj*);
obj* l_Lean_registerAttribute___closed__1;
obj* l_Array_miterateAux___main___at_Lean_regScopeManagerExtension___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_mkStateFromImportedEntries___at_Lean_regScopeManagerExtension___spec__1(obj*, obj*);
namespace lean {
obj* register_namespace_core(obj*, obj*);
}
obj* l_Lean_regScopeManagerExtension___lambda__2(obj*);
obj* l_IO_Prim_mkRef(obj*, obj*, obj*);
obj* l_Lean_Environment_getAttributeImpl___rarg___closed__1;
obj* l_Lean_scopeManagerExt___elambda__2___boxed(obj*);
obj* l_Array_miterateAux___main___at_Lean_Environment_activateScopedAttributes___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Environment_getAttributeNames___boxed(obj*);
obj* l_Lean_scopeManagerExt___elambda__4___boxed(obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_Environment_toValidNamespace___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_ScopeManagerState_saveNamespace(obj*, obj*);
obj* l_Lean_regScopeManagerExtension___closed__1;
obj* l_HashMapImp_moveEntries___main___at_Lean_registerAttribute___spec__5(obj*, obj*, obj*);
obj* l_Lean_Environment_popScopeCore(obj*);
obj* l_Lean_Environment_getNamespaceSet___boxed(obj*);
obj* l_Lean_PersistentEnvExtension_addEntry___rarg(obj*, obj*, obj*);
obj* l_IO_Prim_Ref_get(obj*, obj*, obj*);
obj* l_Lean_Environment_isAttribute___rarg(obj*, obj*);
obj* l_HashMapImp_find___at_Lean_Environment_getAttributeImpl___spec__1___boxed(obj*, obj*);
namespace lean {
usize usize_modn(usize, obj*);
}
obj* l_Lean_scopeManagerExt___elambda__3(obj*, obj*);
obj* l_Lean_scopeManagerExt___elambda__1___boxed(obj*);
obj* l_Array_miterateAux___main___at_Lean_Environment_pushScope___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_size(obj*, obj*);
obj* l_Array_fset(obj*, obj*, obj*, obj*);
obj* l_mkHashMapImp___rarg(obj*);
obj* l_Lean_Environment_registerNamespace___main(obj*, obj*);
obj* l_AssocList_contains___main___at_Lean_registerAttribute___spec__2___boxed(obj*, obj*);
obj* l_List_tail___main___rarg(obj*);
obj* l_Lean_Environment_getAttributeImpl___rarg(obj*, obj*);
extern obj* l_Lean_Name_toString___closed__1;
obj* l_Lean_Environment_pushScopeCore___boxed(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l_Lean_scopeManagerExt___elambda__2(obj*);
obj* l_Array_miterateAux___main___at_Lean_Environment_pushScope___spec__1(uint8, obj*, obj*, obj*, obj*, obj*, obj*);
namespace lean {
uint8 in_section_core(obj*);
}
obj* l_Lean_Environment_pushScopeCore(obj*, obj*, uint8);
obj* l_AssocList_replace___main___at_Lean_registerAttribute___spec__7(obj*, obj*, obj*);
obj* l_Lean_Environment_isNamespace___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_Environment_getAttributeNames___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_attributeMapRef;
obj* l_Lean_Environment_hasOpenScopes___boxed(obj*);
namespace lean {
obj* pop_scope_core(obj*, obj*);
}
obj* l_Lean_Name_append___main(obj*, obj*);
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l_Lean_Environment_pushScopeCore___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_mkAttributeMapRef___closed__1;
namespace lean {
obj* to_valid_namespace_core(obj*, obj*);
}
obj* l_IO_Prim_Ref_reset(obj*, obj*, obj*);
obj* l_Lean_scopeManagerExt___elambda__4(obj*, obj*, obj*);
obj* l_Lean_Environment_eraseAttribute___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Environment_isAttribute(obj*);
obj* l_Lean_regScopeManagerExtension___lambda__3(obj*);
obj* l_Array_miterateAux___main___at_Lean_Environment_getAttributeNames___spec__2(obj*, obj*, obj*, obj*);
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
uint8 l_Lean_Environment_hasOpenScopes(obj* x_1) {
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
obj* l_Lean_Environment_hasOpenScopes___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_Environment_hasOpenScopes(x_1);
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
switch (lean::obj_tag(x_2)) {
case 0:
{
return x_1;
}
case 1:
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = l_Lean_Environment_registerNamespaceAux(x_1, x_2);
x_1 = x_4;
x_2 = x_3;
goto _start;
}
default: 
{
lean::dec(x_2);
return x_1;
}
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
obj* l_mkHashMap___at_Lean_mkAttributeMapRef___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
obj* _init_l_Lean_mkAttributeMapRef___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
obj* l_Lean_mkAttributeMapRef(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_mkAttributeMapRef___closed__1;
x_3 = lean::io_mk_ref(x_2, x_1);
return x_3;
}
}
obj* l_Lean_mkAttributeArrayRef(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Array_empty___closed__1;
x_3 = lean::io_mk_ref(x_2, x_1);
return x_3;
}
}
uint8 l_AssocList_contains___main___at_Lean_registerAttribute___spec__2(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 2);
x_6 = lean_name_dec_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8 x_8; 
x_8 = 1;
return x_8;
}
}
}
}
uint8 l_HashMapImp_contains___at_Lean_registerAttribute___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; usize x_5; usize x_6; obj* x_7; usize x_8; obj* x_9; uint8 x_10; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::array_get_size(x_3);
x_5 = lean_name_hash_usize(x_2);
x_6 = lean::usize_modn(x_5, x_4);
lean::dec(x_4);
x_7 = lean::box_size_t(x_6);
x_8 = lean::unbox_size_t(x_7);
lean::dec(x_7);
x_9 = lean::array_uget(x_3, x_8);
x_10 = l_AssocList_contains___main___at_Lean_registerAttribute___spec__2(x_2, x_9);
lean::dec(x_9);
return x_10;
}
}
obj* l_AssocList_mfoldl___main___at_Lean_registerAttribute___spec__6(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; usize x_7; usize x_8; obj* x_9; usize x_10; obj* x_11; usize x_12; obj* x_13; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 2);
x_6 = lean::array_get_size(x_1);
x_7 = lean_name_hash_usize(x_4);
x_8 = lean::usize_modn(x_7, x_6);
lean::dec(x_6);
x_9 = lean::box_size_t(x_8);
x_10 = lean::unbox_size_t(x_9);
x_11 = lean::array_uget(x_1, x_10);
lean::cnstr_set(x_2, 2, x_11);
x_12 = lean::unbox_size_t(x_9);
lean::dec(x_9);
x_13 = lean::array_uset(x_1, x_12, x_2);
x_1 = x_13;
x_2 = x_5;
goto _start;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; usize x_19; usize x_20; obj* x_21; usize x_22; obj* x_23; obj* x_24; usize x_25; obj* x_26; 
x_15 = lean::cnstr_get(x_2, 0);
x_16 = lean::cnstr_get(x_2, 1);
x_17 = lean::cnstr_get(x_2, 2);
lean::inc(x_17);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_2);
x_18 = lean::array_get_size(x_1);
x_19 = lean_name_hash_usize(x_15);
x_20 = lean::usize_modn(x_19, x_18);
lean::dec(x_18);
x_21 = lean::box_size_t(x_20);
x_22 = lean::unbox_size_t(x_21);
x_23 = lean::array_uget(x_1, x_22);
x_24 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_24, 0, x_15);
lean::cnstr_set(x_24, 1, x_16);
lean::cnstr_set(x_24, 2, x_23);
x_25 = lean::unbox_size_t(x_21);
lean::dec(x_21);
x_26 = lean::array_uset(x_1, x_25, x_24);
x_1 = x_26;
x_2 = x_17;
goto _start;
}
}
}
}
obj* l_HashMapImp_moveEntries___main___at_Lean_registerAttribute___spec__5(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_2);
x_5 = lean::nat_dec_lt(x_1, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_6 = lean::array_fget(x_2, x_1);
x_7 = lean::box(0);
x_8 = lean::array_fset(x_2, x_1, x_7);
x_9 = l_AssocList_mfoldl___main___at_Lean_registerAttribute___spec__6(x_3, x_6);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_1, x_10);
lean::dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
obj* l_HashMapImp_expand___at_Lean_registerAttribute___spec__4(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_3 = lean::array_get_size(x_2);
x_4 = lean::mk_nat_obj(2u);
x_5 = lean::nat_mul(x_3, x_4);
lean::dec(x_3);
x_6 = lean::box(0);
x_7 = lean::mk_array(x_5, x_6);
x_8 = lean::mk_nat_obj(0u);
x_9 = l_HashMapImp_moveEntries___main___at_Lean_registerAttribute___spec__5(x_8, x_2, x_7);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_AssocList_replace___main___at_Lean_registerAttribute___spec__7(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
x_7 = lean::cnstr_get(x_3, 2);
x_8 = lean_name_dec_eq(x_5, x_1);
if (x_8 == 0)
{
obj* x_9; 
x_9 = l_AssocList_replace___main___at_Lean_registerAttribute___spec__7(x_1, x_2, x_7);
lean::cnstr_set(x_3, 2, x_9);
return x_3;
}
else
{
lean::dec(x_6);
lean::dec(x_5);
lean::cnstr_set(x_3, 1, x_2);
lean::cnstr_set(x_3, 0, x_1);
return x_3;
}
}
else
{
obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_10 = lean::cnstr_get(x_3, 0);
x_11 = lean::cnstr_get(x_3, 1);
x_12 = lean::cnstr_get(x_3, 2);
lean::inc(x_12);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_3);
x_13 = lean_name_dec_eq(x_10, x_1);
if (x_13 == 0)
{
obj* x_14; obj* x_15; 
x_14 = l_AssocList_replace___main___at_Lean_registerAttribute___spec__7(x_1, x_2, x_12);
x_15 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_15, 0, x_10);
lean::cnstr_set(x_15, 1, x_11);
lean::cnstr_set(x_15, 2, x_14);
return x_15;
}
else
{
obj* x_16; 
lean::dec(x_11);
lean::dec(x_10);
x_16 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_16, 0, x_1);
lean::cnstr_set(x_16, 1, x_2);
lean::cnstr_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
obj* l_HashMapImp_insert___at_Lean_registerAttribute___spec__3(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; usize x_8; usize x_9; obj* x_10; usize x_11; obj* x_12; uint8 x_13; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
x_7 = lean::array_get_size(x_6);
x_8 = lean_name_hash_usize(x_2);
x_9 = lean::usize_modn(x_8, x_7);
x_10 = lean::box_size_t(x_9);
x_11 = lean::unbox_size_t(x_10);
x_12 = lean::array_uget(x_6, x_11);
x_13 = l_AssocList_contains___main___at_Lean_registerAttribute___spec__2(x_2, x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; usize x_17; obj* x_18; uint8 x_19; 
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_5, x_14);
lean::dec(x_5);
x_16 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_16, 0, x_2);
lean::cnstr_set(x_16, 1, x_3);
lean::cnstr_set(x_16, 2, x_12);
x_17 = lean::unbox_size_t(x_10);
lean::dec(x_10);
x_18 = lean::array_uset(x_6, x_17, x_16);
x_19 = lean::nat_dec_le(x_15, x_7);
lean::dec(x_7);
if (x_19 == 0)
{
obj* x_20; 
lean::free_heap_obj(x_1);
x_20 = l_HashMapImp_expand___at_Lean_registerAttribute___spec__4(x_15, x_18);
return x_20;
}
else
{
lean::cnstr_set(x_1, 1, x_18);
lean::cnstr_set(x_1, 0, x_15);
return x_1;
}
}
else
{
obj* x_21; usize x_22; obj* x_23; 
lean::dec(x_7);
x_21 = l_AssocList_replace___main___at_Lean_registerAttribute___spec__7(x_2, x_3, x_12);
x_22 = lean::unbox_size_t(x_10);
lean::dec(x_10);
x_23 = lean::array_uset(x_6, x_22, x_21);
lean::cnstr_set(x_1, 1, x_23);
return x_1;
}
}
else
{
obj* x_24; obj* x_25; obj* x_26; usize x_27; usize x_28; obj* x_29; usize x_30; obj* x_31; uint8 x_32; 
x_24 = lean::cnstr_get(x_1, 0);
x_25 = lean::cnstr_get(x_1, 1);
lean::inc(x_25);
lean::inc(x_24);
lean::dec(x_1);
x_26 = lean::array_get_size(x_25);
x_27 = lean_name_hash_usize(x_2);
x_28 = lean::usize_modn(x_27, x_26);
x_29 = lean::box_size_t(x_28);
x_30 = lean::unbox_size_t(x_29);
x_31 = lean::array_uget(x_25, x_30);
x_32 = l_AssocList_contains___main___at_Lean_registerAttribute___spec__2(x_2, x_31);
if (x_32 == 0)
{
obj* x_33; obj* x_34; obj* x_35; usize x_36; obj* x_37; uint8 x_38; 
x_33 = lean::mk_nat_obj(1u);
x_34 = lean::nat_add(x_24, x_33);
lean::dec(x_24);
x_35 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_35, 0, x_2);
lean::cnstr_set(x_35, 1, x_3);
lean::cnstr_set(x_35, 2, x_31);
x_36 = lean::unbox_size_t(x_29);
lean::dec(x_29);
x_37 = lean::array_uset(x_25, x_36, x_35);
x_38 = lean::nat_dec_le(x_34, x_26);
lean::dec(x_26);
if (x_38 == 0)
{
obj* x_39; 
x_39 = l_HashMapImp_expand___at_Lean_registerAttribute___spec__4(x_34, x_37);
return x_39;
}
else
{
obj* x_40; 
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_34);
lean::cnstr_set(x_40, 1, x_37);
return x_40;
}
}
else
{
obj* x_41; usize x_42; obj* x_43; obj* x_44; 
lean::dec(x_26);
x_41 = l_AssocList_replace___main___at_Lean_registerAttribute___spec__7(x_2, x_3, x_31);
x_42 = lean::unbox_size_t(x_29);
lean::dec(x_29);
x_43 = lean::array_uset(x_25, x_42, x_41);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_24);
lean::cnstr_set(x_44, 1, x_43);
return x_44;
}
}
}
}
obj* _init_l_Lean_registerAttribute___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("failed to register attribute, attributes can only be registered during initialization");
return x_1;
}
}
obj* _init_l_Lean_registerAttribute___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("invalid attribute declaration, '");
return x_1;
}
}
obj* l_Lean_registerAttribute(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_attributeMapRef;
x_4 = lean::io_ref_get(x_3, x_2);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_8 = l_HashMapImp_contains___at_Lean_registerAttribute___spec__1(x_6, x_7);
lean::dec(x_6);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::box(0);
lean::cnstr_set(x_4, 0, x_9);
x_10 = lean_io_initializing(x_4);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; uint8 x_12; 
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_12 = lean::unbox(x_11);
lean::dec(x_11);
if (x_12 == 0)
{
uint8 x_13; 
lean::dec(x_7);
lean::dec(x_1);
x_13 = !lean::is_exclusive(x_10);
if (x_13 == 0)
{
obj* x_14; obj* x_15; 
x_14 = lean::cnstr_get(x_10, 0);
lean::dec(x_14);
x_15 = l_Lean_registerAttribute___closed__1;
lean::cnstr_set_tag(x_10, 1);
lean::cnstr_set(x_10, 0, x_15);
return x_10;
}
else
{
obj* x_16; obj* x_17; obj* x_18; 
x_16 = lean::cnstr_get(x_10, 1);
lean::inc(x_16);
lean::dec(x_10);
x_17 = l_Lean_registerAttribute___closed__1;
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8 x_19; 
x_19 = !lean::is_exclusive(x_10);
if (x_19 == 0)
{
obj* x_20; obj* x_21; 
x_20 = lean::cnstr_get(x_10, 0);
lean::dec(x_20);
lean::cnstr_set(x_10, 0, x_9);
x_21 = lean::io_ref_get(x_3, x_10);
if (lean::obj_tag(x_21) == 0)
{
uint8 x_22; 
x_22 = !lean::is_exclusive(x_21);
if (x_22 == 0)
{
obj* x_23; obj* x_24; 
x_23 = lean::cnstr_get(x_21, 0);
lean::cnstr_set(x_21, 0, x_9);
x_24 = lean::io_ref_reset(x_3, x_21);
if (lean::obj_tag(x_24) == 0)
{
uint8 x_25; 
x_25 = !lean::is_exclusive(x_24);
if (x_25 == 0)
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = lean::cnstr_get(x_24, 0);
lean::dec(x_26);
lean::cnstr_set(x_24, 0, x_9);
lean::inc(x_1);
x_27 = l_HashMapImp_insert___at_Lean_registerAttribute___spec__3(x_23, x_7, x_1);
x_28 = lean::io_ref_set(x_3, x_27, x_24);
if (lean::obj_tag(x_28) == 0)
{
uint8 x_29; 
x_29 = !lean::is_exclusive(x_28);
if (x_29 == 0)
{
obj* x_30; obj* x_31; obj* x_32; 
x_30 = lean::cnstr_get(x_28, 0);
lean::dec(x_30);
lean::cnstr_set(x_28, 0, x_9);
x_31 = l_Lean_attributeArrayRef;
x_32 = lean::io_ref_get(x_31, x_28);
if (lean::obj_tag(x_32) == 0)
{
uint8 x_33; 
x_33 = !lean::is_exclusive(x_32);
if (x_33 == 0)
{
obj* x_34; obj* x_35; 
x_34 = lean::cnstr_get(x_32, 0);
lean::cnstr_set(x_32, 0, x_9);
x_35 = lean::io_ref_reset(x_31, x_32);
if (lean::obj_tag(x_35) == 0)
{
uint8 x_36; 
x_36 = !lean::is_exclusive(x_35);
if (x_36 == 0)
{
obj* x_37; obj* x_38; obj* x_39; 
x_37 = lean::cnstr_get(x_35, 0);
lean::dec(x_37);
lean::cnstr_set(x_35, 0, x_9);
x_38 = lean::array_push(x_34, x_1);
x_39 = lean::io_ref_set(x_31, x_38, x_35);
return x_39;
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_40 = lean::cnstr_get(x_35, 1);
lean::inc(x_40);
lean::dec(x_35);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_9);
lean::cnstr_set(x_41, 1, x_40);
x_42 = lean::array_push(x_34, x_1);
x_43 = lean::io_ref_set(x_31, x_42, x_41);
return x_43;
}
}
else
{
uint8 x_44; 
lean::dec(x_34);
lean::dec(x_1);
x_44 = !lean::is_exclusive(x_35);
if (x_44 == 0)
{
return x_35;
}
else
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = lean::cnstr_get(x_35, 0);
x_46 = lean::cnstr_get(x_35, 1);
lean::inc(x_46);
lean::inc(x_45);
lean::dec(x_35);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_48 = lean::cnstr_get(x_32, 0);
x_49 = lean::cnstr_get(x_32, 1);
lean::inc(x_49);
lean::inc(x_48);
lean::dec(x_32);
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_9);
lean::cnstr_set(x_50, 1, x_49);
x_51 = lean::io_ref_reset(x_31, x_50);
if (lean::obj_tag(x_51) == 0)
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_52 = lean::cnstr_get(x_51, 1);
lean::inc(x_52);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_release(x_51, 0);
 lean::cnstr_release(x_51, 1);
 x_53 = x_51;
} else {
 lean::dec_ref(x_51);
 x_53 = lean::box(0);
}
if (lean::is_scalar(x_53)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_53;
}
lean::cnstr_set(x_54, 0, x_9);
lean::cnstr_set(x_54, 1, x_52);
x_55 = lean::array_push(x_48, x_1);
x_56 = lean::io_ref_set(x_31, x_55, x_54);
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_48);
lean::dec(x_1);
x_57 = lean::cnstr_get(x_51, 0);
lean::inc(x_57);
x_58 = lean::cnstr_get(x_51, 1);
lean::inc(x_58);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_release(x_51, 0);
 lean::cnstr_release(x_51, 1);
 x_59 = x_51;
} else {
 lean::dec_ref(x_51);
 x_59 = lean::box(0);
}
if (lean::is_scalar(x_59)) {
 x_60 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_60 = x_59;
}
lean::cnstr_set(x_60, 0, x_57);
lean::cnstr_set(x_60, 1, x_58);
return x_60;
}
}
}
else
{
uint8 x_61; 
lean::dec(x_1);
x_61 = !lean::is_exclusive(x_32);
if (x_61 == 0)
{
return x_32;
}
else
{
obj* x_62; obj* x_63; obj* x_64; 
x_62 = lean::cnstr_get(x_32, 0);
x_63 = lean::cnstr_get(x_32, 1);
lean::inc(x_63);
lean::inc(x_62);
lean::dec(x_32);
x_64 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_64, 0, x_62);
lean::cnstr_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_65 = lean::cnstr_get(x_28, 1);
lean::inc(x_65);
lean::dec(x_28);
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_9);
lean::cnstr_set(x_66, 1, x_65);
x_67 = l_Lean_attributeArrayRef;
x_68 = lean::io_ref_get(x_67, x_66);
if (lean::obj_tag(x_68) == 0)
{
obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
x_69 = lean::cnstr_get(x_68, 0);
lean::inc(x_69);
x_70 = lean::cnstr_get(x_68, 1);
lean::inc(x_70);
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 lean::cnstr_release(x_68, 1);
 x_71 = x_68;
} else {
 lean::dec_ref(x_68);
 x_71 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_71;
}
lean::cnstr_set(x_72, 0, x_9);
lean::cnstr_set(x_72, 1, x_70);
x_73 = lean::io_ref_reset(x_67, x_72);
if (lean::obj_tag(x_73) == 0)
{
obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_74 = lean::cnstr_get(x_73, 1);
lean::inc(x_74);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_release(x_73, 0);
 lean::cnstr_release(x_73, 1);
 x_75 = x_73;
} else {
 lean::dec_ref(x_73);
 x_75 = lean::box(0);
}
if (lean::is_scalar(x_75)) {
 x_76 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_76 = x_75;
}
lean::cnstr_set(x_76, 0, x_9);
lean::cnstr_set(x_76, 1, x_74);
x_77 = lean::array_push(x_69, x_1);
x_78 = lean::io_ref_set(x_67, x_77, x_76);
return x_78;
}
else
{
obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
lean::dec(x_69);
lean::dec(x_1);
x_79 = lean::cnstr_get(x_73, 0);
lean::inc(x_79);
x_80 = lean::cnstr_get(x_73, 1);
lean::inc(x_80);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_release(x_73, 0);
 lean::cnstr_release(x_73, 1);
 x_81 = x_73;
} else {
 lean::dec_ref(x_73);
 x_81 = lean::box(0);
}
if (lean::is_scalar(x_81)) {
 x_82 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_82 = x_81;
}
lean::cnstr_set(x_82, 0, x_79);
lean::cnstr_set(x_82, 1, x_80);
return x_82;
}
}
else
{
obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
lean::dec(x_1);
x_83 = lean::cnstr_get(x_68, 0);
lean::inc(x_83);
x_84 = lean::cnstr_get(x_68, 1);
lean::inc(x_84);
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 lean::cnstr_release(x_68, 1);
 x_85 = x_68;
} else {
 lean::dec_ref(x_68);
 x_85 = lean::box(0);
}
if (lean::is_scalar(x_85)) {
 x_86 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_86 = x_85;
}
lean::cnstr_set(x_86, 0, x_83);
lean::cnstr_set(x_86, 1, x_84);
return x_86;
}
}
}
else
{
uint8 x_87; 
lean::dec(x_1);
x_87 = !lean::is_exclusive(x_28);
if (x_87 == 0)
{
return x_28;
}
else
{
obj* x_88; obj* x_89; obj* x_90; 
x_88 = lean::cnstr_get(x_28, 0);
x_89 = lean::cnstr_get(x_28, 1);
lean::inc(x_89);
lean::inc(x_88);
lean::dec(x_28);
x_90 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_90, 0, x_88);
lean::cnstr_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
x_91 = lean::cnstr_get(x_24, 1);
lean::inc(x_91);
lean::dec(x_24);
x_92 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_92, 0, x_9);
lean::cnstr_set(x_92, 1, x_91);
lean::inc(x_1);
x_93 = l_HashMapImp_insert___at_Lean_registerAttribute___spec__3(x_23, x_7, x_1);
x_94 = lean::io_ref_set(x_3, x_93, x_92);
if (lean::obj_tag(x_94) == 0)
{
obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
x_95 = lean::cnstr_get(x_94, 1);
lean::inc(x_95);
if (lean::is_exclusive(x_94)) {
 lean::cnstr_release(x_94, 0);
 lean::cnstr_release(x_94, 1);
 x_96 = x_94;
} else {
 lean::dec_ref(x_94);
 x_96 = lean::box(0);
}
if (lean::is_scalar(x_96)) {
 x_97 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_97 = x_96;
}
lean::cnstr_set(x_97, 0, x_9);
lean::cnstr_set(x_97, 1, x_95);
x_98 = l_Lean_attributeArrayRef;
x_99 = lean::io_ref_get(x_98, x_97);
if (lean::obj_tag(x_99) == 0)
{
obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
x_100 = lean::cnstr_get(x_99, 0);
lean::inc(x_100);
x_101 = lean::cnstr_get(x_99, 1);
lean::inc(x_101);
if (lean::is_exclusive(x_99)) {
 lean::cnstr_release(x_99, 0);
 lean::cnstr_release(x_99, 1);
 x_102 = x_99;
} else {
 lean::dec_ref(x_99);
 x_102 = lean::box(0);
}
if (lean::is_scalar(x_102)) {
 x_103 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_103 = x_102;
}
lean::cnstr_set(x_103, 0, x_9);
lean::cnstr_set(x_103, 1, x_101);
x_104 = lean::io_ref_reset(x_98, x_103);
if (lean::obj_tag(x_104) == 0)
{
obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
x_105 = lean::cnstr_get(x_104, 1);
lean::inc(x_105);
if (lean::is_exclusive(x_104)) {
 lean::cnstr_release(x_104, 0);
 lean::cnstr_release(x_104, 1);
 x_106 = x_104;
} else {
 lean::dec_ref(x_104);
 x_106 = lean::box(0);
}
if (lean::is_scalar(x_106)) {
 x_107 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_107 = x_106;
}
lean::cnstr_set(x_107, 0, x_9);
lean::cnstr_set(x_107, 1, x_105);
x_108 = lean::array_push(x_100, x_1);
x_109 = lean::io_ref_set(x_98, x_108, x_107);
return x_109;
}
else
{
obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
lean::dec(x_100);
lean::dec(x_1);
x_110 = lean::cnstr_get(x_104, 0);
lean::inc(x_110);
x_111 = lean::cnstr_get(x_104, 1);
lean::inc(x_111);
if (lean::is_exclusive(x_104)) {
 lean::cnstr_release(x_104, 0);
 lean::cnstr_release(x_104, 1);
 x_112 = x_104;
} else {
 lean::dec_ref(x_104);
 x_112 = lean::box(0);
}
if (lean::is_scalar(x_112)) {
 x_113 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_113 = x_112;
}
lean::cnstr_set(x_113, 0, x_110);
lean::cnstr_set(x_113, 1, x_111);
return x_113;
}
}
else
{
obj* x_114; obj* x_115; obj* x_116; obj* x_117; 
lean::dec(x_1);
x_114 = lean::cnstr_get(x_99, 0);
lean::inc(x_114);
x_115 = lean::cnstr_get(x_99, 1);
lean::inc(x_115);
if (lean::is_exclusive(x_99)) {
 lean::cnstr_release(x_99, 0);
 lean::cnstr_release(x_99, 1);
 x_116 = x_99;
} else {
 lean::dec_ref(x_99);
 x_116 = lean::box(0);
}
if (lean::is_scalar(x_116)) {
 x_117 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_117 = x_116;
}
lean::cnstr_set(x_117, 0, x_114);
lean::cnstr_set(x_117, 1, x_115);
return x_117;
}
}
else
{
obj* x_118; obj* x_119; obj* x_120; obj* x_121; 
lean::dec(x_1);
x_118 = lean::cnstr_get(x_94, 0);
lean::inc(x_118);
x_119 = lean::cnstr_get(x_94, 1);
lean::inc(x_119);
if (lean::is_exclusive(x_94)) {
 lean::cnstr_release(x_94, 0);
 lean::cnstr_release(x_94, 1);
 x_120 = x_94;
} else {
 lean::dec_ref(x_94);
 x_120 = lean::box(0);
}
if (lean::is_scalar(x_120)) {
 x_121 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_121 = x_120;
}
lean::cnstr_set(x_121, 0, x_118);
lean::cnstr_set(x_121, 1, x_119);
return x_121;
}
}
}
else
{
uint8 x_122; 
lean::dec(x_23);
lean::dec(x_7);
lean::dec(x_1);
x_122 = !lean::is_exclusive(x_24);
if (x_122 == 0)
{
return x_24;
}
else
{
obj* x_123; obj* x_124; obj* x_125; 
x_123 = lean::cnstr_get(x_24, 0);
x_124 = lean::cnstr_get(x_24, 1);
lean::inc(x_124);
lean::inc(x_123);
lean::dec(x_24);
x_125 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_125, 0, x_123);
lean::cnstr_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
obj* x_126; obj* x_127; obj* x_128; obj* x_129; 
x_126 = lean::cnstr_get(x_21, 0);
x_127 = lean::cnstr_get(x_21, 1);
lean::inc(x_127);
lean::inc(x_126);
lean::dec(x_21);
x_128 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_128, 0, x_9);
lean::cnstr_set(x_128, 1, x_127);
x_129 = lean::io_ref_reset(x_3, x_128);
if (lean::obj_tag(x_129) == 0)
{
obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
x_130 = lean::cnstr_get(x_129, 1);
lean::inc(x_130);
if (lean::is_exclusive(x_129)) {
 lean::cnstr_release(x_129, 0);
 lean::cnstr_release(x_129, 1);
 x_131 = x_129;
} else {
 lean::dec_ref(x_129);
 x_131 = lean::box(0);
}
if (lean::is_scalar(x_131)) {
 x_132 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_132 = x_131;
}
lean::cnstr_set(x_132, 0, x_9);
lean::cnstr_set(x_132, 1, x_130);
lean::inc(x_1);
x_133 = l_HashMapImp_insert___at_Lean_registerAttribute___spec__3(x_126, x_7, x_1);
x_134 = lean::io_ref_set(x_3, x_133, x_132);
if (lean::obj_tag(x_134) == 0)
{
obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; 
x_135 = lean::cnstr_get(x_134, 1);
lean::inc(x_135);
if (lean::is_exclusive(x_134)) {
 lean::cnstr_release(x_134, 0);
 lean::cnstr_release(x_134, 1);
 x_136 = x_134;
} else {
 lean::dec_ref(x_134);
 x_136 = lean::box(0);
}
if (lean::is_scalar(x_136)) {
 x_137 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_137 = x_136;
}
lean::cnstr_set(x_137, 0, x_9);
lean::cnstr_set(x_137, 1, x_135);
x_138 = l_Lean_attributeArrayRef;
x_139 = lean::io_ref_get(x_138, x_137);
if (lean::obj_tag(x_139) == 0)
{
obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; 
x_140 = lean::cnstr_get(x_139, 0);
lean::inc(x_140);
x_141 = lean::cnstr_get(x_139, 1);
lean::inc(x_141);
if (lean::is_exclusive(x_139)) {
 lean::cnstr_release(x_139, 0);
 lean::cnstr_release(x_139, 1);
 x_142 = x_139;
} else {
 lean::dec_ref(x_139);
 x_142 = lean::box(0);
}
if (lean::is_scalar(x_142)) {
 x_143 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_143 = x_142;
}
lean::cnstr_set(x_143, 0, x_9);
lean::cnstr_set(x_143, 1, x_141);
x_144 = lean::io_ref_reset(x_138, x_143);
if (lean::obj_tag(x_144) == 0)
{
obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; 
x_145 = lean::cnstr_get(x_144, 1);
lean::inc(x_145);
if (lean::is_exclusive(x_144)) {
 lean::cnstr_release(x_144, 0);
 lean::cnstr_release(x_144, 1);
 x_146 = x_144;
} else {
 lean::dec_ref(x_144);
 x_146 = lean::box(0);
}
if (lean::is_scalar(x_146)) {
 x_147 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_147 = x_146;
}
lean::cnstr_set(x_147, 0, x_9);
lean::cnstr_set(x_147, 1, x_145);
x_148 = lean::array_push(x_140, x_1);
x_149 = lean::io_ref_set(x_138, x_148, x_147);
return x_149;
}
else
{
obj* x_150; obj* x_151; obj* x_152; obj* x_153; 
lean::dec(x_140);
lean::dec(x_1);
x_150 = lean::cnstr_get(x_144, 0);
lean::inc(x_150);
x_151 = lean::cnstr_get(x_144, 1);
lean::inc(x_151);
if (lean::is_exclusive(x_144)) {
 lean::cnstr_release(x_144, 0);
 lean::cnstr_release(x_144, 1);
 x_152 = x_144;
} else {
 lean::dec_ref(x_144);
 x_152 = lean::box(0);
}
if (lean::is_scalar(x_152)) {
 x_153 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_153 = x_152;
}
lean::cnstr_set(x_153, 0, x_150);
lean::cnstr_set(x_153, 1, x_151);
return x_153;
}
}
else
{
obj* x_154; obj* x_155; obj* x_156; obj* x_157; 
lean::dec(x_1);
x_154 = lean::cnstr_get(x_139, 0);
lean::inc(x_154);
x_155 = lean::cnstr_get(x_139, 1);
lean::inc(x_155);
if (lean::is_exclusive(x_139)) {
 lean::cnstr_release(x_139, 0);
 lean::cnstr_release(x_139, 1);
 x_156 = x_139;
} else {
 lean::dec_ref(x_139);
 x_156 = lean::box(0);
}
if (lean::is_scalar(x_156)) {
 x_157 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_157 = x_156;
}
lean::cnstr_set(x_157, 0, x_154);
lean::cnstr_set(x_157, 1, x_155);
return x_157;
}
}
else
{
obj* x_158; obj* x_159; obj* x_160; obj* x_161; 
lean::dec(x_1);
x_158 = lean::cnstr_get(x_134, 0);
lean::inc(x_158);
x_159 = lean::cnstr_get(x_134, 1);
lean::inc(x_159);
if (lean::is_exclusive(x_134)) {
 lean::cnstr_release(x_134, 0);
 lean::cnstr_release(x_134, 1);
 x_160 = x_134;
} else {
 lean::dec_ref(x_134);
 x_160 = lean::box(0);
}
if (lean::is_scalar(x_160)) {
 x_161 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_161 = x_160;
}
lean::cnstr_set(x_161, 0, x_158);
lean::cnstr_set(x_161, 1, x_159);
return x_161;
}
}
else
{
obj* x_162; obj* x_163; obj* x_164; obj* x_165; 
lean::dec(x_126);
lean::dec(x_7);
lean::dec(x_1);
x_162 = lean::cnstr_get(x_129, 0);
lean::inc(x_162);
x_163 = lean::cnstr_get(x_129, 1);
lean::inc(x_163);
if (lean::is_exclusive(x_129)) {
 lean::cnstr_release(x_129, 0);
 lean::cnstr_release(x_129, 1);
 x_164 = x_129;
} else {
 lean::dec_ref(x_129);
 x_164 = lean::box(0);
}
if (lean::is_scalar(x_164)) {
 x_165 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_165 = x_164;
}
lean::cnstr_set(x_165, 0, x_162);
lean::cnstr_set(x_165, 1, x_163);
return x_165;
}
}
}
else
{
uint8 x_166; 
lean::dec(x_7);
lean::dec(x_1);
x_166 = !lean::is_exclusive(x_21);
if (x_166 == 0)
{
return x_21;
}
else
{
obj* x_167; obj* x_168; obj* x_169; 
x_167 = lean::cnstr_get(x_21, 0);
x_168 = lean::cnstr_get(x_21, 1);
lean::inc(x_168);
lean::inc(x_167);
lean::dec(x_21);
x_169 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_169, 0, x_167);
lean::cnstr_set(x_169, 1, x_168);
return x_169;
}
}
}
else
{
obj* x_170; obj* x_171; obj* x_172; 
x_170 = lean::cnstr_get(x_10, 1);
lean::inc(x_170);
lean::dec(x_10);
x_171 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_171, 0, x_9);
lean::cnstr_set(x_171, 1, x_170);
x_172 = lean::io_ref_get(x_3, x_171);
if (lean::obj_tag(x_172) == 0)
{
obj* x_173; obj* x_174; obj* x_175; obj* x_176; obj* x_177; 
x_173 = lean::cnstr_get(x_172, 0);
lean::inc(x_173);
x_174 = lean::cnstr_get(x_172, 1);
lean::inc(x_174);
if (lean::is_exclusive(x_172)) {
 lean::cnstr_release(x_172, 0);
 lean::cnstr_release(x_172, 1);
 x_175 = x_172;
} else {
 lean::dec_ref(x_172);
 x_175 = lean::box(0);
}
if (lean::is_scalar(x_175)) {
 x_176 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_176 = x_175;
}
lean::cnstr_set(x_176, 0, x_9);
lean::cnstr_set(x_176, 1, x_174);
x_177 = lean::io_ref_reset(x_3, x_176);
if (lean::obj_tag(x_177) == 0)
{
obj* x_178; obj* x_179; obj* x_180; obj* x_181; obj* x_182; 
x_178 = lean::cnstr_get(x_177, 1);
lean::inc(x_178);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 x_179 = x_177;
} else {
 lean::dec_ref(x_177);
 x_179 = lean::box(0);
}
if (lean::is_scalar(x_179)) {
 x_180 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_180 = x_179;
}
lean::cnstr_set(x_180, 0, x_9);
lean::cnstr_set(x_180, 1, x_178);
lean::inc(x_1);
x_181 = l_HashMapImp_insert___at_Lean_registerAttribute___spec__3(x_173, x_7, x_1);
x_182 = lean::io_ref_set(x_3, x_181, x_180);
if (lean::obj_tag(x_182) == 0)
{
obj* x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; 
x_183 = lean::cnstr_get(x_182, 1);
lean::inc(x_183);
if (lean::is_exclusive(x_182)) {
 lean::cnstr_release(x_182, 0);
 lean::cnstr_release(x_182, 1);
 x_184 = x_182;
} else {
 lean::dec_ref(x_182);
 x_184 = lean::box(0);
}
if (lean::is_scalar(x_184)) {
 x_185 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_185 = x_184;
}
lean::cnstr_set(x_185, 0, x_9);
lean::cnstr_set(x_185, 1, x_183);
x_186 = l_Lean_attributeArrayRef;
x_187 = lean::io_ref_get(x_186, x_185);
if (lean::obj_tag(x_187) == 0)
{
obj* x_188; obj* x_189; obj* x_190; obj* x_191; obj* x_192; 
x_188 = lean::cnstr_get(x_187, 0);
lean::inc(x_188);
x_189 = lean::cnstr_get(x_187, 1);
lean::inc(x_189);
if (lean::is_exclusive(x_187)) {
 lean::cnstr_release(x_187, 0);
 lean::cnstr_release(x_187, 1);
 x_190 = x_187;
} else {
 lean::dec_ref(x_187);
 x_190 = lean::box(0);
}
if (lean::is_scalar(x_190)) {
 x_191 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_191 = x_190;
}
lean::cnstr_set(x_191, 0, x_9);
lean::cnstr_set(x_191, 1, x_189);
x_192 = lean::io_ref_reset(x_186, x_191);
if (lean::obj_tag(x_192) == 0)
{
obj* x_193; obj* x_194; obj* x_195; obj* x_196; obj* x_197; 
x_193 = lean::cnstr_get(x_192, 1);
lean::inc(x_193);
if (lean::is_exclusive(x_192)) {
 lean::cnstr_release(x_192, 0);
 lean::cnstr_release(x_192, 1);
 x_194 = x_192;
} else {
 lean::dec_ref(x_192);
 x_194 = lean::box(0);
}
if (lean::is_scalar(x_194)) {
 x_195 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_195 = x_194;
}
lean::cnstr_set(x_195, 0, x_9);
lean::cnstr_set(x_195, 1, x_193);
x_196 = lean::array_push(x_188, x_1);
x_197 = lean::io_ref_set(x_186, x_196, x_195);
return x_197;
}
else
{
obj* x_198; obj* x_199; obj* x_200; obj* x_201; 
lean::dec(x_188);
lean::dec(x_1);
x_198 = lean::cnstr_get(x_192, 0);
lean::inc(x_198);
x_199 = lean::cnstr_get(x_192, 1);
lean::inc(x_199);
if (lean::is_exclusive(x_192)) {
 lean::cnstr_release(x_192, 0);
 lean::cnstr_release(x_192, 1);
 x_200 = x_192;
} else {
 lean::dec_ref(x_192);
 x_200 = lean::box(0);
}
if (lean::is_scalar(x_200)) {
 x_201 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_201 = x_200;
}
lean::cnstr_set(x_201, 0, x_198);
lean::cnstr_set(x_201, 1, x_199);
return x_201;
}
}
else
{
obj* x_202; obj* x_203; obj* x_204; obj* x_205; 
lean::dec(x_1);
x_202 = lean::cnstr_get(x_187, 0);
lean::inc(x_202);
x_203 = lean::cnstr_get(x_187, 1);
lean::inc(x_203);
if (lean::is_exclusive(x_187)) {
 lean::cnstr_release(x_187, 0);
 lean::cnstr_release(x_187, 1);
 x_204 = x_187;
} else {
 lean::dec_ref(x_187);
 x_204 = lean::box(0);
}
if (lean::is_scalar(x_204)) {
 x_205 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_205 = x_204;
}
lean::cnstr_set(x_205, 0, x_202);
lean::cnstr_set(x_205, 1, x_203);
return x_205;
}
}
else
{
obj* x_206; obj* x_207; obj* x_208; obj* x_209; 
lean::dec(x_1);
x_206 = lean::cnstr_get(x_182, 0);
lean::inc(x_206);
x_207 = lean::cnstr_get(x_182, 1);
lean::inc(x_207);
if (lean::is_exclusive(x_182)) {
 lean::cnstr_release(x_182, 0);
 lean::cnstr_release(x_182, 1);
 x_208 = x_182;
} else {
 lean::dec_ref(x_182);
 x_208 = lean::box(0);
}
if (lean::is_scalar(x_208)) {
 x_209 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_209 = x_208;
}
lean::cnstr_set(x_209, 0, x_206);
lean::cnstr_set(x_209, 1, x_207);
return x_209;
}
}
else
{
obj* x_210; obj* x_211; obj* x_212; obj* x_213; 
lean::dec(x_173);
lean::dec(x_7);
lean::dec(x_1);
x_210 = lean::cnstr_get(x_177, 0);
lean::inc(x_210);
x_211 = lean::cnstr_get(x_177, 1);
lean::inc(x_211);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 x_212 = x_177;
} else {
 lean::dec_ref(x_177);
 x_212 = lean::box(0);
}
if (lean::is_scalar(x_212)) {
 x_213 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_213 = x_212;
}
lean::cnstr_set(x_213, 0, x_210);
lean::cnstr_set(x_213, 1, x_211);
return x_213;
}
}
else
{
obj* x_214; obj* x_215; obj* x_216; obj* x_217; 
lean::dec(x_7);
lean::dec(x_1);
x_214 = lean::cnstr_get(x_172, 0);
lean::inc(x_214);
x_215 = lean::cnstr_get(x_172, 1);
lean::inc(x_215);
if (lean::is_exclusive(x_172)) {
 lean::cnstr_release(x_172, 0);
 lean::cnstr_release(x_172, 1);
 x_216 = x_172;
} else {
 lean::dec_ref(x_172);
 x_216 = lean::box(0);
}
if (lean::is_scalar(x_216)) {
 x_217 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_217 = x_216;
}
lean::cnstr_set(x_217, 0, x_214);
lean::cnstr_set(x_217, 1, x_215);
return x_217;
}
}
}
}
else
{
uint8 x_218; 
lean::dec(x_7);
lean::dec(x_1);
x_218 = !lean::is_exclusive(x_10);
if (x_218 == 0)
{
return x_10;
}
else
{
obj* x_219; obj* x_220; obj* x_221; 
x_219 = lean::cnstr_get(x_10, 0);
x_220 = lean::cnstr_get(x_10, 1);
lean::inc(x_220);
lean::inc(x_219);
lean::dec(x_10);
x_221 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_221, 0, x_219);
lean::cnstr_set(x_221, 1, x_220);
return x_221;
}
}
}
else
{
obj* x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; 
lean::dec(x_1);
x_222 = l_Lean_Name_toString___closed__1;
x_223 = l_Lean_Name_toStringWithSep___main(x_222, x_7);
x_224 = l_Lean_registerAttribute___closed__2;
x_225 = lean::string_append(x_224, x_223);
lean::dec(x_223);
x_226 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_227 = lean::string_append(x_225, x_226);
lean::cnstr_set_tag(x_4, 1);
lean::cnstr_set(x_4, 0, x_227);
return x_4;
}
}
else
{
obj* x_228; obj* x_229; obj* x_230; uint8 x_231; 
x_228 = lean::cnstr_get(x_4, 0);
x_229 = lean::cnstr_get(x_4, 1);
lean::inc(x_229);
lean::inc(x_228);
lean::dec(x_4);
x_230 = lean::cnstr_get(x_1, 0);
lean::inc(x_230);
x_231 = l_HashMapImp_contains___at_Lean_registerAttribute___spec__1(x_228, x_230);
lean::dec(x_228);
if (x_231 == 0)
{
obj* x_232; obj* x_233; obj* x_234; 
x_232 = lean::box(0);
x_233 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_233, 0, x_232);
lean::cnstr_set(x_233, 1, x_229);
x_234 = lean_io_initializing(x_233);
if (lean::obj_tag(x_234) == 0)
{
obj* x_235; uint8 x_236; 
x_235 = lean::cnstr_get(x_234, 0);
lean::inc(x_235);
x_236 = lean::unbox(x_235);
lean::dec(x_235);
if (x_236 == 0)
{
obj* x_237; obj* x_238; obj* x_239; obj* x_240; 
lean::dec(x_230);
lean::dec(x_1);
x_237 = lean::cnstr_get(x_234, 1);
lean::inc(x_237);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 x_238 = x_234;
} else {
 lean::dec_ref(x_234);
 x_238 = lean::box(0);
}
x_239 = l_Lean_registerAttribute___closed__1;
if (lean::is_scalar(x_238)) {
 x_240 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_240 = x_238;
 lean::cnstr_set_tag(x_240, 1);
}
lean::cnstr_set(x_240, 0, x_239);
lean::cnstr_set(x_240, 1, x_237);
return x_240;
}
else
{
obj* x_241; obj* x_242; obj* x_243; obj* x_244; 
x_241 = lean::cnstr_get(x_234, 1);
lean::inc(x_241);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 x_242 = x_234;
} else {
 lean::dec_ref(x_234);
 x_242 = lean::box(0);
}
if (lean::is_scalar(x_242)) {
 x_243 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_243 = x_242;
}
lean::cnstr_set(x_243, 0, x_232);
lean::cnstr_set(x_243, 1, x_241);
x_244 = lean::io_ref_get(x_3, x_243);
if (lean::obj_tag(x_244) == 0)
{
obj* x_245; obj* x_246; obj* x_247; obj* x_248; obj* x_249; 
x_245 = lean::cnstr_get(x_244, 0);
lean::inc(x_245);
x_246 = lean::cnstr_get(x_244, 1);
lean::inc(x_246);
if (lean::is_exclusive(x_244)) {
 lean::cnstr_release(x_244, 0);
 lean::cnstr_release(x_244, 1);
 x_247 = x_244;
} else {
 lean::dec_ref(x_244);
 x_247 = lean::box(0);
}
if (lean::is_scalar(x_247)) {
 x_248 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_248 = x_247;
}
lean::cnstr_set(x_248, 0, x_232);
lean::cnstr_set(x_248, 1, x_246);
x_249 = lean::io_ref_reset(x_3, x_248);
if (lean::obj_tag(x_249) == 0)
{
obj* x_250; obj* x_251; obj* x_252; obj* x_253; obj* x_254; 
x_250 = lean::cnstr_get(x_249, 1);
lean::inc(x_250);
if (lean::is_exclusive(x_249)) {
 lean::cnstr_release(x_249, 0);
 lean::cnstr_release(x_249, 1);
 x_251 = x_249;
} else {
 lean::dec_ref(x_249);
 x_251 = lean::box(0);
}
if (lean::is_scalar(x_251)) {
 x_252 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_252 = x_251;
}
lean::cnstr_set(x_252, 0, x_232);
lean::cnstr_set(x_252, 1, x_250);
lean::inc(x_1);
x_253 = l_HashMapImp_insert___at_Lean_registerAttribute___spec__3(x_245, x_230, x_1);
x_254 = lean::io_ref_set(x_3, x_253, x_252);
if (lean::obj_tag(x_254) == 0)
{
obj* x_255; obj* x_256; obj* x_257; obj* x_258; obj* x_259; 
x_255 = lean::cnstr_get(x_254, 1);
lean::inc(x_255);
if (lean::is_exclusive(x_254)) {
 lean::cnstr_release(x_254, 0);
 lean::cnstr_release(x_254, 1);
 x_256 = x_254;
} else {
 lean::dec_ref(x_254);
 x_256 = lean::box(0);
}
if (lean::is_scalar(x_256)) {
 x_257 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_257 = x_256;
}
lean::cnstr_set(x_257, 0, x_232);
lean::cnstr_set(x_257, 1, x_255);
x_258 = l_Lean_attributeArrayRef;
x_259 = lean::io_ref_get(x_258, x_257);
if (lean::obj_tag(x_259) == 0)
{
obj* x_260; obj* x_261; obj* x_262; obj* x_263; obj* x_264; 
x_260 = lean::cnstr_get(x_259, 0);
lean::inc(x_260);
x_261 = lean::cnstr_get(x_259, 1);
lean::inc(x_261);
if (lean::is_exclusive(x_259)) {
 lean::cnstr_release(x_259, 0);
 lean::cnstr_release(x_259, 1);
 x_262 = x_259;
} else {
 lean::dec_ref(x_259);
 x_262 = lean::box(0);
}
if (lean::is_scalar(x_262)) {
 x_263 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_263 = x_262;
}
lean::cnstr_set(x_263, 0, x_232);
lean::cnstr_set(x_263, 1, x_261);
x_264 = lean::io_ref_reset(x_258, x_263);
if (lean::obj_tag(x_264) == 0)
{
obj* x_265; obj* x_266; obj* x_267; obj* x_268; obj* x_269; 
x_265 = lean::cnstr_get(x_264, 1);
lean::inc(x_265);
if (lean::is_exclusive(x_264)) {
 lean::cnstr_release(x_264, 0);
 lean::cnstr_release(x_264, 1);
 x_266 = x_264;
} else {
 lean::dec_ref(x_264);
 x_266 = lean::box(0);
}
if (lean::is_scalar(x_266)) {
 x_267 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_267 = x_266;
}
lean::cnstr_set(x_267, 0, x_232);
lean::cnstr_set(x_267, 1, x_265);
x_268 = lean::array_push(x_260, x_1);
x_269 = lean::io_ref_set(x_258, x_268, x_267);
return x_269;
}
else
{
obj* x_270; obj* x_271; obj* x_272; obj* x_273; 
lean::dec(x_260);
lean::dec(x_1);
x_270 = lean::cnstr_get(x_264, 0);
lean::inc(x_270);
x_271 = lean::cnstr_get(x_264, 1);
lean::inc(x_271);
if (lean::is_exclusive(x_264)) {
 lean::cnstr_release(x_264, 0);
 lean::cnstr_release(x_264, 1);
 x_272 = x_264;
} else {
 lean::dec_ref(x_264);
 x_272 = lean::box(0);
}
if (lean::is_scalar(x_272)) {
 x_273 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_273 = x_272;
}
lean::cnstr_set(x_273, 0, x_270);
lean::cnstr_set(x_273, 1, x_271);
return x_273;
}
}
else
{
obj* x_274; obj* x_275; obj* x_276; obj* x_277; 
lean::dec(x_1);
x_274 = lean::cnstr_get(x_259, 0);
lean::inc(x_274);
x_275 = lean::cnstr_get(x_259, 1);
lean::inc(x_275);
if (lean::is_exclusive(x_259)) {
 lean::cnstr_release(x_259, 0);
 lean::cnstr_release(x_259, 1);
 x_276 = x_259;
} else {
 lean::dec_ref(x_259);
 x_276 = lean::box(0);
}
if (lean::is_scalar(x_276)) {
 x_277 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_277 = x_276;
}
lean::cnstr_set(x_277, 0, x_274);
lean::cnstr_set(x_277, 1, x_275);
return x_277;
}
}
else
{
obj* x_278; obj* x_279; obj* x_280; obj* x_281; 
lean::dec(x_1);
x_278 = lean::cnstr_get(x_254, 0);
lean::inc(x_278);
x_279 = lean::cnstr_get(x_254, 1);
lean::inc(x_279);
if (lean::is_exclusive(x_254)) {
 lean::cnstr_release(x_254, 0);
 lean::cnstr_release(x_254, 1);
 x_280 = x_254;
} else {
 lean::dec_ref(x_254);
 x_280 = lean::box(0);
}
if (lean::is_scalar(x_280)) {
 x_281 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_281 = x_280;
}
lean::cnstr_set(x_281, 0, x_278);
lean::cnstr_set(x_281, 1, x_279);
return x_281;
}
}
else
{
obj* x_282; obj* x_283; obj* x_284; obj* x_285; 
lean::dec(x_245);
lean::dec(x_230);
lean::dec(x_1);
x_282 = lean::cnstr_get(x_249, 0);
lean::inc(x_282);
x_283 = lean::cnstr_get(x_249, 1);
lean::inc(x_283);
if (lean::is_exclusive(x_249)) {
 lean::cnstr_release(x_249, 0);
 lean::cnstr_release(x_249, 1);
 x_284 = x_249;
} else {
 lean::dec_ref(x_249);
 x_284 = lean::box(0);
}
if (lean::is_scalar(x_284)) {
 x_285 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_285 = x_284;
}
lean::cnstr_set(x_285, 0, x_282);
lean::cnstr_set(x_285, 1, x_283);
return x_285;
}
}
else
{
obj* x_286; obj* x_287; obj* x_288; obj* x_289; 
lean::dec(x_230);
lean::dec(x_1);
x_286 = lean::cnstr_get(x_244, 0);
lean::inc(x_286);
x_287 = lean::cnstr_get(x_244, 1);
lean::inc(x_287);
if (lean::is_exclusive(x_244)) {
 lean::cnstr_release(x_244, 0);
 lean::cnstr_release(x_244, 1);
 x_288 = x_244;
} else {
 lean::dec_ref(x_244);
 x_288 = lean::box(0);
}
if (lean::is_scalar(x_288)) {
 x_289 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_289 = x_288;
}
lean::cnstr_set(x_289, 0, x_286);
lean::cnstr_set(x_289, 1, x_287);
return x_289;
}
}
}
else
{
obj* x_290; obj* x_291; obj* x_292; obj* x_293; 
lean::dec(x_230);
lean::dec(x_1);
x_290 = lean::cnstr_get(x_234, 0);
lean::inc(x_290);
x_291 = lean::cnstr_get(x_234, 1);
lean::inc(x_291);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 x_292 = x_234;
} else {
 lean::dec_ref(x_234);
 x_292 = lean::box(0);
}
if (lean::is_scalar(x_292)) {
 x_293 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_293 = x_292;
}
lean::cnstr_set(x_293, 0, x_290);
lean::cnstr_set(x_293, 1, x_291);
return x_293;
}
}
else
{
obj* x_294; obj* x_295; obj* x_296; obj* x_297; obj* x_298; obj* x_299; obj* x_300; 
lean::dec(x_1);
x_294 = l_Lean_Name_toString___closed__1;
x_295 = l_Lean_Name_toStringWithSep___main(x_294, x_230);
x_296 = l_Lean_registerAttribute___closed__2;
x_297 = lean::string_append(x_296, x_295);
lean::dec(x_295);
x_298 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_299 = lean::string_append(x_297, x_298);
x_300 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_300, 0, x_299);
lean::cnstr_set(x_300, 1, x_229);
return x_300;
}
}
}
else
{
uint8 x_301; 
lean::dec(x_1);
x_301 = !lean::is_exclusive(x_4);
if (x_301 == 0)
{
return x_4;
}
else
{
obj* x_302; obj* x_303; obj* x_304; 
x_302 = lean::cnstr_get(x_4, 0);
x_303 = lean::cnstr_get(x_4, 1);
lean::inc(x_303);
lean::inc(x_302);
lean::dec(x_4);
x_304 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_304, 0, x_302);
lean::cnstr_set(x_304, 1, x_303);
return x_304;
}
}
}
}
obj* l_AssocList_contains___main___at_Lean_registerAttribute___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_registerAttribute___spec__2(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_HashMapImp_contains___at_Lean_registerAttribute___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_HashMapImp_contains___at_Lean_registerAttribute___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Lean_Environment_isAttribute___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_attributeMapRef;
x_4 = lean::io_ref_get(x_3, x_2);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; uint8 x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_4, 0);
x_7 = l_HashMapImp_contains___at_Lean_registerAttribute___spec__1(x_6, x_1);
lean::dec(x_6);
x_8 = lean::box(x_7);
lean::cnstr_set(x_4, 0, x_8);
return x_4;
}
else
{
obj* x_9; obj* x_10; uint8 x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_4, 0);
x_10 = lean::cnstr_get(x_4, 1);
lean::inc(x_10);
lean::inc(x_9);
lean::dec(x_4);
x_11 = l_HashMapImp_contains___at_Lean_registerAttribute___spec__1(x_9, x_1);
lean::dec(x_9);
x_12 = lean::box(x_11);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_10);
return x_13;
}
}
else
{
uint8 x_14; 
x_14 = !lean::is_exclusive(x_4);
if (x_14 == 0)
{
return x_4;
}
else
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean::cnstr_get(x_4, 0);
x_16 = lean::cnstr_get(x_4, 1);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_4);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
}
obj* l_Lean_Environment_isAttribute(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Environment_isAttribute___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Lean_Environment_isAttribute___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Environment_isAttribute___rarg(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Environment_isAttribute___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Environment_isAttribute(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_AssocList_mfoldl___main___at_Lean_Environment_getAttributeNames___spec__1(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean::cnstr_get(x_2, 2);
lean::inc(x_3);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_1);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_Lean_Environment_getAttributeNames___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
x_8 = l_AssocList_mfoldl___main___at_Lean_Environment_getAttributeNames___spec__1(x_4, x_7);
lean::dec(x_7);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_add(x_3, x_9);
lean::dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
obj* l_Lean_Environment_getAttributeNames___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_attributeMapRef;
x_3 = lean::io_ref_get(x_2, x_1);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::box(0);
x_7 = lean::cnstr_get(x_5, 1);
lean::inc(x_7);
x_8 = lean::mk_nat_obj(0u);
x_9 = l_Array_miterateAux___main___at_Lean_Environment_getAttributeNames___spec__2(x_5, x_7, x_8, x_6);
lean::dec(x_7);
lean::dec(x_5);
lean::cnstr_set(x_3, 0, x_9);
return x_3;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_10 = lean::cnstr_get(x_3, 0);
x_11 = lean::cnstr_get(x_3, 1);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_3);
x_12 = lean::box(0);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
x_14 = lean::mk_nat_obj(0u);
x_15 = l_Array_miterateAux___main___at_Lean_Environment_getAttributeNames___spec__2(x_10, x_13, x_14, x_12);
lean::dec(x_13);
lean::dec(x_10);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_11);
return x_16;
}
}
else
{
uint8 x_17; 
x_17 = !lean::is_exclusive(x_3);
if (x_17 == 0)
{
return x_3;
}
else
{
obj* x_18; obj* x_19; obj* x_20; 
x_18 = lean::cnstr_get(x_3, 0);
x_19 = lean::cnstr_get(x_3, 1);
lean::inc(x_19);
lean::inc(x_18);
lean::dec(x_3);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
}
}
obj* l_Lean_Environment_getAttributeNames(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Environment_getAttributeNames___rarg), 1, 0);
return x_2;
}
}
obj* l_AssocList_mfoldl___main___at_Lean_Environment_getAttributeNames___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_AssocList_mfoldl___main___at_Lean_Environment_getAttributeNames___spec__1(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Lean_Environment_getAttributeNames___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_Environment_getAttributeNames___spec__2(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Environment_getAttributeNames___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Environment_getAttributeNames(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_AssocList_find___main___at_Lean_Environment_getAttributeImpl___spec__2(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
x_6 = lean::cnstr_get(x_2, 2);
x_7 = lean_name_dec_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
obj* x_9; 
lean::inc(x_5);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_5);
return x_9;
}
}
}
}
obj* l_HashMapImp_find___at_Lean_Environment_getAttributeImpl___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; usize x_5; usize x_6; obj* x_7; usize x_8; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::array_get_size(x_3);
x_5 = lean_name_hash_usize(x_2);
x_6 = lean::usize_modn(x_5, x_4);
lean::dec(x_4);
x_7 = lean::box_size_t(x_6);
x_8 = lean::unbox_size_t(x_7);
lean::dec(x_7);
x_9 = lean::array_uget(x_3, x_8);
x_10 = l_AssocList_find___main___at_Lean_Environment_getAttributeImpl___spec__2(x_2, x_9);
lean::dec(x_9);
return x_10;
}
}
obj* _init_l_Lean_Environment_getAttributeImpl___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("unknown attribute '");
return x_1;
}
}
obj* l_Lean_Environment_getAttributeImpl___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_attributeMapRef;
x_4 = lean::io_ref_get(x_3, x_2);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_4, 0);
x_7 = l_HashMapImp_find___at_Lean_Environment_getAttributeImpl___spec__1(x_6, x_1);
lean::dec(x_6);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_8 = l_Lean_Name_toString___closed__1;
x_9 = l_Lean_Name_toStringWithSep___main(x_8, x_1);
x_10 = l_Lean_Environment_getAttributeImpl___rarg___closed__1;
x_11 = lean::string_append(x_10, x_9);
lean::dec(x_9);
x_12 = l_Char_HasRepr___closed__1;
x_13 = lean::string_append(x_11, x_12);
lean::cnstr_set_tag(x_4, 1);
lean::cnstr_set(x_4, 0, x_13);
return x_4;
}
else
{
obj* x_14; 
lean::dec(x_1);
x_14 = lean::cnstr_get(x_7, 0);
lean::inc(x_14);
lean::dec(x_7);
lean::cnstr_set(x_4, 0, x_14);
return x_4;
}
}
else
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean::cnstr_get(x_4, 0);
x_16 = lean::cnstr_get(x_4, 1);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_4);
x_17 = l_HashMapImp_find___at_Lean_Environment_getAttributeImpl___spec__1(x_15, x_1);
lean::dec(x_15);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_18 = l_Lean_Name_toString___closed__1;
x_19 = l_Lean_Name_toStringWithSep___main(x_18, x_1);
x_20 = l_Lean_Environment_getAttributeImpl___rarg___closed__1;
x_21 = lean::string_append(x_20, x_19);
lean::dec(x_19);
x_22 = l_Char_HasRepr___closed__1;
x_23 = lean::string_append(x_21, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_16);
return x_24;
}
else
{
obj* x_25; obj* x_26; 
lean::dec(x_1);
x_25 = lean::cnstr_get(x_17, 0);
lean::inc(x_25);
lean::dec(x_17);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_16);
return x_26;
}
}
}
else
{
uint8 x_27; 
lean::dec(x_1);
x_27 = !lean::is_exclusive(x_4);
if (x_27 == 0)
{
return x_4;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = lean::cnstr_get(x_4, 0);
x_29 = lean::cnstr_get(x_4, 1);
lean::inc(x_29);
lean::inc(x_28);
lean::dec(x_4);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set(x_30, 1, x_29);
return x_30;
}
}
}
}
obj* l_Lean_Environment_getAttributeImpl(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Environment_getAttributeImpl___rarg), 2, 0);
return x_2;
}
}
obj* l_AssocList_find___main___at_Lean_Environment_getAttributeImpl___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_AssocList_find___main___at_Lean_Environment_getAttributeImpl___spec__2(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_HashMapImp_find___at_Lean_Environment_getAttributeImpl___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_HashMapImp_find___at_Lean_Environment_getAttributeImpl___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Environment_getAttributeImpl___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Environment_getAttributeImpl(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Environment_addAttribute(obj* x_1, obj* x_2, obj* x_3, obj* x_4, uint8 x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Environment_getAttributeImpl___rarg(x_3, x_6);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_7, 0);
x_10 = lean::box(0);
lean::cnstr_set(x_7, 0, x_10);
x_11 = lean::cnstr_get(x_9, 2);
lean::inc(x_11);
lean::dec(x_9);
x_12 = lean::box(x_5);
x_13 = lean::apply_5(x_11, x_1, x_2, x_4, x_12, x_7);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_14 = lean::cnstr_get(x_7, 0);
x_15 = lean::cnstr_get(x_7, 1);
lean::inc(x_15);
lean::inc(x_14);
lean::dec(x_7);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_15);
x_18 = lean::cnstr_get(x_14, 2);
lean::inc(x_18);
lean::dec(x_14);
x_19 = lean::box(x_5);
x_20 = lean::apply_5(x_18, x_1, x_2, x_4, x_19, x_17);
return x_20;
}
}
else
{
uint8 x_21; 
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_1);
x_21 = !lean::is_exclusive(x_7);
if (x_21 == 0)
{
return x_7;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = lean::cnstr_get(x_7, 0);
x_23 = lean::cnstr_get(x_7, 1);
lean::inc(x_23);
lean::inc(x_22);
lean::dec(x_7);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
}
}
obj* l_Lean_Environment_addAttribute___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_5);
lean::dec(x_5);
x_8 = l_Lean_Environment_addAttribute(x_1, x_2, x_3, x_4, x_7, x_6);
return x_8;
}
}
obj* l_Lean_Environment_addScopedAttribute(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Environment_getAttributeImpl___rarg(x_3, x_5);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_6, 0);
x_9 = lean::box(0);
lean::cnstr_set(x_6, 0, x_9);
x_10 = lean::cnstr_get(x_8, 3);
lean::inc(x_10);
lean::dec(x_8);
x_11 = lean::apply_4(x_10, x_1, x_2, x_4, x_6);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_12 = lean::cnstr_get(x_6, 0);
x_13 = lean::cnstr_get(x_6, 1);
lean::inc(x_13);
lean::inc(x_12);
lean::dec(x_6);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_13);
x_16 = lean::cnstr_get(x_12, 3);
lean::inc(x_16);
lean::dec(x_12);
x_17 = lean::apply_4(x_16, x_1, x_2, x_4, x_15);
return x_17;
}
}
else
{
uint8 x_18; 
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_1);
x_18 = !lean::is_exclusive(x_6);
if (x_18 == 0)
{
return x_6;
}
else
{
obj* x_19; obj* x_20; obj* x_21; 
x_19 = lean::cnstr_get(x_6, 0);
x_20 = lean::cnstr_get(x_6, 1);
lean::inc(x_20);
lean::inc(x_19);
lean::dec(x_6);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
}
}
obj* l_Lean_Environment_eraseAttribute(obj* x_1, obj* x_2, obj* x_3, uint8 x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Environment_getAttributeImpl___rarg(x_3, x_5);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_6, 0);
x_9 = lean::box(0);
lean::cnstr_set(x_6, 0, x_9);
x_10 = lean::cnstr_get(x_8, 4);
lean::inc(x_10);
lean::dec(x_8);
x_11 = lean::box(x_4);
x_12 = lean::apply_4(x_10, x_1, x_2, x_11, x_6);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_13 = lean::cnstr_get(x_6, 0);
x_14 = lean::cnstr_get(x_6, 1);
lean::inc(x_14);
lean::inc(x_13);
lean::dec(x_6);
x_15 = lean::box(0);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_14);
x_17 = lean::cnstr_get(x_13, 4);
lean::inc(x_17);
lean::dec(x_13);
x_18 = lean::box(x_4);
x_19 = lean::apply_4(x_17, x_1, x_2, x_18, x_16);
return x_19;
}
}
else
{
uint8 x_20; 
lean::dec(x_2);
lean::dec(x_1);
x_20 = !lean::is_exclusive(x_6);
if (x_20 == 0)
{
return x_6;
}
else
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::cnstr_get(x_6, 0);
x_22 = lean::cnstr_get(x_6, 1);
lean::inc(x_22);
lean::inc(x_21);
lean::dec(x_6);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
return x_23;
}
}
}
}
obj* l_Lean_Environment_eraseAttribute___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_4);
lean::dec(x_4);
x_7 = l_Lean_Environment_eraseAttribute(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
obj* l_Lean_Environment_activateScopedAttribute(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Environment_getAttributeImpl___rarg(x_2, x_4);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::cnstr_get(x_5, 0);
x_8 = lean::box(0);
lean::cnstr_set(x_5, 0, x_8);
x_9 = lean::cnstr_get(x_7, 5);
lean::inc(x_9);
lean::dec(x_7);
x_10 = lean::apply_3(x_9, x_1, x_3, x_5);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_11 = lean::cnstr_get(x_5, 0);
x_12 = lean::cnstr_get(x_5, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_5);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_12);
x_15 = lean::cnstr_get(x_11, 5);
lean::inc(x_15);
lean::dec(x_11);
x_16 = lean::apply_3(x_15, x_1, x_3, x_14);
return x_16;
}
}
else
{
uint8 x_17; 
lean::dec(x_3);
lean::dec(x_1);
x_17 = !lean::is_exclusive(x_5);
if (x_17 == 0)
{
return x_5;
}
else
{
obj* x_18; obj* x_19; obj* x_20; 
x_18 = lean::cnstr_get(x_5, 0);
x_19 = lean::cnstr_get(x_5, 1);
lean::inc(x_19);
lean::inc(x_18);
lean::dec(x_5);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_Environment_activateScopedAttributes___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::array_get_size(x_3);
x_8 = lean::nat_dec_lt(x_4, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
uint8 x_9; 
lean::dec(x_4);
lean::dec(x_1);
x_9 = !lean::is_exclusive(x_6);
if (x_9 == 0)
{
obj* x_10; 
x_10 = lean::cnstr_get(x_6, 0);
lean::dec(x_10);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
else
{
obj* x_11; obj* x_12; 
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
lean::dec(x_6);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_5);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_13 = lean::array_fget(x_3, x_4);
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_4, x_14);
lean::dec(x_4);
x_16 = lean::cnstr_get(x_13, 5);
lean::inc(x_16);
lean::dec(x_13);
lean::inc(x_1);
x_17 = lean::apply_3(x_16, x_5, x_1, x_6);
if (lean::obj_tag(x_17) == 0)
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; 
x_19 = lean::cnstr_get(x_17, 0);
x_20 = lean::box(0);
lean::cnstr_set(x_17, 0, x_20);
x_4 = x_15;
x_5 = x_19;
x_6 = x_17;
goto _start;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_22 = lean::cnstr_get(x_17, 0);
x_23 = lean::cnstr_get(x_17, 1);
lean::inc(x_23);
lean::inc(x_22);
lean::dec(x_17);
x_24 = lean::box(0);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_23);
x_4 = x_15;
x_5 = x_22;
x_6 = x_25;
goto _start;
}
}
else
{
uint8 x_27; 
lean::dec(x_15);
lean::dec(x_1);
x_27 = !lean::is_exclusive(x_17);
if (x_27 == 0)
{
return x_17;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = lean::cnstr_get(x_17, 0);
x_29 = lean::cnstr_get(x_17, 1);
lean::inc(x_29);
lean::inc(x_28);
lean::dec(x_17);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
obj* l_Lean_Environment_activateScopedAttributes(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_attributeArrayRef;
x_5 = lean::io_ref_get(x_4, x_3);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::cnstr_get(x_5, 0);
x_8 = lean::box(0);
lean::cnstr_set(x_5, 0, x_8);
x_9 = lean::mk_nat_obj(0u);
x_10 = l_Array_miterateAux___main___at_Lean_Environment_activateScopedAttributes___spec__1(x_2, x_7, x_7, x_9, x_1, x_5);
lean::dec(x_7);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_11 = lean::cnstr_get(x_5, 0);
x_12 = lean::cnstr_get(x_5, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_5);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_12);
x_15 = lean::mk_nat_obj(0u);
x_16 = l_Array_miterateAux___main___at_Lean_Environment_activateScopedAttributes___spec__1(x_2, x_11, x_11, x_15, x_1, x_14);
lean::dec(x_11);
return x_16;
}
}
else
{
uint8 x_17; 
lean::dec(x_2);
lean::dec(x_1);
x_17 = !lean::is_exclusive(x_5);
if (x_17 == 0)
{
return x_5;
}
else
{
obj* x_18; obj* x_19; obj* x_20; 
x_18 = lean::cnstr_get(x_5, 0);
x_19 = lean::cnstr_get(x_5, 1);
lean::inc(x_19);
lean::inc(x_18);
lean::dec(x_5);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_Environment_activateScopedAttributes___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_miterateAux___main___at_Lean_Environment_activateScopedAttributes___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_3);
lean::dec(x_2);
return x_7;
}
}
obj* l_Array_miterateAux___main___at_Lean_Environment_pushScope___spec__1(uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; uint8 x_9; 
x_8 = lean::array_get_size(x_4);
x_9 = lean::nat_dec_lt(x_5, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
uint8 x_10; 
lean::dec(x_5);
lean::dec(x_2);
x_10 = !lean::is_exclusive(x_7);
if (x_10 == 0)
{
obj* x_11; 
x_11 = lean::cnstr_get(x_7, 0);
lean::dec(x_11);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_7, 1);
lean::inc(x_12);
lean::dec(x_7);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_6);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_14 = lean::array_fget(x_4, x_5);
x_15 = lean::mk_nat_obj(1u);
x_16 = lean::nat_add(x_5, x_15);
lean::dec(x_5);
x_17 = lean::cnstr_get(x_14, 6);
lean::inc(x_17);
x_18 = lean::apply_2(x_17, x_6, x_7);
if (lean::obj_tag(x_18) == 0)
{
if (x_1 == 0)
{
uint8 x_19; 
lean::dec(x_14);
x_19 = !lean::is_exclusive(x_18);
if (x_19 == 0)
{
obj* x_20; obj* x_21; 
x_20 = lean::cnstr_get(x_18, 0);
x_21 = lean::box(0);
lean::cnstr_set(x_18, 0, x_21);
x_5 = x_16;
x_6 = x_20;
x_7 = x_18;
goto _start;
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_23 = lean::cnstr_get(x_18, 0);
x_24 = lean::cnstr_get(x_18, 1);
lean::inc(x_24);
lean::inc(x_23);
lean::dec(x_18);
x_25 = lean::box(0);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_24);
x_5 = x_16;
x_6 = x_23;
x_7 = x_26;
goto _start;
}
}
else
{
uint8 x_28; 
x_28 = !lean::is_exclusive(x_18);
if (x_28 == 0)
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_29 = lean::cnstr_get(x_18, 0);
x_30 = lean::box(0);
lean::cnstr_set(x_18, 0, x_30);
x_31 = lean::cnstr_get(x_14, 5);
lean::inc(x_31);
lean::dec(x_14);
lean::inc(x_2);
x_32 = lean::apply_3(x_31, x_29, x_2, x_18);
if (lean::obj_tag(x_32) == 0)
{
uint8 x_33; 
x_33 = !lean::is_exclusive(x_32);
if (x_33 == 0)
{
obj* x_34; 
x_34 = lean::cnstr_get(x_32, 0);
lean::cnstr_set(x_32, 0, x_30);
x_5 = x_16;
x_6 = x_34;
x_7 = x_32;
goto _start;
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = lean::cnstr_get(x_32, 0);
x_37 = lean::cnstr_get(x_32, 1);
lean::inc(x_37);
lean::inc(x_36);
lean::dec(x_32);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_30);
lean::cnstr_set(x_38, 1, x_37);
x_5 = x_16;
x_6 = x_36;
x_7 = x_38;
goto _start;
}
}
else
{
uint8 x_40; 
lean::dec(x_16);
lean::dec(x_2);
x_40 = !lean::is_exclusive(x_32);
if (x_40 == 0)
{
return x_32;
}
else
{
obj* x_41; obj* x_42; obj* x_43; 
x_41 = lean::cnstr_get(x_32, 0);
x_42 = lean::cnstr_get(x_32, 1);
lean::inc(x_42);
lean::inc(x_41);
lean::dec(x_32);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_44 = lean::cnstr_get(x_18, 0);
x_45 = lean::cnstr_get(x_18, 1);
lean::inc(x_45);
lean::inc(x_44);
lean::dec(x_18);
x_46 = lean::box(0);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_45);
x_48 = lean::cnstr_get(x_14, 5);
lean::inc(x_48);
lean::dec(x_14);
lean::inc(x_2);
x_49 = lean::apply_3(x_48, x_44, x_2, x_47);
if (lean::obj_tag(x_49) == 0)
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_51 = lean::cnstr_get(x_49, 1);
lean::inc(x_51);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_release(x_49, 0);
 lean::cnstr_release(x_49, 1);
 x_52 = x_49;
} else {
 lean::dec_ref(x_49);
 x_52 = lean::box(0);
}
if (lean::is_scalar(x_52)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_52;
}
lean::cnstr_set(x_53, 0, x_46);
lean::cnstr_set(x_53, 1, x_51);
x_5 = x_16;
x_6 = x_50;
x_7 = x_53;
goto _start;
}
else
{
obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
lean::dec(x_16);
lean::dec(x_2);
x_55 = lean::cnstr_get(x_49, 0);
lean::inc(x_55);
x_56 = lean::cnstr_get(x_49, 1);
lean::inc(x_56);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_release(x_49, 0);
 lean::cnstr_release(x_49, 1);
 x_57 = x_49;
} else {
 lean::dec_ref(x_49);
 x_57 = lean::box(0);
}
if (lean::is_scalar(x_57)) {
 x_58 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_58 = x_57;
}
lean::cnstr_set(x_58, 0, x_55);
lean::cnstr_set(x_58, 1, x_56);
return x_58;
}
}
}
}
else
{
uint8 x_59; 
lean::dec(x_16);
lean::dec(x_14);
lean::dec(x_2);
x_59 = !lean::is_exclusive(x_18);
if (x_59 == 0)
{
return x_18;
}
else
{
obj* x_60; obj* x_61; obj* x_62; 
x_60 = lean::cnstr_get(x_18, 0);
x_61 = lean::cnstr_get(x_18, 1);
lean::inc(x_61);
lean::inc(x_60);
lean::dec(x_18);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_60);
lean::cnstr_set(x_62, 1, x_61);
return x_62;
}
}
}
}
}
namespace lean {
obj* push_scope_core(obj* x_1, obj* x_2, uint8 x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = l_Lean_Environment_pushScopeCore(x_1, x_2, x_3);
lean::inc(x_5);
x_6 = lean::get_namespace_core(x_5);
x_7 = l_Lean_attributeArrayRef;
x_8 = lean::io_ref_get(x_7, x_4);
if (lean::obj_tag(x_8) == 0)
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_10 = lean::cnstr_get(x_8, 0);
x_11 = lean::box(0);
lean::cnstr_set(x_8, 0, x_11);
x_12 = lean::mk_nat_obj(0u);
x_13 = l_Array_miterateAux___main___at_Lean_Environment_pushScope___spec__1(x_3, x_6, x_10, x_10, x_12, x_5, x_8);
lean::dec(x_10);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_14 = lean::cnstr_get(x_8, 0);
x_15 = lean::cnstr_get(x_8, 1);
lean::inc(x_15);
lean::inc(x_14);
lean::dec(x_8);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_15);
x_18 = lean::mk_nat_obj(0u);
x_19 = l_Array_miterateAux___main___at_Lean_Environment_pushScope___spec__1(x_3, x_6, x_14, x_14, x_18, x_5, x_17);
lean::dec(x_14);
return x_19;
}
}
else
{
uint8 x_20; 
lean::dec(x_6);
lean::dec(x_5);
x_20 = !lean::is_exclusive(x_8);
if (x_20 == 0)
{
return x_8;
}
else
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::cnstr_get(x_8, 0);
x_22 = lean::cnstr_get(x_8, 1);
lean::inc(x_22);
lean::inc(x_21);
lean::dec(x_8);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_Environment_pushScope___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; obj* x_9; 
x_8 = lean::unbox(x_1);
lean::dec(x_1);
x_9 = l_Array_miterateAux___main___at_Lean_Environment_pushScope___spec__1(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_4);
lean::dec(x_3);
return x_9;
}
}
obj* l_Lean_Environment_pushScope___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_3);
lean::dec(x_3);
x_6 = lean::push_scope_core(x_1, x_2, x_5, x_4);
return x_6;
}
}
obj* l_Array_miterateAux___main___at_Lean_Environment_popScope___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_2);
x_7 = lean::nat_dec_lt(x_3, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
uint8 x_8; 
lean::dec(x_3);
x_8 = !lean::is_exclusive(x_5);
if (x_8 == 0)
{
obj* x_9; 
x_9 = lean::cnstr_get(x_5, 0);
lean::dec(x_9);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
else
{
obj* x_10; obj* x_11; 
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
lean::dec(x_5);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_4);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_12 = lean::array_fget(x_2, x_3);
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_add(x_3, x_13);
lean::dec(x_3);
x_15 = lean::cnstr_get(x_12, 7);
lean::inc(x_15);
lean::dec(x_12);
x_16 = lean::apply_2(x_15, x_4, x_5);
if (lean::obj_tag(x_16) == 0)
{
uint8 x_17; 
x_17 = !lean::is_exclusive(x_16);
if (x_17 == 0)
{
obj* x_18; obj* x_19; 
x_18 = lean::cnstr_get(x_16, 0);
x_19 = lean::box(0);
lean::cnstr_set(x_16, 0, x_19);
x_3 = x_14;
x_4 = x_18;
x_5 = x_16;
goto _start;
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_21 = lean::cnstr_get(x_16, 0);
x_22 = lean::cnstr_get(x_16, 1);
lean::inc(x_22);
lean::inc(x_21);
lean::dec(x_16);
x_23 = lean::box(0);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_22);
x_3 = x_14;
x_4 = x_21;
x_5 = x_24;
goto _start;
}
}
else
{
uint8 x_26; 
lean::dec(x_14);
x_26 = !lean::is_exclusive(x_16);
if (x_26 == 0)
{
return x_16;
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = lean::cnstr_get(x_16, 0);
x_28 = lean::cnstr_get(x_16, 1);
lean::inc(x_28);
lean::inc(x_27);
lean::dec(x_16);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
namespace lean {
obj* pop_scope_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_Lean_Environment_popScopeCore(x_1);
x_4 = l_Lean_attributeArrayRef;
x_5 = lean::io_ref_get(x_4, x_2);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::cnstr_get(x_5, 0);
x_8 = lean::box(0);
lean::cnstr_set(x_5, 0, x_8);
x_9 = lean::mk_nat_obj(0u);
x_10 = l_Array_miterateAux___main___at_Lean_Environment_popScope___spec__1(x_7, x_7, x_9, x_3, x_5);
lean::dec(x_7);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_11 = lean::cnstr_get(x_5, 0);
x_12 = lean::cnstr_get(x_5, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_5);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_12);
x_15 = lean::mk_nat_obj(0u);
x_16 = l_Array_miterateAux___main___at_Lean_Environment_popScope___spec__1(x_11, x_11, x_15, x_3, x_14);
lean::dec(x_11);
return x_16;
}
}
else
{
uint8 x_17; 
lean::dec(x_3);
x_17 = !lean::is_exclusive(x_5);
if (x_17 == 0)
{
return x_5;
}
else
{
obj* x_18; obj* x_19; obj* x_20; 
x_18 = lean::cnstr_get(x_5, 0);
x_19 = lean::cnstr_get(x_5, 1);
lean::inc(x_19);
lean::inc(x_18);
lean::dec(x_5);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_Environment_popScope___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_Environment_popScope___spec__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
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
l_Lean_Environment_popScopeCore___closed__1 = _init_l_Lean_Environment_popScopeCore___closed__1();
lean::mark_persistent(l_Lean_Environment_popScopeCore___closed__1);
l_Lean_mkAttributeMapRef___closed__1 = _init_l_Lean_mkAttributeMapRef___closed__1();
lean::mark_persistent(l_Lean_mkAttributeMapRef___closed__1);
w = l_Lean_mkAttributeMapRef(w);
if (io_result_is_error(w)) return w;
l_Lean_attributeMapRef = io_result_get_value(w);
lean::mark_persistent(l_Lean_attributeMapRef);
w = l_Lean_mkAttributeArrayRef(w);
if (io_result_is_error(w)) return w;
l_Lean_attributeArrayRef = io_result_get_value(w);
lean::mark_persistent(l_Lean_attributeArrayRef);
l_Lean_registerAttribute___closed__1 = _init_l_Lean_registerAttribute___closed__1();
lean::mark_persistent(l_Lean_registerAttribute___closed__1);
l_Lean_registerAttribute___closed__2 = _init_l_Lean_registerAttribute___closed__2();
lean::mark_persistent(l_Lean_registerAttribute___closed__2);
l_Lean_Environment_getAttributeImpl___rarg___closed__1 = _init_l_Lean_Environment_getAttributeImpl___rarg___closed__1();
lean::mark_persistent(l_Lean_Environment_getAttributeImpl___rarg___closed__1);
return w;
}

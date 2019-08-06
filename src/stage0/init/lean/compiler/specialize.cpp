// Lean compiler output
// Module: init.lean.compiler.specialize
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
obj* l_RBNode_setBlack___main___rarg(obj*);
obj* l_unsafeCast(obj*, obj*, obj*, obj*);
obj* l_Lean_Compiler_specExtension___closed__5;
extern "C" uint8 lean_expr_quick_lt(obj*, obj*);
obj* l_Lean_Compiler_specExtension___elambda__2___boxed(obj*);
obj* l_Lean_Compiler_SpecializeAttributeKind_beq___boxed(obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_AssocList_replace___main___at_Lean_Compiler_SpecState_addEntry___spec__18(obj*, obj*, obj*);
obj* l_Lean_SMap_switch___at_Lean_Compiler_SpecState_switch___main___spec__2(obj*);
obj* l___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux___main___boxed(obj*, obj*, obj*);
obj* l_Array_binSearchAux___main___at___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux___main___spec__3___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_find___main___at_Lean_Compiler_getSpecializationInfo___spec__1(obj*, obj*);
obj* l_HashMapImp_insert___at_Lean_Compiler_SpecState_addEntry___spec__4(obj*, obj*, obj*);
extern obj* l_Array_empty___closed__1;
obj* l_RBNode_fold___main___at_Lean_Compiler_mkSpecializeAttrs___spec__2(obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
extern obj* l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
obj* l_Lean_SMap_switch___at_Lean_Compiler_SpecState_switch___main___spec__1(obj*);
obj* l_Lean_Compiler_mkSpecExtension___closed__2;
obj* l_Lean_Compiler_specExtension___closed__2;
extern obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
obj* l_Array_miterateAux___main___at_Lean_Compiler_mkSpecExtension___spec__2(obj*, obj*, obj*, obj*);
uint8 l_AssocList_contains___main___at_Lean_Compiler_SpecState_addEntry___spec__14(obj*, obj*);
obj* l_Lean_registerEnumAttributes___at_Lean_Compiler_mkSpecializeAttrs___spec__1___lambda__1(obj*, obj*);
obj* l_Array_mkArray(obj*, obj*, obj*);
obj* l_Lean_registerEnumAttributes___at_Lean_Compiler_mkSpecializeAttrs___spec__1___closed__1;
extern "C" usize lean_expr_hash(obj*);
obj* l_RBNode_find___main___at_Lean_Compiler_getCachedSpecialization___spec__2(obj*, obj*);
extern obj* l_Lean_EnvExtension_Inhabited___rarg___closed__1;
obj* l_Lean_SMap_insert___main___at_Lean_Compiler_SpecState_addEntry___spec__1(obj*, obj*, obj*);
obj* l_Lean_Compiler_SpecState_Inhabited___closed__2;
extern obj* l_Lean_AttributeImpl_inhabited___closed__5;
obj* l_Lean_Compiler_SpecializeAttributeKind_HasBeq;
obj* l_Lean_Compiler_mkSpecExtension___lambda__1(obj*);
extern obj* l_Lean_registerTagAttribute___lambda__4___closed__4;
obj* l_AssocList_contains___main___at_Lean_Compiler_SpecState_addEntry___spec__5___boxed(obj*, obj*);
obj* l_Lean_Compiler_mkSpecExtension(obj*);
obj* l_Lean_Compiler_mkSpecializeAttrs___closed__3;
obj* l_Lean_Compiler_mkSpecializeAttrs___closed__8;
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7(obj*, obj*);
obj* l_Lean_Compiler_SpecState_Inhabited;
obj* l_RBNode_find___main___at___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux___main___spec__2(obj*, obj*);
obj* l_Lean_EnumAttributes_getValue___at___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_Array_qsortAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__3(obj*, obj*, obj*);
obj* l_Lean_Compiler_mkSpecializeAttrs___closed__15;
obj* l_Lean_Expr_quickLt___boxed(obj*, obj*);
obj* l_Lean_registerEnumAttributes___at_Lean_Compiler_mkSpecializeAttrs___spec__1(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux___boxed(obj*, obj*, obj*);
obj* l_Lean_Compiler_mkSpecializeAttrs___closed__9;
obj* l_Array_miterateAux___main___at_Lean_Compiler_mkSpecExtension___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Compiler_mkSpecializeAttrs___spec__8___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Compiler_specExtension___elambda__1(obj*);
obj* l_Array_uget(obj*, obj*, usize, obj*);
extern obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l_Lean_Compiler_SpecState_Inhabited___closed__3;
obj* l_Lean_SimplePersistentEnvExtension_getState___rarg(obj*, obj*);
obj* l_AssocList_mfoldl___main___at_Lean_Compiler_SpecState_addEntry___spec__17(obj*, obj*);
obj* l_Lean_Compiler_SpecState_Inhabited___closed__1;
extern obj* l_Lean_Inhabited;
obj* l_Array_uset(obj*, obj*, usize, obj*, obj*);
obj* l_IO_Prim_Ref_set(obj*, obj*, obj*, obj*);
obj* l_Lean_Compiler_SpecializeAttributeKind_beq___main___boxed(obj*, obj*);
obj* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__2(obj*, obj*, obj*);
obj* l_Lean_Compiler_SpecState_Inhabited___closed__5;
obj* l_Lean_Compiler_mkSpecializeAttrs(obj*);
obj* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__3(obj*, obj*);
obj* l_Lean_Compiler_specExtension___closed__4;
extern "C" obj* lean_io_initializing(obj*);
obj* l_HashMapImp_find___at_Lean_Compiler_getCachedSpecialization___spec__3___boxed(obj*, obj*);
obj* l_Lean_Compiler_mkSpecializeAttrs___closed__12;
obj* l_Array_binSearchAux___main___at___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux___main___spec__3(obj*, obj*, obj*, obj*);
obj* l_AssocList_find___main___at_Lean_Compiler_getSpecializationInfo___spec__4(obj*, obj*);
obj* l_Lean_EnumAttributes_getValue___at___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux___main___spec__1(obj*, obj*, obj*);
obj* l_HashMapImp_moveEntries___main___at_Lean_Compiler_SpecState_addEntry___spec__7(obj*, obj*, obj*);
extern obj* l_Lean_registerEnumAttributes___rarg___closed__1;
obj* l_mkHashMap___at_Lean_Compiler_SpecState_Inhabited___spec__2(obj*);
extern obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_registerTagAttribute___spec__6___closed__1;
obj* l_Array_swap(obj*, obj*, obj*, obj*);
obj* l_AssocList_find___main___at_Lean_Compiler_getSpecializationInfo___spec__4___boxed(obj*, obj*);
extern obj* l_Lean_AttributeImpl_inhabited___closed__4;
obj* l_Lean_Compiler_specExtension___elambda__4___rarg(obj*);
obj* l_RBNode_insert___at_Lean_Compiler_SpecState_addEntry___spec__2(obj*, obj*, obj*);
obj* l_Lean_registerTagAttribute___lambda__5___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_EnumAttributes_Inhabited___closed__1;
obj* l_Lean_Compiler_SpecState_Inhabited___closed__6;
obj* l_RBNode_find___main___at_Lean_Compiler_getSpecializationInfo___spec__2___boxed(obj*, obj*);
obj* l_Lean_SMap_find___main___at_Lean_Compiler_getCachedSpecialization___spec__1(obj*, obj*);
obj* l_Lean_Compiler_specExtension___elambda__4___boxed(obj*);
namespace lean {
obj* add_specialization_info_core(obj*, obj*, obj*);
}
obj* l_Lean_Compiler_specExtension___elambda__2(obj*);
obj* l_Lean_Compiler_specExtension;
obj* l_Lean_Compiler_specExtension___closed__1;
extern "C" usize lean_name_hash_usize(obj*);
obj* l_Array_anyMAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__6___boxed(obj*, obj*, obj*);
obj* l_RBNode_find___main___at___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux___main___spec__2___boxed(obj*, obj*);
extern obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
extern "C" uint8 lean_expr_eqv(obj*, obj*);
obj* l_Lean_PersistentEnvExtension_getState___rarg(obj*, obj*);
obj* l_List_mfor___main___at_Lean_registerEnumAttributes___spec__11(obj*, obj*);
obj* l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__4___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_HashMapImp_expand___at_Lean_Compiler_SpecState_addEntry___spec__6(obj*, obj*);
obj* l_Lean_Environment_getModuleIdxFor(obj*, obj*);
obj* l_Lean_Compiler_mkSpecializeAttrs___closed__11;
obj* l_Lean_mkStateFromImportedEntries___at_Lean_Compiler_mkSpecExtension___spec__1(obj*, obj*);
obj* l_mkHashMap___at_Lean_Compiler_SpecState_Inhabited___spec__1(obj*);
extern obj* l_Lean_registerTagAttribute___lambda__4___closed__1;
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_RBNode_insert___at_Lean_Compiler_SpecState_addEntry___spec__11(obj*, obj*, obj*);
obj* l_Lean_Compiler_mkSpecializeAttrs___closed__1;
obj* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Compiler_mkSpecializeAttrs___closed__14;
namespace lean {
uint8 has_specialize_attribute_core(obj*, obj*);
}
uint8 l_Lean_Compiler_SpecializeAttributeKind_beq___main(uint8, uint8);
obj* l_Lean_Compiler_SpecState_switch___main(obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__4___closed__1;
obj* l_Lean_Compiler_specExtension___closed__3;
obj* l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(obj*, obj*, obj*);
uint8 l_Lean_Compiler_SpecializeAttributeKind_Inhabited;
namespace lean {
obj* cache_specialization_core(obj*, obj*, obj*);
}
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__2;
obj* l_Array_fget(obj*, obj*, obj*);
obj* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Compiler_mkSpecializeAttrs___spec__5(obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_registerSimplePersistentEnvExtension___at_Lean_Compiler_mkSpecExtension___spec__4(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_SMap_find___main___at_Lean_Compiler_getSpecializationInfo___spec__1___boxed(obj*, obj*);
obj* l_Lean_PersistentEnvExtension_getModuleEntries___rarg(obj*, obj*, obj*);
obj* l_Lean_Compiler_SpecState_switch(obj*);
obj* l_Lean_Compiler_mkSpecializeAttrs___closed__7;
extern obj* l_Lean_registerTagAttribute___lambda__4___closed__3;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_HashMapImp_expand___at_Lean_Compiler_SpecState_addEntry___spec__15(obj*, obj*);
obj* l_Lean_Compiler_specExtension___closed__6;
obj* l_Array_push(obj*, obj*, obj*);
uint8 l_RBNode_isRed___main___rarg(obj*);
uint8 l_Lean_Compiler_SpecializeAttributeKind_beq(uint8, uint8);
obj* l_RBNode_fold___main___at_Lean_Compiler_mkSpecializeAttrs___spec__2___boxed(obj*, obj*);
obj* l_Lean_Compiler_specExtension___elambda__3(obj*, obj*);
extern obj* l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1;
obj* l_Lean_Compiler_hasNospecializeAttribute___boxed(obj*, obj*);
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__3;
obj* l_Lean_Compiler_mkSpecializeAttrs___closed__2;
obj* l_HashMapImp_find___at_Lean_Compiler_getSpecializationInfo___spec__3(obj*, obj*);
obj* l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__4(obj*, obj*, obj*, obj*, obj*);
obj* l_AssocList_find___main___at_Lean_Compiler_getCachedSpecialization___spec__4___boxed(obj*, obj*);
obj* l_Array_anyMAux___main___at_Lean_Compiler_mkSpecExtension___spec__6___boxed(obj*, obj*, obj*);
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__4;
obj* l_Lean_Compiler_mkSpecializeAttrs___closed__6;
obj* l_Lean_Compiler_mkSpecializeAttrs___closed__5;
uint8 l_Array_anyMAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__6(obj*, obj*, obj*);
obj* l_EState_bind___rarg(obj*, obj*, obj*);
obj* l_RBNode_find___main___at_Lean_Compiler_getSpecializationInfo___spec__2(obj*, obj*);
obj* l_RBNode_find___main___at_Lean_Compiler_getCachedSpecialization___spec__2___boxed(obj*, obj*);
namespace lean {
obj* get_specialization_info_core(obj*, obj*);
}
obj* l_Lean_mkStateFromImportedEntries___at_Lean_Compiler_mkSpecExtension___spec__1___boxed(obj*, obj*);
obj* l_Lean_Compiler_mkSpecializeAttrs___lambda__1(obj*, obj*, uint8);
obj* l_Lean_PersistentEnvExtension_addEntry___rarg(obj*, obj*, obj*);
obj* l_IO_Prim_Ref_get(obj*, obj*, obj*);
uint8 l_Lean_Name_quickLt(obj*, obj*);
obj* l_HashMapImp_moveEntries___main___at_Lean_Compiler_SpecState_addEntry___spec__16(obj*, obj*, obj*);
namespace lean {
usize usize_modn(usize, obj*);
}
obj* l_Lean_Compiler_mkSpecializeAttrs___lambda__1___boxed(obj*, obj*, obj*);
obj* l_HashMapImp_insert___at_Lean_Compiler_SpecState_addEntry___spec__13(obj*, obj*, obj*);
obj* l_Lean_Compiler_specializeAttrs;
uint8 l_AssocList_contains___main___at_Lean_Compiler_SpecState_addEntry___spec__5(obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__3(obj*, obj*, obj*);
obj* l_Lean_Compiler_SpecializeAttributeKind_HasBeq___closed__1;
obj* l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__12(obj*, obj*, obj*);
obj* l_Lean_SMap_find___main___at_Lean_Compiler_getCachedSpecialization___spec__1___boxed(obj*, obj*);
obj* l_Lean_Compiler_SpecState_addEntry(obj*, obj*);
extern obj* l_HashMap_Inhabited___closed__1;
obj* l_Lean_Compiler_hasSpecializeAttribute___boxed(obj*, obj*);
obj* l_Array_size(obj*, obj*);
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__1;
uint8 l___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux___main(obj*, uint8, obj*);
obj* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__5(obj*, obj*);
obj* l_Lean_registerEnumAttributes___at_Lean_Compiler_mkSpecializeAttrs___spec__1___lambda__2(obj*);
obj* l_Array_fset(obj*, obj*, obj*, obj*);
obj* l_Array_get(obj*, obj*, obj*, obj*);
obj* l_mkHashMapImp___rarg(obj*);
obj* l_Lean_Name_getPrefix___main(obj*);
obj* l_Array_miterateAux___main___at_Lean_Compiler_mkSpecExtension___spec__3(obj*, obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Compiler_mkSpecializeAttrs___spec__8___lambda__1(obj*, obj*, uint8, obj*, obj*, obj*, obj*, uint8, obj*);
extern obj* l_Lean_registerTagAttribute___lambda__4___closed__5;
obj* l_List_map___main___at_Lean_Compiler_mkSpecializeAttrs___spec__8(obj*, obj*, obj*);
obj* l_Lean_SMap_insert___main___at_Lean_Compiler_SpecState_addEntry___spec__10(obj*, obj*, obj*);
obj* l_AssocList_find___main___at_Lean_Compiler_getCachedSpecialization___spec__4(obj*, obj*);
obj* l_Lean_registerEnumAttributes___at_Lean_Compiler_mkSpecializeAttrs___spec__1___lambda__2___boxed(obj*);
uint8 l_Array_anyMAux___main___at_Lean_Compiler_mkSpecExtension___spec__6(obj*, obj*, obj*);
extern obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
extern obj* l_Lean_Name_toString___closed__1;
namespace lean {
obj* get_cached_specialization_core(obj*, obj*);
}
obj* l_Lean_Compiler_mkSpecializeAttrs___closed__10;
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l_AssocList_mfoldl___main___at_Lean_Compiler_SpecState_addEntry___spec__8(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_Compiler_mkSpecExtension___spec__3___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Compiler_SpecState_Inhabited___closed__4;
obj* l_AssocList_replace___main___at_Lean_Compiler_SpecState_addEntry___spec__9(obj*, obj*, obj*);
obj* l_Lean_Compiler_checkIsDefinition(obj*, obj*);
obj* l_Lean_Compiler_mkSpecExtension___lambda__1___boxed(obj*);
namespace lean {
obj* nat_div(obj*, obj*);
}
obj* l_AssocList_contains___main___at_Lean_Compiler_SpecState_addEntry___spec__14___boxed(obj*, obj*);
obj* l_Lean_registerEnumAttributes___at_Lean_Compiler_mkSpecializeAttrs___spec__1___closed__2;
obj* l_HashMapImp_find___at_Lean_Compiler_getSpecializationInfo___spec__3___boxed(obj*, obj*);
obj* l_Lean_Compiler_specExtension___elambda__3___boxed(obj*, obj*);
extern obj* l___private_init_lean_environment_8__persistentEnvExtensionsRef;
obj* l_Lean_Compiler_mkSpecExtension___closed__3;
uint8 l_Lean_Name_isInternal___main(obj*);
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecializeAttrs___spec__7(obj*, obj*);
obj* l_HashMapImp_find___at_Lean_Compiler_getCachedSpecialization___spec__3(obj*, obj*);
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__5;
extern obj* l_Lean_registerTagAttribute___closed__1;
extern obj* l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
extern obj* l_Lean_regNamespacesExtension___closed__5;
obj* l_IO_Prim_Ref_reset(obj*, obj*, obj*);
obj* l_Lean_Compiler_specExtension___elambda__1___boxed(obj*);
extern obj* l___private_init_lean_environment_5__envExtensionsRef;
obj* l_Lean_Compiler_mkSpecExtension___closed__1;
namespace lean {
uint8 has_nospecialize_attribute_core(obj*, obj*);
}
uint8 l___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux(obj*, uint8, obj*);
obj* l_Lean_Compiler_mkSpecializeAttrs___closed__4;
obj* l_Lean_Compiler_specExtension___elambda__4(obj*);
obj* l_Array_qsortAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__3___boxed(obj*, obj*, obj*);
obj* l_Lean_registerTagAttribute___lambda__6___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Compiler_mkSpecializeAttrs___closed__13;
extern obj* l_String_splitAux___main___closed__1;
uint8 _init_l_Lean_Compiler_SpecializeAttributeKind_Inhabited() {
_start:
{
uint8 x_1; 
x_1 = 0;
return x_1;
}
}
uint8 l_Lean_Compiler_SpecializeAttributeKind_beq___main(uint8 x_1, uint8 x_2) {
_start:
{
if (x_1 == 0)
{
if (x_2 == 0)
{
uint8 x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (x_2 == 0)
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8 x_6; 
x_6 = 1;
return x_6;
}
}
}
}
obj* l_Lean_Compiler_SpecializeAttributeKind_beq___main___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; uint8 x_4; uint8 x_5; obj* x_6; 
x_3 = lean::unbox(x_1);
lean::dec(x_1);
x_4 = lean::unbox(x_2);
lean::dec(x_2);
x_5 = l_Lean_Compiler_SpecializeAttributeKind_beq___main(x_3, x_4);
x_6 = lean::box(x_5);
return x_6;
}
}
uint8 l_Lean_Compiler_SpecializeAttributeKind_beq(uint8 x_1, uint8 x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Lean_Compiler_SpecializeAttributeKind_beq___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Compiler_SpecializeAttributeKind_beq___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; uint8 x_4; uint8 x_5; obj* x_6; 
x_3 = lean::unbox(x_1);
lean::dec(x_1);
x_4 = lean::unbox(x_2);
lean::dec(x_2);
x_5 = l_Lean_Compiler_SpecializeAttributeKind_beq(x_3, x_4);
x_6 = lean::box(x_5);
return x_6;
}
}
obj* _init_l_Lean_Compiler_SpecializeAttributeKind_HasBeq___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_SpecializeAttributeKind_beq___boxed), 2, 0);
return x_1;
}
}
obj* _init_l_Lean_Compiler_SpecializeAttributeKind_HasBeq() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Compiler_SpecializeAttributeKind_HasBeq___closed__1;
return x_1;
}
}
obj* l_RBNode_fold___main___at_Lean_Compiler_mkSpecializeAttrs___spec__2(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean::cnstr_get(x_2, 1);
x_5 = lean::cnstr_get(x_2, 2);
x_6 = lean::cnstr_get(x_2, 3);
x_7 = l_RBNode_fold___main___at_Lean_Compiler_mkSpecializeAttrs___spec__2(x_1, x_3);
lean::inc(x_5);
lean::inc(x_4);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_4);
lean::cnstr_set(x_8, 1, x_5);
x_9 = lean::array_push(x_7, x_8);
x_1 = x_9;
x_2 = x_6;
goto _start;
}
}
}
obj* _init_l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__4___closed__1() {
_start:
{
obj* x_1; uint8 x_2; obj* x_3; obj* x_4; 
x_1 = l_Lean_Inhabited;
x_2 = l_Lean_Compiler_SpecializeAttributeKind_Inhabited;
x_3 = lean::box(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__4(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; 
x_6 = lean::nat_dec_lt(x_5, x_1);
if (x_6 == 0)
{
obj* x_7; obj* x_8; 
lean::dec(x_5);
x_7 = lean::array_swap(x_3, x_4, x_1);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_4);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_9 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__4___closed__1;
x_10 = lean::array_get(x_9, x_3, x_5);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
lean::dec(x_10);
x_12 = lean::cnstr_get(x_2, 0);
x_13 = l_Lean_Name_quickLt(x_11, x_12);
lean::dec(x_11);
if (x_13 == 0)
{
obj* x_14; obj* x_15; 
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_5, x_14);
lean::dec(x_5);
x_5 = x_15;
goto _start;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_17 = lean::array_swap(x_3, x_4, x_5);
x_18 = lean::mk_nat_obj(1u);
x_19 = lean::nat_add(x_4, x_18);
lean::dec(x_4);
x_20 = lean::nat_add(x_5, x_18);
lean::dec(x_5);
x_3 = x_17;
x_4 = x_19;
x_5 = x_20;
goto _start;
}
}
}
}
obj* l_Array_qsortAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__3(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean::dec(x_2);
return x_1;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; uint8 x_62; 
x_5 = lean::nat_add(x_2, x_3);
x_6 = lean::mk_nat_obj(2u);
x_7 = lean::nat_div(x_5, x_6);
lean::dec(x_5);
x_57 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__4___closed__1;
x_58 = lean::array_get(x_57, x_1, x_7);
x_59 = lean::array_get(x_57, x_1, x_2);
x_60 = lean::cnstr_get(x_58, 0);
lean::inc(x_60);
lean::dec(x_58);
x_61 = lean::cnstr_get(x_59, 0);
lean::inc(x_61);
lean::dec(x_59);
x_62 = l_Lean_Name_quickLt(x_60, x_61);
lean::dec(x_61);
lean::dec(x_60);
if (x_62 == 0)
{
x_8 = x_1;
goto block_56;
}
else
{
obj* x_63; 
x_63 = lean::array_swap(x_1, x_2, x_7);
x_8 = x_63;
goto block_56;
}
block_56:
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_9 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__4___closed__1;
x_10 = lean::array_get(x_9, x_8, x_3);
x_11 = lean::array_get(x_9, x_8, x_2);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
x_13 = lean::cnstr_get(x_11, 0);
lean::inc(x_13);
lean::dec(x_11);
x_14 = l_Lean_Name_quickLt(x_12, x_13);
lean::dec(x_13);
if (x_14 == 0)
{
obj* x_15; obj* x_16; uint8 x_17; 
x_15 = lean::array_get(x_9, x_8, x_7);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
lean::dec(x_15);
x_17 = l_Lean_Name_quickLt(x_16, x_12);
lean::dec(x_12);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_7);
lean::inc(x_2, 2);
x_18 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__4(x_3, x_10, x_8, x_2, x_2);
lean::dec(x_10);
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
x_20 = lean::cnstr_get(x_18, 1);
lean::inc(x_20);
lean::dec(x_18);
x_21 = l_Array_qsortAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__3(x_20, x_2, x_19);
x_22 = lean::mk_nat_obj(1u);
x_23 = lean::nat_add(x_19, x_22);
lean::dec(x_19);
x_1 = x_21;
x_2 = x_23;
goto _start;
}
else
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_10);
x_25 = lean::array_swap(x_8, x_7, x_3);
lean::dec(x_7);
x_26 = lean::array_get(x_9, x_25, x_3);
lean::inc(x_2, 2);
x_27 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__4(x_3, x_26, x_25, x_2, x_2);
lean::dec(x_26);
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
x_29 = lean::cnstr_get(x_27, 1);
lean::inc(x_29);
lean::dec(x_27);
x_30 = l_Array_qsortAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__3(x_29, x_2, x_28);
x_31 = lean::mk_nat_obj(1u);
x_32 = lean::nat_add(x_28, x_31);
lean::dec(x_28);
x_1 = x_30;
x_2 = x_32;
goto _start;
}
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; uint8 x_39; 
lean::dec(x_12);
lean::dec(x_10);
x_34 = lean::array_swap(x_8, x_2, x_3);
x_35 = lean::array_get(x_9, x_34, x_7);
x_36 = lean::array_get(x_9, x_34, x_3);
x_37 = lean::cnstr_get(x_35, 0);
lean::inc(x_37);
lean::dec(x_35);
x_38 = lean::cnstr_get(x_36, 0);
lean::inc(x_38);
x_39 = l_Lean_Name_quickLt(x_37, x_38);
lean::dec(x_38);
lean::dec(x_37);
if (x_39 == 0)
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
lean::dec(x_7);
lean::inc(x_2, 2);
x_40 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__4(x_3, x_36, x_34, x_2, x_2);
lean::dec(x_36);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_42 = lean::cnstr_get(x_40, 1);
lean::inc(x_42);
lean::dec(x_40);
x_43 = l_Array_qsortAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__3(x_42, x_2, x_41);
x_44 = lean::mk_nat_obj(1u);
x_45 = lean::nat_add(x_41, x_44);
lean::dec(x_41);
x_1 = x_43;
x_2 = x_45;
goto _start;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_36);
x_47 = lean::array_swap(x_34, x_7, x_3);
lean::dec(x_7);
x_48 = lean::array_get(x_9, x_47, x_3);
lean::inc(x_2, 2);
x_49 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__4(x_3, x_48, x_47, x_2, x_2);
lean::dec(x_48);
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_51 = lean::cnstr_get(x_49, 1);
lean::inc(x_51);
lean::dec(x_49);
x_52 = l_Array_qsortAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__3(x_51, x_2, x_50);
x_53 = lean::mk_nat_obj(1u);
x_54 = lean::nat_add(x_50, x_53);
lean::dec(x_50);
x_1 = x_52;
x_2 = x_54;
goto _start;
}
}
}
}
}
}
uint8 l_Array_anyMAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__6(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_2);
x_5 = lean::nat_dec_lt(x_3, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_6; 
lean::dec(x_3);
x_6 = 0;
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_7 = lean::array_fget(x_2, x_3);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::cnstr_get(x_1, 0);
x_10 = lean_name_dec_eq(x_8, x_9);
lean::dec(x_8);
if (x_10 == 0)
{
obj* x_11; obj* x_12; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_add(x_3, x_11);
lean::dec(x_3);
x_3 = x_12;
goto _start;
}
else
{
lean::dec(x_3);
return x_10;
}
}
}
}
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecializeAttrs___spec__7(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_io_initializing(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; uint8 x_5; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::unbox(x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_6; 
lean::dec(x_1);
x_6 = !lean::is_exclusive(x_3);
if (x_6 == 0)
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_3, 0);
lean::dec(x_7);
x_8 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
lean::cnstr_set_tag(x_3, 1);
lean::cnstr_set(x_3, 0, x_8);
return x_3;
}
else
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
lean::dec(x_3);
x_10 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_3);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_13 = lean::cnstr_get(x_3, 0);
lean::dec(x_13);
x_14 = lean::box(0);
lean::cnstr_set(x_3, 0, x_14);
x_15 = l___private_init_lean_environment_5__envExtensionsRef;
x_16 = lean::io_ref_get(x_15, x_3);
if (lean::obj_tag(x_16) == 0)
{
uint8 x_17; 
x_17 = !lean::is_exclusive(x_16);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_18 = lean::cnstr_get(x_16, 0);
lean::cnstr_set(x_16, 0, x_14);
x_19 = lean::array_get_size(x_18);
lean::dec(x_18);
x_20 = l_Lean_registerEnvExtensionUnsafe___at_Lean_registerTagAttribute___spec__6___closed__1;
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_1);
lean::cnstr_set(x_21, 2, x_20);
x_22 = lean::io_ref_get(x_15, x_16);
if (lean::obj_tag(x_22) == 0)
{
uint8 x_23; 
x_23 = !lean::is_exclusive(x_22);
if (x_23 == 0)
{
obj* x_24; obj* x_25; 
x_24 = lean::cnstr_get(x_22, 0);
lean::cnstr_set(x_22, 0, x_14);
x_25 = lean::io_ref_reset(x_15, x_22);
if (lean::obj_tag(x_25) == 0)
{
uint8 x_26; 
x_26 = !lean::is_exclusive(x_25);
if (x_26 == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_27 = lean::cnstr_get(x_25, 0);
lean::dec(x_27);
lean::cnstr_set(x_25, 0, x_14);
x_28 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_21);
x_29 = x_21;
x_30 = lean::array_push(x_24, x_29);
x_31 = lean::io_ref_set(x_15, x_30, x_25);
if (lean::obj_tag(x_31) == 0)
{
uint8 x_32; 
x_32 = !lean::is_exclusive(x_31);
if (x_32 == 0)
{
obj* x_33; 
x_33 = lean::cnstr_get(x_31, 0);
lean::dec(x_33);
lean::cnstr_set(x_31, 0, x_21);
return x_31;
}
else
{
obj* x_34; obj* x_35; 
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_21);
lean::cnstr_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8 x_36; 
lean::dec(x_21);
x_36 = !lean::is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
obj* x_37; obj* x_38; obj* x_39; 
x_37 = lean::cnstr_get(x_31, 0);
x_38 = lean::cnstr_get(x_31, 1);
lean::inc(x_38);
lean::inc(x_37);
lean::dec(x_31);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_40 = lean::cnstr_get(x_25, 1);
lean::inc(x_40);
lean::dec(x_25);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_14);
lean::cnstr_set(x_41, 1, x_40);
x_42 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_21);
x_43 = x_21;
x_44 = lean::array_push(x_24, x_43);
x_45 = lean::io_ref_set(x_15, x_44, x_41);
if (lean::obj_tag(x_45) == 0)
{
obj* x_46; obj* x_47; obj* x_48; 
x_46 = lean::cnstr_get(x_45, 1);
lean::inc(x_46);
if (lean::is_exclusive(x_45)) {
 lean::cnstr_release(x_45, 0);
 lean::cnstr_release(x_45, 1);
 x_47 = x_45;
} else {
 lean::dec_ref(x_45);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_21);
lean::cnstr_set(x_48, 1, x_46);
return x_48;
}
else
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
lean::dec(x_21);
x_49 = lean::cnstr_get(x_45, 0);
lean::inc(x_49);
x_50 = lean::cnstr_get(x_45, 1);
lean::inc(x_50);
if (lean::is_exclusive(x_45)) {
 lean::cnstr_release(x_45, 0);
 lean::cnstr_release(x_45, 1);
 x_51 = x_45;
} else {
 lean::dec_ref(x_45);
 x_51 = lean::box(0);
}
if (lean::is_scalar(x_51)) {
 x_52 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_52 = x_51;
}
lean::cnstr_set(x_52, 0, x_49);
lean::cnstr_set(x_52, 1, x_50);
return x_52;
}
}
}
else
{
uint8 x_53; 
lean::dec(x_24);
lean::dec(x_21);
x_53 = !lean::is_exclusive(x_25);
if (x_53 == 0)
{
return x_25;
}
else
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = lean::cnstr_get(x_25, 0);
x_55 = lean::cnstr_get(x_25, 1);
lean::inc(x_55);
lean::inc(x_54);
lean::dec(x_25);
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_54);
lean::cnstr_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_57 = lean::cnstr_get(x_22, 0);
x_58 = lean::cnstr_get(x_22, 1);
lean::inc(x_58);
lean::inc(x_57);
lean::dec(x_22);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_14);
lean::cnstr_set(x_59, 1, x_58);
x_60 = lean::io_ref_reset(x_15, x_59);
if (lean::obj_tag(x_60) == 0)
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_61 = lean::cnstr_get(x_60, 1);
lean::inc(x_61);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_release(x_60, 0);
 lean::cnstr_release(x_60, 1);
 x_62 = x_60;
} else {
 lean::dec_ref(x_60);
 x_62 = lean::box(0);
}
if (lean::is_scalar(x_62)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_62;
}
lean::cnstr_set(x_63, 0, x_14);
lean::cnstr_set(x_63, 1, x_61);
x_64 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_21);
x_65 = x_21;
x_66 = lean::array_push(x_57, x_65);
x_67 = lean::io_ref_set(x_15, x_66, x_63);
if (lean::obj_tag(x_67) == 0)
{
obj* x_68; obj* x_69; obj* x_70; 
x_68 = lean::cnstr_get(x_67, 1);
lean::inc(x_68);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_release(x_67, 0);
 lean::cnstr_release(x_67, 1);
 x_69 = x_67;
} else {
 lean::dec_ref(x_67);
 x_69 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_69;
}
lean::cnstr_set(x_70, 0, x_21);
lean::cnstr_set(x_70, 1, x_68);
return x_70;
}
else
{
obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_21);
x_71 = lean::cnstr_get(x_67, 0);
lean::inc(x_71);
x_72 = lean::cnstr_get(x_67, 1);
lean::inc(x_72);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_release(x_67, 0);
 lean::cnstr_release(x_67, 1);
 x_73 = x_67;
} else {
 lean::dec_ref(x_67);
 x_73 = lean::box(0);
}
if (lean::is_scalar(x_73)) {
 x_74 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_74 = x_73;
}
lean::cnstr_set(x_74, 0, x_71);
lean::cnstr_set(x_74, 1, x_72);
return x_74;
}
}
else
{
obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
lean::dec(x_57);
lean::dec(x_21);
x_75 = lean::cnstr_get(x_60, 0);
lean::inc(x_75);
x_76 = lean::cnstr_get(x_60, 1);
lean::inc(x_76);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_release(x_60, 0);
 lean::cnstr_release(x_60, 1);
 x_77 = x_60;
} else {
 lean::dec_ref(x_60);
 x_77 = lean::box(0);
}
if (lean::is_scalar(x_77)) {
 x_78 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_78 = x_77;
}
lean::cnstr_set(x_78, 0, x_75);
lean::cnstr_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
uint8 x_79; 
lean::dec(x_21);
x_79 = !lean::is_exclusive(x_22);
if (x_79 == 0)
{
return x_22;
}
else
{
obj* x_80; obj* x_81; obj* x_82; 
x_80 = lean::cnstr_get(x_22, 0);
x_81 = lean::cnstr_get(x_22, 1);
lean::inc(x_81);
lean::inc(x_80);
lean::dec(x_22);
x_82 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_82, 0, x_80);
lean::cnstr_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
x_83 = lean::cnstr_get(x_16, 0);
x_84 = lean::cnstr_get(x_16, 1);
lean::inc(x_84);
lean::inc(x_83);
lean::dec(x_16);
x_85 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_85, 0, x_14);
lean::cnstr_set(x_85, 1, x_84);
x_86 = lean::array_get_size(x_83);
lean::dec(x_83);
x_87 = l_Lean_registerEnvExtensionUnsafe___at_Lean_registerTagAttribute___spec__6___closed__1;
x_88 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_88, 0, x_86);
lean::cnstr_set(x_88, 1, x_1);
lean::cnstr_set(x_88, 2, x_87);
x_89 = lean::io_ref_get(x_15, x_85);
if (lean::obj_tag(x_89) == 0)
{
obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
x_90 = lean::cnstr_get(x_89, 0);
lean::inc(x_90);
x_91 = lean::cnstr_get(x_89, 1);
lean::inc(x_91);
if (lean::is_exclusive(x_89)) {
 lean::cnstr_release(x_89, 0);
 lean::cnstr_release(x_89, 1);
 x_92 = x_89;
} else {
 lean::dec_ref(x_89);
 x_92 = lean::box(0);
}
if (lean::is_scalar(x_92)) {
 x_93 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_93 = x_92;
}
lean::cnstr_set(x_93, 0, x_14);
lean::cnstr_set(x_93, 1, x_91);
x_94 = lean::io_ref_reset(x_15, x_93);
if (lean::obj_tag(x_94) == 0)
{
obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
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
lean::cnstr_set(x_97, 0, x_14);
lean::cnstr_set(x_97, 1, x_95);
x_98 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_88);
x_99 = x_88;
x_100 = lean::array_push(x_90, x_99);
x_101 = lean::io_ref_set(x_15, x_100, x_97);
if (lean::obj_tag(x_101) == 0)
{
obj* x_102; obj* x_103; obj* x_104; 
x_102 = lean::cnstr_get(x_101, 1);
lean::inc(x_102);
if (lean::is_exclusive(x_101)) {
 lean::cnstr_release(x_101, 0);
 lean::cnstr_release(x_101, 1);
 x_103 = x_101;
} else {
 lean::dec_ref(x_101);
 x_103 = lean::box(0);
}
if (lean::is_scalar(x_103)) {
 x_104 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_104 = x_103;
}
lean::cnstr_set(x_104, 0, x_88);
lean::cnstr_set(x_104, 1, x_102);
return x_104;
}
else
{
obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
lean::dec(x_88);
x_105 = lean::cnstr_get(x_101, 0);
lean::inc(x_105);
x_106 = lean::cnstr_get(x_101, 1);
lean::inc(x_106);
if (lean::is_exclusive(x_101)) {
 lean::cnstr_release(x_101, 0);
 lean::cnstr_release(x_101, 1);
 x_107 = x_101;
} else {
 lean::dec_ref(x_101);
 x_107 = lean::box(0);
}
if (lean::is_scalar(x_107)) {
 x_108 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_108 = x_107;
}
lean::cnstr_set(x_108, 0, x_105);
lean::cnstr_set(x_108, 1, x_106);
return x_108;
}
}
else
{
obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_90);
lean::dec(x_88);
x_109 = lean::cnstr_get(x_94, 0);
lean::inc(x_109);
x_110 = lean::cnstr_get(x_94, 1);
lean::inc(x_110);
if (lean::is_exclusive(x_94)) {
 lean::cnstr_release(x_94, 0);
 lean::cnstr_release(x_94, 1);
 x_111 = x_94;
} else {
 lean::dec_ref(x_94);
 x_111 = lean::box(0);
}
if (lean::is_scalar(x_111)) {
 x_112 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_112 = x_111;
}
lean::cnstr_set(x_112, 0, x_109);
lean::cnstr_set(x_112, 1, x_110);
return x_112;
}
}
else
{
obj* x_113; obj* x_114; obj* x_115; obj* x_116; 
lean::dec(x_88);
x_113 = lean::cnstr_get(x_89, 0);
lean::inc(x_113);
x_114 = lean::cnstr_get(x_89, 1);
lean::inc(x_114);
if (lean::is_exclusive(x_89)) {
 lean::cnstr_release(x_89, 0);
 lean::cnstr_release(x_89, 1);
 x_115 = x_89;
} else {
 lean::dec_ref(x_89);
 x_115 = lean::box(0);
}
if (lean::is_scalar(x_115)) {
 x_116 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_116 = x_115;
}
lean::cnstr_set(x_116, 0, x_113);
lean::cnstr_set(x_116, 1, x_114);
return x_116;
}
}
}
else
{
uint8 x_117; 
lean::dec(x_1);
x_117 = !lean::is_exclusive(x_16);
if (x_117 == 0)
{
return x_16;
}
else
{
obj* x_118; obj* x_119; obj* x_120; 
x_118 = lean::cnstr_get(x_16, 0);
x_119 = lean::cnstr_get(x_16, 1);
lean::inc(x_119);
lean::inc(x_118);
lean::dec(x_16);
x_120 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_120, 0, x_118);
lean::cnstr_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; 
x_121 = lean::cnstr_get(x_3, 1);
lean::inc(x_121);
lean::dec(x_3);
x_122 = lean::box(0);
x_123 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_123, 0, x_122);
lean::cnstr_set(x_123, 1, x_121);
x_124 = l___private_init_lean_environment_5__envExtensionsRef;
x_125 = lean::io_ref_get(x_124, x_123);
if (lean::obj_tag(x_125) == 0)
{
obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
x_126 = lean::cnstr_get(x_125, 0);
lean::inc(x_126);
x_127 = lean::cnstr_get(x_125, 1);
lean::inc(x_127);
if (lean::is_exclusive(x_125)) {
 lean::cnstr_release(x_125, 0);
 lean::cnstr_release(x_125, 1);
 x_128 = x_125;
} else {
 lean::dec_ref(x_125);
 x_128 = lean::box(0);
}
if (lean::is_scalar(x_128)) {
 x_129 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_129 = x_128;
}
lean::cnstr_set(x_129, 0, x_122);
lean::cnstr_set(x_129, 1, x_127);
x_130 = lean::array_get_size(x_126);
lean::dec(x_126);
x_131 = l_Lean_registerEnvExtensionUnsafe___at_Lean_registerTagAttribute___spec__6___closed__1;
x_132 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_132, 0, x_130);
lean::cnstr_set(x_132, 1, x_1);
lean::cnstr_set(x_132, 2, x_131);
x_133 = lean::io_ref_get(x_124, x_129);
if (lean::obj_tag(x_133) == 0)
{
obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; 
x_134 = lean::cnstr_get(x_133, 0);
lean::inc(x_134);
x_135 = lean::cnstr_get(x_133, 1);
lean::inc(x_135);
if (lean::is_exclusive(x_133)) {
 lean::cnstr_release(x_133, 0);
 lean::cnstr_release(x_133, 1);
 x_136 = x_133;
} else {
 lean::dec_ref(x_133);
 x_136 = lean::box(0);
}
if (lean::is_scalar(x_136)) {
 x_137 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_137 = x_136;
}
lean::cnstr_set(x_137, 0, x_122);
lean::cnstr_set(x_137, 1, x_135);
x_138 = lean::io_ref_reset(x_124, x_137);
if (lean::obj_tag(x_138) == 0)
{
obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; 
x_139 = lean::cnstr_get(x_138, 1);
lean::inc(x_139);
if (lean::is_exclusive(x_138)) {
 lean::cnstr_release(x_138, 0);
 lean::cnstr_release(x_138, 1);
 x_140 = x_138;
} else {
 lean::dec_ref(x_138);
 x_140 = lean::box(0);
}
if (lean::is_scalar(x_140)) {
 x_141 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_141 = x_140;
}
lean::cnstr_set(x_141, 0, x_122);
lean::cnstr_set(x_141, 1, x_139);
x_142 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_132);
x_143 = x_132;
x_144 = lean::array_push(x_134, x_143);
x_145 = lean::io_ref_set(x_124, x_144, x_141);
if (lean::obj_tag(x_145) == 0)
{
obj* x_146; obj* x_147; obj* x_148; 
x_146 = lean::cnstr_get(x_145, 1);
lean::inc(x_146);
if (lean::is_exclusive(x_145)) {
 lean::cnstr_release(x_145, 0);
 lean::cnstr_release(x_145, 1);
 x_147 = x_145;
} else {
 lean::dec_ref(x_145);
 x_147 = lean::box(0);
}
if (lean::is_scalar(x_147)) {
 x_148 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_148 = x_147;
}
lean::cnstr_set(x_148, 0, x_132);
lean::cnstr_set(x_148, 1, x_146);
return x_148;
}
else
{
obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
lean::dec(x_132);
x_149 = lean::cnstr_get(x_145, 0);
lean::inc(x_149);
x_150 = lean::cnstr_get(x_145, 1);
lean::inc(x_150);
if (lean::is_exclusive(x_145)) {
 lean::cnstr_release(x_145, 0);
 lean::cnstr_release(x_145, 1);
 x_151 = x_145;
} else {
 lean::dec_ref(x_145);
 x_151 = lean::box(0);
}
if (lean::is_scalar(x_151)) {
 x_152 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_152 = x_151;
}
lean::cnstr_set(x_152, 0, x_149);
lean::cnstr_set(x_152, 1, x_150);
return x_152;
}
}
else
{
obj* x_153; obj* x_154; obj* x_155; obj* x_156; 
lean::dec(x_134);
lean::dec(x_132);
x_153 = lean::cnstr_get(x_138, 0);
lean::inc(x_153);
x_154 = lean::cnstr_get(x_138, 1);
lean::inc(x_154);
if (lean::is_exclusive(x_138)) {
 lean::cnstr_release(x_138, 0);
 lean::cnstr_release(x_138, 1);
 x_155 = x_138;
} else {
 lean::dec_ref(x_138);
 x_155 = lean::box(0);
}
if (lean::is_scalar(x_155)) {
 x_156 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_156 = x_155;
}
lean::cnstr_set(x_156, 0, x_153);
lean::cnstr_set(x_156, 1, x_154);
return x_156;
}
}
else
{
obj* x_157; obj* x_158; obj* x_159; obj* x_160; 
lean::dec(x_132);
x_157 = lean::cnstr_get(x_133, 0);
lean::inc(x_157);
x_158 = lean::cnstr_get(x_133, 1);
lean::inc(x_158);
if (lean::is_exclusive(x_133)) {
 lean::cnstr_release(x_133, 0);
 lean::cnstr_release(x_133, 1);
 x_159 = x_133;
} else {
 lean::dec_ref(x_133);
 x_159 = lean::box(0);
}
if (lean::is_scalar(x_159)) {
 x_160 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_160 = x_159;
}
lean::cnstr_set(x_160, 0, x_157);
lean::cnstr_set(x_160, 1, x_158);
return x_160;
}
}
else
{
obj* x_161; obj* x_162; obj* x_163; obj* x_164; 
lean::dec(x_1);
x_161 = lean::cnstr_get(x_125, 0);
lean::inc(x_161);
x_162 = lean::cnstr_get(x_125, 1);
lean::inc(x_162);
if (lean::is_exclusive(x_125)) {
 lean::cnstr_release(x_125, 0);
 lean::cnstr_release(x_125, 1);
 x_163 = x_125;
} else {
 lean::dec_ref(x_125);
 x_163 = lean::box(0);
}
if (lean::is_scalar(x_163)) {
 x_164 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_164 = x_163;
}
lean::cnstr_set(x_164, 0, x_161);
lean::cnstr_set(x_164, 1, x_162);
return x_164;
}
}
}
}
else
{
uint8 x_165; 
lean::dec(x_1);
x_165 = !lean::is_exclusive(x_3);
if (x_165 == 0)
{
return x_3;
}
else
{
obj* x_166; obj* x_167; obj* x_168; 
x_166 = lean::cnstr_get(x_3, 0);
x_167 = lean::cnstr_get(x_3, 1);
lean::inc(x_167);
lean::inc(x_166);
lean::dec(x_3);
x_168 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_168, 0, x_166);
lean::cnstr_set(x_168, 1, x_167);
return x_168;
}
}
}
}
obj* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Compiler_mkSpecializeAttrs___spec__5(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l___private_init_lean_environment_8__persistentEnvExtensionsRef;
x_4 = lean::io_ref_get(x_3, x_2);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::cnstr_get(x_4, 0);
x_7 = lean::mk_nat_obj(0u);
x_8 = l_Array_anyMAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__6(x_1, x_6, x_7);
lean::dec(x_6);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_9 = lean::box(0);
lean::cnstr_set(x_4, 0, x_9);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
x_11 = l_Array_empty___closed__1;
lean::inc(x_10);
x_12 = lean::apply_1(x_10, x_11);
x_13 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_bind___rarg), 3, 2);
lean::closure_set(x_14, 0, x_12);
lean::closure_set(x_14, 1, x_13);
x_15 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecializeAttrs___spec__7(x_14, x_4);
if (lean::obj_tag(x_15) == 0)
{
uint8 x_16; 
x_16 = !lean::is_exclusive(x_15);
if (x_16 == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_17 = lean::cnstr_get(x_15, 0);
lean::cnstr_set(x_15, 0, x_9);
x_18 = lean::cnstr_get(x_1, 0);
lean::inc(x_18);
x_19 = lean::cnstr_get(x_1, 2);
lean::inc(x_19);
x_20 = lean::cnstr_get(x_1, 3);
lean::inc(x_20);
x_21 = lean::cnstr_get(x_1, 4);
lean::inc(x_21);
lean::dec(x_1);
x_22 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_22, 0, x_17);
lean::cnstr_set(x_22, 1, x_18);
lean::cnstr_set(x_22, 2, x_10);
lean::cnstr_set(x_22, 3, x_19);
lean::cnstr_set(x_22, 4, x_20);
lean::cnstr_set(x_22, 5, x_21);
x_23 = lean::io_ref_get(x_3, x_15);
if (lean::obj_tag(x_23) == 0)
{
uint8 x_24; 
x_24 = !lean::is_exclusive(x_23);
if (x_24 == 0)
{
obj* x_25; obj* x_26; 
x_25 = lean::cnstr_get(x_23, 0);
lean::cnstr_set(x_23, 0, x_9);
x_26 = lean::io_ref_reset(x_3, x_23);
if (lean::obj_tag(x_26) == 0)
{
uint8 x_27; 
x_27 = !lean::is_exclusive(x_26);
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_28 = lean::cnstr_get(x_26, 0);
lean::dec(x_28);
lean::cnstr_set(x_26, 0, x_9);
x_29 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_22);
x_30 = x_22;
x_31 = lean::array_push(x_25, x_30);
x_32 = lean::io_ref_set(x_3, x_31, x_26);
if (lean::obj_tag(x_32) == 0)
{
uint8 x_33; 
x_33 = !lean::is_exclusive(x_32);
if (x_33 == 0)
{
obj* x_34; 
x_34 = lean::cnstr_get(x_32, 0);
lean::dec(x_34);
lean::cnstr_set(x_32, 0, x_22);
return x_32;
}
else
{
obj* x_35; obj* x_36; 
x_35 = lean::cnstr_get(x_32, 1);
lean::inc(x_35);
lean::dec(x_32);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_22);
lean::cnstr_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8 x_37; 
lean::dec(x_22);
x_37 = !lean::is_exclusive(x_32);
if (x_37 == 0)
{
return x_32;
}
else
{
obj* x_38; obj* x_39; obj* x_40; 
x_38 = lean::cnstr_get(x_32, 0);
x_39 = lean::cnstr_get(x_32, 1);
lean::inc(x_39);
lean::inc(x_38);
lean::dec(x_32);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_38);
lean::cnstr_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_41 = lean::cnstr_get(x_26, 1);
lean::inc(x_41);
lean::dec(x_26);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_9);
lean::cnstr_set(x_42, 1, x_41);
x_43 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_22);
x_44 = x_22;
x_45 = lean::array_push(x_25, x_44);
x_46 = lean::io_ref_set(x_3, x_45, x_42);
if (lean::obj_tag(x_46) == 0)
{
obj* x_47; obj* x_48; obj* x_49; 
x_47 = lean::cnstr_get(x_46, 1);
lean::inc(x_47);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 lean::cnstr_release(x_46, 1);
 x_48 = x_46;
} else {
 lean::dec_ref(x_46);
 x_48 = lean::box(0);
}
if (lean::is_scalar(x_48)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_48;
}
lean::cnstr_set(x_49, 0, x_22);
lean::cnstr_set(x_49, 1, x_47);
return x_49;
}
else
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_22);
x_50 = lean::cnstr_get(x_46, 0);
lean::inc(x_50);
x_51 = lean::cnstr_get(x_46, 1);
lean::inc(x_51);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 lean::cnstr_release(x_46, 1);
 x_52 = x_46;
} else {
 lean::dec_ref(x_46);
 x_52 = lean::box(0);
}
if (lean::is_scalar(x_52)) {
 x_53 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_53 = x_52;
}
lean::cnstr_set(x_53, 0, x_50);
lean::cnstr_set(x_53, 1, x_51);
return x_53;
}
}
}
else
{
uint8 x_54; 
lean::dec(x_25);
lean::dec(x_22);
x_54 = !lean::is_exclusive(x_26);
if (x_54 == 0)
{
return x_26;
}
else
{
obj* x_55; obj* x_56; obj* x_57; 
x_55 = lean::cnstr_get(x_26, 0);
x_56 = lean::cnstr_get(x_26, 1);
lean::inc(x_56);
lean::inc(x_55);
lean::dec(x_26);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_55);
lean::cnstr_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_58 = lean::cnstr_get(x_23, 0);
x_59 = lean::cnstr_get(x_23, 1);
lean::inc(x_59);
lean::inc(x_58);
lean::dec(x_23);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_9);
lean::cnstr_set(x_60, 1, x_59);
x_61 = lean::io_ref_reset(x_3, x_60);
if (lean::obj_tag(x_61) == 0)
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_62 = lean::cnstr_get(x_61, 1);
lean::inc(x_62);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_release(x_61, 0);
 lean::cnstr_release(x_61, 1);
 x_63 = x_61;
} else {
 lean::dec_ref(x_61);
 x_63 = lean::box(0);
}
if (lean::is_scalar(x_63)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_63;
}
lean::cnstr_set(x_64, 0, x_9);
lean::cnstr_set(x_64, 1, x_62);
x_65 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_22);
x_66 = x_22;
x_67 = lean::array_push(x_58, x_66);
x_68 = lean::io_ref_set(x_3, x_67, x_64);
if (lean::obj_tag(x_68) == 0)
{
obj* x_69; obj* x_70; obj* x_71; 
x_69 = lean::cnstr_get(x_68, 1);
lean::inc(x_69);
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 lean::cnstr_release(x_68, 1);
 x_70 = x_68;
} else {
 lean::dec_ref(x_68);
 x_70 = lean::box(0);
}
if (lean::is_scalar(x_70)) {
 x_71 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_71 = x_70;
}
lean::cnstr_set(x_71, 0, x_22);
lean::cnstr_set(x_71, 1, x_69);
return x_71;
}
else
{
obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
lean::dec(x_22);
x_72 = lean::cnstr_get(x_68, 0);
lean::inc(x_72);
x_73 = lean::cnstr_get(x_68, 1);
lean::inc(x_73);
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 lean::cnstr_release(x_68, 1);
 x_74 = x_68;
} else {
 lean::dec_ref(x_68);
 x_74 = lean::box(0);
}
if (lean::is_scalar(x_74)) {
 x_75 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_75 = x_74;
}
lean::cnstr_set(x_75, 0, x_72);
lean::cnstr_set(x_75, 1, x_73);
return x_75;
}
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_58);
lean::dec(x_22);
x_76 = lean::cnstr_get(x_61, 0);
lean::inc(x_76);
x_77 = lean::cnstr_get(x_61, 1);
lean::inc(x_77);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_release(x_61, 0);
 lean::cnstr_release(x_61, 1);
 x_78 = x_61;
} else {
 lean::dec_ref(x_61);
 x_78 = lean::box(0);
}
if (lean::is_scalar(x_78)) {
 x_79 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_79 = x_78;
}
lean::cnstr_set(x_79, 0, x_76);
lean::cnstr_set(x_79, 1, x_77);
return x_79;
}
}
}
else
{
uint8 x_80; 
lean::dec(x_22);
x_80 = !lean::is_exclusive(x_23);
if (x_80 == 0)
{
return x_23;
}
else
{
obj* x_81; obj* x_82; obj* x_83; 
x_81 = lean::cnstr_get(x_23, 0);
x_82 = lean::cnstr_get(x_23, 1);
lean::inc(x_82);
lean::inc(x_81);
lean::dec(x_23);
x_83 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_83, 0, x_81);
lean::cnstr_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_84 = lean::cnstr_get(x_15, 0);
x_85 = lean::cnstr_get(x_15, 1);
lean::inc(x_85);
lean::inc(x_84);
lean::dec(x_15);
x_86 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_86, 0, x_9);
lean::cnstr_set(x_86, 1, x_85);
x_87 = lean::cnstr_get(x_1, 0);
lean::inc(x_87);
x_88 = lean::cnstr_get(x_1, 2);
lean::inc(x_88);
x_89 = lean::cnstr_get(x_1, 3);
lean::inc(x_89);
x_90 = lean::cnstr_get(x_1, 4);
lean::inc(x_90);
lean::dec(x_1);
x_91 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_91, 0, x_84);
lean::cnstr_set(x_91, 1, x_87);
lean::cnstr_set(x_91, 2, x_10);
lean::cnstr_set(x_91, 3, x_88);
lean::cnstr_set(x_91, 4, x_89);
lean::cnstr_set(x_91, 5, x_90);
x_92 = lean::io_ref_get(x_3, x_86);
if (lean::obj_tag(x_92) == 0)
{
obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_93 = lean::cnstr_get(x_92, 0);
lean::inc(x_93);
x_94 = lean::cnstr_get(x_92, 1);
lean::inc(x_94);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 lean::cnstr_release(x_92, 1);
 x_95 = x_92;
} else {
 lean::dec_ref(x_92);
 x_95 = lean::box(0);
}
if (lean::is_scalar(x_95)) {
 x_96 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_96 = x_95;
}
lean::cnstr_set(x_96, 0, x_9);
lean::cnstr_set(x_96, 1, x_94);
x_97 = lean::io_ref_reset(x_3, x_96);
if (lean::obj_tag(x_97) == 0)
{
obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
x_98 = lean::cnstr_get(x_97, 1);
lean::inc(x_98);
if (lean::is_exclusive(x_97)) {
 lean::cnstr_release(x_97, 0);
 lean::cnstr_release(x_97, 1);
 x_99 = x_97;
} else {
 lean::dec_ref(x_97);
 x_99 = lean::box(0);
}
if (lean::is_scalar(x_99)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_99;
}
lean::cnstr_set(x_100, 0, x_9);
lean::cnstr_set(x_100, 1, x_98);
x_101 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_91);
x_102 = x_91;
x_103 = lean::array_push(x_93, x_102);
x_104 = lean::io_ref_set(x_3, x_103, x_100);
if (lean::obj_tag(x_104) == 0)
{
obj* x_105; obj* x_106; obj* x_107; 
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
lean::cnstr_set(x_107, 0, x_91);
lean::cnstr_set(x_107, 1, x_105);
return x_107;
}
else
{
obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
lean::dec(x_91);
x_108 = lean::cnstr_get(x_104, 0);
lean::inc(x_108);
x_109 = lean::cnstr_get(x_104, 1);
lean::inc(x_109);
if (lean::is_exclusive(x_104)) {
 lean::cnstr_release(x_104, 0);
 lean::cnstr_release(x_104, 1);
 x_110 = x_104;
} else {
 lean::dec_ref(x_104);
 x_110 = lean::box(0);
}
if (lean::is_scalar(x_110)) {
 x_111 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_111 = x_110;
}
lean::cnstr_set(x_111, 0, x_108);
lean::cnstr_set(x_111, 1, x_109);
return x_111;
}
}
else
{
obj* x_112; obj* x_113; obj* x_114; obj* x_115; 
lean::dec(x_93);
lean::dec(x_91);
x_112 = lean::cnstr_get(x_97, 0);
lean::inc(x_112);
x_113 = lean::cnstr_get(x_97, 1);
lean::inc(x_113);
if (lean::is_exclusive(x_97)) {
 lean::cnstr_release(x_97, 0);
 lean::cnstr_release(x_97, 1);
 x_114 = x_97;
} else {
 lean::dec_ref(x_97);
 x_114 = lean::box(0);
}
if (lean::is_scalar(x_114)) {
 x_115 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_115 = x_114;
}
lean::cnstr_set(x_115, 0, x_112);
lean::cnstr_set(x_115, 1, x_113);
return x_115;
}
}
else
{
obj* x_116; obj* x_117; obj* x_118; obj* x_119; 
lean::dec(x_91);
x_116 = lean::cnstr_get(x_92, 0);
lean::inc(x_116);
x_117 = lean::cnstr_get(x_92, 1);
lean::inc(x_117);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 lean::cnstr_release(x_92, 1);
 x_118 = x_92;
} else {
 lean::dec_ref(x_92);
 x_118 = lean::box(0);
}
if (lean::is_scalar(x_118)) {
 x_119 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_119 = x_118;
}
lean::cnstr_set(x_119, 0, x_116);
lean::cnstr_set(x_119, 1, x_117);
return x_119;
}
}
}
else
{
uint8 x_120; 
lean::dec(x_10);
lean::dec(x_1);
x_120 = !lean::is_exclusive(x_15);
if (x_120 == 0)
{
return x_15;
}
else
{
obj* x_121; obj* x_122; obj* x_123; 
x_121 = lean::cnstr_get(x_15, 0);
x_122 = lean::cnstr_get(x_15, 1);
lean::inc(x_122);
lean::inc(x_121);
lean::dec(x_15);
x_123 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_123, 0, x_121);
lean::cnstr_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; 
x_124 = lean::cnstr_get(x_1, 0);
lean::inc(x_124);
lean::dec(x_1);
x_125 = l_Lean_Name_toString___closed__1;
x_126 = l_Lean_Name_toStringWithSep___main(x_125, x_124);
x_127 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_128 = lean::string_append(x_127, x_126);
lean::dec(x_126);
x_129 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_130 = lean::string_append(x_128, x_129);
lean::cnstr_set_tag(x_4, 1);
lean::cnstr_set(x_4, 0, x_130);
return x_4;
}
}
else
{
obj* x_131; obj* x_132; obj* x_133; uint8 x_134; 
x_131 = lean::cnstr_get(x_4, 0);
x_132 = lean::cnstr_get(x_4, 1);
lean::inc(x_132);
lean::inc(x_131);
lean::dec(x_4);
x_133 = lean::mk_nat_obj(0u);
x_134 = l_Array_anyMAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__6(x_1, x_131, x_133);
lean::dec(x_131);
if (x_134 == 0)
{
obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; 
x_135 = lean::box(0);
x_136 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_136, 0, x_135);
lean::cnstr_set(x_136, 1, x_132);
x_137 = lean::cnstr_get(x_1, 1);
lean::inc(x_137);
x_138 = l_Array_empty___closed__1;
lean::inc(x_137);
x_139 = lean::apply_1(x_137, x_138);
x_140 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_141 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_bind___rarg), 3, 2);
lean::closure_set(x_141, 0, x_139);
lean::closure_set(x_141, 1, x_140);
x_142 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecializeAttrs___spec__7(x_141, x_136);
if (lean::obj_tag(x_142) == 0)
{
obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
x_143 = lean::cnstr_get(x_142, 0);
lean::inc(x_143);
x_144 = lean::cnstr_get(x_142, 1);
lean::inc(x_144);
if (lean::is_exclusive(x_142)) {
 lean::cnstr_release(x_142, 0);
 lean::cnstr_release(x_142, 1);
 x_145 = x_142;
} else {
 lean::dec_ref(x_142);
 x_145 = lean::box(0);
}
if (lean::is_scalar(x_145)) {
 x_146 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_146 = x_145;
}
lean::cnstr_set(x_146, 0, x_135);
lean::cnstr_set(x_146, 1, x_144);
x_147 = lean::cnstr_get(x_1, 0);
lean::inc(x_147);
x_148 = lean::cnstr_get(x_1, 2);
lean::inc(x_148);
x_149 = lean::cnstr_get(x_1, 3);
lean::inc(x_149);
x_150 = lean::cnstr_get(x_1, 4);
lean::inc(x_150);
lean::dec(x_1);
x_151 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_151, 0, x_143);
lean::cnstr_set(x_151, 1, x_147);
lean::cnstr_set(x_151, 2, x_137);
lean::cnstr_set(x_151, 3, x_148);
lean::cnstr_set(x_151, 4, x_149);
lean::cnstr_set(x_151, 5, x_150);
x_152 = lean::io_ref_get(x_3, x_146);
if (lean::obj_tag(x_152) == 0)
{
obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; 
x_153 = lean::cnstr_get(x_152, 0);
lean::inc(x_153);
x_154 = lean::cnstr_get(x_152, 1);
lean::inc(x_154);
if (lean::is_exclusive(x_152)) {
 lean::cnstr_release(x_152, 0);
 lean::cnstr_release(x_152, 1);
 x_155 = x_152;
} else {
 lean::dec_ref(x_152);
 x_155 = lean::box(0);
}
if (lean::is_scalar(x_155)) {
 x_156 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_156 = x_155;
}
lean::cnstr_set(x_156, 0, x_135);
lean::cnstr_set(x_156, 1, x_154);
x_157 = lean::io_ref_reset(x_3, x_156);
if (lean::obj_tag(x_157) == 0)
{
obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; 
x_158 = lean::cnstr_get(x_157, 1);
lean::inc(x_158);
if (lean::is_exclusive(x_157)) {
 lean::cnstr_release(x_157, 0);
 lean::cnstr_release(x_157, 1);
 x_159 = x_157;
} else {
 lean::dec_ref(x_157);
 x_159 = lean::box(0);
}
if (lean::is_scalar(x_159)) {
 x_160 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_160 = x_159;
}
lean::cnstr_set(x_160, 0, x_135);
lean::cnstr_set(x_160, 1, x_158);
x_161 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_151);
x_162 = x_151;
x_163 = lean::array_push(x_153, x_162);
x_164 = lean::io_ref_set(x_3, x_163, x_160);
if (lean::obj_tag(x_164) == 0)
{
obj* x_165; obj* x_166; obj* x_167; 
x_165 = lean::cnstr_get(x_164, 1);
lean::inc(x_165);
if (lean::is_exclusive(x_164)) {
 lean::cnstr_release(x_164, 0);
 lean::cnstr_release(x_164, 1);
 x_166 = x_164;
} else {
 lean::dec_ref(x_164);
 x_166 = lean::box(0);
}
if (lean::is_scalar(x_166)) {
 x_167 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_167 = x_166;
}
lean::cnstr_set(x_167, 0, x_151);
lean::cnstr_set(x_167, 1, x_165);
return x_167;
}
else
{
obj* x_168; obj* x_169; obj* x_170; obj* x_171; 
lean::dec(x_151);
x_168 = lean::cnstr_get(x_164, 0);
lean::inc(x_168);
x_169 = lean::cnstr_get(x_164, 1);
lean::inc(x_169);
if (lean::is_exclusive(x_164)) {
 lean::cnstr_release(x_164, 0);
 lean::cnstr_release(x_164, 1);
 x_170 = x_164;
} else {
 lean::dec_ref(x_164);
 x_170 = lean::box(0);
}
if (lean::is_scalar(x_170)) {
 x_171 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_171 = x_170;
}
lean::cnstr_set(x_171, 0, x_168);
lean::cnstr_set(x_171, 1, x_169);
return x_171;
}
}
else
{
obj* x_172; obj* x_173; obj* x_174; obj* x_175; 
lean::dec(x_153);
lean::dec(x_151);
x_172 = lean::cnstr_get(x_157, 0);
lean::inc(x_172);
x_173 = lean::cnstr_get(x_157, 1);
lean::inc(x_173);
if (lean::is_exclusive(x_157)) {
 lean::cnstr_release(x_157, 0);
 lean::cnstr_release(x_157, 1);
 x_174 = x_157;
} else {
 lean::dec_ref(x_157);
 x_174 = lean::box(0);
}
if (lean::is_scalar(x_174)) {
 x_175 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_175 = x_174;
}
lean::cnstr_set(x_175, 0, x_172);
lean::cnstr_set(x_175, 1, x_173);
return x_175;
}
}
else
{
obj* x_176; obj* x_177; obj* x_178; obj* x_179; 
lean::dec(x_151);
x_176 = lean::cnstr_get(x_152, 0);
lean::inc(x_176);
x_177 = lean::cnstr_get(x_152, 1);
lean::inc(x_177);
if (lean::is_exclusive(x_152)) {
 lean::cnstr_release(x_152, 0);
 lean::cnstr_release(x_152, 1);
 x_178 = x_152;
} else {
 lean::dec_ref(x_152);
 x_178 = lean::box(0);
}
if (lean::is_scalar(x_178)) {
 x_179 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_179 = x_178;
}
lean::cnstr_set(x_179, 0, x_176);
lean::cnstr_set(x_179, 1, x_177);
return x_179;
}
}
else
{
obj* x_180; obj* x_181; obj* x_182; obj* x_183; 
lean::dec(x_137);
lean::dec(x_1);
x_180 = lean::cnstr_get(x_142, 0);
lean::inc(x_180);
x_181 = lean::cnstr_get(x_142, 1);
lean::inc(x_181);
if (lean::is_exclusive(x_142)) {
 lean::cnstr_release(x_142, 0);
 lean::cnstr_release(x_142, 1);
 x_182 = x_142;
} else {
 lean::dec_ref(x_142);
 x_182 = lean::box(0);
}
if (lean::is_scalar(x_182)) {
 x_183 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_183 = x_182;
}
lean::cnstr_set(x_183, 0, x_180);
lean::cnstr_set(x_183, 1, x_181);
return x_183;
}
}
else
{
obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; 
x_184 = lean::cnstr_get(x_1, 0);
lean::inc(x_184);
lean::dec(x_1);
x_185 = l_Lean_Name_toString___closed__1;
x_186 = l_Lean_Name_toStringWithSep___main(x_185, x_184);
x_187 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_188 = lean::string_append(x_187, x_186);
lean::dec(x_186);
x_189 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_190 = lean::string_append(x_188, x_189);
x_191 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_191, 0, x_190);
lean::cnstr_set(x_191, 1, x_132);
return x_191;
}
}
}
else
{
uint8 x_192; 
lean::dec(x_1);
x_192 = !lean::is_exclusive(x_4);
if (x_192 == 0)
{
return x_4;
}
else
{
obj* x_193; obj* x_194; obj* x_195; 
x_193 = lean::cnstr_get(x_4, 0);
x_194 = lean::cnstr_get(x_4, 1);
lean::inc(x_194);
lean::inc(x_193);
lean::dec(x_4);
x_195 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_195, 0, x_193);
lean::cnstr_set(x_195, 1, x_194);
return x_195;
}
}
}
}
obj* l_List_map___main___at_Lean_Compiler_mkSpecializeAttrs___spec__8___lambda__1(obj* x_1, obj* x_2, uint8 x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, uint8 x_8, obj* x_9) {
_start:
{
if (x_8 == 0)
{
uint8 x_10; 
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_2);
x_10 = !lean::is_exclusive(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_11 = lean::cnstr_get(x_9, 0);
lean::dec(x_11);
x_12 = l_Lean_Name_toString___closed__1;
x_13 = l_Lean_Name_toStringWithSep___main(x_12, x_1);
x_14 = l_Lean_registerTagAttribute___lambda__4___closed__1;
x_15 = lean::string_append(x_14, x_13);
lean::dec(x_13);
x_16 = l_Lean_registerTagAttribute___lambda__4___closed__3;
x_17 = lean::string_append(x_15, x_16);
lean::cnstr_set_tag(x_9, 1);
lean::cnstr_set(x_9, 0, x_17);
return x_9;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_18 = lean::cnstr_get(x_9, 1);
lean::inc(x_18);
lean::dec(x_9);
x_19 = l_Lean_Name_toString___closed__1;
x_20 = l_Lean_Name_toStringWithSep___main(x_19, x_1);
x_21 = l_Lean_registerTagAttribute___lambda__4___closed__1;
x_22 = lean::string_append(x_21, x_20);
lean::dec(x_20);
x_23 = l_Lean_registerTagAttribute___lambda__4___closed__3;
x_24 = lean::string_append(x_22, x_23);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_18);
return x_25;
}
}
else
{
uint8 x_26; 
x_26 = !lean::is_exclusive(x_9);
if (x_26 == 0)
{
obj* x_27; obj* x_28; 
x_27 = lean::cnstr_get(x_9, 0);
lean::dec(x_27);
x_28 = l_Lean_Environment_getModuleIdxFor(x_5, x_6);
if (lean::obj_tag(x_28) == 0)
{
obj* x_29; obj* x_30; 
x_29 = lean::box(x_3);
lean::inc(x_6);
lean::inc(x_5);
x_30 = lean::apply_3(x_2, x_5, x_6, x_29);
if (lean::obj_tag(x_30) == 0)
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
lean::dec(x_30);
x_32 = l_Lean_Name_toString___closed__1;
x_33 = l_Lean_Name_toStringWithSep___main(x_32, x_1);
x_34 = l_Lean_registerTagAttribute___lambda__4___closed__1;
x_35 = lean::string_append(x_34, x_33);
lean::dec(x_33);
x_36 = l_Lean_registerTagAttribute___lambda__4___closed__4;
x_37 = lean::string_append(x_35, x_36);
x_38 = lean::string_append(x_37, x_31);
lean::dec(x_31);
lean::cnstr_set_tag(x_9, 1);
lean::cnstr_set(x_9, 0, x_38);
return x_9;
}
else
{
obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_30);
lean::dec(x_1);
x_39 = lean::box(x_3);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_6);
lean::cnstr_set(x_40, 1, x_39);
x_41 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_4, x_5, x_40);
lean::cnstr_set(x_9, 0, x_41);
return x_9;
}
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
lean::dec(x_28);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_2);
x_42 = l_Lean_Name_toString___closed__1;
x_43 = l_Lean_Name_toStringWithSep___main(x_42, x_1);
x_44 = l_Lean_registerTagAttribute___lambda__4___closed__1;
x_45 = lean::string_append(x_44, x_43);
lean::dec(x_43);
x_46 = l_Lean_registerTagAttribute___lambda__4___closed__5;
x_47 = lean::string_append(x_45, x_46);
lean::cnstr_set_tag(x_9, 1);
lean::cnstr_set(x_9, 0, x_47);
return x_9;
}
}
else
{
obj* x_48; obj* x_49; 
x_48 = lean::cnstr_get(x_9, 1);
lean::inc(x_48);
lean::dec(x_9);
x_49 = l_Lean_Environment_getModuleIdxFor(x_5, x_6);
if (lean::obj_tag(x_49) == 0)
{
obj* x_50; obj* x_51; 
x_50 = lean::box(x_3);
lean::inc(x_6);
lean::inc(x_5);
x_51 = lean::apply_3(x_2, x_5, x_6, x_50);
if (lean::obj_tag(x_51) == 0)
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
x_52 = lean::cnstr_get(x_51, 0);
lean::inc(x_52);
lean::dec(x_51);
x_53 = l_Lean_Name_toString___closed__1;
x_54 = l_Lean_Name_toStringWithSep___main(x_53, x_1);
x_55 = l_Lean_registerTagAttribute___lambda__4___closed__1;
x_56 = lean::string_append(x_55, x_54);
lean::dec(x_54);
x_57 = l_Lean_registerTagAttribute___lambda__4___closed__4;
x_58 = lean::string_append(x_56, x_57);
x_59 = lean::string_append(x_58, x_52);
lean::dec(x_52);
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_48);
return x_60;
}
else
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
lean::dec(x_51);
lean::dec(x_1);
x_61 = lean::box(x_3);
x_62 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_62, 0, x_6);
lean::cnstr_set(x_62, 1, x_61);
x_63 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_4, x_5, x_62);
x_64 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_48);
return x_64;
}
}
else
{
obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
lean::dec(x_49);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_2);
x_65 = l_Lean_Name_toString___closed__1;
x_66 = l_Lean_Name_toStringWithSep___main(x_65, x_1);
x_67 = l_Lean_registerTagAttribute___lambda__4___closed__1;
x_68 = lean::string_append(x_67, x_66);
lean::dec(x_66);
x_69 = l_Lean_registerTagAttribute___lambda__4___closed__5;
x_70 = lean::string_append(x_68, x_69);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_48);
return x_71;
}
}
}
}
}
obj* l_List_map___main___at_Lean_Compiler_mkSpecializeAttrs___spec__8(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(0);
return x_4;
}
else
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_3);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; obj* x_19; 
x_6 = lean::cnstr_get(x_3, 0);
x_7 = lean::cnstr_get(x_3, 1);
lean::inc(x_2);
lean::inc(x_1);
x_8 = l_List_map___main___at_Lean_Compiler_mkSpecializeAttrs___spec__8(x_1, x_2, x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_6, 0);
lean::inc(x_10);
lean::dec(x_6);
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
lean::inc(x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___main___at_Lean_Compiler_mkSpecializeAttrs___spec__8___lambda__1___boxed), 9, 4);
lean::closure_set(x_13, 0, x_10);
lean::closure_set(x_13, 1, x_1);
lean::closure_set(x_13, 2, x_12);
lean::closure_set(x_13, 3, x_2);
lean::inc(x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__5___boxed), 5, 1);
lean::closure_set(x_14, 0, x_10);
lean::inc(x_10);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean::closure_set(x_15, 0, x_10);
x_16 = l_Lean_AttributeImpl_inhabited___closed__4;
x_17 = l_Lean_AttributeImpl_inhabited___closed__5;
x_18 = 0;
x_19 = lean::alloc_cnstr(0, 8, 1);
lean::cnstr_set(x_19, 0, x_10);
lean::cnstr_set(x_19, 1, x_11);
lean::cnstr_set(x_19, 2, x_13);
lean::cnstr_set(x_19, 3, x_14);
lean::cnstr_set(x_19, 4, x_15);
lean::cnstr_set(x_19, 5, x_16);
lean::cnstr_set(x_19, 6, x_17);
lean::cnstr_set(x_19, 7, x_17);
lean::cnstr_set_scalar(x_19, sizeof(void*)*8, x_18);
lean::cnstr_set(x_3, 1, x_8);
lean::cnstr_set(x_3, 0, x_19);
return x_3;
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; uint8 x_32; obj* x_33; obj* x_34; 
x_20 = lean::cnstr_get(x_3, 0);
x_21 = lean::cnstr_get(x_3, 1);
lean::inc(x_21);
lean::inc(x_20);
lean::dec(x_3);
lean::inc(x_2);
lean::inc(x_1);
x_22 = l_List_map___main___at_Lean_Compiler_mkSpecializeAttrs___spec__8(x_1, x_2, x_21);
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
x_24 = lean::cnstr_get(x_20, 0);
lean::inc(x_24);
lean::dec(x_20);
x_25 = lean::cnstr_get(x_23, 0);
lean::inc(x_25);
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
lean::dec(x_23);
lean::inc(x_24);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___main___at_Lean_Compiler_mkSpecializeAttrs___spec__8___lambda__1___boxed), 9, 4);
lean::closure_set(x_27, 0, x_24);
lean::closure_set(x_27, 1, x_1);
lean::closure_set(x_27, 2, x_26);
lean::closure_set(x_27, 3, x_2);
lean::inc(x_24);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__5___boxed), 5, 1);
lean::closure_set(x_28, 0, x_24);
lean::inc(x_24);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean::closure_set(x_29, 0, x_24);
x_30 = l_Lean_AttributeImpl_inhabited___closed__4;
x_31 = l_Lean_AttributeImpl_inhabited___closed__5;
x_32 = 0;
x_33 = lean::alloc_cnstr(0, 8, 1);
lean::cnstr_set(x_33, 0, x_24);
lean::cnstr_set(x_33, 1, x_25);
lean::cnstr_set(x_33, 2, x_27);
lean::cnstr_set(x_33, 3, x_28);
lean::cnstr_set(x_33, 4, x_29);
lean::cnstr_set(x_33, 5, x_30);
lean::cnstr_set(x_33, 6, x_31);
lean::cnstr_set(x_33, 7, x_31);
lean::cnstr_set_scalar(x_33, sizeof(void*)*8, x_32);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_22);
return x_34;
}
}
}
}
obj* l_Lean_registerEnumAttributes___at_Lean_Compiler_mkSpecializeAttrs___spec__1___lambda__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
lean::dec(x_2);
x_5 = l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_1, x_3, x_4);
return x_5;
}
}
obj* l_Lean_registerEnumAttributes___at_Lean_Compiler_mkSpecializeAttrs___spec__1___lambda__2(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_2 = l_Array_empty___closed__1;
x_3 = l_RBNode_fold___main___at_Lean_Compiler_mkSpecializeAttrs___spec__2(x_2, x_1);
x_4 = lean::array_get_size(x_3);
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_4, x_5);
lean::dec(x_4);
x_7 = lean::mk_nat_obj(0u);
x_8 = l_Array_qsortAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__3(x_3, x_7, x_6);
lean::dec(x_6);
return x_8;
}
}
obj* _init_l_Lean_registerEnumAttributes___at_Lean_Compiler_mkSpecializeAttrs___spec__1___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerEnumAttributes___at_Lean_Compiler_mkSpecializeAttrs___spec__1___lambda__1), 2, 0);
return x_1;
}
}
obj* _init_l_Lean_registerEnumAttributes___at_Lean_Compiler_mkSpecializeAttrs___spec__1___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerEnumAttributes___at_Lean_Compiler_mkSpecializeAttrs___spec__1___lambda__2___boxed), 1, 0);
return x_1;
}
}
obj* l_Lean_registerEnumAttributes___at_Lean_Compiler_mkSpecializeAttrs___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_5 = l_Lean_registerTagAttribute___closed__1;
x_6 = l_Lean_registerEnumAttributes___at_Lean_Compiler_mkSpecializeAttrs___spec__1___closed__1;
x_7 = l_Lean_registerEnumAttributes___at_Lean_Compiler_mkSpecializeAttrs___spec__1___closed__2;
x_8 = l_Lean_registerEnumAttributes___rarg___closed__1;
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_5);
lean::cnstr_set(x_9, 2, x_6);
lean::cnstr_set(x_9, 3, x_7);
lean::cnstr_set(x_9, 4, x_8);
x_10 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Compiler_mkSpecializeAttrs___spec__5(x_9, x_4);
if (lean::obj_tag(x_10) == 0)
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_10);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_12 = lean::cnstr_get(x_10, 0);
x_13 = lean::box(0);
lean::cnstr_set(x_10, 0, x_13);
lean::inc(x_12);
x_14 = l_List_map___main___at_Lean_Compiler_mkSpecializeAttrs___spec__8(x_3, x_12, x_2);
lean::inc(x_14);
x_15 = l_List_mfor___main___at_Lean_registerEnumAttributes___spec__11(x_14, x_10);
if (lean::obj_tag(x_15) == 0)
{
uint8 x_16; 
x_16 = !lean::is_exclusive(x_15);
if (x_16 == 0)
{
obj* x_17; obj* x_18; 
x_17 = lean::cnstr_get(x_15, 0);
lean::dec(x_17);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_14);
lean::cnstr_set(x_18, 1, x_12);
lean::cnstr_set(x_15, 0, x_18);
return x_15;
}
else
{
obj* x_19; obj* x_20; obj* x_21; 
x_19 = lean::cnstr_get(x_15, 1);
lean::inc(x_19);
lean::dec(x_15);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_14);
lean::cnstr_set(x_20, 1, x_12);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8 x_22; 
lean::dec(x_14);
lean::dec(x_12);
x_22 = !lean::is_exclusive(x_15);
if (x_22 == 0)
{
return x_15;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = lean::cnstr_get(x_15, 0);
x_24 = lean::cnstr_get(x_15, 1);
lean::inc(x_24);
lean::inc(x_23);
lean::dec(x_15);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_26 = lean::cnstr_get(x_10, 0);
x_27 = lean::cnstr_get(x_10, 1);
lean::inc(x_27);
lean::inc(x_26);
lean::dec(x_10);
x_28 = lean::box(0);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_27);
lean::inc(x_26);
x_30 = l_List_map___main___at_Lean_Compiler_mkSpecializeAttrs___spec__8(x_3, x_26, x_2);
lean::inc(x_30);
x_31 = l_List_mfor___main___at_Lean_registerEnumAttributes___spec__11(x_30, x_29);
if (lean::obj_tag(x_31) == 0)
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_32 = lean::cnstr_get(x_31, 1);
lean::inc(x_32);
if (lean::is_exclusive(x_31)) {
 lean::cnstr_release(x_31, 0);
 lean::cnstr_release(x_31, 1);
 x_33 = x_31;
} else {
 lean::dec_ref(x_31);
 x_33 = lean::box(0);
}
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_30);
lean::cnstr_set(x_34, 1, x_26);
if (lean::is_scalar(x_33)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_33;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_32);
return x_35;
}
else
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_30);
lean::dec(x_26);
x_36 = lean::cnstr_get(x_31, 0);
lean::inc(x_36);
x_37 = lean::cnstr_get(x_31, 1);
lean::inc(x_37);
if (lean::is_exclusive(x_31)) {
 lean::cnstr_release(x_31, 0);
 lean::cnstr_release(x_31, 1);
 x_38 = x_31;
} else {
 lean::dec_ref(x_31);
 x_38 = lean::box(0);
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_36);
lean::cnstr_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
uint8 x_40; 
lean::dec(x_3);
lean::dec(x_2);
x_40 = !lean::is_exclusive(x_10);
if (x_40 == 0)
{
return x_10;
}
else
{
obj* x_41; obj* x_42; obj* x_43; 
x_41 = lean::cnstr_get(x_10, 0);
x_42 = lean::cnstr_get(x_10, 1);
lean::inc(x_42);
lean::inc(x_41);
lean::dec(x_10);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_42);
return x_43;
}
}
}
}
obj* l_Lean_Compiler_mkSpecializeAttrs___lambda__1(obj* x_1, obj* x_2, uint8 x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Compiler_checkIsDefinition(x_1, x_2);
return x_4;
}
}
obj* _init_l_Lean_Compiler_mkSpecializeAttrs___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("specializeAttrs");
return x_1;
}
}
obj* _init_l_Lean_Compiler_mkSpecializeAttrs___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Compiler_mkSpecializeAttrs___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Compiler_mkSpecializeAttrs___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("specialize");
return x_1;
}
}
obj* _init_l_Lean_Compiler_mkSpecializeAttrs___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Compiler_mkSpecializeAttrs___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Compiler_mkSpecializeAttrs___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("mark definition to always be inlined");
return x_1;
}
}
obj* _init_l_Lean_Compiler_mkSpecializeAttrs___closed__6() {
_start:
{
obj* x_1; uint8 x_2; obj* x_3; obj* x_4; 
x_1 = l_Lean_Compiler_mkSpecializeAttrs___closed__5;
x_2 = 0;
x_3 = lean::box(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* _init_l_Lean_Compiler_mkSpecializeAttrs___closed__7() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Compiler_mkSpecializeAttrs___closed__4;
x_2 = l_Lean_Compiler_mkSpecializeAttrs___closed__6;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Compiler_mkSpecializeAttrs___closed__8() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("nospecialize");
return x_1;
}
}
obj* _init_l_Lean_Compiler_mkSpecializeAttrs___closed__9() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Compiler_mkSpecializeAttrs___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Compiler_mkSpecializeAttrs___closed__10() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("mark definition to never be inlined");
return x_1;
}
}
obj* _init_l_Lean_Compiler_mkSpecializeAttrs___closed__11() {
_start:
{
obj* x_1; uint8 x_2; obj* x_3; obj* x_4; 
x_1 = l_Lean_Compiler_mkSpecializeAttrs___closed__10;
x_2 = 1;
x_3 = lean::box(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* _init_l_Lean_Compiler_mkSpecializeAttrs___closed__12() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Compiler_mkSpecializeAttrs___closed__9;
x_2 = l_Lean_Compiler_mkSpecializeAttrs___closed__11;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Compiler_mkSpecializeAttrs___closed__13() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Compiler_mkSpecializeAttrs___closed__12;
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
}
}
obj* _init_l_Lean_Compiler_mkSpecializeAttrs___closed__14() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Compiler_mkSpecializeAttrs___closed__7;
x_2 = l_Lean_Compiler_mkSpecializeAttrs___closed__13;
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Compiler_mkSpecializeAttrs___closed__15() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_mkSpecializeAttrs___lambda__1___boxed), 3, 0);
return x_1;
}
}
obj* l_Lean_Compiler_mkSpecializeAttrs(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Compiler_mkSpecializeAttrs___closed__2;
x_3 = l_Lean_Compiler_mkSpecializeAttrs___closed__14;
x_4 = l_Lean_Compiler_mkSpecializeAttrs___closed__15;
x_5 = l_Lean_registerEnumAttributes___at_Lean_Compiler_mkSpecializeAttrs___spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l_RBNode_fold___main___at_Lean_Compiler_mkSpecializeAttrs___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_fold___main___at_Lean_Compiler_mkSpecializeAttrs___spec__2(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__4___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__4(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Array_qsortAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_qsortAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__3(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Array_anyMAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__6___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_Array_anyMAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__6(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_List_map___main___at_Lean_Compiler_mkSpecializeAttrs___spec__8___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9) {
_start:
{
uint8 x_10; uint8 x_11; obj* x_12; 
x_10 = lean::unbox(x_3);
lean::dec(x_3);
x_11 = lean::unbox(x_8);
lean::dec(x_8);
x_12 = l_List_map___main___at_Lean_Compiler_mkSpecializeAttrs___spec__8___lambda__1(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_11, x_9);
lean::dec(x_7);
return x_12;
}
}
obj* l_Lean_registerEnumAttributes___at_Lean_Compiler_mkSpecializeAttrs___spec__1___lambda__2___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_registerEnumAttributes___at_Lean_Compiler_mkSpecializeAttrs___spec__1___lambda__2(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Compiler_mkSpecializeAttrs___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_3);
lean::dec(x_3);
x_5 = l_Lean_Compiler_mkSpecializeAttrs___lambda__1(x_1, x_2, x_4);
return x_5;
}
}
obj* l_RBNode_find___main___at___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux___main___spec__2(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_7 = lean::cnstr_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8 x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
obj* x_10; 
lean::inc(x_6);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_6);
return x_10;
}
else
{
x_1 = x_7;
goto _start;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
obj* l_Array_binSearchAux___main___at___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux___main___spec__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = lean::nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
obj* x_6; 
lean::dec(x_4);
lean::dec(x_3);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_7 = lean::nat_add(x_3, x_4);
x_8 = lean::mk_nat_obj(2u);
x_9 = lean::nat_div(x_7, x_8);
lean::dec(x_7);
x_10 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__4___closed__1;
x_11 = lean::array_get(x_10, x_1, x_9);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_13 = lean::cnstr_get(x_2, 0);
x_14 = l_Lean_Name_quickLt(x_12, x_13);
if (x_14 == 0)
{
uint8 x_15; 
lean::dec(x_4);
x_15 = l_Lean_Name_quickLt(x_13, x_12);
lean::dec(x_12);
if (x_15 == 0)
{
obj* x_16; 
lean::dec(x_9);
lean::dec(x_3);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_11);
return x_16;
}
else
{
obj* x_17; uint8 x_18; 
lean::dec(x_11);
x_17 = lean::mk_nat_obj(0u);
x_18 = lean::nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; 
x_19 = lean::mk_nat_obj(1u);
x_20 = lean::nat_sub(x_9, x_19);
lean::dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
obj* x_22; 
lean::dec(x_9);
lean::dec(x_3);
x_22 = lean::box(0);
return x_22;
}
}
}
else
{
obj* x_23; obj* x_24; 
lean::dec(x_12);
lean::dec(x_11);
lean::dec(x_3);
x_23 = lean::mk_nat_obj(1u);
x_24 = lean::nat_add(x_9, x_23);
lean::dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
obj* l_Lean_EnumAttributes_getValue___at___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux___main___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Environment_getModuleIdxFor(x_2, x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_6 = l_Lean_PersistentEnvExtension_getState___rarg(x_5, x_2);
x_7 = l_RBNode_find___main___at___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux___main___spec__2(x_6, x_3);
lean::dec(x_3);
lean::dec(x_6);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; uint8 x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::dec(x_1);
x_10 = l_Lean_PersistentEnvExtension_getModuleEntries___rarg(x_9, x_2, x_8);
lean::dec(x_8);
x_11 = 0;
x_12 = lean::box(x_11);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_3);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::array_get_size(x_10);
x_15 = lean::mk_nat_obj(1u);
x_16 = lean::nat_sub(x_14, x_15);
lean::dec(x_14);
x_17 = lean::mk_nat_obj(0u);
x_18 = l_Array_binSearchAux___main___at___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux___main___spec__3(x_10, x_13, x_17, x_16);
lean::dec(x_13);
lean::dec(x_10);
if (lean::obj_tag(x_18) == 0)
{
obj* x_19; 
x_19 = lean::box(0);
return x_19;
}
else
{
uint8 x_20; 
x_20 = !lean::is_exclusive(x_18);
if (x_20 == 0)
{
obj* x_21; obj* x_22; 
x_21 = lean::cnstr_get(x_18, 0);
x_22 = lean::cnstr_get(x_21, 1);
lean::inc(x_22);
lean::dec(x_21);
lean::cnstr_set(x_18, 0, x_22);
return x_18;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = lean::cnstr_get(x_18, 0);
lean::inc(x_23);
lean::dec(x_18);
x_24 = lean::cnstr_get(x_23, 1);
lean::inc(x_24);
lean::dec(x_23);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
return x_25;
}
}
}
}
}
uint8 l___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux___main(obj* x_1, uint8 x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_Compiler_specializeAttrs;
lean::inc(x_3);
x_5 = l_Lean_EnumAttributes_getValue___at___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux___main___spec__1(x_4, x_1, x_3);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = l_Lean_Name_isInternal___main(x_3);
if (x_6 == 0)
{
uint8 x_7; 
lean::dec(x_3);
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
obj* x_10; uint8 x_11; uint8 x_12; 
lean::dec(x_3);
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::dec(x_5);
x_11 = lean::unbox(x_10);
lean::dec(x_10);
x_12 = l_Lean_Compiler_SpecializeAttributeKind_beq___main(x_2, x_11);
return x_12;
}
}
}
obj* l_RBNode_find___main___at___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux___main___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___at___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux___main___spec__2(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Array_binSearchAux___main___at___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux___main___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_binSearchAux___main___at___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux___main___spec__3(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_EnumAttributes_getValue___at___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux___main___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_EnumAttributes_getValue___at___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux___main___spec__1(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; uint8 x_5; obj* x_6; 
x_4 = lean::unbox(x_2);
lean::dec(x_2);
x_5 = l___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux___main(x_1, x_4, x_3);
lean::dec(x_1);
x_6 = lean::box(x_5);
return x_6;
}
}
uint8 l___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux(obj* x_1, uint8 x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; uint8 x_5; obj* x_6; 
x_4 = lean::unbox(x_2);
lean::dec(x_2);
x_5 = l___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux(x_1, x_4, x_3);
lean::dec(x_1);
x_6 = lean::box(x_5);
return x_6;
}
}
namespace lean {
uint8 has_specialize_attribute_core(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; uint8 x_4; 
x_3 = 0;
x_4 = l___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux___main(x_1, x_3, x_2);
lean::dec(x_1);
return x_4;
}
}
}
obj* l_Lean_Compiler_hasSpecializeAttribute___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::has_specialize_attribute_core(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
namespace lean {
uint8 has_nospecialize_attribute_core(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; uint8 x_4; 
x_3 = 1;
x_4 = l___private_init_lean_compiler_specialize_1__hasSpecializeAttrAux___main(x_1, x_3, x_2);
lean::dec(x_1);
return x_4;
}
}
}
obj* l_Lean_Compiler_hasNospecializeAttribute___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::has_nospecialize_attribute_core(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_mkHashMap___at_Lean_Compiler_SpecState_Inhabited___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
obj* l_mkHashMap___at_Lean_Compiler_SpecState_Inhabited___spec__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
obj* _init_l_Lean_Compiler_SpecState_Inhabited___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
obj* _init_l_Lean_Compiler_SpecState_Inhabited___closed__2() {
_start:
{
obj* x_1; uint8 x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = 1;
x_3 = l_Lean_Compiler_SpecState_Inhabited___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set_scalar(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
obj* _init_l_Lean_Compiler_SpecState_Inhabited___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
obj* _init_l_Lean_Compiler_SpecState_Inhabited___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expr_quickLt___boxed), 2, 0);
return x_1;
}
}
obj* _init_l_Lean_Compiler_SpecState_Inhabited___closed__5() {
_start:
{
obj* x_1; uint8 x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = 1;
x_3 = l_Lean_Compiler_SpecState_Inhabited___closed__3;
x_4 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set_scalar(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
obj* _init_l_Lean_Compiler_SpecState_Inhabited___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Compiler_SpecState_Inhabited___closed__2;
x_2 = l_Lean_Compiler_SpecState_Inhabited___closed__5;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Compiler_SpecState_Inhabited() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Compiler_SpecState_Inhabited___closed__6;
return x_1;
}
}
obj* l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__3(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_1);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::cnstr_get(x_1, 2);
x_11 = lean::cnstr_get(x_1, 3);
x_12 = l_Lean_Name_quickLt(x_2, x_9);
if (x_12 == 0)
{
uint8 x_13; 
x_13 = l_Lean_Name_quickLt(x_9, x_2);
if (x_13 == 0)
{
lean::dec(x_10);
lean::dec(x_9);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
return x_1;
}
else
{
obj* x_14; 
x_14 = l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__3(x_11, x_2, x_3);
lean::cnstr_set(x_1, 3, x_14);
return x_1;
}
}
else
{
obj* x_15; 
x_15 = l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__3(x_8, x_2, x_3);
lean::cnstr_set(x_1, 0, x_15);
return x_1;
}
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint8 x_20; 
x_16 = lean::cnstr_get(x_1, 0);
x_17 = lean::cnstr_get(x_1, 1);
x_18 = lean::cnstr_get(x_1, 2);
x_19 = lean::cnstr_get(x_1, 3);
lean::inc(x_19);
lean::inc(x_18);
lean::inc(x_17);
lean::inc(x_16);
lean::dec(x_1);
x_20 = l_Lean_Name_quickLt(x_2, x_17);
if (x_20 == 0)
{
uint8 x_21; 
x_21 = l_Lean_Name_quickLt(x_17, x_2);
if (x_21 == 0)
{
obj* x_22; 
lean::dec(x_18);
lean::dec(x_17);
x_22 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_22, 0, x_16);
lean::cnstr_set(x_22, 1, x_2);
lean::cnstr_set(x_22, 2, x_3);
lean::cnstr_set(x_22, 3, x_19);
lean::cnstr_set_scalar(x_22, sizeof(void*)*4, x_6);
return x_22;
}
else
{
obj* x_23; obj* x_24; 
x_23 = l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__3(x_19, x_2, x_3);
x_24 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_24, 0, x_16);
lean::cnstr_set(x_24, 1, x_17);
lean::cnstr_set(x_24, 2, x_18);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_6);
return x_24;
}
}
else
{
obj* x_25; obj* x_26; 
x_25 = l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__3(x_16, x_2, x_3);
x_26 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
lean::cnstr_set(x_26, 2, x_18);
lean::cnstr_set(x_26, 3, x_19);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
return x_26;
}
}
}
else
{
uint8 x_27; 
x_27 = !lean::is_exclusive(x_1);
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; uint8 x_32; 
x_28 = lean::cnstr_get(x_1, 0);
x_29 = lean::cnstr_get(x_1, 1);
x_30 = lean::cnstr_get(x_1, 2);
x_31 = lean::cnstr_get(x_1, 3);
x_32 = l_Lean_Name_quickLt(x_2, x_29);
if (x_32 == 0)
{
uint8 x_33; 
x_33 = l_Lean_Name_quickLt(x_29, x_2);
if (x_33 == 0)
{
lean::dec(x_30);
lean::dec(x_29);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
return x_1;
}
else
{
uint8 x_34; 
x_34 = l_RBNode_isRed___main___rarg(x_31);
if (x_34 == 0)
{
obj* x_35; 
x_35 = l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__3(x_31, x_2, x_3);
lean::cnstr_set(x_1, 3, x_35);
return x_1;
}
else
{
obj* x_36; 
x_36 = l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__3(x_31, x_2, x_3);
if (lean::obj_tag(x_36) == 0)
{
lean::free_heap_obj(x_1);
lean::dec(x_30);
lean::dec(x_29);
lean::dec(x_28);
return x_36;
}
else
{
obj* x_37; 
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; 
x_38 = lean::cnstr_get(x_36, 3);
lean::inc(x_38);
if (lean::obj_tag(x_38) == 0)
{
uint8 x_39; 
x_39 = !lean::is_exclusive(x_36);
if (x_39 == 0)
{
obj* x_40; obj* x_41; uint8 x_42; uint8 x_43; 
x_40 = lean::cnstr_get(x_36, 3);
lean::dec(x_40);
x_41 = lean::cnstr_get(x_36, 0);
lean::dec(x_41);
x_42 = 0;
lean::cnstr_set(x_36, 0, x_38);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_42);
x_43 = 1;
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_43);
return x_1;
}
else
{
obj* x_44; obj* x_45; uint8 x_46; obj* x_47; uint8 x_48; 
x_44 = lean::cnstr_get(x_36, 1);
x_45 = lean::cnstr_get(x_36, 2);
lean::inc(x_45);
lean::inc(x_44);
lean::dec(x_36);
x_46 = 0;
x_47 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_47, 0, x_38);
lean::cnstr_set(x_47, 1, x_44);
lean::cnstr_set(x_47, 2, x_45);
lean::cnstr_set(x_47, 3, x_38);
lean::cnstr_set_scalar(x_47, sizeof(void*)*4, x_46);
x_48 = 1;
lean::cnstr_set(x_1, 3, x_47);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_48);
return x_1;
}
}
else
{
uint8 x_49; 
x_49 = lean::cnstr_get_scalar<uint8>(x_38, sizeof(void*)*4);
if (x_49 == 0)
{
uint8 x_50; 
x_50 = !lean::is_exclusive(x_36);
if (x_50 == 0)
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; uint8 x_55; 
x_51 = lean::cnstr_get(x_36, 1);
x_52 = lean::cnstr_get(x_36, 2);
x_53 = lean::cnstr_get(x_36, 3);
lean::dec(x_53);
x_54 = lean::cnstr_get(x_36, 0);
lean::dec(x_54);
x_55 = !lean::is_exclusive(x_38);
if (x_55 == 0)
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; uint8 x_60; 
x_56 = lean::cnstr_get(x_38, 0);
x_57 = lean::cnstr_get(x_38, 1);
x_58 = lean::cnstr_get(x_38, 2);
x_59 = lean::cnstr_get(x_38, 3);
x_60 = 1;
lean::cnstr_set(x_38, 3, x_37);
lean::cnstr_set(x_38, 2, x_30);
lean::cnstr_set(x_38, 1, x_29);
lean::cnstr_set(x_38, 0, x_28);
lean::cnstr_set_scalar(x_38, sizeof(void*)*4, x_60);
lean::cnstr_set(x_36, 3, x_59);
lean::cnstr_set(x_36, 2, x_58);
lean::cnstr_set(x_36, 1, x_57);
lean::cnstr_set(x_36, 0, x_56);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_60);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_52);
lean::cnstr_set(x_1, 1, x_51);
lean::cnstr_set(x_1, 0, x_38);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; uint8 x_65; obj* x_66; 
x_61 = lean::cnstr_get(x_38, 0);
x_62 = lean::cnstr_get(x_38, 1);
x_63 = lean::cnstr_get(x_38, 2);
x_64 = lean::cnstr_get(x_38, 3);
lean::inc(x_64);
lean::inc(x_63);
lean::inc(x_62);
lean::inc(x_61);
lean::dec(x_38);
x_65 = 1;
x_66 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_66, 0, x_28);
lean::cnstr_set(x_66, 1, x_29);
lean::cnstr_set(x_66, 2, x_30);
lean::cnstr_set(x_66, 3, x_37);
lean::cnstr_set_scalar(x_66, sizeof(void*)*4, x_65);
lean::cnstr_set(x_36, 3, x_64);
lean::cnstr_set(x_36, 2, x_63);
lean::cnstr_set(x_36, 1, x_62);
lean::cnstr_set(x_36, 0, x_61);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_65);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_52);
lean::cnstr_set(x_1, 1, x_51);
lean::cnstr_set(x_1, 0, x_66);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; uint8 x_74; obj* x_75; obj* x_76; 
x_67 = lean::cnstr_get(x_36, 1);
x_68 = lean::cnstr_get(x_36, 2);
lean::inc(x_68);
lean::inc(x_67);
lean::dec(x_36);
x_69 = lean::cnstr_get(x_38, 0);
lean::inc(x_69);
x_70 = lean::cnstr_get(x_38, 1);
lean::inc(x_70);
x_71 = lean::cnstr_get(x_38, 2);
lean::inc(x_71);
x_72 = lean::cnstr_get(x_38, 3);
lean::inc(x_72);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 lean::cnstr_release(x_38, 1);
 lean::cnstr_release(x_38, 2);
 lean::cnstr_release(x_38, 3);
 x_73 = x_38;
} else {
 lean::dec_ref(x_38);
 x_73 = lean::box(0);
}
x_74 = 1;
if (lean::is_scalar(x_73)) {
 x_75 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_75 = x_73;
}
lean::cnstr_set(x_75, 0, x_28);
lean::cnstr_set(x_75, 1, x_29);
lean::cnstr_set(x_75, 2, x_30);
lean::cnstr_set(x_75, 3, x_37);
lean::cnstr_set_scalar(x_75, sizeof(void*)*4, x_74);
x_76 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_76, 0, x_69);
lean::cnstr_set(x_76, 1, x_70);
lean::cnstr_set(x_76, 2, x_71);
lean::cnstr_set(x_76, 3, x_72);
lean::cnstr_set_scalar(x_76, sizeof(void*)*4, x_74);
lean::cnstr_set(x_1, 3, x_76);
lean::cnstr_set(x_1, 2, x_68);
lean::cnstr_set(x_1, 1, x_67);
lean::cnstr_set(x_1, 0, x_75);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
uint8 x_77; 
x_77 = !lean::is_exclusive(x_36);
if (x_77 == 0)
{
obj* x_78; obj* x_79; uint8 x_80; 
x_78 = lean::cnstr_get(x_36, 3);
lean::dec(x_78);
x_79 = lean::cnstr_get(x_36, 0);
lean::dec(x_79);
x_80 = 0;
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_80);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
obj* x_81; obj* x_82; uint8 x_83; obj* x_84; 
x_81 = lean::cnstr_get(x_36, 1);
x_82 = lean::cnstr_get(x_36, 2);
lean::inc(x_82);
lean::inc(x_81);
lean::dec(x_36);
x_83 = 0;
x_84 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_84, 0, x_37);
lean::cnstr_set(x_84, 1, x_81);
lean::cnstr_set(x_84, 2, x_82);
lean::cnstr_set(x_84, 3, x_38);
lean::cnstr_set_scalar(x_84, sizeof(void*)*4, x_83);
lean::cnstr_set(x_1, 3, x_84);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
}
}
else
{
uint8 x_85; 
x_85 = lean::cnstr_get_scalar<uint8>(x_37, sizeof(void*)*4);
if (x_85 == 0)
{
uint8 x_86; 
x_86 = !lean::is_exclusive(x_36);
if (x_86 == 0)
{
obj* x_87; uint8 x_88; 
x_87 = lean::cnstr_get(x_36, 0);
lean::dec(x_87);
x_88 = !lean::is_exclusive(x_37);
if (x_88 == 0)
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; uint8 x_93; 
x_89 = lean::cnstr_get(x_37, 0);
x_90 = lean::cnstr_get(x_37, 1);
x_91 = lean::cnstr_get(x_37, 2);
x_92 = lean::cnstr_get(x_37, 3);
x_93 = 1;
lean::cnstr_set(x_37, 3, x_89);
lean::cnstr_set(x_37, 2, x_30);
lean::cnstr_set(x_37, 1, x_29);
lean::cnstr_set(x_37, 0, x_28);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_93);
lean::cnstr_set(x_36, 0, x_92);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_93);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_91);
lean::cnstr_set(x_1, 1, x_90);
lean::cnstr_set(x_1, 0, x_37);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
obj* x_94; obj* x_95; obj* x_96; obj* x_97; uint8 x_98; obj* x_99; 
x_94 = lean::cnstr_get(x_37, 0);
x_95 = lean::cnstr_get(x_37, 1);
x_96 = lean::cnstr_get(x_37, 2);
x_97 = lean::cnstr_get(x_37, 3);
lean::inc(x_97);
lean::inc(x_96);
lean::inc(x_95);
lean::inc(x_94);
lean::dec(x_37);
x_98 = 1;
x_99 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_99, 0, x_28);
lean::cnstr_set(x_99, 1, x_29);
lean::cnstr_set(x_99, 2, x_30);
lean::cnstr_set(x_99, 3, x_94);
lean::cnstr_set_scalar(x_99, sizeof(void*)*4, x_98);
lean::cnstr_set(x_36, 0, x_97);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_98);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_96);
lean::cnstr_set(x_1, 1, x_95);
lean::cnstr_set(x_1, 0, x_99);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; uint8 x_108; obj* x_109; obj* x_110; 
x_100 = lean::cnstr_get(x_36, 1);
x_101 = lean::cnstr_get(x_36, 2);
x_102 = lean::cnstr_get(x_36, 3);
lean::inc(x_102);
lean::inc(x_101);
lean::inc(x_100);
lean::dec(x_36);
x_103 = lean::cnstr_get(x_37, 0);
lean::inc(x_103);
x_104 = lean::cnstr_get(x_37, 1);
lean::inc(x_104);
x_105 = lean::cnstr_get(x_37, 2);
lean::inc(x_105);
x_106 = lean::cnstr_get(x_37, 3);
lean::inc(x_106);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_107 = x_37;
} else {
 lean::dec_ref(x_37);
 x_107 = lean::box(0);
}
x_108 = 1;
if (lean::is_scalar(x_107)) {
 x_109 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_109 = x_107;
}
lean::cnstr_set(x_109, 0, x_28);
lean::cnstr_set(x_109, 1, x_29);
lean::cnstr_set(x_109, 2, x_30);
lean::cnstr_set(x_109, 3, x_103);
lean::cnstr_set_scalar(x_109, sizeof(void*)*4, x_108);
x_110 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_110, 0, x_106);
lean::cnstr_set(x_110, 1, x_100);
lean::cnstr_set(x_110, 2, x_101);
lean::cnstr_set(x_110, 3, x_102);
lean::cnstr_set_scalar(x_110, sizeof(void*)*4, x_108);
lean::cnstr_set(x_1, 3, x_110);
lean::cnstr_set(x_1, 2, x_105);
lean::cnstr_set(x_1, 1, x_104);
lean::cnstr_set(x_1, 0, x_109);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
obj* x_111; 
x_111 = lean::cnstr_get(x_36, 3);
lean::inc(x_111);
if (lean::obj_tag(x_111) == 0)
{
uint8 x_112; 
x_112 = !lean::is_exclusive(x_36);
if (x_112 == 0)
{
obj* x_113; obj* x_114; uint8 x_115; 
x_113 = lean::cnstr_get(x_36, 3);
lean::dec(x_113);
x_114 = lean::cnstr_get(x_36, 0);
lean::dec(x_114);
x_115 = 0;
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_115);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
obj* x_116; obj* x_117; uint8 x_118; obj* x_119; 
x_116 = lean::cnstr_get(x_36, 1);
x_117 = lean::cnstr_get(x_36, 2);
lean::inc(x_117);
lean::inc(x_116);
lean::dec(x_36);
x_118 = 0;
x_119 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_119, 0, x_37);
lean::cnstr_set(x_119, 1, x_116);
lean::cnstr_set(x_119, 2, x_117);
lean::cnstr_set(x_119, 3, x_111);
lean::cnstr_set_scalar(x_119, sizeof(void*)*4, x_118);
lean::cnstr_set(x_1, 3, x_119);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
uint8 x_120; 
x_120 = lean::cnstr_get_scalar<uint8>(x_111, sizeof(void*)*4);
if (x_120 == 0)
{
uint8 x_121; 
lean::free_heap_obj(x_1);
x_121 = !lean::is_exclusive(x_36);
if (x_121 == 0)
{
obj* x_122; obj* x_123; uint8 x_124; 
x_122 = lean::cnstr_get(x_36, 3);
lean::dec(x_122);
x_123 = lean::cnstr_get(x_36, 0);
lean::dec(x_123);
x_124 = !lean::is_exclusive(x_111);
if (x_124 == 0)
{
obj* x_125; obj* x_126; obj* x_127; obj* x_128; uint8 x_129; 
x_125 = lean::cnstr_get(x_111, 0);
x_126 = lean::cnstr_get(x_111, 1);
x_127 = lean::cnstr_get(x_111, 2);
x_128 = lean::cnstr_get(x_111, 3);
lean::inc(x_37);
lean::cnstr_set(x_111, 3, x_37);
lean::cnstr_set(x_111, 2, x_30);
lean::cnstr_set(x_111, 1, x_29);
lean::cnstr_set(x_111, 0, x_28);
x_129 = !lean::is_exclusive(x_37);
if (x_129 == 0)
{
obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
x_130 = lean::cnstr_get(x_37, 3);
lean::dec(x_130);
x_131 = lean::cnstr_get(x_37, 2);
lean::dec(x_131);
x_132 = lean::cnstr_get(x_37, 1);
lean::dec(x_132);
x_133 = lean::cnstr_get(x_37, 0);
lean::dec(x_133);
lean::cnstr_set_scalar(x_111, sizeof(void*)*4, x_85);
lean::cnstr_set(x_37, 3, x_128);
lean::cnstr_set(x_37, 2, x_127);
lean::cnstr_set(x_37, 1, x_126);
lean::cnstr_set(x_37, 0, x_125);
lean::cnstr_set(x_36, 3, x_37);
lean::cnstr_set(x_36, 0, x_111);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_120);
return x_36;
}
else
{
obj* x_134; 
lean::dec(x_37);
lean::cnstr_set_scalar(x_111, sizeof(void*)*4, x_85);
x_134 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_134, 0, x_125);
lean::cnstr_set(x_134, 1, x_126);
lean::cnstr_set(x_134, 2, x_127);
lean::cnstr_set(x_134, 3, x_128);
lean::cnstr_set_scalar(x_134, sizeof(void*)*4, x_85);
lean::cnstr_set(x_36, 3, x_134);
lean::cnstr_set(x_36, 0, x_111);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; 
x_135 = lean::cnstr_get(x_111, 0);
x_136 = lean::cnstr_get(x_111, 1);
x_137 = lean::cnstr_get(x_111, 2);
x_138 = lean::cnstr_get(x_111, 3);
lean::inc(x_138);
lean::inc(x_137);
lean::inc(x_136);
lean::inc(x_135);
lean::dec(x_111);
lean::inc(x_37);
x_139 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_139, 0, x_28);
lean::cnstr_set(x_139, 1, x_29);
lean::cnstr_set(x_139, 2, x_30);
lean::cnstr_set(x_139, 3, x_37);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_140 = x_37;
} else {
 lean::dec_ref(x_37);
 x_140 = lean::box(0);
}
lean::cnstr_set_scalar(x_139, sizeof(void*)*4, x_85);
if (lean::is_scalar(x_140)) {
 x_141 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_141 = x_140;
}
lean::cnstr_set(x_141, 0, x_135);
lean::cnstr_set(x_141, 1, x_136);
lean::cnstr_set(x_141, 2, x_137);
lean::cnstr_set(x_141, 3, x_138);
lean::cnstr_set_scalar(x_141, sizeof(void*)*4, x_85);
lean::cnstr_set(x_36, 3, x_141);
lean::cnstr_set(x_36, 0, x_139);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
x_142 = lean::cnstr_get(x_36, 1);
x_143 = lean::cnstr_get(x_36, 2);
lean::inc(x_143);
lean::inc(x_142);
lean::dec(x_36);
x_144 = lean::cnstr_get(x_111, 0);
lean::inc(x_144);
x_145 = lean::cnstr_get(x_111, 1);
lean::inc(x_145);
x_146 = lean::cnstr_get(x_111, 2);
lean::inc(x_146);
x_147 = lean::cnstr_get(x_111, 3);
lean::inc(x_147);
if (lean::is_exclusive(x_111)) {
 lean::cnstr_release(x_111, 0);
 lean::cnstr_release(x_111, 1);
 lean::cnstr_release(x_111, 2);
 lean::cnstr_release(x_111, 3);
 x_148 = x_111;
} else {
 lean::dec_ref(x_111);
 x_148 = lean::box(0);
}
lean::inc(x_37);
if (lean::is_scalar(x_148)) {
 x_149 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_149 = x_148;
}
lean::cnstr_set(x_149, 0, x_28);
lean::cnstr_set(x_149, 1, x_29);
lean::cnstr_set(x_149, 2, x_30);
lean::cnstr_set(x_149, 3, x_37);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_150 = x_37;
} else {
 lean::dec_ref(x_37);
 x_150 = lean::box(0);
}
lean::cnstr_set_scalar(x_149, sizeof(void*)*4, x_85);
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_144);
lean::cnstr_set(x_151, 1, x_145);
lean::cnstr_set(x_151, 2, x_146);
lean::cnstr_set(x_151, 3, x_147);
lean::cnstr_set_scalar(x_151, sizeof(void*)*4, x_85);
x_152 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_152, 0, x_149);
lean::cnstr_set(x_152, 1, x_142);
lean::cnstr_set(x_152, 2, x_143);
lean::cnstr_set(x_152, 3, x_151);
lean::cnstr_set_scalar(x_152, sizeof(void*)*4, x_120);
return x_152;
}
}
else
{
uint8 x_153; 
x_153 = !lean::is_exclusive(x_36);
if (x_153 == 0)
{
obj* x_154; obj* x_155; uint8 x_156; 
x_154 = lean::cnstr_get(x_36, 3);
lean::dec(x_154);
x_155 = lean::cnstr_get(x_36, 0);
lean::dec(x_155);
x_156 = !lean::is_exclusive(x_37);
if (x_156 == 0)
{
uint8 x_157; 
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_120);
x_157 = 0;
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_157);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_120);
return x_1;
}
else
{
obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; uint8 x_163; 
x_158 = lean::cnstr_get(x_37, 0);
x_159 = lean::cnstr_get(x_37, 1);
x_160 = lean::cnstr_get(x_37, 2);
x_161 = lean::cnstr_get(x_37, 3);
lean::inc(x_161);
lean::inc(x_160);
lean::inc(x_159);
lean::inc(x_158);
lean::dec(x_37);
x_162 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_162, 0, x_158);
lean::cnstr_set(x_162, 1, x_159);
lean::cnstr_set(x_162, 2, x_160);
lean::cnstr_set(x_162, 3, x_161);
lean::cnstr_set_scalar(x_162, sizeof(void*)*4, x_120);
x_163 = 0;
lean::cnstr_set(x_36, 0, x_162);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_163);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_120);
return x_1;
}
}
else
{
obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; uint8 x_172; obj* x_173; 
x_164 = lean::cnstr_get(x_36, 1);
x_165 = lean::cnstr_get(x_36, 2);
lean::inc(x_165);
lean::inc(x_164);
lean::dec(x_36);
x_166 = lean::cnstr_get(x_37, 0);
lean::inc(x_166);
x_167 = lean::cnstr_get(x_37, 1);
lean::inc(x_167);
x_168 = lean::cnstr_get(x_37, 2);
lean::inc(x_168);
x_169 = lean::cnstr_get(x_37, 3);
lean::inc(x_169);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_170 = x_37;
} else {
 lean::dec_ref(x_37);
 x_170 = lean::box(0);
}
if (lean::is_scalar(x_170)) {
 x_171 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_171 = x_170;
}
lean::cnstr_set(x_171, 0, x_166);
lean::cnstr_set(x_171, 1, x_167);
lean::cnstr_set(x_171, 2, x_168);
lean::cnstr_set(x_171, 3, x_169);
lean::cnstr_set_scalar(x_171, sizeof(void*)*4, x_120);
x_172 = 0;
x_173 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_173, 0, x_171);
lean::cnstr_set(x_173, 1, x_164);
lean::cnstr_set(x_173, 2, x_165);
lean::cnstr_set(x_173, 3, x_111);
lean::cnstr_set_scalar(x_173, sizeof(void*)*4, x_172);
lean::cnstr_set(x_1, 3, x_173);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_120);
return x_1;
}
}
}
}
}
}
}
}
}
else
{
uint8 x_174; 
x_174 = l_RBNode_isRed___main___rarg(x_28);
if (x_174 == 0)
{
obj* x_175; 
x_175 = l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__3(x_28, x_2, x_3);
lean::cnstr_set(x_1, 0, x_175);
return x_1;
}
else
{
obj* x_176; 
x_176 = l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__3(x_28, x_2, x_3);
if (lean::obj_tag(x_176) == 0)
{
lean::free_heap_obj(x_1);
lean::dec(x_31);
lean::dec(x_30);
lean::dec(x_29);
return x_176;
}
else
{
obj* x_177; 
x_177 = lean::cnstr_get(x_176, 0);
lean::inc(x_177);
if (lean::obj_tag(x_177) == 0)
{
obj* x_178; 
x_178 = lean::cnstr_get(x_176, 3);
lean::inc(x_178);
if (lean::obj_tag(x_178) == 0)
{
uint8 x_179; 
x_179 = !lean::is_exclusive(x_176);
if (x_179 == 0)
{
obj* x_180; obj* x_181; uint8 x_182; uint8 x_183; 
x_180 = lean::cnstr_get(x_176, 3);
lean::dec(x_180);
x_181 = lean::cnstr_get(x_176, 0);
lean::dec(x_181);
x_182 = 0;
lean::cnstr_set(x_176, 0, x_178);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_182);
x_183 = 1;
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_183);
return x_1;
}
else
{
obj* x_184; obj* x_185; uint8 x_186; obj* x_187; uint8 x_188; 
x_184 = lean::cnstr_get(x_176, 1);
x_185 = lean::cnstr_get(x_176, 2);
lean::inc(x_185);
lean::inc(x_184);
lean::dec(x_176);
x_186 = 0;
x_187 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_187, 0, x_178);
lean::cnstr_set(x_187, 1, x_184);
lean::cnstr_set(x_187, 2, x_185);
lean::cnstr_set(x_187, 3, x_178);
lean::cnstr_set_scalar(x_187, sizeof(void*)*4, x_186);
x_188 = 1;
lean::cnstr_set(x_1, 0, x_187);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
else
{
uint8 x_189; 
x_189 = lean::cnstr_get_scalar<uint8>(x_178, sizeof(void*)*4);
if (x_189 == 0)
{
uint8 x_190; 
x_190 = !lean::is_exclusive(x_176);
if (x_190 == 0)
{
obj* x_191; obj* x_192; obj* x_193; obj* x_194; uint8 x_195; 
x_191 = lean::cnstr_get(x_176, 1);
x_192 = lean::cnstr_get(x_176, 2);
x_193 = lean::cnstr_get(x_176, 3);
lean::dec(x_193);
x_194 = lean::cnstr_get(x_176, 0);
lean::dec(x_194);
x_195 = !lean::is_exclusive(x_178);
if (x_195 == 0)
{
obj* x_196; obj* x_197; obj* x_198; obj* x_199; uint8 x_200; 
x_196 = lean::cnstr_get(x_178, 0);
x_197 = lean::cnstr_get(x_178, 1);
x_198 = lean::cnstr_get(x_178, 2);
x_199 = lean::cnstr_get(x_178, 3);
x_200 = 1;
lean::cnstr_set(x_178, 3, x_196);
lean::cnstr_set(x_178, 2, x_192);
lean::cnstr_set(x_178, 1, x_191);
lean::cnstr_set(x_178, 0, x_177);
lean::cnstr_set_scalar(x_178, sizeof(void*)*4, x_200);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_199);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_200);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_198);
lean::cnstr_set(x_1, 1, x_197);
lean::cnstr_set(x_1, 0, x_178);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
obj* x_201; obj* x_202; obj* x_203; obj* x_204; uint8 x_205; obj* x_206; 
x_201 = lean::cnstr_get(x_178, 0);
x_202 = lean::cnstr_get(x_178, 1);
x_203 = lean::cnstr_get(x_178, 2);
x_204 = lean::cnstr_get(x_178, 3);
lean::inc(x_204);
lean::inc(x_203);
lean::inc(x_202);
lean::inc(x_201);
lean::dec(x_178);
x_205 = 1;
x_206 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_206, 0, x_177);
lean::cnstr_set(x_206, 1, x_191);
lean::cnstr_set(x_206, 2, x_192);
lean::cnstr_set(x_206, 3, x_201);
lean::cnstr_set_scalar(x_206, sizeof(void*)*4, x_205);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_204);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_205);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_203);
lean::cnstr_set(x_1, 1, x_202);
lean::cnstr_set(x_1, 0, x_206);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; uint8 x_214; obj* x_215; obj* x_216; 
x_207 = lean::cnstr_get(x_176, 1);
x_208 = lean::cnstr_get(x_176, 2);
lean::inc(x_208);
lean::inc(x_207);
lean::dec(x_176);
x_209 = lean::cnstr_get(x_178, 0);
lean::inc(x_209);
x_210 = lean::cnstr_get(x_178, 1);
lean::inc(x_210);
x_211 = lean::cnstr_get(x_178, 2);
lean::inc(x_211);
x_212 = lean::cnstr_get(x_178, 3);
lean::inc(x_212);
if (lean::is_exclusive(x_178)) {
 lean::cnstr_release(x_178, 0);
 lean::cnstr_release(x_178, 1);
 lean::cnstr_release(x_178, 2);
 lean::cnstr_release(x_178, 3);
 x_213 = x_178;
} else {
 lean::dec_ref(x_178);
 x_213 = lean::box(0);
}
x_214 = 1;
if (lean::is_scalar(x_213)) {
 x_215 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_215 = x_213;
}
lean::cnstr_set(x_215, 0, x_177);
lean::cnstr_set(x_215, 1, x_207);
lean::cnstr_set(x_215, 2, x_208);
lean::cnstr_set(x_215, 3, x_209);
lean::cnstr_set_scalar(x_215, sizeof(void*)*4, x_214);
x_216 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_216, 0, x_212);
lean::cnstr_set(x_216, 1, x_29);
lean::cnstr_set(x_216, 2, x_30);
lean::cnstr_set(x_216, 3, x_31);
lean::cnstr_set_scalar(x_216, sizeof(void*)*4, x_214);
lean::cnstr_set(x_1, 3, x_216);
lean::cnstr_set(x_1, 2, x_211);
lean::cnstr_set(x_1, 1, x_210);
lean::cnstr_set(x_1, 0, x_215);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
uint8 x_217; 
x_217 = !lean::is_exclusive(x_176);
if (x_217 == 0)
{
obj* x_218; obj* x_219; uint8 x_220; 
x_218 = lean::cnstr_get(x_176, 3);
lean::dec(x_218);
x_219 = lean::cnstr_get(x_176, 0);
lean::dec(x_219);
x_220 = 0;
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_220);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
obj* x_221; obj* x_222; uint8 x_223; obj* x_224; 
x_221 = lean::cnstr_get(x_176, 1);
x_222 = lean::cnstr_get(x_176, 2);
lean::inc(x_222);
lean::inc(x_221);
lean::dec(x_176);
x_223 = 0;
x_224 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_224, 0, x_177);
lean::cnstr_set(x_224, 1, x_221);
lean::cnstr_set(x_224, 2, x_222);
lean::cnstr_set(x_224, 3, x_178);
lean::cnstr_set_scalar(x_224, sizeof(void*)*4, x_223);
lean::cnstr_set(x_1, 0, x_224);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
}
}
else
{
uint8 x_225; 
x_225 = lean::cnstr_get_scalar<uint8>(x_177, sizeof(void*)*4);
if (x_225 == 0)
{
uint8 x_226; 
x_226 = !lean::is_exclusive(x_176);
if (x_226 == 0)
{
obj* x_227; obj* x_228; obj* x_229; obj* x_230; uint8 x_231; 
x_227 = lean::cnstr_get(x_176, 1);
x_228 = lean::cnstr_get(x_176, 2);
x_229 = lean::cnstr_get(x_176, 3);
x_230 = lean::cnstr_get(x_176, 0);
lean::dec(x_230);
x_231 = !lean::is_exclusive(x_177);
if (x_231 == 0)
{
uint8 x_232; 
x_232 = 1;
lean::cnstr_set_scalar(x_177, sizeof(void*)*4, x_232);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_229);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_232);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_228);
lean::cnstr_set(x_1, 1, x_227);
lean::cnstr_set(x_1, 0, x_177);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
obj* x_233; obj* x_234; obj* x_235; obj* x_236; uint8 x_237; obj* x_238; 
x_233 = lean::cnstr_get(x_177, 0);
x_234 = lean::cnstr_get(x_177, 1);
x_235 = lean::cnstr_get(x_177, 2);
x_236 = lean::cnstr_get(x_177, 3);
lean::inc(x_236);
lean::inc(x_235);
lean::inc(x_234);
lean::inc(x_233);
lean::dec(x_177);
x_237 = 1;
x_238 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_238, 0, x_233);
lean::cnstr_set(x_238, 1, x_234);
lean::cnstr_set(x_238, 2, x_235);
lean::cnstr_set(x_238, 3, x_236);
lean::cnstr_set_scalar(x_238, sizeof(void*)*4, x_237);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_229);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_237);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_228);
lean::cnstr_set(x_1, 1, x_227);
lean::cnstr_set(x_1, 0, x_238);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
obj* x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; obj* x_244; obj* x_245; obj* x_246; uint8 x_247; obj* x_248; obj* x_249; 
x_239 = lean::cnstr_get(x_176, 1);
x_240 = lean::cnstr_get(x_176, 2);
x_241 = lean::cnstr_get(x_176, 3);
lean::inc(x_241);
lean::inc(x_240);
lean::inc(x_239);
lean::dec(x_176);
x_242 = lean::cnstr_get(x_177, 0);
lean::inc(x_242);
x_243 = lean::cnstr_get(x_177, 1);
lean::inc(x_243);
x_244 = lean::cnstr_get(x_177, 2);
lean::inc(x_244);
x_245 = lean::cnstr_get(x_177, 3);
lean::inc(x_245);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_246 = x_177;
} else {
 lean::dec_ref(x_177);
 x_246 = lean::box(0);
}
x_247 = 1;
if (lean::is_scalar(x_246)) {
 x_248 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_248 = x_246;
}
lean::cnstr_set(x_248, 0, x_242);
lean::cnstr_set(x_248, 1, x_243);
lean::cnstr_set(x_248, 2, x_244);
lean::cnstr_set(x_248, 3, x_245);
lean::cnstr_set_scalar(x_248, sizeof(void*)*4, x_247);
x_249 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_249, 0, x_241);
lean::cnstr_set(x_249, 1, x_29);
lean::cnstr_set(x_249, 2, x_30);
lean::cnstr_set(x_249, 3, x_31);
lean::cnstr_set_scalar(x_249, sizeof(void*)*4, x_247);
lean::cnstr_set(x_1, 3, x_249);
lean::cnstr_set(x_1, 2, x_240);
lean::cnstr_set(x_1, 1, x_239);
lean::cnstr_set(x_1, 0, x_248);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
obj* x_250; 
x_250 = lean::cnstr_get(x_176, 3);
lean::inc(x_250);
if (lean::obj_tag(x_250) == 0)
{
uint8 x_251; 
x_251 = !lean::is_exclusive(x_176);
if (x_251 == 0)
{
obj* x_252; obj* x_253; uint8 x_254; 
x_252 = lean::cnstr_get(x_176, 3);
lean::dec(x_252);
x_253 = lean::cnstr_get(x_176, 0);
lean::dec(x_253);
x_254 = 0;
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_254);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
obj* x_255; obj* x_256; uint8 x_257; obj* x_258; 
x_255 = lean::cnstr_get(x_176, 1);
x_256 = lean::cnstr_get(x_176, 2);
lean::inc(x_256);
lean::inc(x_255);
lean::dec(x_176);
x_257 = 0;
x_258 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_258, 0, x_177);
lean::cnstr_set(x_258, 1, x_255);
lean::cnstr_set(x_258, 2, x_256);
lean::cnstr_set(x_258, 3, x_250);
lean::cnstr_set_scalar(x_258, sizeof(void*)*4, x_257);
lean::cnstr_set(x_1, 0, x_258);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
uint8 x_259; 
x_259 = lean::cnstr_get_scalar<uint8>(x_250, sizeof(void*)*4);
if (x_259 == 0)
{
uint8 x_260; 
lean::free_heap_obj(x_1);
x_260 = !lean::is_exclusive(x_176);
if (x_260 == 0)
{
obj* x_261; obj* x_262; obj* x_263; obj* x_264; uint8 x_265; 
x_261 = lean::cnstr_get(x_176, 1);
x_262 = lean::cnstr_get(x_176, 2);
x_263 = lean::cnstr_get(x_176, 3);
lean::dec(x_263);
x_264 = lean::cnstr_get(x_176, 0);
lean::dec(x_264);
x_265 = !lean::is_exclusive(x_250);
if (x_265 == 0)
{
obj* x_266; obj* x_267; obj* x_268; obj* x_269; uint8 x_270; 
x_266 = lean::cnstr_get(x_250, 0);
x_267 = lean::cnstr_get(x_250, 1);
x_268 = lean::cnstr_get(x_250, 2);
x_269 = lean::cnstr_get(x_250, 3);
lean::inc(x_177);
lean::cnstr_set(x_250, 3, x_266);
lean::cnstr_set(x_250, 2, x_262);
lean::cnstr_set(x_250, 1, x_261);
lean::cnstr_set(x_250, 0, x_177);
x_270 = !lean::is_exclusive(x_177);
if (x_270 == 0)
{
obj* x_271; obj* x_272; obj* x_273; obj* x_274; 
x_271 = lean::cnstr_get(x_177, 3);
lean::dec(x_271);
x_272 = lean::cnstr_get(x_177, 2);
lean::dec(x_272);
x_273 = lean::cnstr_get(x_177, 1);
lean::dec(x_273);
x_274 = lean::cnstr_get(x_177, 0);
lean::dec(x_274);
lean::cnstr_set_scalar(x_250, sizeof(void*)*4, x_225);
lean::cnstr_set(x_177, 3, x_31);
lean::cnstr_set(x_177, 2, x_30);
lean::cnstr_set(x_177, 1, x_29);
lean::cnstr_set(x_177, 0, x_269);
lean::cnstr_set(x_176, 3, x_177);
lean::cnstr_set(x_176, 2, x_268);
lean::cnstr_set(x_176, 1, x_267);
lean::cnstr_set(x_176, 0, x_250);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_259);
return x_176;
}
else
{
obj* x_275; 
lean::dec(x_177);
lean::cnstr_set_scalar(x_250, sizeof(void*)*4, x_225);
x_275 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_275, 0, x_269);
lean::cnstr_set(x_275, 1, x_29);
lean::cnstr_set(x_275, 2, x_30);
lean::cnstr_set(x_275, 3, x_31);
lean::cnstr_set_scalar(x_275, sizeof(void*)*4, x_225);
lean::cnstr_set(x_176, 3, x_275);
lean::cnstr_set(x_176, 2, x_268);
lean::cnstr_set(x_176, 1, x_267);
lean::cnstr_set(x_176, 0, x_250);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
obj* x_276; obj* x_277; obj* x_278; obj* x_279; obj* x_280; obj* x_281; obj* x_282; 
x_276 = lean::cnstr_get(x_250, 0);
x_277 = lean::cnstr_get(x_250, 1);
x_278 = lean::cnstr_get(x_250, 2);
x_279 = lean::cnstr_get(x_250, 3);
lean::inc(x_279);
lean::inc(x_278);
lean::inc(x_277);
lean::inc(x_276);
lean::dec(x_250);
lean::inc(x_177);
x_280 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_280, 0, x_177);
lean::cnstr_set(x_280, 1, x_261);
lean::cnstr_set(x_280, 2, x_262);
lean::cnstr_set(x_280, 3, x_276);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_281 = x_177;
} else {
 lean::dec_ref(x_177);
 x_281 = lean::box(0);
}
lean::cnstr_set_scalar(x_280, sizeof(void*)*4, x_225);
if (lean::is_scalar(x_281)) {
 x_282 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_282 = x_281;
}
lean::cnstr_set(x_282, 0, x_279);
lean::cnstr_set(x_282, 1, x_29);
lean::cnstr_set(x_282, 2, x_30);
lean::cnstr_set(x_282, 3, x_31);
lean::cnstr_set_scalar(x_282, sizeof(void*)*4, x_225);
lean::cnstr_set(x_176, 3, x_282);
lean::cnstr_set(x_176, 2, x_278);
lean::cnstr_set(x_176, 1, x_277);
lean::cnstr_set(x_176, 0, x_280);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
obj* x_283; obj* x_284; obj* x_285; obj* x_286; obj* x_287; obj* x_288; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; 
x_283 = lean::cnstr_get(x_176, 1);
x_284 = lean::cnstr_get(x_176, 2);
lean::inc(x_284);
lean::inc(x_283);
lean::dec(x_176);
x_285 = lean::cnstr_get(x_250, 0);
lean::inc(x_285);
x_286 = lean::cnstr_get(x_250, 1);
lean::inc(x_286);
x_287 = lean::cnstr_get(x_250, 2);
lean::inc(x_287);
x_288 = lean::cnstr_get(x_250, 3);
lean::inc(x_288);
if (lean::is_exclusive(x_250)) {
 lean::cnstr_release(x_250, 0);
 lean::cnstr_release(x_250, 1);
 lean::cnstr_release(x_250, 2);
 lean::cnstr_release(x_250, 3);
 x_289 = x_250;
} else {
 lean::dec_ref(x_250);
 x_289 = lean::box(0);
}
lean::inc(x_177);
if (lean::is_scalar(x_289)) {
 x_290 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_290 = x_289;
}
lean::cnstr_set(x_290, 0, x_177);
lean::cnstr_set(x_290, 1, x_283);
lean::cnstr_set(x_290, 2, x_284);
lean::cnstr_set(x_290, 3, x_285);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_291 = x_177;
} else {
 lean::dec_ref(x_177);
 x_291 = lean::box(0);
}
lean::cnstr_set_scalar(x_290, sizeof(void*)*4, x_225);
if (lean::is_scalar(x_291)) {
 x_292 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_292 = x_291;
}
lean::cnstr_set(x_292, 0, x_288);
lean::cnstr_set(x_292, 1, x_29);
lean::cnstr_set(x_292, 2, x_30);
lean::cnstr_set(x_292, 3, x_31);
lean::cnstr_set_scalar(x_292, sizeof(void*)*4, x_225);
x_293 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_293, 0, x_290);
lean::cnstr_set(x_293, 1, x_286);
lean::cnstr_set(x_293, 2, x_287);
lean::cnstr_set(x_293, 3, x_292);
lean::cnstr_set_scalar(x_293, sizeof(void*)*4, x_259);
return x_293;
}
}
else
{
uint8 x_294; 
x_294 = !lean::is_exclusive(x_176);
if (x_294 == 0)
{
obj* x_295; obj* x_296; uint8 x_297; 
x_295 = lean::cnstr_get(x_176, 3);
lean::dec(x_295);
x_296 = lean::cnstr_get(x_176, 0);
lean::dec(x_296);
x_297 = !lean::is_exclusive(x_177);
if (x_297 == 0)
{
uint8 x_298; 
lean::cnstr_set_scalar(x_177, sizeof(void*)*4, x_259);
x_298 = 0;
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_298);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_259);
return x_1;
}
else
{
obj* x_299; obj* x_300; obj* x_301; obj* x_302; obj* x_303; uint8 x_304; 
x_299 = lean::cnstr_get(x_177, 0);
x_300 = lean::cnstr_get(x_177, 1);
x_301 = lean::cnstr_get(x_177, 2);
x_302 = lean::cnstr_get(x_177, 3);
lean::inc(x_302);
lean::inc(x_301);
lean::inc(x_300);
lean::inc(x_299);
lean::dec(x_177);
x_303 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_303, 0, x_299);
lean::cnstr_set(x_303, 1, x_300);
lean::cnstr_set(x_303, 2, x_301);
lean::cnstr_set(x_303, 3, x_302);
lean::cnstr_set_scalar(x_303, sizeof(void*)*4, x_259);
x_304 = 0;
lean::cnstr_set(x_176, 0, x_303);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_304);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
else
{
obj* x_305; obj* x_306; obj* x_307; obj* x_308; obj* x_309; obj* x_310; obj* x_311; obj* x_312; uint8 x_313; obj* x_314; 
x_305 = lean::cnstr_get(x_176, 1);
x_306 = lean::cnstr_get(x_176, 2);
lean::inc(x_306);
lean::inc(x_305);
lean::dec(x_176);
x_307 = lean::cnstr_get(x_177, 0);
lean::inc(x_307);
x_308 = lean::cnstr_get(x_177, 1);
lean::inc(x_308);
x_309 = lean::cnstr_get(x_177, 2);
lean::inc(x_309);
x_310 = lean::cnstr_get(x_177, 3);
lean::inc(x_310);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_311 = x_177;
} else {
 lean::dec_ref(x_177);
 x_311 = lean::box(0);
}
if (lean::is_scalar(x_311)) {
 x_312 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_312 = x_311;
}
lean::cnstr_set(x_312, 0, x_307);
lean::cnstr_set(x_312, 1, x_308);
lean::cnstr_set(x_312, 2, x_309);
lean::cnstr_set(x_312, 3, x_310);
lean::cnstr_set_scalar(x_312, sizeof(void*)*4, x_259);
x_313 = 0;
x_314 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_314, 0, x_312);
lean::cnstr_set(x_314, 1, x_305);
lean::cnstr_set(x_314, 2, x_306);
lean::cnstr_set(x_314, 3, x_250);
lean::cnstr_set_scalar(x_314, sizeof(void*)*4, x_313);
lean::cnstr_set(x_1, 0, x_314);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
}
}
}
}
}
}
}
else
{
obj* x_315; obj* x_316; obj* x_317; obj* x_318; uint8 x_319; 
x_315 = lean::cnstr_get(x_1, 0);
x_316 = lean::cnstr_get(x_1, 1);
x_317 = lean::cnstr_get(x_1, 2);
x_318 = lean::cnstr_get(x_1, 3);
lean::inc(x_318);
lean::inc(x_317);
lean::inc(x_316);
lean::inc(x_315);
lean::dec(x_1);
x_319 = l_Lean_Name_quickLt(x_2, x_316);
if (x_319 == 0)
{
uint8 x_320; 
x_320 = l_Lean_Name_quickLt(x_316, x_2);
if (x_320 == 0)
{
obj* x_321; 
lean::dec(x_317);
lean::dec(x_316);
x_321 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_321, 0, x_315);
lean::cnstr_set(x_321, 1, x_2);
lean::cnstr_set(x_321, 2, x_3);
lean::cnstr_set(x_321, 3, x_318);
lean::cnstr_set_scalar(x_321, sizeof(void*)*4, x_6);
return x_321;
}
else
{
uint8 x_322; 
x_322 = l_RBNode_isRed___main___rarg(x_318);
if (x_322 == 0)
{
obj* x_323; obj* x_324; 
x_323 = l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__3(x_318, x_2, x_3);
x_324 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_324, 0, x_315);
lean::cnstr_set(x_324, 1, x_316);
lean::cnstr_set(x_324, 2, x_317);
lean::cnstr_set(x_324, 3, x_323);
lean::cnstr_set_scalar(x_324, sizeof(void*)*4, x_6);
return x_324;
}
else
{
obj* x_325; 
x_325 = l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__3(x_318, x_2, x_3);
if (lean::obj_tag(x_325) == 0)
{
lean::dec(x_317);
lean::dec(x_316);
lean::dec(x_315);
return x_325;
}
else
{
obj* x_326; 
x_326 = lean::cnstr_get(x_325, 0);
lean::inc(x_326);
if (lean::obj_tag(x_326) == 0)
{
obj* x_327; 
x_327 = lean::cnstr_get(x_325, 3);
lean::inc(x_327);
if (lean::obj_tag(x_327) == 0)
{
obj* x_328; obj* x_329; obj* x_330; uint8 x_331; obj* x_332; uint8 x_333; obj* x_334; 
x_328 = lean::cnstr_get(x_325, 1);
lean::inc(x_328);
x_329 = lean::cnstr_get(x_325, 2);
lean::inc(x_329);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_330 = x_325;
} else {
 lean::dec_ref(x_325);
 x_330 = lean::box(0);
}
x_331 = 0;
if (lean::is_scalar(x_330)) {
 x_332 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_332 = x_330;
}
lean::cnstr_set(x_332, 0, x_327);
lean::cnstr_set(x_332, 1, x_328);
lean::cnstr_set(x_332, 2, x_329);
lean::cnstr_set(x_332, 3, x_327);
lean::cnstr_set_scalar(x_332, sizeof(void*)*4, x_331);
x_333 = 1;
x_334 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_334, 0, x_315);
lean::cnstr_set(x_334, 1, x_316);
lean::cnstr_set(x_334, 2, x_317);
lean::cnstr_set(x_334, 3, x_332);
lean::cnstr_set_scalar(x_334, sizeof(void*)*4, x_333);
return x_334;
}
else
{
uint8 x_335; 
x_335 = lean::cnstr_get_scalar<uint8>(x_327, sizeof(void*)*4);
if (x_335 == 0)
{
obj* x_336; obj* x_337; obj* x_338; obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_343; uint8 x_344; obj* x_345; obj* x_346; obj* x_347; 
x_336 = lean::cnstr_get(x_325, 1);
lean::inc(x_336);
x_337 = lean::cnstr_get(x_325, 2);
lean::inc(x_337);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_338 = x_325;
} else {
 lean::dec_ref(x_325);
 x_338 = lean::box(0);
}
x_339 = lean::cnstr_get(x_327, 0);
lean::inc(x_339);
x_340 = lean::cnstr_get(x_327, 1);
lean::inc(x_340);
x_341 = lean::cnstr_get(x_327, 2);
lean::inc(x_341);
x_342 = lean::cnstr_get(x_327, 3);
lean::inc(x_342);
if (lean::is_exclusive(x_327)) {
 lean::cnstr_release(x_327, 0);
 lean::cnstr_release(x_327, 1);
 lean::cnstr_release(x_327, 2);
 lean::cnstr_release(x_327, 3);
 x_343 = x_327;
} else {
 lean::dec_ref(x_327);
 x_343 = lean::box(0);
}
x_344 = 1;
if (lean::is_scalar(x_343)) {
 x_345 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_345 = x_343;
}
lean::cnstr_set(x_345, 0, x_315);
lean::cnstr_set(x_345, 1, x_316);
lean::cnstr_set(x_345, 2, x_317);
lean::cnstr_set(x_345, 3, x_326);
lean::cnstr_set_scalar(x_345, sizeof(void*)*4, x_344);
if (lean::is_scalar(x_338)) {
 x_346 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_346 = x_338;
}
lean::cnstr_set(x_346, 0, x_339);
lean::cnstr_set(x_346, 1, x_340);
lean::cnstr_set(x_346, 2, x_341);
lean::cnstr_set(x_346, 3, x_342);
lean::cnstr_set_scalar(x_346, sizeof(void*)*4, x_344);
x_347 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_347, 0, x_345);
lean::cnstr_set(x_347, 1, x_336);
lean::cnstr_set(x_347, 2, x_337);
lean::cnstr_set(x_347, 3, x_346);
lean::cnstr_set_scalar(x_347, sizeof(void*)*4, x_335);
return x_347;
}
else
{
obj* x_348; obj* x_349; obj* x_350; uint8 x_351; obj* x_352; obj* x_353; 
x_348 = lean::cnstr_get(x_325, 1);
lean::inc(x_348);
x_349 = lean::cnstr_get(x_325, 2);
lean::inc(x_349);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_350 = x_325;
} else {
 lean::dec_ref(x_325);
 x_350 = lean::box(0);
}
x_351 = 0;
if (lean::is_scalar(x_350)) {
 x_352 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_352 = x_350;
}
lean::cnstr_set(x_352, 0, x_326);
lean::cnstr_set(x_352, 1, x_348);
lean::cnstr_set(x_352, 2, x_349);
lean::cnstr_set(x_352, 3, x_327);
lean::cnstr_set_scalar(x_352, sizeof(void*)*4, x_351);
x_353 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_353, 0, x_315);
lean::cnstr_set(x_353, 1, x_316);
lean::cnstr_set(x_353, 2, x_317);
lean::cnstr_set(x_353, 3, x_352);
lean::cnstr_set_scalar(x_353, sizeof(void*)*4, x_335);
return x_353;
}
}
}
else
{
uint8 x_354; 
x_354 = lean::cnstr_get_scalar<uint8>(x_326, sizeof(void*)*4);
if (x_354 == 0)
{
obj* x_355; obj* x_356; obj* x_357; obj* x_358; obj* x_359; obj* x_360; obj* x_361; obj* x_362; obj* x_363; uint8 x_364; obj* x_365; obj* x_366; obj* x_367; 
x_355 = lean::cnstr_get(x_325, 1);
lean::inc(x_355);
x_356 = lean::cnstr_get(x_325, 2);
lean::inc(x_356);
x_357 = lean::cnstr_get(x_325, 3);
lean::inc(x_357);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_358 = x_325;
} else {
 lean::dec_ref(x_325);
 x_358 = lean::box(0);
}
x_359 = lean::cnstr_get(x_326, 0);
lean::inc(x_359);
x_360 = lean::cnstr_get(x_326, 1);
lean::inc(x_360);
x_361 = lean::cnstr_get(x_326, 2);
lean::inc(x_361);
x_362 = lean::cnstr_get(x_326, 3);
lean::inc(x_362);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 lean::cnstr_release(x_326, 2);
 lean::cnstr_release(x_326, 3);
 x_363 = x_326;
} else {
 lean::dec_ref(x_326);
 x_363 = lean::box(0);
}
x_364 = 1;
if (lean::is_scalar(x_363)) {
 x_365 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_365 = x_363;
}
lean::cnstr_set(x_365, 0, x_315);
lean::cnstr_set(x_365, 1, x_316);
lean::cnstr_set(x_365, 2, x_317);
lean::cnstr_set(x_365, 3, x_359);
lean::cnstr_set_scalar(x_365, sizeof(void*)*4, x_364);
if (lean::is_scalar(x_358)) {
 x_366 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_366 = x_358;
}
lean::cnstr_set(x_366, 0, x_362);
lean::cnstr_set(x_366, 1, x_355);
lean::cnstr_set(x_366, 2, x_356);
lean::cnstr_set(x_366, 3, x_357);
lean::cnstr_set_scalar(x_366, sizeof(void*)*4, x_364);
x_367 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_367, 0, x_365);
lean::cnstr_set(x_367, 1, x_360);
lean::cnstr_set(x_367, 2, x_361);
lean::cnstr_set(x_367, 3, x_366);
lean::cnstr_set_scalar(x_367, sizeof(void*)*4, x_354);
return x_367;
}
else
{
obj* x_368; 
x_368 = lean::cnstr_get(x_325, 3);
lean::inc(x_368);
if (lean::obj_tag(x_368) == 0)
{
obj* x_369; obj* x_370; obj* x_371; uint8 x_372; obj* x_373; obj* x_374; 
x_369 = lean::cnstr_get(x_325, 1);
lean::inc(x_369);
x_370 = lean::cnstr_get(x_325, 2);
lean::inc(x_370);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_371 = x_325;
} else {
 lean::dec_ref(x_325);
 x_371 = lean::box(0);
}
x_372 = 0;
if (lean::is_scalar(x_371)) {
 x_373 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_373 = x_371;
}
lean::cnstr_set(x_373, 0, x_326);
lean::cnstr_set(x_373, 1, x_369);
lean::cnstr_set(x_373, 2, x_370);
lean::cnstr_set(x_373, 3, x_368);
lean::cnstr_set_scalar(x_373, sizeof(void*)*4, x_372);
x_374 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_374, 0, x_315);
lean::cnstr_set(x_374, 1, x_316);
lean::cnstr_set(x_374, 2, x_317);
lean::cnstr_set(x_374, 3, x_373);
lean::cnstr_set_scalar(x_374, sizeof(void*)*4, x_354);
return x_374;
}
else
{
uint8 x_375; 
x_375 = lean::cnstr_get_scalar<uint8>(x_368, sizeof(void*)*4);
if (x_375 == 0)
{
obj* x_376; obj* x_377; obj* x_378; obj* x_379; obj* x_380; obj* x_381; obj* x_382; obj* x_383; obj* x_384; obj* x_385; obj* x_386; obj* x_387; 
x_376 = lean::cnstr_get(x_325, 1);
lean::inc(x_376);
x_377 = lean::cnstr_get(x_325, 2);
lean::inc(x_377);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_378 = x_325;
} else {
 lean::dec_ref(x_325);
 x_378 = lean::box(0);
}
x_379 = lean::cnstr_get(x_368, 0);
lean::inc(x_379);
x_380 = lean::cnstr_get(x_368, 1);
lean::inc(x_380);
x_381 = lean::cnstr_get(x_368, 2);
lean::inc(x_381);
x_382 = lean::cnstr_get(x_368, 3);
lean::inc(x_382);
if (lean::is_exclusive(x_368)) {
 lean::cnstr_release(x_368, 0);
 lean::cnstr_release(x_368, 1);
 lean::cnstr_release(x_368, 2);
 lean::cnstr_release(x_368, 3);
 x_383 = x_368;
} else {
 lean::dec_ref(x_368);
 x_383 = lean::box(0);
}
lean::inc(x_326);
if (lean::is_scalar(x_383)) {
 x_384 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_384 = x_383;
}
lean::cnstr_set(x_384, 0, x_315);
lean::cnstr_set(x_384, 1, x_316);
lean::cnstr_set(x_384, 2, x_317);
lean::cnstr_set(x_384, 3, x_326);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 lean::cnstr_release(x_326, 2);
 lean::cnstr_release(x_326, 3);
 x_385 = x_326;
} else {
 lean::dec_ref(x_326);
 x_385 = lean::box(0);
}
lean::cnstr_set_scalar(x_384, sizeof(void*)*4, x_354);
if (lean::is_scalar(x_385)) {
 x_386 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_386 = x_385;
}
lean::cnstr_set(x_386, 0, x_379);
lean::cnstr_set(x_386, 1, x_380);
lean::cnstr_set(x_386, 2, x_381);
lean::cnstr_set(x_386, 3, x_382);
lean::cnstr_set_scalar(x_386, sizeof(void*)*4, x_354);
if (lean::is_scalar(x_378)) {
 x_387 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_387 = x_378;
}
lean::cnstr_set(x_387, 0, x_384);
lean::cnstr_set(x_387, 1, x_376);
lean::cnstr_set(x_387, 2, x_377);
lean::cnstr_set(x_387, 3, x_386);
lean::cnstr_set_scalar(x_387, sizeof(void*)*4, x_375);
return x_387;
}
else
{
obj* x_388; obj* x_389; obj* x_390; obj* x_391; obj* x_392; obj* x_393; obj* x_394; obj* x_395; obj* x_396; uint8 x_397; obj* x_398; obj* x_399; 
x_388 = lean::cnstr_get(x_325, 1);
lean::inc(x_388);
x_389 = lean::cnstr_get(x_325, 2);
lean::inc(x_389);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_390 = x_325;
} else {
 lean::dec_ref(x_325);
 x_390 = lean::box(0);
}
x_391 = lean::cnstr_get(x_326, 0);
lean::inc(x_391);
x_392 = lean::cnstr_get(x_326, 1);
lean::inc(x_392);
x_393 = lean::cnstr_get(x_326, 2);
lean::inc(x_393);
x_394 = lean::cnstr_get(x_326, 3);
lean::inc(x_394);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 lean::cnstr_release(x_326, 2);
 lean::cnstr_release(x_326, 3);
 x_395 = x_326;
} else {
 lean::dec_ref(x_326);
 x_395 = lean::box(0);
}
if (lean::is_scalar(x_395)) {
 x_396 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_396 = x_395;
}
lean::cnstr_set(x_396, 0, x_391);
lean::cnstr_set(x_396, 1, x_392);
lean::cnstr_set(x_396, 2, x_393);
lean::cnstr_set(x_396, 3, x_394);
lean::cnstr_set_scalar(x_396, sizeof(void*)*4, x_375);
x_397 = 0;
if (lean::is_scalar(x_390)) {
 x_398 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_398 = x_390;
}
lean::cnstr_set(x_398, 0, x_396);
lean::cnstr_set(x_398, 1, x_388);
lean::cnstr_set(x_398, 2, x_389);
lean::cnstr_set(x_398, 3, x_368);
lean::cnstr_set_scalar(x_398, sizeof(void*)*4, x_397);
x_399 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_399, 0, x_315);
lean::cnstr_set(x_399, 1, x_316);
lean::cnstr_set(x_399, 2, x_317);
lean::cnstr_set(x_399, 3, x_398);
lean::cnstr_set_scalar(x_399, sizeof(void*)*4, x_375);
return x_399;
}
}
}
}
}
}
}
}
else
{
uint8 x_400; 
x_400 = l_RBNode_isRed___main___rarg(x_315);
if (x_400 == 0)
{
obj* x_401; obj* x_402; 
x_401 = l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__3(x_315, x_2, x_3);
x_402 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_402, 0, x_401);
lean::cnstr_set(x_402, 1, x_316);
lean::cnstr_set(x_402, 2, x_317);
lean::cnstr_set(x_402, 3, x_318);
lean::cnstr_set_scalar(x_402, sizeof(void*)*4, x_6);
return x_402;
}
else
{
obj* x_403; 
x_403 = l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__3(x_315, x_2, x_3);
if (lean::obj_tag(x_403) == 0)
{
lean::dec(x_318);
lean::dec(x_317);
lean::dec(x_316);
return x_403;
}
else
{
obj* x_404; 
x_404 = lean::cnstr_get(x_403, 0);
lean::inc(x_404);
if (lean::obj_tag(x_404) == 0)
{
obj* x_405; 
x_405 = lean::cnstr_get(x_403, 3);
lean::inc(x_405);
if (lean::obj_tag(x_405) == 0)
{
obj* x_406; obj* x_407; obj* x_408; uint8 x_409; obj* x_410; uint8 x_411; obj* x_412; 
x_406 = lean::cnstr_get(x_403, 1);
lean::inc(x_406);
x_407 = lean::cnstr_get(x_403, 2);
lean::inc(x_407);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_408 = x_403;
} else {
 lean::dec_ref(x_403);
 x_408 = lean::box(0);
}
x_409 = 0;
if (lean::is_scalar(x_408)) {
 x_410 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_410 = x_408;
}
lean::cnstr_set(x_410, 0, x_405);
lean::cnstr_set(x_410, 1, x_406);
lean::cnstr_set(x_410, 2, x_407);
lean::cnstr_set(x_410, 3, x_405);
lean::cnstr_set_scalar(x_410, sizeof(void*)*4, x_409);
x_411 = 1;
x_412 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_412, 0, x_410);
lean::cnstr_set(x_412, 1, x_316);
lean::cnstr_set(x_412, 2, x_317);
lean::cnstr_set(x_412, 3, x_318);
lean::cnstr_set_scalar(x_412, sizeof(void*)*4, x_411);
return x_412;
}
else
{
uint8 x_413; 
x_413 = lean::cnstr_get_scalar<uint8>(x_405, sizeof(void*)*4);
if (x_413 == 0)
{
obj* x_414; obj* x_415; obj* x_416; obj* x_417; obj* x_418; obj* x_419; obj* x_420; obj* x_421; uint8 x_422; obj* x_423; obj* x_424; obj* x_425; 
x_414 = lean::cnstr_get(x_403, 1);
lean::inc(x_414);
x_415 = lean::cnstr_get(x_403, 2);
lean::inc(x_415);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_416 = x_403;
} else {
 lean::dec_ref(x_403);
 x_416 = lean::box(0);
}
x_417 = lean::cnstr_get(x_405, 0);
lean::inc(x_417);
x_418 = lean::cnstr_get(x_405, 1);
lean::inc(x_418);
x_419 = lean::cnstr_get(x_405, 2);
lean::inc(x_419);
x_420 = lean::cnstr_get(x_405, 3);
lean::inc(x_420);
if (lean::is_exclusive(x_405)) {
 lean::cnstr_release(x_405, 0);
 lean::cnstr_release(x_405, 1);
 lean::cnstr_release(x_405, 2);
 lean::cnstr_release(x_405, 3);
 x_421 = x_405;
} else {
 lean::dec_ref(x_405);
 x_421 = lean::box(0);
}
x_422 = 1;
if (lean::is_scalar(x_421)) {
 x_423 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_423 = x_421;
}
lean::cnstr_set(x_423, 0, x_404);
lean::cnstr_set(x_423, 1, x_414);
lean::cnstr_set(x_423, 2, x_415);
lean::cnstr_set(x_423, 3, x_417);
lean::cnstr_set_scalar(x_423, sizeof(void*)*4, x_422);
if (lean::is_scalar(x_416)) {
 x_424 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_424 = x_416;
}
lean::cnstr_set(x_424, 0, x_420);
lean::cnstr_set(x_424, 1, x_316);
lean::cnstr_set(x_424, 2, x_317);
lean::cnstr_set(x_424, 3, x_318);
lean::cnstr_set_scalar(x_424, sizeof(void*)*4, x_422);
x_425 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_425, 0, x_423);
lean::cnstr_set(x_425, 1, x_418);
lean::cnstr_set(x_425, 2, x_419);
lean::cnstr_set(x_425, 3, x_424);
lean::cnstr_set_scalar(x_425, sizeof(void*)*4, x_413);
return x_425;
}
else
{
obj* x_426; obj* x_427; obj* x_428; uint8 x_429; obj* x_430; obj* x_431; 
x_426 = lean::cnstr_get(x_403, 1);
lean::inc(x_426);
x_427 = lean::cnstr_get(x_403, 2);
lean::inc(x_427);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_428 = x_403;
} else {
 lean::dec_ref(x_403);
 x_428 = lean::box(0);
}
x_429 = 0;
if (lean::is_scalar(x_428)) {
 x_430 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_430 = x_428;
}
lean::cnstr_set(x_430, 0, x_404);
lean::cnstr_set(x_430, 1, x_426);
lean::cnstr_set(x_430, 2, x_427);
lean::cnstr_set(x_430, 3, x_405);
lean::cnstr_set_scalar(x_430, sizeof(void*)*4, x_429);
x_431 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_431, 0, x_430);
lean::cnstr_set(x_431, 1, x_316);
lean::cnstr_set(x_431, 2, x_317);
lean::cnstr_set(x_431, 3, x_318);
lean::cnstr_set_scalar(x_431, sizeof(void*)*4, x_413);
return x_431;
}
}
}
else
{
uint8 x_432; 
x_432 = lean::cnstr_get_scalar<uint8>(x_404, sizeof(void*)*4);
if (x_432 == 0)
{
obj* x_433; obj* x_434; obj* x_435; obj* x_436; obj* x_437; obj* x_438; obj* x_439; obj* x_440; obj* x_441; uint8 x_442; obj* x_443; obj* x_444; obj* x_445; 
x_433 = lean::cnstr_get(x_403, 1);
lean::inc(x_433);
x_434 = lean::cnstr_get(x_403, 2);
lean::inc(x_434);
x_435 = lean::cnstr_get(x_403, 3);
lean::inc(x_435);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_436 = x_403;
} else {
 lean::dec_ref(x_403);
 x_436 = lean::box(0);
}
x_437 = lean::cnstr_get(x_404, 0);
lean::inc(x_437);
x_438 = lean::cnstr_get(x_404, 1);
lean::inc(x_438);
x_439 = lean::cnstr_get(x_404, 2);
lean::inc(x_439);
x_440 = lean::cnstr_get(x_404, 3);
lean::inc(x_440);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 lean::cnstr_release(x_404, 2);
 lean::cnstr_release(x_404, 3);
 x_441 = x_404;
} else {
 lean::dec_ref(x_404);
 x_441 = lean::box(0);
}
x_442 = 1;
if (lean::is_scalar(x_441)) {
 x_443 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_443 = x_441;
}
lean::cnstr_set(x_443, 0, x_437);
lean::cnstr_set(x_443, 1, x_438);
lean::cnstr_set(x_443, 2, x_439);
lean::cnstr_set(x_443, 3, x_440);
lean::cnstr_set_scalar(x_443, sizeof(void*)*4, x_442);
if (lean::is_scalar(x_436)) {
 x_444 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_444 = x_436;
}
lean::cnstr_set(x_444, 0, x_435);
lean::cnstr_set(x_444, 1, x_316);
lean::cnstr_set(x_444, 2, x_317);
lean::cnstr_set(x_444, 3, x_318);
lean::cnstr_set_scalar(x_444, sizeof(void*)*4, x_442);
x_445 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_445, 0, x_443);
lean::cnstr_set(x_445, 1, x_433);
lean::cnstr_set(x_445, 2, x_434);
lean::cnstr_set(x_445, 3, x_444);
lean::cnstr_set_scalar(x_445, sizeof(void*)*4, x_432);
return x_445;
}
else
{
obj* x_446; 
x_446 = lean::cnstr_get(x_403, 3);
lean::inc(x_446);
if (lean::obj_tag(x_446) == 0)
{
obj* x_447; obj* x_448; obj* x_449; uint8 x_450; obj* x_451; obj* x_452; 
x_447 = lean::cnstr_get(x_403, 1);
lean::inc(x_447);
x_448 = lean::cnstr_get(x_403, 2);
lean::inc(x_448);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_449 = x_403;
} else {
 lean::dec_ref(x_403);
 x_449 = lean::box(0);
}
x_450 = 0;
if (lean::is_scalar(x_449)) {
 x_451 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_451 = x_449;
}
lean::cnstr_set(x_451, 0, x_404);
lean::cnstr_set(x_451, 1, x_447);
lean::cnstr_set(x_451, 2, x_448);
lean::cnstr_set(x_451, 3, x_446);
lean::cnstr_set_scalar(x_451, sizeof(void*)*4, x_450);
x_452 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_452, 0, x_451);
lean::cnstr_set(x_452, 1, x_316);
lean::cnstr_set(x_452, 2, x_317);
lean::cnstr_set(x_452, 3, x_318);
lean::cnstr_set_scalar(x_452, sizeof(void*)*4, x_432);
return x_452;
}
else
{
uint8 x_453; 
x_453 = lean::cnstr_get_scalar<uint8>(x_446, sizeof(void*)*4);
if (x_453 == 0)
{
obj* x_454; obj* x_455; obj* x_456; obj* x_457; obj* x_458; obj* x_459; obj* x_460; obj* x_461; obj* x_462; obj* x_463; obj* x_464; obj* x_465; 
x_454 = lean::cnstr_get(x_403, 1);
lean::inc(x_454);
x_455 = lean::cnstr_get(x_403, 2);
lean::inc(x_455);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_456 = x_403;
} else {
 lean::dec_ref(x_403);
 x_456 = lean::box(0);
}
x_457 = lean::cnstr_get(x_446, 0);
lean::inc(x_457);
x_458 = lean::cnstr_get(x_446, 1);
lean::inc(x_458);
x_459 = lean::cnstr_get(x_446, 2);
lean::inc(x_459);
x_460 = lean::cnstr_get(x_446, 3);
lean::inc(x_460);
if (lean::is_exclusive(x_446)) {
 lean::cnstr_release(x_446, 0);
 lean::cnstr_release(x_446, 1);
 lean::cnstr_release(x_446, 2);
 lean::cnstr_release(x_446, 3);
 x_461 = x_446;
} else {
 lean::dec_ref(x_446);
 x_461 = lean::box(0);
}
lean::inc(x_404);
if (lean::is_scalar(x_461)) {
 x_462 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_462 = x_461;
}
lean::cnstr_set(x_462, 0, x_404);
lean::cnstr_set(x_462, 1, x_454);
lean::cnstr_set(x_462, 2, x_455);
lean::cnstr_set(x_462, 3, x_457);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 lean::cnstr_release(x_404, 2);
 lean::cnstr_release(x_404, 3);
 x_463 = x_404;
} else {
 lean::dec_ref(x_404);
 x_463 = lean::box(0);
}
lean::cnstr_set_scalar(x_462, sizeof(void*)*4, x_432);
if (lean::is_scalar(x_463)) {
 x_464 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_464 = x_463;
}
lean::cnstr_set(x_464, 0, x_460);
lean::cnstr_set(x_464, 1, x_316);
lean::cnstr_set(x_464, 2, x_317);
lean::cnstr_set(x_464, 3, x_318);
lean::cnstr_set_scalar(x_464, sizeof(void*)*4, x_432);
if (lean::is_scalar(x_456)) {
 x_465 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_465 = x_456;
}
lean::cnstr_set(x_465, 0, x_462);
lean::cnstr_set(x_465, 1, x_458);
lean::cnstr_set(x_465, 2, x_459);
lean::cnstr_set(x_465, 3, x_464);
lean::cnstr_set_scalar(x_465, sizeof(void*)*4, x_453);
return x_465;
}
else
{
obj* x_466; obj* x_467; obj* x_468; obj* x_469; obj* x_470; obj* x_471; obj* x_472; obj* x_473; obj* x_474; uint8 x_475; obj* x_476; obj* x_477; 
x_466 = lean::cnstr_get(x_403, 1);
lean::inc(x_466);
x_467 = lean::cnstr_get(x_403, 2);
lean::inc(x_467);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_468 = x_403;
} else {
 lean::dec_ref(x_403);
 x_468 = lean::box(0);
}
x_469 = lean::cnstr_get(x_404, 0);
lean::inc(x_469);
x_470 = lean::cnstr_get(x_404, 1);
lean::inc(x_470);
x_471 = lean::cnstr_get(x_404, 2);
lean::inc(x_471);
x_472 = lean::cnstr_get(x_404, 3);
lean::inc(x_472);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 lean::cnstr_release(x_404, 2);
 lean::cnstr_release(x_404, 3);
 x_473 = x_404;
} else {
 lean::dec_ref(x_404);
 x_473 = lean::box(0);
}
if (lean::is_scalar(x_473)) {
 x_474 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_474 = x_473;
}
lean::cnstr_set(x_474, 0, x_469);
lean::cnstr_set(x_474, 1, x_470);
lean::cnstr_set(x_474, 2, x_471);
lean::cnstr_set(x_474, 3, x_472);
lean::cnstr_set_scalar(x_474, sizeof(void*)*4, x_453);
x_475 = 0;
if (lean::is_scalar(x_468)) {
 x_476 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_476 = x_468;
}
lean::cnstr_set(x_476, 0, x_474);
lean::cnstr_set(x_476, 1, x_466);
lean::cnstr_set(x_476, 2, x_467);
lean::cnstr_set(x_476, 3, x_446);
lean::cnstr_set_scalar(x_476, sizeof(void*)*4, x_475);
x_477 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_477, 0, x_476);
lean::cnstr_set(x_477, 1, x_316);
lean::cnstr_set(x_477, 2, x_317);
lean::cnstr_set(x_477, 3, x_318);
lean::cnstr_set_scalar(x_477, sizeof(void*)*4, x_453);
return x_477;
}
}
}
}
}
}
}
}
}
}
}
}
obj* l_RBNode_insert___at_Lean_Compiler_SpecState_addEntry___spec__2(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__3(x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__3(x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
uint8 l_AssocList_contains___main___at_Lean_Compiler_SpecState_addEntry___spec__5(obj* x_1, obj* x_2) {
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
obj* l_AssocList_mfoldl___main___at_Lean_Compiler_SpecState_addEntry___spec__8(obj* x_1, obj* x_2) {
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
obj* l_HashMapImp_moveEntries___main___at_Lean_Compiler_SpecState_addEntry___spec__7(obj* x_1, obj* x_2, obj* x_3) {
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
x_9 = l_AssocList_mfoldl___main___at_Lean_Compiler_SpecState_addEntry___spec__8(x_3, x_6);
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
obj* l_HashMapImp_expand___at_Lean_Compiler_SpecState_addEntry___spec__6(obj* x_1, obj* x_2) {
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
x_9 = l_HashMapImp_moveEntries___main___at_Lean_Compiler_SpecState_addEntry___spec__7(x_8, x_2, x_7);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_AssocList_replace___main___at_Lean_Compiler_SpecState_addEntry___spec__9(obj* x_1, obj* x_2, obj* x_3) {
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
x_9 = l_AssocList_replace___main___at_Lean_Compiler_SpecState_addEntry___spec__9(x_1, x_2, x_7);
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
x_14 = l_AssocList_replace___main___at_Lean_Compiler_SpecState_addEntry___spec__9(x_1, x_2, x_12);
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
obj* l_HashMapImp_insert___at_Lean_Compiler_SpecState_addEntry___spec__4(obj* x_1, obj* x_2, obj* x_3) {
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
x_13 = l_AssocList_contains___main___at_Lean_Compiler_SpecState_addEntry___spec__5(x_2, x_12);
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
x_20 = l_HashMapImp_expand___at_Lean_Compiler_SpecState_addEntry___spec__6(x_15, x_18);
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
x_21 = l_AssocList_replace___main___at_Lean_Compiler_SpecState_addEntry___spec__9(x_2, x_3, x_12);
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
x_32 = l_AssocList_contains___main___at_Lean_Compiler_SpecState_addEntry___spec__5(x_2, x_31);
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
x_39 = l_HashMapImp_expand___at_Lean_Compiler_SpecState_addEntry___spec__6(x_34, x_37);
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
x_41 = l_AssocList_replace___main___at_Lean_Compiler_SpecState_addEntry___spec__9(x_2, x_3, x_31);
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
obj* l_Lean_SMap_insert___main___at_Lean_Compiler_SpecState_addEntry___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*2);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_1);
if (x_5 == 0)
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_1, 1);
x_7 = l_RBNode_insert___at_Lean_Compiler_SpecState_addEntry___spec__2(x_6, x_2, x_3);
lean::cnstr_set(x_1, 1, x_7);
return x_1;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_1);
x_10 = l_RBNode_insert___at_Lean_Compiler_SpecState_addEntry___spec__2(x_9, x_2, x_3);
x_11 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_4);
return x_11;
}
}
else
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_1);
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
x_13 = lean::cnstr_get(x_1, 0);
x_14 = l_HashMapImp_insert___at_Lean_Compiler_SpecState_addEntry___spec__4(x_13, x_2, x_3);
lean::cnstr_set(x_1, 0, x_14);
return x_1;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = lean::cnstr_get(x_1, 0);
x_16 = lean::cnstr_get(x_1, 1);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_1);
x_17 = l_HashMapImp_insert___at_Lean_Compiler_SpecState_addEntry___spec__4(x_15, x_2, x_3);
x_18 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_16);
lean::cnstr_set_scalar(x_18, sizeof(void*)*2, x_4);
return x_18;
}
}
}
}
obj* l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__12(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_1);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::cnstr_get(x_1, 2);
x_11 = lean::cnstr_get(x_1, 3);
x_12 = lean_expr_quick_lt(x_2, x_9);
if (x_12 == 0)
{
uint8 x_13; 
x_13 = lean_expr_quick_lt(x_9, x_2);
if (x_13 == 0)
{
lean::dec(x_10);
lean::dec(x_9);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
return x_1;
}
else
{
obj* x_14; 
x_14 = l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__12(x_11, x_2, x_3);
lean::cnstr_set(x_1, 3, x_14);
return x_1;
}
}
else
{
obj* x_15; 
x_15 = l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__12(x_8, x_2, x_3);
lean::cnstr_set(x_1, 0, x_15);
return x_1;
}
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint8 x_20; 
x_16 = lean::cnstr_get(x_1, 0);
x_17 = lean::cnstr_get(x_1, 1);
x_18 = lean::cnstr_get(x_1, 2);
x_19 = lean::cnstr_get(x_1, 3);
lean::inc(x_19);
lean::inc(x_18);
lean::inc(x_17);
lean::inc(x_16);
lean::dec(x_1);
x_20 = lean_expr_quick_lt(x_2, x_17);
if (x_20 == 0)
{
uint8 x_21; 
x_21 = lean_expr_quick_lt(x_17, x_2);
if (x_21 == 0)
{
obj* x_22; 
lean::dec(x_18);
lean::dec(x_17);
x_22 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_22, 0, x_16);
lean::cnstr_set(x_22, 1, x_2);
lean::cnstr_set(x_22, 2, x_3);
lean::cnstr_set(x_22, 3, x_19);
lean::cnstr_set_scalar(x_22, sizeof(void*)*4, x_6);
return x_22;
}
else
{
obj* x_23; obj* x_24; 
x_23 = l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__12(x_19, x_2, x_3);
x_24 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_24, 0, x_16);
lean::cnstr_set(x_24, 1, x_17);
lean::cnstr_set(x_24, 2, x_18);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_6);
return x_24;
}
}
else
{
obj* x_25; obj* x_26; 
x_25 = l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__12(x_16, x_2, x_3);
x_26 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
lean::cnstr_set(x_26, 2, x_18);
lean::cnstr_set(x_26, 3, x_19);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
return x_26;
}
}
}
else
{
uint8 x_27; 
x_27 = !lean::is_exclusive(x_1);
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; uint8 x_32; 
x_28 = lean::cnstr_get(x_1, 0);
x_29 = lean::cnstr_get(x_1, 1);
x_30 = lean::cnstr_get(x_1, 2);
x_31 = lean::cnstr_get(x_1, 3);
x_32 = lean_expr_quick_lt(x_2, x_29);
if (x_32 == 0)
{
uint8 x_33; 
x_33 = lean_expr_quick_lt(x_29, x_2);
if (x_33 == 0)
{
lean::dec(x_30);
lean::dec(x_29);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
return x_1;
}
else
{
uint8 x_34; 
x_34 = l_RBNode_isRed___main___rarg(x_31);
if (x_34 == 0)
{
obj* x_35; 
x_35 = l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__12(x_31, x_2, x_3);
lean::cnstr_set(x_1, 3, x_35);
return x_1;
}
else
{
obj* x_36; 
x_36 = l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__12(x_31, x_2, x_3);
if (lean::obj_tag(x_36) == 0)
{
lean::free_heap_obj(x_1);
lean::dec(x_30);
lean::dec(x_29);
lean::dec(x_28);
return x_36;
}
else
{
obj* x_37; 
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; 
x_38 = lean::cnstr_get(x_36, 3);
lean::inc(x_38);
if (lean::obj_tag(x_38) == 0)
{
uint8 x_39; 
x_39 = !lean::is_exclusive(x_36);
if (x_39 == 0)
{
obj* x_40; obj* x_41; uint8 x_42; uint8 x_43; 
x_40 = lean::cnstr_get(x_36, 3);
lean::dec(x_40);
x_41 = lean::cnstr_get(x_36, 0);
lean::dec(x_41);
x_42 = 0;
lean::cnstr_set(x_36, 0, x_38);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_42);
x_43 = 1;
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_43);
return x_1;
}
else
{
obj* x_44; obj* x_45; uint8 x_46; obj* x_47; uint8 x_48; 
x_44 = lean::cnstr_get(x_36, 1);
x_45 = lean::cnstr_get(x_36, 2);
lean::inc(x_45);
lean::inc(x_44);
lean::dec(x_36);
x_46 = 0;
x_47 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_47, 0, x_38);
lean::cnstr_set(x_47, 1, x_44);
lean::cnstr_set(x_47, 2, x_45);
lean::cnstr_set(x_47, 3, x_38);
lean::cnstr_set_scalar(x_47, sizeof(void*)*4, x_46);
x_48 = 1;
lean::cnstr_set(x_1, 3, x_47);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_48);
return x_1;
}
}
else
{
uint8 x_49; 
x_49 = lean::cnstr_get_scalar<uint8>(x_38, sizeof(void*)*4);
if (x_49 == 0)
{
uint8 x_50; 
x_50 = !lean::is_exclusive(x_36);
if (x_50 == 0)
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; uint8 x_55; 
x_51 = lean::cnstr_get(x_36, 1);
x_52 = lean::cnstr_get(x_36, 2);
x_53 = lean::cnstr_get(x_36, 3);
lean::dec(x_53);
x_54 = lean::cnstr_get(x_36, 0);
lean::dec(x_54);
x_55 = !lean::is_exclusive(x_38);
if (x_55 == 0)
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; uint8 x_60; 
x_56 = lean::cnstr_get(x_38, 0);
x_57 = lean::cnstr_get(x_38, 1);
x_58 = lean::cnstr_get(x_38, 2);
x_59 = lean::cnstr_get(x_38, 3);
x_60 = 1;
lean::cnstr_set(x_38, 3, x_37);
lean::cnstr_set(x_38, 2, x_30);
lean::cnstr_set(x_38, 1, x_29);
lean::cnstr_set(x_38, 0, x_28);
lean::cnstr_set_scalar(x_38, sizeof(void*)*4, x_60);
lean::cnstr_set(x_36, 3, x_59);
lean::cnstr_set(x_36, 2, x_58);
lean::cnstr_set(x_36, 1, x_57);
lean::cnstr_set(x_36, 0, x_56);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_60);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_52);
lean::cnstr_set(x_1, 1, x_51);
lean::cnstr_set(x_1, 0, x_38);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; uint8 x_65; obj* x_66; 
x_61 = lean::cnstr_get(x_38, 0);
x_62 = lean::cnstr_get(x_38, 1);
x_63 = lean::cnstr_get(x_38, 2);
x_64 = lean::cnstr_get(x_38, 3);
lean::inc(x_64);
lean::inc(x_63);
lean::inc(x_62);
lean::inc(x_61);
lean::dec(x_38);
x_65 = 1;
x_66 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_66, 0, x_28);
lean::cnstr_set(x_66, 1, x_29);
lean::cnstr_set(x_66, 2, x_30);
lean::cnstr_set(x_66, 3, x_37);
lean::cnstr_set_scalar(x_66, sizeof(void*)*4, x_65);
lean::cnstr_set(x_36, 3, x_64);
lean::cnstr_set(x_36, 2, x_63);
lean::cnstr_set(x_36, 1, x_62);
lean::cnstr_set(x_36, 0, x_61);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_65);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_52);
lean::cnstr_set(x_1, 1, x_51);
lean::cnstr_set(x_1, 0, x_66);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; uint8 x_74; obj* x_75; obj* x_76; 
x_67 = lean::cnstr_get(x_36, 1);
x_68 = lean::cnstr_get(x_36, 2);
lean::inc(x_68);
lean::inc(x_67);
lean::dec(x_36);
x_69 = lean::cnstr_get(x_38, 0);
lean::inc(x_69);
x_70 = lean::cnstr_get(x_38, 1);
lean::inc(x_70);
x_71 = lean::cnstr_get(x_38, 2);
lean::inc(x_71);
x_72 = lean::cnstr_get(x_38, 3);
lean::inc(x_72);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 lean::cnstr_release(x_38, 1);
 lean::cnstr_release(x_38, 2);
 lean::cnstr_release(x_38, 3);
 x_73 = x_38;
} else {
 lean::dec_ref(x_38);
 x_73 = lean::box(0);
}
x_74 = 1;
if (lean::is_scalar(x_73)) {
 x_75 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_75 = x_73;
}
lean::cnstr_set(x_75, 0, x_28);
lean::cnstr_set(x_75, 1, x_29);
lean::cnstr_set(x_75, 2, x_30);
lean::cnstr_set(x_75, 3, x_37);
lean::cnstr_set_scalar(x_75, sizeof(void*)*4, x_74);
x_76 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_76, 0, x_69);
lean::cnstr_set(x_76, 1, x_70);
lean::cnstr_set(x_76, 2, x_71);
lean::cnstr_set(x_76, 3, x_72);
lean::cnstr_set_scalar(x_76, sizeof(void*)*4, x_74);
lean::cnstr_set(x_1, 3, x_76);
lean::cnstr_set(x_1, 2, x_68);
lean::cnstr_set(x_1, 1, x_67);
lean::cnstr_set(x_1, 0, x_75);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
uint8 x_77; 
x_77 = !lean::is_exclusive(x_36);
if (x_77 == 0)
{
obj* x_78; obj* x_79; uint8 x_80; 
x_78 = lean::cnstr_get(x_36, 3);
lean::dec(x_78);
x_79 = lean::cnstr_get(x_36, 0);
lean::dec(x_79);
x_80 = 0;
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_80);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
obj* x_81; obj* x_82; uint8 x_83; obj* x_84; 
x_81 = lean::cnstr_get(x_36, 1);
x_82 = lean::cnstr_get(x_36, 2);
lean::inc(x_82);
lean::inc(x_81);
lean::dec(x_36);
x_83 = 0;
x_84 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_84, 0, x_37);
lean::cnstr_set(x_84, 1, x_81);
lean::cnstr_set(x_84, 2, x_82);
lean::cnstr_set(x_84, 3, x_38);
lean::cnstr_set_scalar(x_84, sizeof(void*)*4, x_83);
lean::cnstr_set(x_1, 3, x_84);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
}
}
else
{
uint8 x_85; 
x_85 = lean::cnstr_get_scalar<uint8>(x_37, sizeof(void*)*4);
if (x_85 == 0)
{
uint8 x_86; 
x_86 = !lean::is_exclusive(x_36);
if (x_86 == 0)
{
obj* x_87; uint8 x_88; 
x_87 = lean::cnstr_get(x_36, 0);
lean::dec(x_87);
x_88 = !lean::is_exclusive(x_37);
if (x_88 == 0)
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; uint8 x_93; 
x_89 = lean::cnstr_get(x_37, 0);
x_90 = lean::cnstr_get(x_37, 1);
x_91 = lean::cnstr_get(x_37, 2);
x_92 = lean::cnstr_get(x_37, 3);
x_93 = 1;
lean::cnstr_set(x_37, 3, x_89);
lean::cnstr_set(x_37, 2, x_30);
lean::cnstr_set(x_37, 1, x_29);
lean::cnstr_set(x_37, 0, x_28);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_93);
lean::cnstr_set(x_36, 0, x_92);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_93);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_91);
lean::cnstr_set(x_1, 1, x_90);
lean::cnstr_set(x_1, 0, x_37);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
obj* x_94; obj* x_95; obj* x_96; obj* x_97; uint8 x_98; obj* x_99; 
x_94 = lean::cnstr_get(x_37, 0);
x_95 = lean::cnstr_get(x_37, 1);
x_96 = lean::cnstr_get(x_37, 2);
x_97 = lean::cnstr_get(x_37, 3);
lean::inc(x_97);
lean::inc(x_96);
lean::inc(x_95);
lean::inc(x_94);
lean::dec(x_37);
x_98 = 1;
x_99 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_99, 0, x_28);
lean::cnstr_set(x_99, 1, x_29);
lean::cnstr_set(x_99, 2, x_30);
lean::cnstr_set(x_99, 3, x_94);
lean::cnstr_set_scalar(x_99, sizeof(void*)*4, x_98);
lean::cnstr_set(x_36, 0, x_97);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_98);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_96);
lean::cnstr_set(x_1, 1, x_95);
lean::cnstr_set(x_1, 0, x_99);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; uint8 x_108; obj* x_109; obj* x_110; 
x_100 = lean::cnstr_get(x_36, 1);
x_101 = lean::cnstr_get(x_36, 2);
x_102 = lean::cnstr_get(x_36, 3);
lean::inc(x_102);
lean::inc(x_101);
lean::inc(x_100);
lean::dec(x_36);
x_103 = lean::cnstr_get(x_37, 0);
lean::inc(x_103);
x_104 = lean::cnstr_get(x_37, 1);
lean::inc(x_104);
x_105 = lean::cnstr_get(x_37, 2);
lean::inc(x_105);
x_106 = lean::cnstr_get(x_37, 3);
lean::inc(x_106);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_107 = x_37;
} else {
 lean::dec_ref(x_37);
 x_107 = lean::box(0);
}
x_108 = 1;
if (lean::is_scalar(x_107)) {
 x_109 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_109 = x_107;
}
lean::cnstr_set(x_109, 0, x_28);
lean::cnstr_set(x_109, 1, x_29);
lean::cnstr_set(x_109, 2, x_30);
lean::cnstr_set(x_109, 3, x_103);
lean::cnstr_set_scalar(x_109, sizeof(void*)*4, x_108);
x_110 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_110, 0, x_106);
lean::cnstr_set(x_110, 1, x_100);
lean::cnstr_set(x_110, 2, x_101);
lean::cnstr_set(x_110, 3, x_102);
lean::cnstr_set_scalar(x_110, sizeof(void*)*4, x_108);
lean::cnstr_set(x_1, 3, x_110);
lean::cnstr_set(x_1, 2, x_105);
lean::cnstr_set(x_1, 1, x_104);
lean::cnstr_set(x_1, 0, x_109);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
obj* x_111; 
x_111 = lean::cnstr_get(x_36, 3);
lean::inc(x_111);
if (lean::obj_tag(x_111) == 0)
{
uint8 x_112; 
x_112 = !lean::is_exclusive(x_36);
if (x_112 == 0)
{
obj* x_113; obj* x_114; uint8 x_115; 
x_113 = lean::cnstr_get(x_36, 3);
lean::dec(x_113);
x_114 = lean::cnstr_get(x_36, 0);
lean::dec(x_114);
x_115 = 0;
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_115);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
obj* x_116; obj* x_117; uint8 x_118; obj* x_119; 
x_116 = lean::cnstr_get(x_36, 1);
x_117 = lean::cnstr_get(x_36, 2);
lean::inc(x_117);
lean::inc(x_116);
lean::dec(x_36);
x_118 = 0;
x_119 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_119, 0, x_37);
lean::cnstr_set(x_119, 1, x_116);
lean::cnstr_set(x_119, 2, x_117);
lean::cnstr_set(x_119, 3, x_111);
lean::cnstr_set_scalar(x_119, sizeof(void*)*4, x_118);
lean::cnstr_set(x_1, 3, x_119);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
uint8 x_120; 
x_120 = lean::cnstr_get_scalar<uint8>(x_111, sizeof(void*)*4);
if (x_120 == 0)
{
uint8 x_121; 
lean::free_heap_obj(x_1);
x_121 = !lean::is_exclusive(x_36);
if (x_121 == 0)
{
obj* x_122; obj* x_123; uint8 x_124; 
x_122 = lean::cnstr_get(x_36, 3);
lean::dec(x_122);
x_123 = lean::cnstr_get(x_36, 0);
lean::dec(x_123);
x_124 = !lean::is_exclusive(x_111);
if (x_124 == 0)
{
obj* x_125; obj* x_126; obj* x_127; obj* x_128; uint8 x_129; 
x_125 = lean::cnstr_get(x_111, 0);
x_126 = lean::cnstr_get(x_111, 1);
x_127 = lean::cnstr_get(x_111, 2);
x_128 = lean::cnstr_get(x_111, 3);
lean::inc(x_37);
lean::cnstr_set(x_111, 3, x_37);
lean::cnstr_set(x_111, 2, x_30);
lean::cnstr_set(x_111, 1, x_29);
lean::cnstr_set(x_111, 0, x_28);
x_129 = !lean::is_exclusive(x_37);
if (x_129 == 0)
{
obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
x_130 = lean::cnstr_get(x_37, 3);
lean::dec(x_130);
x_131 = lean::cnstr_get(x_37, 2);
lean::dec(x_131);
x_132 = lean::cnstr_get(x_37, 1);
lean::dec(x_132);
x_133 = lean::cnstr_get(x_37, 0);
lean::dec(x_133);
lean::cnstr_set_scalar(x_111, sizeof(void*)*4, x_85);
lean::cnstr_set(x_37, 3, x_128);
lean::cnstr_set(x_37, 2, x_127);
lean::cnstr_set(x_37, 1, x_126);
lean::cnstr_set(x_37, 0, x_125);
lean::cnstr_set(x_36, 3, x_37);
lean::cnstr_set(x_36, 0, x_111);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_120);
return x_36;
}
else
{
obj* x_134; 
lean::dec(x_37);
lean::cnstr_set_scalar(x_111, sizeof(void*)*4, x_85);
x_134 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_134, 0, x_125);
lean::cnstr_set(x_134, 1, x_126);
lean::cnstr_set(x_134, 2, x_127);
lean::cnstr_set(x_134, 3, x_128);
lean::cnstr_set_scalar(x_134, sizeof(void*)*4, x_85);
lean::cnstr_set(x_36, 3, x_134);
lean::cnstr_set(x_36, 0, x_111);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; 
x_135 = lean::cnstr_get(x_111, 0);
x_136 = lean::cnstr_get(x_111, 1);
x_137 = lean::cnstr_get(x_111, 2);
x_138 = lean::cnstr_get(x_111, 3);
lean::inc(x_138);
lean::inc(x_137);
lean::inc(x_136);
lean::inc(x_135);
lean::dec(x_111);
lean::inc(x_37);
x_139 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_139, 0, x_28);
lean::cnstr_set(x_139, 1, x_29);
lean::cnstr_set(x_139, 2, x_30);
lean::cnstr_set(x_139, 3, x_37);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_140 = x_37;
} else {
 lean::dec_ref(x_37);
 x_140 = lean::box(0);
}
lean::cnstr_set_scalar(x_139, sizeof(void*)*4, x_85);
if (lean::is_scalar(x_140)) {
 x_141 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_141 = x_140;
}
lean::cnstr_set(x_141, 0, x_135);
lean::cnstr_set(x_141, 1, x_136);
lean::cnstr_set(x_141, 2, x_137);
lean::cnstr_set(x_141, 3, x_138);
lean::cnstr_set_scalar(x_141, sizeof(void*)*4, x_85);
lean::cnstr_set(x_36, 3, x_141);
lean::cnstr_set(x_36, 0, x_139);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
x_142 = lean::cnstr_get(x_36, 1);
x_143 = lean::cnstr_get(x_36, 2);
lean::inc(x_143);
lean::inc(x_142);
lean::dec(x_36);
x_144 = lean::cnstr_get(x_111, 0);
lean::inc(x_144);
x_145 = lean::cnstr_get(x_111, 1);
lean::inc(x_145);
x_146 = lean::cnstr_get(x_111, 2);
lean::inc(x_146);
x_147 = lean::cnstr_get(x_111, 3);
lean::inc(x_147);
if (lean::is_exclusive(x_111)) {
 lean::cnstr_release(x_111, 0);
 lean::cnstr_release(x_111, 1);
 lean::cnstr_release(x_111, 2);
 lean::cnstr_release(x_111, 3);
 x_148 = x_111;
} else {
 lean::dec_ref(x_111);
 x_148 = lean::box(0);
}
lean::inc(x_37);
if (lean::is_scalar(x_148)) {
 x_149 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_149 = x_148;
}
lean::cnstr_set(x_149, 0, x_28);
lean::cnstr_set(x_149, 1, x_29);
lean::cnstr_set(x_149, 2, x_30);
lean::cnstr_set(x_149, 3, x_37);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_150 = x_37;
} else {
 lean::dec_ref(x_37);
 x_150 = lean::box(0);
}
lean::cnstr_set_scalar(x_149, sizeof(void*)*4, x_85);
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_144);
lean::cnstr_set(x_151, 1, x_145);
lean::cnstr_set(x_151, 2, x_146);
lean::cnstr_set(x_151, 3, x_147);
lean::cnstr_set_scalar(x_151, sizeof(void*)*4, x_85);
x_152 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_152, 0, x_149);
lean::cnstr_set(x_152, 1, x_142);
lean::cnstr_set(x_152, 2, x_143);
lean::cnstr_set(x_152, 3, x_151);
lean::cnstr_set_scalar(x_152, sizeof(void*)*4, x_120);
return x_152;
}
}
else
{
uint8 x_153; 
x_153 = !lean::is_exclusive(x_36);
if (x_153 == 0)
{
obj* x_154; obj* x_155; uint8 x_156; 
x_154 = lean::cnstr_get(x_36, 3);
lean::dec(x_154);
x_155 = lean::cnstr_get(x_36, 0);
lean::dec(x_155);
x_156 = !lean::is_exclusive(x_37);
if (x_156 == 0)
{
uint8 x_157; 
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_120);
x_157 = 0;
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_157);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_120);
return x_1;
}
else
{
obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; uint8 x_163; 
x_158 = lean::cnstr_get(x_37, 0);
x_159 = lean::cnstr_get(x_37, 1);
x_160 = lean::cnstr_get(x_37, 2);
x_161 = lean::cnstr_get(x_37, 3);
lean::inc(x_161);
lean::inc(x_160);
lean::inc(x_159);
lean::inc(x_158);
lean::dec(x_37);
x_162 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_162, 0, x_158);
lean::cnstr_set(x_162, 1, x_159);
lean::cnstr_set(x_162, 2, x_160);
lean::cnstr_set(x_162, 3, x_161);
lean::cnstr_set_scalar(x_162, sizeof(void*)*4, x_120);
x_163 = 0;
lean::cnstr_set(x_36, 0, x_162);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_163);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_120);
return x_1;
}
}
else
{
obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; uint8 x_172; obj* x_173; 
x_164 = lean::cnstr_get(x_36, 1);
x_165 = lean::cnstr_get(x_36, 2);
lean::inc(x_165);
lean::inc(x_164);
lean::dec(x_36);
x_166 = lean::cnstr_get(x_37, 0);
lean::inc(x_166);
x_167 = lean::cnstr_get(x_37, 1);
lean::inc(x_167);
x_168 = lean::cnstr_get(x_37, 2);
lean::inc(x_168);
x_169 = lean::cnstr_get(x_37, 3);
lean::inc(x_169);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_170 = x_37;
} else {
 lean::dec_ref(x_37);
 x_170 = lean::box(0);
}
if (lean::is_scalar(x_170)) {
 x_171 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_171 = x_170;
}
lean::cnstr_set(x_171, 0, x_166);
lean::cnstr_set(x_171, 1, x_167);
lean::cnstr_set(x_171, 2, x_168);
lean::cnstr_set(x_171, 3, x_169);
lean::cnstr_set_scalar(x_171, sizeof(void*)*4, x_120);
x_172 = 0;
x_173 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_173, 0, x_171);
lean::cnstr_set(x_173, 1, x_164);
lean::cnstr_set(x_173, 2, x_165);
lean::cnstr_set(x_173, 3, x_111);
lean::cnstr_set_scalar(x_173, sizeof(void*)*4, x_172);
lean::cnstr_set(x_1, 3, x_173);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_120);
return x_1;
}
}
}
}
}
}
}
}
}
else
{
uint8 x_174; 
x_174 = l_RBNode_isRed___main___rarg(x_28);
if (x_174 == 0)
{
obj* x_175; 
x_175 = l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__12(x_28, x_2, x_3);
lean::cnstr_set(x_1, 0, x_175);
return x_1;
}
else
{
obj* x_176; 
x_176 = l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__12(x_28, x_2, x_3);
if (lean::obj_tag(x_176) == 0)
{
lean::free_heap_obj(x_1);
lean::dec(x_31);
lean::dec(x_30);
lean::dec(x_29);
return x_176;
}
else
{
obj* x_177; 
x_177 = lean::cnstr_get(x_176, 0);
lean::inc(x_177);
if (lean::obj_tag(x_177) == 0)
{
obj* x_178; 
x_178 = lean::cnstr_get(x_176, 3);
lean::inc(x_178);
if (lean::obj_tag(x_178) == 0)
{
uint8 x_179; 
x_179 = !lean::is_exclusive(x_176);
if (x_179 == 0)
{
obj* x_180; obj* x_181; uint8 x_182; uint8 x_183; 
x_180 = lean::cnstr_get(x_176, 3);
lean::dec(x_180);
x_181 = lean::cnstr_get(x_176, 0);
lean::dec(x_181);
x_182 = 0;
lean::cnstr_set(x_176, 0, x_178);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_182);
x_183 = 1;
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_183);
return x_1;
}
else
{
obj* x_184; obj* x_185; uint8 x_186; obj* x_187; uint8 x_188; 
x_184 = lean::cnstr_get(x_176, 1);
x_185 = lean::cnstr_get(x_176, 2);
lean::inc(x_185);
lean::inc(x_184);
lean::dec(x_176);
x_186 = 0;
x_187 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_187, 0, x_178);
lean::cnstr_set(x_187, 1, x_184);
lean::cnstr_set(x_187, 2, x_185);
lean::cnstr_set(x_187, 3, x_178);
lean::cnstr_set_scalar(x_187, sizeof(void*)*4, x_186);
x_188 = 1;
lean::cnstr_set(x_1, 0, x_187);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
else
{
uint8 x_189; 
x_189 = lean::cnstr_get_scalar<uint8>(x_178, sizeof(void*)*4);
if (x_189 == 0)
{
uint8 x_190; 
x_190 = !lean::is_exclusive(x_176);
if (x_190 == 0)
{
obj* x_191; obj* x_192; obj* x_193; obj* x_194; uint8 x_195; 
x_191 = lean::cnstr_get(x_176, 1);
x_192 = lean::cnstr_get(x_176, 2);
x_193 = lean::cnstr_get(x_176, 3);
lean::dec(x_193);
x_194 = lean::cnstr_get(x_176, 0);
lean::dec(x_194);
x_195 = !lean::is_exclusive(x_178);
if (x_195 == 0)
{
obj* x_196; obj* x_197; obj* x_198; obj* x_199; uint8 x_200; 
x_196 = lean::cnstr_get(x_178, 0);
x_197 = lean::cnstr_get(x_178, 1);
x_198 = lean::cnstr_get(x_178, 2);
x_199 = lean::cnstr_get(x_178, 3);
x_200 = 1;
lean::cnstr_set(x_178, 3, x_196);
lean::cnstr_set(x_178, 2, x_192);
lean::cnstr_set(x_178, 1, x_191);
lean::cnstr_set(x_178, 0, x_177);
lean::cnstr_set_scalar(x_178, sizeof(void*)*4, x_200);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_199);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_200);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_198);
lean::cnstr_set(x_1, 1, x_197);
lean::cnstr_set(x_1, 0, x_178);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
obj* x_201; obj* x_202; obj* x_203; obj* x_204; uint8 x_205; obj* x_206; 
x_201 = lean::cnstr_get(x_178, 0);
x_202 = lean::cnstr_get(x_178, 1);
x_203 = lean::cnstr_get(x_178, 2);
x_204 = lean::cnstr_get(x_178, 3);
lean::inc(x_204);
lean::inc(x_203);
lean::inc(x_202);
lean::inc(x_201);
lean::dec(x_178);
x_205 = 1;
x_206 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_206, 0, x_177);
lean::cnstr_set(x_206, 1, x_191);
lean::cnstr_set(x_206, 2, x_192);
lean::cnstr_set(x_206, 3, x_201);
lean::cnstr_set_scalar(x_206, sizeof(void*)*4, x_205);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_204);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_205);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_203);
lean::cnstr_set(x_1, 1, x_202);
lean::cnstr_set(x_1, 0, x_206);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; uint8 x_214; obj* x_215; obj* x_216; 
x_207 = lean::cnstr_get(x_176, 1);
x_208 = lean::cnstr_get(x_176, 2);
lean::inc(x_208);
lean::inc(x_207);
lean::dec(x_176);
x_209 = lean::cnstr_get(x_178, 0);
lean::inc(x_209);
x_210 = lean::cnstr_get(x_178, 1);
lean::inc(x_210);
x_211 = lean::cnstr_get(x_178, 2);
lean::inc(x_211);
x_212 = lean::cnstr_get(x_178, 3);
lean::inc(x_212);
if (lean::is_exclusive(x_178)) {
 lean::cnstr_release(x_178, 0);
 lean::cnstr_release(x_178, 1);
 lean::cnstr_release(x_178, 2);
 lean::cnstr_release(x_178, 3);
 x_213 = x_178;
} else {
 lean::dec_ref(x_178);
 x_213 = lean::box(0);
}
x_214 = 1;
if (lean::is_scalar(x_213)) {
 x_215 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_215 = x_213;
}
lean::cnstr_set(x_215, 0, x_177);
lean::cnstr_set(x_215, 1, x_207);
lean::cnstr_set(x_215, 2, x_208);
lean::cnstr_set(x_215, 3, x_209);
lean::cnstr_set_scalar(x_215, sizeof(void*)*4, x_214);
x_216 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_216, 0, x_212);
lean::cnstr_set(x_216, 1, x_29);
lean::cnstr_set(x_216, 2, x_30);
lean::cnstr_set(x_216, 3, x_31);
lean::cnstr_set_scalar(x_216, sizeof(void*)*4, x_214);
lean::cnstr_set(x_1, 3, x_216);
lean::cnstr_set(x_1, 2, x_211);
lean::cnstr_set(x_1, 1, x_210);
lean::cnstr_set(x_1, 0, x_215);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
uint8 x_217; 
x_217 = !lean::is_exclusive(x_176);
if (x_217 == 0)
{
obj* x_218; obj* x_219; uint8 x_220; 
x_218 = lean::cnstr_get(x_176, 3);
lean::dec(x_218);
x_219 = lean::cnstr_get(x_176, 0);
lean::dec(x_219);
x_220 = 0;
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_220);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
obj* x_221; obj* x_222; uint8 x_223; obj* x_224; 
x_221 = lean::cnstr_get(x_176, 1);
x_222 = lean::cnstr_get(x_176, 2);
lean::inc(x_222);
lean::inc(x_221);
lean::dec(x_176);
x_223 = 0;
x_224 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_224, 0, x_177);
lean::cnstr_set(x_224, 1, x_221);
lean::cnstr_set(x_224, 2, x_222);
lean::cnstr_set(x_224, 3, x_178);
lean::cnstr_set_scalar(x_224, sizeof(void*)*4, x_223);
lean::cnstr_set(x_1, 0, x_224);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
}
}
else
{
uint8 x_225; 
x_225 = lean::cnstr_get_scalar<uint8>(x_177, sizeof(void*)*4);
if (x_225 == 0)
{
uint8 x_226; 
x_226 = !lean::is_exclusive(x_176);
if (x_226 == 0)
{
obj* x_227; obj* x_228; obj* x_229; obj* x_230; uint8 x_231; 
x_227 = lean::cnstr_get(x_176, 1);
x_228 = lean::cnstr_get(x_176, 2);
x_229 = lean::cnstr_get(x_176, 3);
x_230 = lean::cnstr_get(x_176, 0);
lean::dec(x_230);
x_231 = !lean::is_exclusive(x_177);
if (x_231 == 0)
{
uint8 x_232; 
x_232 = 1;
lean::cnstr_set_scalar(x_177, sizeof(void*)*4, x_232);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_229);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_232);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_228);
lean::cnstr_set(x_1, 1, x_227);
lean::cnstr_set(x_1, 0, x_177);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
obj* x_233; obj* x_234; obj* x_235; obj* x_236; uint8 x_237; obj* x_238; 
x_233 = lean::cnstr_get(x_177, 0);
x_234 = lean::cnstr_get(x_177, 1);
x_235 = lean::cnstr_get(x_177, 2);
x_236 = lean::cnstr_get(x_177, 3);
lean::inc(x_236);
lean::inc(x_235);
lean::inc(x_234);
lean::inc(x_233);
lean::dec(x_177);
x_237 = 1;
x_238 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_238, 0, x_233);
lean::cnstr_set(x_238, 1, x_234);
lean::cnstr_set(x_238, 2, x_235);
lean::cnstr_set(x_238, 3, x_236);
lean::cnstr_set_scalar(x_238, sizeof(void*)*4, x_237);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_229);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_237);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_228);
lean::cnstr_set(x_1, 1, x_227);
lean::cnstr_set(x_1, 0, x_238);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
obj* x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; obj* x_244; obj* x_245; obj* x_246; uint8 x_247; obj* x_248; obj* x_249; 
x_239 = lean::cnstr_get(x_176, 1);
x_240 = lean::cnstr_get(x_176, 2);
x_241 = lean::cnstr_get(x_176, 3);
lean::inc(x_241);
lean::inc(x_240);
lean::inc(x_239);
lean::dec(x_176);
x_242 = lean::cnstr_get(x_177, 0);
lean::inc(x_242);
x_243 = lean::cnstr_get(x_177, 1);
lean::inc(x_243);
x_244 = lean::cnstr_get(x_177, 2);
lean::inc(x_244);
x_245 = lean::cnstr_get(x_177, 3);
lean::inc(x_245);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_246 = x_177;
} else {
 lean::dec_ref(x_177);
 x_246 = lean::box(0);
}
x_247 = 1;
if (lean::is_scalar(x_246)) {
 x_248 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_248 = x_246;
}
lean::cnstr_set(x_248, 0, x_242);
lean::cnstr_set(x_248, 1, x_243);
lean::cnstr_set(x_248, 2, x_244);
lean::cnstr_set(x_248, 3, x_245);
lean::cnstr_set_scalar(x_248, sizeof(void*)*4, x_247);
x_249 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_249, 0, x_241);
lean::cnstr_set(x_249, 1, x_29);
lean::cnstr_set(x_249, 2, x_30);
lean::cnstr_set(x_249, 3, x_31);
lean::cnstr_set_scalar(x_249, sizeof(void*)*4, x_247);
lean::cnstr_set(x_1, 3, x_249);
lean::cnstr_set(x_1, 2, x_240);
lean::cnstr_set(x_1, 1, x_239);
lean::cnstr_set(x_1, 0, x_248);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
obj* x_250; 
x_250 = lean::cnstr_get(x_176, 3);
lean::inc(x_250);
if (lean::obj_tag(x_250) == 0)
{
uint8 x_251; 
x_251 = !lean::is_exclusive(x_176);
if (x_251 == 0)
{
obj* x_252; obj* x_253; uint8 x_254; 
x_252 = lean::cnstr_get(x_176, 3);
lean::dec(x_252);
x_253 = lean::cnstr_get(x_176, 0);
lean::dec(x_253);
x_254 = 0;
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_254);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
obj* x_255; obj* x_256; uint8 x_257; obj* x_258; 
x_255 = lean::cnstr_get(x_176, 1);
x_256 = lean::cnstr_get(x_176, 2);
lean::inc(x_256);
lean::inc(x_255);
lean::dec(x_176);
x_257 = 0;
x_258 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_258, 0, x_177);
lean::cnstr_set(x_258, 1, x_255);
lean::cnstr_set(x_258, 2, x_256);
lean::cnstr_set(x_258, 3, x_250);
lean::cnstr_set_scalar(x_258, sizeof(void*)*4, x_257);
lean::cnstr_set(x_1, 0, x_258);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
uint8 x_259; 
x_259 = lean::cnstr_get_scalar<uint8>(x_250, sizeof(void*)*4);
if (x_259 == 0)
{
uint8 x_260; 
lean::free_heap_obj(x_1);
x_260 = !lean::is_exclusive(x_176);
if (x_260 == 0)
{
obj* x_261; obj* x_262; obj* x_263; obj* x_264; uint8 x_265; 
x_261 = lean::cnstr_get(x_176, 1);
x_262 = lean::cnstr_get(x_176, 2);
x_263 = lean::cnstr_get(x_176, 3);
lean::dec(x_263);
x_264 = lean::cnstr_get(x_176, 0);
lean::dec(x_264);
x_265 = !lean::is_exclusive(x_250);
if (x_265 == 0)
{
obj* x_266; obj* x_267; obj* x_268; obj* x_269; uint8 x_270; 
x_266 = lean::cnstr_get(x_250, 0);
x_267 = lean::cnstr_get(x_250, 1);
x_268 = lean::cnstr_get(x_250, 2);
x_269 = lean::cnstr_get(x_250, 3);
lean::inc(x_177);
lean::cnstr_set(x_250, 3, x_266);
lean::cnstr_set(x_250, 2, x_262);
lean::cnstr_set(x_250, 1, x_261);
lean::cnstr_set(x_250, 0, x_177);
x_270 = !lean::is_exclusive(x_177);
if (x_270 == 0)
{
obj* x_271; obj* x_272; obj* x_273; obj* x_274; 
x_271 = lean::cnstr_get(x_177, 3);
lean::dec(x_271);
x_272 = lean::cnstr_get(x_177, 2);
lean::dec(x_272);
x_273 = lean::cnstr_get(x_177, 1);
lean::dec(x_273);
x_274 = lean::cnstr_get(x_177, 0);
lean::dec(x_274);
lean::cnstr_set_scalar(x_250, sizeof(void*)*4, x_225);
lean::cnstr_set(x_177, 3, x_31);
lean::cnstr_set(x_177, 2, x_30);
lean::cnstr_set(x_177, 1, x_29);
lean::cnstr_set(x_177, 0, x_269);
lean::cnstr_set(x_176, 3, x_177);
lean::cnstr_set(x_176, 2, x_268);
lean::cnstr_set(x_176, 1, x_267);
lean::cnstr_set(x_176, 0, x_250);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_259);
return x_176;
}
else
{
obj* x_275; 
lean::dec(x_177);
lean::cnstr_set_scalar(x_250, sizeof(void*)*4, x_225);
x_275 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_275, 0, x_269);
lean::cnstr_set(x_275, 1, x_29);
lean::cnstr_set(x_275, 2, x_30);
lean::cnstr_set(x_275, 3, x_31);
lean::cnstr_set_scalar(x_275, sizeof(void*)*4, x_225);
lean::cnstr_set(x_176, 3, x_275);
lean::cnstr_set(x_176, 2, x_268);
lean::cnstr_set(x_176, 1, x_267);
lean::cnstr_set(x_176, 0, x_250);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
obj* x_276; obj* x_277; obj* x_278; obj* x_279; obj* x_280; obj* x_281; obj* x_282; 
x_276 = lean::cnstr_get(x_250, 0);
x_277 = lean::cnstr_get(x_250, 1);
x_278 = lean::cnstr_get(x_250, 2);
x_279 = lean::cnstr_get(x_250, 3);
lean::inc(x_279);
lean::inc(x_278);
lean::inc(x_277);
lean::inc(x_276);
lean::dec(x_250);
lean::inc(x_177);
x_280 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_280, 0, x_177);
lean::cnstr_set(x_280, 1, x_261);
lean::cnstr_set(x_280, 2, x_262);
lean::cnstr_set(x_280, 3, x_276);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_281 = x_177;
} else {
 lean::dec_ref(x_177);
 x_281 = lean::box(0);
}
lean::cnstr_set_scalar(x_280, sizeof(void*)*4, x_225);
if (lean::is_scalar(x_281)) {
 x_282 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_282 = x_281;
}
lean::cnstr_set(x_282, 0, x_279);
lean::cnstr_set(x_282, 1, x_29);
lean::cnstr_set(x_282, 2, x_30);
lean::cnstr_set(x_282, 3, x_31);
lean::cnstr_set_scalar(x_282, sizeof(void*)*4, x_225);
lean::cnstr_set(x_176, 3, x_282);
lean::cnstr_set(x_176, 2, x_278);
lean::cnstr_set(x_176, 1, x_277);
lean::cnstr_set(x_176, 0, x_280);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
obj* x_283; obj* x_284; obj* x_285; obj* x_286; obj* x_287; obj* x_288; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; 
x_283 = lean::cnstr_get(x_176, 1);
x_284 = lean::cnstr_get(x_176, 2);
lean::inc(x_284);
lean::inc(x_283);
lean::dec(x_176);
x_285 = lean::cnstr_get(x_250, 0);
lean::inc(x_285);
x_286 = lean::cnstr_get(x_250, 1);
lean::inc(x_286);
x_287 = lean::cnstr_get(x_250, 2);
lean::inc(x_287);
x_288 = lean::cnstr_get(x_250, 3);
lean::inc(x_288);
if (lean::is_exclusive(x_250)) {
 lean::cnstr_release(x_250, 0);
 lean::cnstr_release(x_250, 1);
 lean::cnstr_release(x_250, 2);
 lean::cnstr_release(x_250, 3);
 x_289 = x_250;
} else {
 lean::dec_ref(x_250);
 x_289 = lean::box(0);
}
lean::inc(x_177);
if (lean::is_scalar(x_289)) {
 x_290 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_290 = x_289;
}
lean::cnstr_set(x_290, 0, x_177);
lean::cnstr_set(x_290, 1, x_283);
lean::cnstr_set(x_290, 2, x_284);
lean::cnstr_set(x_290, 3, x_285);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_291 = x_177;
} else {
 lean::dec_ref(x_177);
 x_291 = lean::box(0);
}
lean::cnstr_set_scalar(x_290, sizeof(void*)*4, x_225);
if (lean::is_scalar(x_291)) {
 x_292 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_292 = x_291;
}
lean::cnstr_set(x_292, 0, x_288);
lean::cnstr_set(x_292, 1, x_29);
lean::cnstr_set(x_292, 2, x_30);
lean::cnstr_set(x_292, 3, x_31);
lean::cnstr_set_scalar(x_292, sizeof(void*)*4, x_225);
x_293 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_293, 0, x_290);
lean::cnstr_set(x_293, 1, x_286);
lean::cnstr_set(x_293, 2, x_287);
lean::cnstr_set(x_293, 3, x_292);
lean::cnstr_set_scalar(x_293, sizeof(void*)*4, x_259);
return x_293;
}
}
else
{
uint8 x_294; 
x_294 = !lean::is_exclusive(x_176);
if (x_294 == 0)
{
obj* x_295; obj* x_296; uint8 x_297; 
x_295 = lean::cnstr_get(x_176, 3);
lean::dec(x_295);
x_296 = lean::cnstr_get(x_176, 0);
lean::dec(x_296);
x_297 = !lean::is_exclusive(x_177);
if (x_297 == 0)
{
uint8 x_298; 
lean::cnstr_set_scalar(x_177, sizeof(void*)*4, x_259);
x_298 = 0;
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_298);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_259);
return x_1;
}
else
{
obj* x_299; obj* x_300; obj* x_301; obj* x_302; obj* x_303; uint8 x_304; 
x_299 = lean::cnstr_get(x_177, 0);
x_300 = lean::cnstr_get(x_177, 1);
x_301 = lean::cnstr_get(x_177, 2);
x_302 = lean::cnstr_get(x_177, 3);
lean::inc(x_302);
lean::inc(x_301);
lean::inc(x_300);
lean::inc(x_299);
lean::dec(x_177);
x_303 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_303, 0, x_299);
lean::cnstr_set(x_303, 1, x_300);
lean::cnstr_set(x_303, 2, x_301);
lean::cnstr_set(x_303, 3, x_302);
lean::cnstr_set_scalar(x_303, sizeof(void*)*4, x_259);
x_304 = 0;
lean::cnstr_set(x_176, 0, x_303);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_304);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
else
{
obj* x_305; obj* x_306; obj* x_307; obj* x_308; obj* x_309; obj* x_310; obj* x_311; obj* x_312; uint8 x_313; obj* x_314; 
x_305 = lean::cnstr_get(x_176, 1);
x_306 = lean::cnstr_get(x_176, 2);
lean::inc(x_306);
lean::inc(x_305);
lean::dec(x_176);
x_307 = lean::cnstr_get(x_177, 0);
lean::inc(x_307);
x_308 = lean::cnstr_get(x_177, 1);
lean::inc(x_308);
x_309 = lean::cnstr_get(x_177, 2);
lean::inc(x_309);
x_310 = lean::cnstr_get(x_177, 3);
lean::inc(x_310);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_311 = x_177;
} else {
 lean::dec_ref(x_177);
 x_311 = lean::box(0);
}
if (lean::is_scalar(x_311)) {
 x_312 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_312 = x_311;
}
lean::cnstr_set(x_312, 0, x_307);
lean::cnstr_set(x_312, 1, x_308);
lean::cnstr_set(x_312, 2, x_309);
lean::cnstr_set(x_312, 3, x_310);
lean::cnstr_set_scalar(x_312, sizeof(void*)*4, x_259);
x_313 = 0;
x_314 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_314, 0, x_312);
lean::cnstr_set(x_314, 1, x_305);
lean::cnstr_set(x_314, 2, x_306);
lean::cnstr_set(x_314, 3, x_250);
lean::cnstr_set_scalar(x_314, sizeof(void*)*4, x_313);
lean::cnstr_set(x_1, 0, x_314);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
}
}
}
}
}
}
}
else
{
obj* x_315; obj* x_316; obj* x_317; obj* x_318; uint8 x_319; 
x_315 = lean::cnstr_get(x_1, 0);
x_316 = lean::cnstr_get(x_1, 1);
x_317 = lean::cnstr_get(x_1, 2);
x_318 = lean::cnstr_get(x_1, 3);
lean::inc(x_318);
lean::inc(x_317);
lean::inc(x_316);
lean::inc(x_315);
lean::dec(x_1);
x_319 = lean_expr_quick_lt(x_2, x_316);
if (x_319 == 0)
{
uint8 x_320; 
x_320 = lean_expr_quick_lt(x_316, x_2);
if (x_320 == 0)
{
obj* x_321; 
lean::dec(x_317);
lean::dec(x_316);
x_321 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_321, 0, x_315);
lean::cnstr_set(x_321, 1, x_2);
lean::cnstr_set(x_321, 2, x_3);
lean::cnstr_set(x_321, 3, x_318);
lean::cnstr_set_scalar(x_321, sizeof(void*)*4, x_6);
return x_321;
}
else
{
uint8 x_322; 
x_322 = l_RBNode_isRed___main___rarg(x_318);
if (x_322 == 0)
{
obj* x_323; obj* x_324; 
x_323 = l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__12(x_318, x_2, x_3);
x_324 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_324, 0, x_315);
lean::cnstr_set(x_324, 1, x_316);
lean::cnstr_set(x_324, 2, x_317);
lean::cnstr_set(x_324, 3, x_323);
lean::cnstr_set_scalar(x_324, sizeof(void*)*4, x_6);
return x_324;
}
else
{
obj* x_325; 
x_325 = l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__12(x_318, x_2, x_3);
if (lean::obj_tag(x_325) == 0)
{
lean::dec(x_317);
lean::dec(x_316);
lean::dec(x_315);
return x_325;
}
else
{
obj* x_326; 
x_326 = lean::cnstr_get(x_325, 0);
lean::inc(x_326);
if (lean::obj_tag(x_326) == 0)
{
obj* x_327; 
x_327 = lean::cnstr_get(x_325, 3);
lean::inc(x_327);
if (lean::obj_tag(x_327) == 0)
{
obj* x_328; obj* x_329; obj* x_330; uint8 x_331; obj* x_332; uint8 x_333; obj* x_334; 
x_328 = lean::cnstr_get(x_325, 1);
lean::inc(x_328);
x_329 = lean::cnstr_get(x_325, 2);
lean::inc(x_329);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_330 = x_325;
} else {
 lean::dec_ref(x_325);
 x_330 = lean::box(0);
}
x_331 = 0;
if (lean::is_scalar(x_330)) {
 x_332 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_332 = x_330;
}
lean::cnstr_set(x_332, 0, x_327);
lean::cnstr_set(x_332, 1, x_328);
lean::cnstr_set(x_332, 2, x_329);
lean::cnstr_set(x_332, 3, x_327);
lean::cnstr_set_scalar(x_332, sizeof(void*)*4, x_331);
x_333 = 1;
x_334 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_334, 0, x_315);
lean::cnstr_set(x_334, 1, x_316);
lean::cnstr_set(x_334, 2, x_317);
lean::cnstr_set(x_334, 3, x_332);
lean::cnstr_set_scalar(x_334, sizeof(void*)*4, x_333);
return x_334;
}
else
{
uint8 x_335; 
x_335 = lean::cnstr_get_scalar<uint8>(x_327, sizeof(void*)*4);
if (x_335 == 0)
{
obj* x_336; obj* x_337; obj* x_338; obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_343; uint8 x_344; obj* x_345; obj* x_346; obj* x_347; 
x_336 = lean::cnstr_get(x_325, 1);
lean::inc(x_336);
x_337 = lean::cnstr_get(x_325, 2);
lean::inc(x_337);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_338 = x_325;
} else {
 lean::dec_ref(x_325);
 x_338 = lean::box(0);
}
x_339 = lean::cnstr_get(x_327, 0);
lean::inc(x_339);
x_340 = lean::cnstr_get(x_327, 1);
lean::inc(x_340);
x_341 = lean::cnstr_get(x_327, 2);
lean::inc(x_341);
x_342 = lean::cnstr_get(x_327, 3);
lean::inc(x_342);
if (lean::is_exclusive(x_327)) {
 lean::cnstr_release(x_327, 0);
 lean::cnstr_release(x_327, 1);
 lean::cnstr_release(x_327, 2);
 lean::cnstr_release(x_327, 3);
 x_343 = x_327;
} else {
 lean::dec_ref(x_327);
 x_343 = lean::box(0);
}
x_344 = 1;
if (lean::is_scalar(x_343)) {
 x_345 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_345 = x_343;
}
lean::cnstr_set(x_345, 0, x_315);
lean::cnstr_set(x_345, 1, x_316);
lean::cnstr_set(x_345, 2, x_317);
lean::cnstr_set(x_345, 3, x_326);
lean::cnstr_set_scalar(x_345, sizeof(void*)*4, x_344);
if (lean::is_scalar(x_338)) {
 x_346 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_346 = x_338;
}
lean::cnstr_set(x_346, 0, x_339);
lean::cnstr_set(x_346, 1, x_340);
lean::cnstr_set(x_346, 2, x_341);
lean::cnstr_set(x_346, 3, x_342);
lean::cnstr_set_scalar(x_346, sizeof(void*)*4, x_344);
x_347 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_347, 0, x_345);
lean::cnstr_set(x_347, 1, x_336);
lean::cnstr_set(x_347, 2, x_337);
lean::cnstr_set(x_347, 3, x_346);
lean::cnstr_set_scalar(x_347, sizeof(void*)*4, x_335);
return x_347;
}
else
{
obj* x_348; obj* x_349; obj* x_350; uint8 x_351; obj* x_352; obj* x_353; 
x_348 = lean::cnstr_get(x_325, 1);
lean::inc(x_348);
x_349 = lean::cnstr_get(x_325, 2);
lean::inc(x_349);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_350 = x_325;
} else {
 lean::dec_ref(x_325);
 x_350 = lean::box(0);
}
x_351 = 0;
if (lean::is_scalar(x_350)) {
 x_352 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_352 = x_350;
}
lean::cnstr_set(x_352, 0, x_326);
lean::cnstr_set(x_352, 1, x_348);
lean::cnstr_set(x_352, 2, x_349);
lean::cnstr_set(x_352, 3, x_327);
lean::cnstr_set_scalar(x_352, sizeof(void*)*4, x_351);
x_353 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_353, 0, x_315);
lean::cnstr_set(x_353, 1, x_316);
lean::cnstr_set(x_353, 2, x_317);
lean::cnstr_set(x_353, 3, x_352);
lean::cnstr_set_scalar(x_353, sizeof(void*)*4, x_335);
return x_353;
}
}
}
else
{
uint8 x_354; 
x_354 = lean::cnstr_get_scalar<uint8>(x_326, sizeof(void*)*4);
if (x_354 == 0)
{
obj* x_355; obj* x_356; obj* x_357; obj* x_358; obj* x_359; obj* x_360; obj* x_361; obj* x_362; obj* x_363; uint8 x_364; obj* x_365; obj* x_366; obj* x_367; 
x_355 = lean::cnstr_get(x_325, 1);
lean::inc(x_355);
x_356 = lean::cnstr_get(x_325, 2);
lean::inc(x_356);
x_357 = lean::cnstr_get(x_325, 3);
lean::inc(x_357);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_358 = x_325;
} else {
 lean::dec_ref(x_325);
 x_358 = lean::box(0);
}
x_359 = lean::cnstr_get(x_326, 0);
lean::inc(x_359);
x_360 = lean::cnstr_get(x_326, 1);
lean::inc(x_360);
x_361 = lean::cnstr_get(x_326, 2);
lean::inc(x_361);
x_362 = lean::cnstr_get(x_326, 3);
lean::inc(x_362);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 lean::cnstr_release(x_326, 2);
 lean::cnstr_release(x_326, 3);
 x_363 = x_326;
} else {
 lean::dec_ref(x_326);
 x_363 = lean::box(0);
}
x_364 = 1;
if (lean::is_scalar(x_363)) {
 x_365 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_365 = x_363;
}
lean::cnstr_set(x_365, 0, x_315);
lean::cnstr_set(x_365, 1, x_316);
lean::cnstr_set(x_365, 2, x_317);
lean::cnstr_set(x_365, 3, x_359);
lean::cnstr_set_scalar(x_365, sizeof(void*)*4, x_364);
if (lean::is_scalar(x_358)) {
 x_366 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_366 = x_358;
}
lean::cnstr_set(x_366, 0, x_362);
lean::cnstr_set(x_366, 1, x_355);
lean::cnstr_set(x_366, 2, x_356);
lean::cnstr_set(x_366, 3, x_357);
lean::cnstr_set_scalar(x_366, sizeof(void*)*4, x_364);
x_367 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_367, 0, x_365);
lean::cnstr_set(x_367, 1, x_360);
lean::cnstr_set(x_367, 2, x_361);
lean::cnstr_set(x_367, 3, x_366);
lean::cnstr_set_scalar(x_367, sizeof(void*)*4, x_354);
return x_367;
}
else
{
obj* x_368; 
x_368 = lean::cnstr_get(x_325, 3);
lean::inc(x_368);
if (lean::obj_tag(x_368) == 0)
{
obj* x_369; obj* x_370; obj* x_371; uint8 x_372; obj* x_373; obj* x_374; 
x_369 = lean::cnstr_get(x_325, 1);
lean::inc(x_369);
x_370 = lean::cnstr_get(x_325, 2);
lean::inc(x_370);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_371 = x_325;
} else {
 lean::dec_ref(x_325);
 x_371 = lean::box(0);
}
x_372 = 0;
if (lean::is_scalar(x_371)) {
 x_373 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_373 = x_371;
}
lean::cnstr_set(x_373, 0, x_326);
lean::cnstr_set(x_373, 1, x_369);
lean::cnstr_set(x_373, 2, x_370);
lean::cnstr_set(x_373, 3, x_368);
lean::cnstr_set_scalar(x_373, sizeof(void*)*4, x_372);
x_374 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_374, 0, x_315);
lean::cnstr_set(x_374, 1, x_316);
lean::cnstr_set(x_374, 2, x_317);
lean::cnstr_set(x_374, 3, x_373);
lean::cnstr_set_scalar(x_374, sizeof(void*)*4, x_354);
return x_374;
}
else
{
uint8 x_375; 
x_375 = lean::cnstr_get_scalar<uint8>(x_368, sizeof(void*)*4);
if (x_375 == 0)
{
obj* x_376; obj* x_377; obj* x_378; obj* x_379; obj* x_380; obj* x_381; obj* x_382; obj* x_383; obj* x_384; obj* x_385; obj* x_386; obj* x_387; 
x_376 = lean::cnstr_get(x_325, 1);
lean::inc(x_376);
x_377 = lean::cnstr_get(x_325, 2);
lean::inc(x_377);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_378 = x_325;
} else {
 lean::dec_ref(x_325);
 x_378 = lean::box(0);
}
x_379 = lean::cnstr_get(x_368, 0);
lean::inc(x_379);
x_380 = lean::cnstr_get(x_368, 1);
lean::inc(x_380);
x_381 = lean::cnstr_get(x_368, 2);
lean::inc(x_381);
x_382 = lean::cnstr_get(x_368, 3);
lean::inc(x_382);
if (lean::is_exclusive(x_368)) {
 lean::cnstr_release(x_368, 0);
 lean::cnstr_release(x_368, 1);
 lean::cnstr_release(x_368, 2);
 lean::cnstr_release(x_368, 3);
 x_383 = x_368;
} else {
 lean::dec_ref(x_368);
 x_383 = lean::box(0);
}
lean::inc(x_326);
if (lean::is_scalar(x_383)) {
 x_384 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_384 = x_383;
}
lean::cnstr_set(x_384, 0, x_315);
lean::cnstr_set(x_384, 1, x_316);
lean::cnstr_set(x_384, 2, x_317);
lean::cnstr_set(x_384, 3, x_326);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 lean::cnstr_release(x_326, 2);
 lean::cnstr_release(x_326, 3);
 x_385 = x_326;
} else {
 lean::dec_ref(x_326);
 x_385 = lean::box(0);
}
lean::cnstr_set_scalar(x_384, sizeof(void*)*4, x_354);
if (lean::is_scalar(x_385)) {
 x_386 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_386 = x_385;
}
lean::cnstr_set(x_386, 0, x_379);
lean::cnstr_set(x_386, 1, x_380);
lean::cnstr_set(x_386, 2, x_381);
lean::cnstr_set(x_386, 3, x_382);
lean::cnstr_set_scalar(x_386, sizeof(void*)*4, x_354);
if (lean::is_scalar(x_378)) {
 x_387 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_387 = x_378;
}
lean::cnstr_set(x_387, 0, x_384);
lean::cnstr_set(x_387, 1, x_376);
lean::cnstr_set(x_387, 2, x_377);
lean::cnstr_set(x_387, 3, x_386);
lean::cnstr_set_scalar(x_387, sizeof(void*)*4, x_375);
return x_387;
}
else
{
obj* x_388; obj* x_389; obj* x_390; obj* x_391; obj* x_392; obj* x_393; obj* x_394; obj* x_395; obj* x_396; uint8 x_397; obj* x_398; obj* x_399; 
x_388 = lean::cnstr_get(x_325, 1);
lean::inc(x_388);
x_389 = lean::cnstr_get(x_325, 2);
lean::inc(x_389);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_390 = x_325;
} else {
 lean::dec_ref(x_325);
 x_390 = lean::box(0);
}
x_391 = lean::cnstr_get(x_326, 0);
lean::inc(x_391);
x_392 = lean::cnstr_get(x_326, 1);
lean::inc(x_392);
x_393 = lean::cnstr_get(x_326, 2);
lean::inc(x_393);
x_394 = lean::cnstr_get(x_326, 3);
lean::inc(x_394);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 lean::cnstr_release(x_326, 2);
 lean::cnstr_release(x_326, 3);
 x_395 = x_326;
} else {
 lean::dec_ref(x_326);
 x_395 = lean::box(0);
}
if (lean::is_scalar(x_395)) {
 x_396 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_396 = x_395;
}
lean::cnstr_set(x_396, 0, x_391);
lean::cnstr_set(x_396, 1, x_392);
lean::cnstr_set(x_396, 2, x_393);
lean::cnstr_set(x_396, 3, x_394);
lean::cnstr_set_scalar(x_396, sizeof(void*)*4, x_375);
x_397 = 0;
if (lean::is_scalar(x_390)) {
 x_398 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_398 = x_390;
}
lean::cnstr_set(x_398, 0, x_396);
lean::cnstr_set(x_398, 1, x_388);
lean::cnstr_set(x_398, 2, x_389);
lean::cnstr_set(x_398, 3, x_368);
lean::cnstr_set_scalar(x_398, sizeof(void*)*4, x_397);
x_399 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_399, 0, x_315);
lean::cnstr_set(x_399, 1, x_316);
lean::cnstr_set(x_399, 2, x_317);
lean::cnstr_set(x_399, 3, x_398);
lean::cnstr_set_scalar(x_399, sizeof(void*)*4, x_375);
return x_399;
}
}
}
}
}
}
}
}
else
{
uint8 x_400; 
x_400 = l_RBNode_isRed___main___rarg(x_315);
if (x_400 == 0)
{
obj* x_401; obj* x_402; 
x_401 = l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__12(x_315, x_2, x_3);
x_402 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_402, 0, x_401);
lean::cnstr_set(x_402, 1, x_316);
lean::cnstr_set(x_402, 2, x_317);
lean::cnstr_set(x_402, 3, x_318);
lean::cnstr_set_scalar(x_402, sizeof(void*)*4, x_6);
return x_402;
}
else
{
obj* x_403; 
x_403 = l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__12(x_315, x_2, x_3);
if (lean::obj_tag(x_403) == 0)
{
lean::dec(x_318);
lean::dec(x_317);
lean::dec(x_316);
return x_403;
}
else
{
obj* x_404; 
x_404 = lean::cnstr_get(x_403, 0);
lean::inc(x_404);
if (lean::obj_tag(x_404) == 0)
{
obj* x_405; 
x_405 = lean::cnstr_get(x_403, 3);
lean::inc(x_405);
if (lean::obj_tag(x_405) == 0)
{
obj* x_406; obj* x_407; obj* x_408; uint8 x_409; obj* x_410; uint8 x_411; obj* x_412; 
x_406 = lean::cnstr_get(x_403, 1);
lean::inc(x_406);
x_407 = lean::cnstr_get(x_403, 2);
lean::inc(x_407);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_408 = x_403;
} else {
 lean::dec_ref(x_403);
 x_408 = lean::box(0);
}
x_409 = 0;
if (lean::is_scalar(x_408)) {
 x_410 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_410 = x_408;
}
lean::cnstr_set(x_410, 0, x_405);
lean::cnstr_set(x_410, 1, x_406);
lean::cnstr_set(x_410, 2, x_407);
lean::cnstr_set(x_410, 3, x_405);
lean::cnstr_set_scalar(x_410, sizeof(void*)*4, x_409);
x_411 = 1;
x_412 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_412, 0, x_410);
lean::cnstr_set(x_412, 1, x_316);
lean::cnstr_set(x_412, 2, x_317);
lean::cnstr_set(x_412, 3, x_318);
lean::cnstr_set_scalar(x_412, sizeof(void*)*4, x_411);
return x_412;
}
else
{
uint8 x_413; 
x_413 = lean::cnstr_get_scalar<uint8>(x_405, sizeof(void*)*4);
if (x_413 == 0)
{
obj* x_414; obj* x_415; obj* x_416; obj* x_417; obj* x_418; obj* x_419; obj* x_420; obj* x_421; uint8 x_422; obj* x_423; obj* x_424; obj* x_425; 
x_414 = lean::cnstr_get(x_403, 1);
lean::inc(x_414);
x_415 = lean::cnstr_get(x_403, 2);
lean::inc(x_415);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_416 = x_403;
} else {
 lean::dec_ref(x_403);
 x_416 = lean::box(0);
}
x_417 = lean::cnstr_get(x_405, 0);
lean::inc(x_417);
x_418 = lean::cnstr_get(x_405, 1);
lean::inc(x_418);
x_419 = lean::cnstr_get(x_405, 2);
lean::inc(x_419);
x_420 = lean::cnstr_get(x_405, 3);
lean::inc(x_420);
if (lean::is_exclusive(x_405)) {
 lean::cnstr_release(x_405, 0);
 lean::cnstr_release(x_405, 1);
 lean::cnstr_release(x_405, 2);
 lean::cnstr_release(x_405, 3);
 x_421 = x_405;
} else {
 lean::dec_ref(x_405);
 x_421 = lean::box(0);
}
x_422 = 1;
if (lean::is_scalar(x_421)) {
 x_423 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_423 = x_421;
}
lean::cnstr_set(x_423, 0, x_404);
lean::cnstr_set(x_423, 1, x_414);
lean::cnstr_set(x_423, 2, x_415);
lean::cnstr_set(x_423, 3, x_417);
lean::cnstr_set_scalar(x_423, sizeof(void*)*4, x_422);
if (lean::is_scalar(x_416)) {
 x_424 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_424 = x_416;
}
lean::cnstr_set(x_424, 0, x_420);
lean::cnstr_set(x_424, 1, x_316);
lean::cnstr_set(x_424, 2, x_317);
lean::cnstr_set(x_424, 3, x_318);
lean::cnstr_set_scalar(x_424, sizeof(void*)*4, x_422);
x_425 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_425, 0, x_423);
lean::cnstr_set(x_425, 1, x_418);
lean::cnstr_set(x_425, 2, x_419);
lean::cnstr_set(x_425, 3, x_424);
lean::cnstr_set_scalar(x_425, sizeof(void*)*4, x_413);
return x_425;
}
else
{
obj* x_426; obj* x_427; obj* x_428; uint8 x_429; obj* x_430; obj* x_431; 
x_426 = lean::cnstr_get(x_403, 1);
lean::inc(x_426);
x_427 = lean::cnstr_get(x_403, 2);
lean::inc(x_427);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_428 = x_403;
} else {
 lean::dec_ref(x_403);
 x_428 = lean::box(0);
}
x_429 = 0;
if (lean::is_scalar(x_428)) {
 x_430 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_430 = x_428;
}
lean::cnstr_set(x_430, 0, x_404);
lean::cnstr_set(x_430, 1, x_426);
lean::cnstr_set(x_430, 2, x_427);
lean::cnstr_set(x_430, 3, x_405);
lean::cnstr_set_scalar(x_430, sizeof(void*)*4, x_429);
x_431 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_431, 0, x_430);
lean::cnstr_set(x_431, 1, x_316);
lean::cnstr_set(x_431, 2, x_317);
lean::cnstr_set(x_431, 3, x_318);
lean::cnstr_set_scalar(x_431, sizeof(void*)*4, x_413);
return x_431;
}
}
}
else
{
uint8 x_432; 
x_432 = lean::cnstr_get_scalar<uint8>(x_404, sizeof(void*)*4);
if (x_432 == 0)
{
obj* x_433; obj* x_434; obj* x_435; obj* x_436; obj* x_437; obj* x_438; obj* x_439; obj* x_440; obj* x_441; uint8 x_442; obj* x_443; obj* x_444; obj* x_445; 
x_433 = lean::cnstr_get(x_403, 1);
lean::inc(x_433);
x_434 = lean::cnstr_get(x_403, 2);
lean::inc(x_434);
x_435 = lean::cnstr_get(x_403, 3);
lean::inc(x_435);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_436 = x_403;
} else {
 lean::dec_ref(x_403);
 x_436 = lean::box(0);
}
x_437 = lean::cnstr_get(x_404, 0);
lean::inc(x_437);
x_438 = lean::cnstr_get(x_404, 1);
lean::inc(x_438);
x_439 = lean::cnstr_get(x_404, 2);
lean::inc(x_439);
x_440 = lean::cnstr_get(x_404, 3);
lean::inc(x_440);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 lean::cnstr_release(x_404, 2);
 lean::cnstr_release(x_404, 3);
 x_441 = x_404;
} else {
 lean::dec_ref(x_404);
 x_441 = lean::box(0);
}
x_442 = 1;
if (lean::is_scalar(x_441)) {
 x_443 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_443 = x_441;
}
lean::cnstr_set(x_443, 0, x_437);
lean::cnstr_set(x_443, 1, x_438);
lean::cnstr_set(x_443, 2, x_439);
lean::cnstr_set(x_443, 3, x_440);
lean::cnstr_set_scalar(x_443, sizeof(void*)*4, x_442);
if (lean::is_scalar(x_436)) {
 x_444 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_444 = x_436;
}
lean::cnstr_set(x_444, 0, x_435);
lean::cnstr_set(x_444, 1, x_316);
lean::cnstr_set(x_444, 2, x_317);
lean::cnstr_set(x_444, 3, x_318);
lean::cnstr_set_scalar(x_444, sizeof(void*)*4, x_442);
x_445 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_445, 0, x_443);
lean::cnstr_set(x_445, 1, x_433);
lean::cnstr_set(x_445, 2, x_434);
lean::cnstr_set(x_445, 3, x_444);
lean::cnstr_set_scalar(x_445, sizeof(void*)*4, x_432);
return x_445;
}
else
{
obj* x_446; 
x_446 = lean::cnstr_get(x_403, 3);
lean::inc(x_446);
if (lean::obj_tag(x_446) == 0)
{
obj* x_447; obj* x_448; obj* x_449; uint8 x_450; obj* x_451; obj* x_452; 
x_447 = lean::cnstr_get(x_403, 1);
lean::inc(x_447);
x_448 = lean::cnstr_get(x_403, 2);
lean::inc(x_448);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_449 = x_403;
} else {
 lean::dec_ref(x_403);
 x_449 = lean::box(0);
}
x_450 = 0;
if (lean::is_scalar(x_449)) {
 x_451 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_451 = x_449;
}
lean::cnstr_set(x_451, 0, x_404);
lean::cnstr_set(x_451, 1, x_447);
lean::cnstr_set(x_451, 2, x_448);
lean::cnstr_set(x_451, 3, x_446);
lean::cnstr_set_scalar(x_451, sizeof(void*)*4, x_450);
x_452 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_452, 0, x_451);
lean::cnstr_set(x_452, 1, x_316);
lean::cnstr_set(x_452, 2, x_317);
lean::cnstr_set(x_452, 3, x_318);
lean::cnstr_set_scalar(x_452, sizeof(void*)*4, x_432);
return x_452;
}
else
{
uint8 x_453; 
x_453 = lean::cnstr_get_scalar<uint8>(x_446, sizeof(void*)*4);
if (x_453 == 0)
{
obj* x_454; obj* x_455; obj* x_456; obj* x_457; obj* x_458; obj* x_459; obj* x_460; obj* x_461; obj* x_462; obj* x_463; obj* x_464; obj* x_465; 
x_454 = lean::cnstr_get(x_403, 1);
lean::inc(x_454);
x_455 = lean::cnstr_get(x_403, 2);
lean::inc(x_455);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_456 = x_403;
} else {
 lean::dec_ref(x_403);
 x_456 = lean::box(0);
}
x_457 = lean::cnstr_get(x_446, 0);
lean::inc(x_457);
x_458 = lean::cnstr_get(x_446, 1);
lean::inc(x_458);
x_459 = lean::cnstr_get(x_446, 2);
lean::inc(x_459);
x_460 = lean::cnstr_get(x_446, 3);
lean::inc(x_460);
if (lean::is_exclusive(x_446)) {
 lean::cnstr_release(x_446, 0);
 lean::cnstr_release(x_446, 1);
 lean::cnstr_release(x_446, 2);
 lean::cnstr_release(x_446, 3);
 x_461 = x_446;
} else {
 lean::dec_ref(x_446);
 x_461 = lean::box(0);
}
lean::inc(x_404);
if (lean::is_scalar(x_461)) {
 x_462 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_462 = x_461;
}
lean::cnstr_set(x_462, 0, x_404);
lean::cnstr_set(x_462, 1, x_454);
lean::cnstr_set(x_462, 2, x_455);
lean::cnstr_set(x_462, 3, x_457);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 lean::cnstr_release(x_404, 2);
 lean::cnstr_release(x_404, 3);
 x_463 = x_404;
} else {
 lean::dec_ref(x_404);
 x_463 = lean::box(0);
}
lean::cnstr_set_scalar(x_462, sizeof(void*)*4, x_432);
if (lean::is_scalar(x_463)) {
 x_464 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_464 = x_463;
}
lean::cnstr_set(x_464, 0, x_460);
lean::cnstr_set(x_464, 1, x_316);
lean::cnstr_set(x_464, 2, x_317);
lean::cnstr_set(x_464, 3, x_318);
lean::cnstr_set_scalar(x_464, sizeof(void*)*4, x_432);
if (lean::is_scalar(x_456)) {
 x_465 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_465 = x_456;
}
lean::cnstr_set(x_465, 0, x_462);
lean::cnstr_set(x_465, 1, x_458);
lean::cnstr_set(x_465, 2, x_459);
lean::cnstr_set(x_465, 3, x_464);
lean::cnstr_set_scalar(x_465, sizeof(void*)*4, x_453);
return x_465;
}
else
{
obj* x_466; obj* x_467; obj* x_468; obj* x_469; obj* x_470; obj* x_471; obj* x_472; obj* x_473; obj* x_474; uint8 x_475; obj* x_476; obj* x_477; 
x_466 = lean::cnstr_get(x_403, 1);
lean::inc(x_466);
x_467 = lean::cnstr_get(x_403, 2);
lean::inc(x_467);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_468 = x_403;
} else {
 lean::dec_ref(x_403);
 x_468 = lean::box(0);
}
x_469 = lean::cnstr_get(x_404, 0);
lean::inc(x_469);
x_470 = lean::cnstr_get(x_404, 1);
lean::inc(x_470);
x_471 = lean::cnstr_get(x_404, 2);
lean::inc(x_471);
x_472 = lean::cnstr_get(x_404, 3);
lean::inc(x_472);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 lean::cnstr_release(x_404, 2);
 lean::cnstr_release(x_404, 3);
 x_473 = x_404;
} else {
 lean::dec_ref(x_404);
 x_473 = lean::box(0);
}
if (lean::is_scalar(x_473)) {
 x_474 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_474 = x_473;
}
lean::cnstr_set(x_474, 0, x_469);
lean::cnstr_set(x_474, 1, x_470);
lean::cnstr_set(x_474, 2, x_471);
lean::cnstr_set(x_474, 3, x_472);
lean::cnstr_set_scalar(x_474, sizeof(void*)*4, x_453);
x_475 = 0;
if (lean::is_scalar(x_468)) {
 x_476 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_476 = x_468;
}
lean::cnstr_set(x_476, 0, x_474);
lean::cnstr_set(x_476, 1, x_466);
lean::cnstr_set(x_476, 2, x_467);
lean::cnstr_set(x_476, 3, x_446);
lean::cnstr_set_scalar(x_476, sizeof(void*)*4, x_475);
x_477 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_477, 0, x_476);
lean::cnstr_set(x_477, 1, x_316);
lean::cnstr_set(x_477, 2, x_317);
lean::cnstr_set(x_477, 3, x_318);
lean::cnstr_set_scalar(x_477, sizeof(void*)*4, x_453);
return x_477;
}
}
}
}
}
}
}
}
}
}
}
}
obj* l_RBNode_insert___at_Lean_Compiler_SpecState_addEntry___spec__11(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__12(x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at_Lean_Compiler_SpecState_addEntry___spec__12(x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
uint8 l_AssocList_contains___main___at_Lean_Compiler_SpecState_addEntry___spec__14(obj* x_1, obj* x_2) {
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
x_6 = lean_expr_eqv(x_4, x_1);
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
obj* l_AssocList_mfoldl___main___at_Lean_Compiler_SpecState_addEntry___spec__17(obj* x_1, obj* x_2) {
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
x_7 = lean_expr_hash(x_4);
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
x_19 = lean_expr_hash(x_15);
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
obj* l_HashMapImp_moveEntries___main___at_Lean_Compiler_SpecState_addEntry___spec__16(obj* x_1, obj* x_2, obj* x_3) {
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
x_9 = l_AssocList_mfoldl___main___at_Lean_Compiler_SpecState_addEntry___spec__17(x_3, x_6);
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
obj* l_HashMapImp_expand___at_Lean_Compiler_SpecState_addEntry___spec__15(obj* x_1, obj* x_2) {
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
x_9 = l_HashMapImp_moveEntries___main___at_Lean_Compiler_SpecState_addEntry___spec__16(x_8, x_2, x_7);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_AssocList_replace___main___at_Lean_Compiler_SpecState_addEntry___spec__18(obj* x_1, obj* x_2, obj* x_3) {
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
x_8 = lean_expr_eqv(x_5, x_1);
if (x_8 == 0)
{
obj* x_9; 
x_9 = l_AssocList_replace___main___at_Lean_Compiler_SpecState_addEntry___spec__18(x_1, x_2, x_7);
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
x_13 = lean_expr_eqv(x_10, x_1);
if (x_13 == 0)
{
obj* x_14; obj* x_15; 
x_14 = l_AssocList_replace___main___at_Lean_Compiler_SpecState_addEntry___spec__18(x_1, x_2, x_12);
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
obj* l_HashMapImp_insert___at_Lean_Compiler_SpecState_addEntry___spec__13(obj* x_1, obj* x_2, obj* x_3) {
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
x_8 = lean_expr_hash(x_2);
x_9 = lean::usize_modn(x_8, x_7);
x_10 = lean::box_size_t(x_9);
x_11 = lean::unbox_size_t(x_10);
x_12 = lean::array_uget(x_6, x_11);
x_13 = l_AssocList_contains___main___at_Lean_Compiler_SpecState_addEntry___spec__14(x_2, x_12);
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
x_20 = l_HashMapImp_expand___at_Lean_Compiler_SpecState_addEntry___spec__15(x_15, x_18);
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
x_21 = l_AssocList_replace___main___at_Lean_Compiler_SpecState_addEntry___spec__18(x_2, x_3, x_12);
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
x_27 = lean_expr_hash(x_2);
x_28 = lean::usize_modn(x_27, x_26);
x_29 = lean::box_size_t(x_28);
x_30 = lean::unbox_size_t(x_29);
x_31 = lean::array_uget(x_25, x_30);
x_32 = l_AssocList_contains___main___at_Lean_Compiler_SpecState_addEntry___spec__14(x_2, x_31);
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
x_39 = l_HashMapImp_expand___at_Lean_Compiler_SpecState_addEntry___spec__15(x_34, x_37);
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
x_41 = l_AssocList_replace___main___at_Lean_Compiler_SpecState_addEntry___spec__18(x_2, x_3, x_31);
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
obj* l_Lean_SMap_insert___main___at_Lean_Compiler_SpecState_addEntry___spec__10(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*2);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_1);
if (x_5 == 0)
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_1, 1);
x_7 = l_RBNode_insert___at_Lean_Compiler_SpecState_addEntry___spec__11(x_6, x_2, x_3);
lean::cnstr_set(x_1, 1, x_7);
return x_1;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_1);
x_10 = l_RBNode_insert___at_Lean_Compiler_SpecState_addEntry___spec__11(x_9, x_2, x_3);
x_11 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_4);
return x_11;
}
}
else
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_1);
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
x_13 = lean::cnstr_get(x_1, 0);
x_14 = l_HashMapImp_insert___at_Lean_Compiler_SpecState_addEntry___spec__13(x_13, x_2, x_3);
lean::cnstr_set(x_1, 0, x_14);
return x_1;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = lean::cnstr_get(x_1, 0);
x_16 = lean::cnstr_get(x_1, 1);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_1);
x_17 = l_HashMapImp_insert___at_Lean_Compiler_SpecState_addEntry___spec__13(x_15, x_2, x_3);
x_18 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_16);
lean::cnstr_set_scalar(x_18, sizeof(void*)*2, x_4);
return x_18;
}
}
}
}
obj* l_Lean_Compiler_SpecState_addEntry(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
lean::dec(x_2);
x_5 = !lean::is_exclusive(x_1);
if (x_5 == 0)
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_1, 0);
x_7 = l_Lean_SMap_insert___main___at_Lean_Compiler_SpecState_addEntry___spec__1(x_6, x_3, x_4);
lean::cnstr_set(x_1, 0, x_7);
return x_1;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_1);
x_10 = l_Lean_SMap_insert___main___at_Lean_Compiler_SpecState_addEntry___spec__1(x_8, x_3, x_4);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
return x_11;
}
}
else
{
obj* x_12; obj* x_13; uint8 x_14; 
x_12 = lean::cnstr_get(x_2, 0);
lean::inc(x_12);
x_13 = lean::cnstr_get(x_2, 1);
lean::inc(x_13);
lean::dec(x_2);
x_14 = !lean::is_exclusive(x_1);
if (x_14 == 0)
{
obj* x_15; obj* x_16; 
x_15 = lean::cnstr_get(x_1, 1);
x_16 = l_Lean_SMap_insert___main___at_Lean_Compiler_SpecState_addEntry___spec__10(x_15, x_12, x_13);
lean::cnstr_set(x_1, 1, x_16);
return x_1;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_17 = lean::cnstr_get(x_1, 0);
x_18 = lean::cnstr_get(x_1, 1);
lean::inc(x_18);
lean::inc(x_17);
lean::dec(x_1);
x_19 = l_Lean_SMap_insert___main___at_Lean_Compiler_SpecState_addEntry___spec__10(x_18, x_12, x_13);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_17);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
}
}
obj* l_AssocList_contains___main___at_Lean_Compiler_SpecState_addEntry___spec__5___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_Compiler_SpecState_addEntry___spec__5(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_AssocList_contains___main___at_Lean_Compiler_SpecState_addEntry___spec__14___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_Compiler_SpecState_addEntry___spec__14(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Lean_SMap_switch___at_Lean_Compiler_SpecState_switch___main___spec__1(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*2);
if (x_2 == 0)
{
return x_1;
}
else
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
uint8 x_4; 
x_4 = 0;
lean::cnstr_set_scalar(x_1, sizeof(void*)*2, x_4);
return x_1;
}
else
{
obj* x_5; obj* x_6; uint8 x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::inc(x_5);
lean::dec(x_1);
x_7 = 0;
x_8 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_8, 0, x_5);
lean::cnstr_set(x_8, 1, x_6);
lean::cnstr_set_scalar(x_8, sizeof(void*)*2, x_7);
return x_8;
}
}
}
}
obj* l_Lean_SMap_switch___at_Lean_Compiler_SpecState_switch___main___spec__2(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*2);
if (x_2 == 0)
{
return x_1;
}
else
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
uint8 x_4; 
x_4 = 0;
lean::cnstr_set_scalar(x_1, sizeof(void*)*2, x_4);
return x_1;
}
else
{
obj* x_5; obj* x_6; uint8 x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::inc(x_5);
lean::dec(x_1);
x_7 = 0;
x_8 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_8, 0, x_5);
lean::cnstr_set(x_8, 1, x_6);
lean::cnstr_set_scalar(x_8, sizeof(void*)*2, x_7);
return x_8;
}
}
}
}
obj* l_Lean_Compiler_SpecState_switch___main(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = l_Lean_SMap_switch___at_Lean_Compiler_SpecState_switch___main___spec__1(x_3);
x_6 = l_Lean_SMap_switch___at_Lean_Compiler_SpecState_switch___main___spec__2(x_4);
lean::cnstr_set(x_1, 1, x_6);
lean::cnstr_set(x_1, 0, x_5);
return x_1;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_1, 0);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::inc(x_7);
lean::dec(x_1);
x_9 = l_Lean_SMap_switch___at_Lean_Compiler_SpecState_switch___main___spec__1(x_7);
x_10 = l_Lean_SMap_switch___at_Lean_Compiler_SpecState_switch___main___spec__2(x_8);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
}
obj* l_Lean_Compiler_SpecState_switch(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Compiler_SpecState_switch___main(x_1);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_Lean_Compiler_mkSpecExtension___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
x_8 = l_Lean_Compiler_SpecState_addEntry(x_4, x_7);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_add(x_3, x_9);
lean::dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_Lean_Compiler_mkSpecExtension___spec__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
x_9 = l_Array_miterateAux___main___at_Lean_Compiler_mkSpecExtension___spec__2(x_7, x_7, x_8, x_4);
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
obj* l_Lean_mkStateFromImportedEntries___at_Lean_Compiler_mkSpecExtension___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l_Array_miterateAux___main___at_Lean_Compiler_mkSpecExtension___spec__3(x_2, x_2, x_3, x_1);
return x_4;
}
}
uint8 l_Array_anyMAux___main___at_Lean_Compiler_mkSpecExtension___spec__6(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_2);
x_5 = lean::nat_dec_lt(x_3, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_6; 
lean::dec(x_3);
x_6 = 0;
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_7 = lean::array_fget(x_2, x_3);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::cnstr_get(x_1, 0);
x_10 = lean_name_dec_eq(x_8, x_9);
lean::dec(x_8);
if (x_10 == 0)
{
obj* x_11; obj* x_12; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_add(x_3, x_11);
lean::dec(x_3);
x_3 = x_12;
goto _start;
}
else
{
lean::dec(x_3);
return x_10;
}
}
}
}
obj* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__1() {
_start:
{
obj* x_1; uint8 x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = 1;
x_3 = l_HashMap_Inhabited___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set_scalar(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
obj* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__2() {
_start:
{
obj* x_1; uint8 x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = 1;
x_3 = l_HashMap_Inhabited___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set_scalar(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
obj* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__1;
x_2 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__2;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__3;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__4;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_io_initializing(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; uint8 x_5; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::unbox(x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_6; 
lean::dec(x_1);
x_6 = !lean::is_exclusive(x_3);
if (x_6 == 0)
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_3, 0);
lean::dec(x_7);
x_8 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
lean::cnstr_set_tag(x_3, 1);
lean::cnstr_set(x_3, 0, x_8);
return x_3;
}
else
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
lean::dec(x_3);
x_10 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_3);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_13 = lean::cnstr_get(x_3, 0);
lean::dec(x_13);
x_14 = lean::box(0);
lean::cnstr_set(x_3, 0, x_14);
x_15 = l___private_init_lean_environment_5__envExtensionsRef;
x_16 = lean::io_ref_get(x_15, x_3);
if (lean::obj_tag(x_16) == 0)
{
uint8 x_17; 
x_17 = !lean::is_exclusive(x_16);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_18 = lean::cnstr_get(x_16, 0);
lean::cnstr_set(x_16, 0, x_14);
x_19 = lean::array_get_size(x_18);
lean::dec(x_18);
x_20 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__5;
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_1);
lean::cnstr_set(x_21, 2, x_20);
x_22 = lean::io_ref_get(x_15, x_16);
if (lean::obj_tag(x_22) == 0)
{
uint8 x_23; 
x_23 = !lean::is_exclusive(x_22);
if (x_23 == 0)
{
obj* x_24; obj* x_25; 
x_24 = lean::cnstr_get(x_22, 0);
lean::cnstr_set(x_22, 0, x_14);
x_25 = lean::io_ref_reset(x_15, x_22);
if (lean::obj_tag(x_25) == 0)
{
uint8 x_26; 
x_26 = !lean::is_exclusive(x_25);
if (x_26 == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_27 = lean::cnstr_get(x_25, 0);
lean::dec(x_27);
lean::cnstr_set(x_25, 0, x_14);
x_28 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_21);
x_29 = x_21;
x_30 = lean::array_push(x_24, x_29);
x_31 = lean::io_ref_set(x_15, x_30, x_25);
if (lean::obj_tag(x_31) == 0)
{
uint8 x_32; 
x_32 = !lean::is_exclusive(x_31);
if (x_32 == 0)
{
obj* x_33; 
x_33 = lean::cnstr_get(x_31, 0);
lean::dec(x_33);
lean::cnstr_set(x_31, 0, x_21);
return x_31;
}
else
{
obj* x_34; obj* x_35; 
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_21);
lean::cnstr_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8 x_36; 
lean::dec(x_21);
x_36 = !lean::is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
obj* x_37; obj* x_38; obj* x_39; 
x_37 = lean::cnstr_get(x_31, 0);
x_38 = lean::cnstr_get(x_31, 1);
lean::inc(x_38);
lean::inc(x_37);
lean::dec(x_31);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_40 = lean::cnstr_get(x_25, 1);
lean::inc(x_40);
lean::dec(x_25);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_14);
lean::cnstr_set(x_41, 1, x_40);
x_42 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_21);
x_43 = x_21;
x_44 = lean::array_push(x_24, x_43);
x_45 = lean::io_ref_set(x_15, x_44, x_41);
if (lean::obj_tag(x_45) == 0)
{
obj* x_46; obj* x_47; obj* x_48; 
x_46 = lean::cnstr_get(x_45, 1);
lean::inc(x_46);
if (lean::is_exclusive(x_45)) {
 lean::cnstr_release(x_45, 0);
 lean::cnstr_release(x_45, 1);
 x_47 = x_45;
} else {
 lean::dec_ref(x_45);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_21);
lean::cnstr_set(x_48, 1, x_46);
return x_48;
}
else
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
lean::dec(x_21);
x_49 = lean::cnstr_get(x_45, 0);
lean::inc(x_49);
x_50 = lean::cnstr_get(x_45, 1);
lean::inc(x_50);
if (lean::is_exclusive(x_45)) {
 lean::cnstr_release(x_45, 0);
 lean::cnstr_release(x_45, 1);
 x_51 = x_45;
} else {
 lean::dec_ref(x_45);
 x_51 = lean::box(0);
}
if (lean::is_scalar(x_51)) {
 x_52 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_52 = x_51;
}
lean::cnstr_set(x_52, 0, x_49);
lean::cnstr_set(x_52, 1, x_50);
return x_52;
}
}
}
else
{
uint8 x_53; 
lean::dec(x_24);
lean::dec(x_21);
x_53 = !lean::is_exclusive(x_25);
if (x_53 == 0)
{
return x_25;
}
else
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = lean::cnstr_get(x_25, 0);
x_55 = lean::cnstr_get(x_25, 1);
lean::inc(x_55);
lean::inc(x_54);
lean::dec(x_25);
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_54);
lean::cnstr_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_57 = lean::cnstr_get(x_22, 0);
x_58 = lean::cnstr_get(x_22, 1);
lean::inc(x_58);
lean::inc(x_57);
lean::dec(x_22);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_14);
lean::cnstr_set(x_59, 1, x_58);
x_60 = lean::io_ref_reset(x_15, x_59);
if (lean::obj_tag(x_60) == 0)
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_61 = lean::cnstr_get(x_60, 1);
lean::inc(x_61);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_release(x_60, 0);
 lean::cnstr_release(x_60, 1);
 x_62 = x_60;
} else {
 lean::dec_ref(x_60);
 x_62 = lean::box(0);
}
if (lean::is_scalar(x_62)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_62;
}
lean::cnstr_set(x_63, 0, x_14);
lean::cnstr_set(x_63, 1, x_61);
x_64 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_21);
x_65 = x_21;
x_66 = lean::array_push(x_57, x_65);
x_67 = lean::io_ref_set(x_15, x_66, x_63);
if (lean::obj_tag(x_67) == 0)
{
obj* x_68; obj* x_69; obj* x_70; 
x_68 = lean::cnstr_get(x_67, 1);
lean::inc(x_68);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_release(x_67, 0);
 lean::cnstr_release(x_67, 1);
 x_69 = x_67;
} else {
 lean::dec_ref(x_67);
 x_69 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_69;
}
lean::cnstr_set(x_70, 0, x_21);
lean::cnstr_set(x_70, 1, x_68);
return x_70;
}
else
{
obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_21);
x_71 = lean::cnstr_get(x_67, 0);
lean::inc(x_71);
x_72 = lean::cnstr_get(x_67, 1);
lean::inc(x_72);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_release(x_67, 0);
 lean::cnstr_release(x_67, 1);
 x_73 = x_67;
} else {
 lean::dec_ref(x_67);
 x_73 = lean::box(0);
}
if (lean::is_scalar(x_73)) {
 x_74 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_74 = x_73;
}
lean::cnstr_set(x_74, 0, x_71);
lean::cnstr_set(x_74, 1, x_72);
return x_74;
}
}
else
{
obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
lean::dec(x_57);
lean::dec(x_21);
x_75 = lean::cnstr_get(x_60, 0);
lean::inc(x_75);
x_76 = lean::cnstr_get(x_60, 1);
lean::inc(x_76);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_release(x_60, 0);
 lean::cnstr_release(x_60, 1);
 x_77 = x_60;
} else {
 lean::dec_ref(x_60);
 x_77 = lean::box(0);
}
if (lean::is_scalar(x_77)) {
 x_78 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_78 = x_77;
}
lean::cnstr_set(x_78, 0, x_75);
lean::cnstr_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
uint8 x_79; 
lean::dec(x_21);
x_79 = !lean::is_exclusive(x_22);
if (x_79 == 0)
{
return x_22;
}
else
{
obj* x_80; obj* x_81; obj* x_82; 
x_80 = lean::cnstr_get(x_22, 0);
x_81 = lean::cnstr_get(x_22, 1);
lean::inc(x_81);
lean::inc(x_80);
lean::dec(x_22);
x_82 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_82, 0, x_80);
lean::cnstr_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
x_83 = lean::cnstr_get(x_16, 0);
x_84 = lean::cnstr_get(x_16, 1);
lean::inc(x_84);
lean::inc(x_83);
lean::dec(x_16);
x_85 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_85, 0, x_14);
lean::cnstr_set(x_85, 1, x_84);
x_86 = lean::array_get_size(x_83);
lean::dec(x_83);
x_87 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__5;
x_88 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_88, 0, x_86);
lean::cnstr_set(x_88, 1, x_1);
lean::cnstr_set(x_88, 2, x_87);
x_89 = lean::io_ref_get(x_15, x_85);
if (lean::obj_tag(x_89) == 0)
{
obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
x_90 = lean::cnstr_get(x_89, 0);
lean::inc(x_90);
x_91 = lean::cnstr_get(x_89, 1);
lean::inc(x_91);
if (lean::is_exclusive(x_89)) {
 lean::cnstr_release(x_89, 0);
 lean::cnstr_release(x_89, 1);
 x_92 = x_89;
} else {
 lean::dec_ref(x_89);
 x_92 = lean::box(0);
}
if (lean::is_scalar(x_92)) {
 x_93 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_93 = x_92;
}
lean::cnstr_set(x_93, 0, x_14);
lean::cnstr_set(x_93, 1, x_91);
x_94 = lean::io_ref_reset(x_15, x_93);
if (lean::obj_tag(x_94) == 0)
{
obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
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
lean::cnstr_set(x_97, 0, x_14);
lean::cnstr_set(x_97, 1, x_95);
x_98 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_88);
x_99 = x_88;
x_100 = lean::array_push(x_90, x_99);
x_101 = lean::io_ref_set(x_15, x_100, x_97);
if (lean::obj_tag(x_101) == 0)
{
obj* x_102; obj* x_103; obj* x_104; 
x_102 = lean::cnstr_get(x_101, 1);
lean::inc(x_102);
if (lean::is_exclusive(x_101)) {
 lean::cnstr_release(x_101, 0);
 lean::cnstr_release(x_101, 1);
 x_103 = x_101;
} else {
 lean::dec_ref(x_101);
 x_103 = lean::box(0);
}
if (lean::is_scalar(x_103)) {
 x_104 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_104 = x_103;
}
lean::cnstr_set(x_104, 0, x_88);
lean::cnstr_set(x_104, 1, x_102);
return x_104;
}
else
{
obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
lean::dec(x_88);
x_105 = lean::cnstr_get(x_101, 0);
lean::inc(x_105);
x_106 = lean::cnstr_get(x_101, 1);
lean::inc(x_106);
if (lean::is_exclusive(x_101)) {
 lean::cnstr_release(x_101, 0);
 lean::cnstr_release(x_101, 1);
 x_107 = x_101;
} else {
 lean::dec_ref(x_101);
 x_107 = lean::box(0);
}
if (lean::is_scalar(x_107)) {
 x_108 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_108 = x_107;
}
lean::cnstr_set(x_108, 0, x_105);
lean::cnstr_set(x_108, 1, x_106);
return x_108;
}
}
else
{
obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_90);
lean::dec(x_88);
x_109 = lean::cnstr_get(x_94, 0);
lean::inc(x_109);
x_110 = lean::cnstr_get(x_94, 1);
lean::inc(x_110);
if (lean::is_exclusive(x_94)) {
 lean::cnstr_release(x_94, 0);
 lean::cnstr_release(x_94, 1);
 x_111 = x_94;
} else {
 lean::dec_ref(x_94);
 x_111 = lean::box(0);
}
if (lean::is_scalar(x_111)) {
 x_112 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_112 = x_111;
}
lean::cnstr_set(x_112, 0, x_109);
lean::cnstr_set(x_112, 1, x_110);
return x_112;
}
}
else
{
obj* x_113; obj* x_114; obj* x_115; obj* x_116; 
lean::dec(x_88);
x_113 = lean::cnstr_get(x_89, 0);
lean::inc(x_113);
x_114 = lean::cnstr_get(x_89, 1);
lean::inc(x_114);
if (lean::is_exclusive(x_89)) {
 lean::cnstr_release(x_89, 0);
 lean::cnstr_release(x_89, 1);
 x_115 = x_89;
} else {
 lean::dec_ref(x_89);
 x_115 = lean::box(0);
}
if (lean::is_scalar(x_115)) {
 x_116 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_116 = x_115;
}
lean::cnstr_set(x_116, 0, x_113);
lean::cnstr_set(x_116, 1, x_114);
return x_116;
}
}
}
else
{
uint8 x_117; 
lean::dec(x_1);
x_117 = !lean::is_exclusive(x_16);
if (x_117 == 0)
{
return x_16;
}
else
{
obj* x_118; obj* x_119; obj* x_120; 
x_118 = lean::cnstr_get(x_16, 0);
x_119 = lean::cnstr_get(x_16, 1);
lean::inc(x_119);
lean::inc(x_118);
lean::dec(x_16);
x_120 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_120, 0, x_118);
lean::cnstr_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; 
x_121 = lean::cnstr_get(x_3, 1);
lean::inc(x_121);
lean::dec(x_3);
x_122 = lean::box(0);
x_123 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_123, 0, x_122);
lean::cnstr_set(x_123, 1, x_121);
x_124 = l___private_init_lean_environment_5__envExtensionsRef;
x_125 = lean::io_ref_get(x_124, x_123);
if (lean::obj_tag(x_125) == 0)
{
obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
x_126 = lean::cnstr_get(x_125, 0);
lean::inc(x_126);
x_127 = lean::cnstr_get(x_125, 1);
lean::inc(x_127);
if (lean::is_exclusive(x_125)) {
 lean::cnstr_release(x_125, 0);
 lean::cnstr_release(x_125, 1);
 x_128 = x_125;
} else {
 lean::dec_ref(x_125);
 x_128 = lean::box(0);
}
if (lean::is_scalar(x_128)) {
 x_129 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_129 = x_128;
}
lean::cnstr_set(x_129, 0, x_122);
lean::cnstr_set(x_129, 1, x_127);
x_130 = lean::array_get_size(x_126);
lean::dec(x_126);
x_131 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__5;
x_132 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_132, 0, x_130);
lean::cnstr_set(x_132, 1, x_1);
lean::cnstr_set(x_132, 2, x_131);
x_133 = lean::io_ref_get(x_124, x_129);
if (lean::obj_tag(x_133) == 0)
{
obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; 
x_134 = lean::cnstr_get(x_133, 0);
lean::inc(x_134);
x_135 = lean::cnstr_get(x_133, 1);
lean::inc(x_135);
if (lean::is_exclusive(x_133)) {
 lean::cnstr_release(x_133, 0);
 lean::cnstr_release(x_133, 1);
 x_136 = x_133;
} else {
 lean::dec_ref(x_133);
 x_136 = lean::box(0);
}
if (lean::is_scalar(x_136)) {
 x_137 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_137 = x_136;
}
lean::cnstr_set(x_137, 0, x_122);
lean::cnstr_set(x_137, 1, x_135);
x_138 = lean::io_ref_reset(x_124, x_137);
if (lean::obj_tag(x_138) == 0)
{
obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; 
x_139 = lean::cnstr_get(x_138, 1);
lean::inc(x_139);
if (lean::is_exclusive(x_138)) {
 lean::cnstr_release(x_138, 0);
 lean::cnstr_release(x_138, 1);
 x_140 = x_138;
} else {
 lean::dec_ref(x_138);
 x_140 = lean::box(0);
}
if (lean::is_scalar(x_140)) {
 x_141 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_141 = x_140;
}
lean::cnstr_set(x_141, 0, x_122);
lean::cnstr_set(x_141, 1, x_139);
x_142 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_132);
x_143 = x_132;
x_144 = lean::array_push(x_134, x_143);
x_145 = lean::io_ref_set(x_124, x_144, x_141);
if (lean::obj_tag(x_145) == 0)
{
obj* x_146; obj* x_147; obj* x_148; 
x_146 = lean::cnstr_get(x_145, 1);
lean::inc(x_146);
if (lean::is_exclusive(x_145)) {
 lean::cnstr_release(x_145, 0);
 lean::cnstr_release(x_145, 1);
 x_147 = x_145;
} else {
 lean::dec_ref(x_145);
 x_147 = lean::box(0);
}
if (lean::is_scalar(x_147)) {
 x_148 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_148 = x_147;
}
lean::cnstr_set(x_148, 0, x_132);
lean::cnstr_set(x_148, 1, x_146);
return x_148;
}
else
{
obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
lean::dec(x_132);
x_149 = lean::cnstr_get(x_145, 0);
lean::inc(x_149);
x_150 = lean::cnstr_get(x_145, 1);
lean::inc(x_150);
if (lean::is_exclusive(x_145)) {
 lean::cnstr_release(x_145, 0);
 lean::cnstr_release(x_145, 1);
 x_151 = x_145;
} else {
 lean::dec_ref(x_145);
 x_151 = lean::box(0);
}
if (lean::is_scalar(x_151)) {
 x_152 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_152 = x_151;
}
lean::cnstr_set(x_152, 0, x_149);
lean::cnstr_set(x_152, 1, x_150);
return x_152;
}
}
else
{
obj* x_153; obj* x_154; obj* x_155; obj* x_156; 
lean::dec(x_134);
lean::dec(x_132);
x_153 = lean::cnstr_get(x_138, 0);
lean::inc(x_153);
x_154 = lean::cnstr_get(x_138, 1);
lean::inc(x_154);
if (lean::is_exclusive(x_138)) {
 lean::cnstr_release(x_138, 0);
 lean::cnstr_release(x_138, 1);
 x_155 = x_138;
} else {
 lean::dec_ref(x_138);
 x_155 = lean::box(0);
}
if (lean::is_scalar(x_155)) {
 x_156 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_156 = x_155;
}
lean::cnstr_set(x_156, 0, x_153);
lean::cnstr_set(x_156, 1, x_154);
return x_156;
}
}
else
{
obj* x_157; obj* x_158; obj* x_159; obj* x_160; 
lean::dec(x_132);
x_157 = lean::cnstr_get(x_133, 0);
lean::inc(x_157);
x_158 = lean::cnstr_get(x_133, 1);
lean::inc(x_158);
if (lean::is_exclusive(x_133)) {
 lean::cnstr_release(x_133, 0);
 lean::cnstr_release(x_133, 1);
 x_159 = x_133;
} else {
 lean::dec_ref(x_133);
 x_159 = lean::box(0);
}
if (lean::is_scalar(x_159)) {
 x_160 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_160 = x_159;
}
lean::cnstr_set(x_160, 0, x_157);
lean::cnstr_set(x_160, 1, x_158);
return x_160;
}
}
else
{
obj* x_161; obj* x_162; obj* x_163; obj* x_164; 
lean::dec(x_1);
x_161 = lean::cnstr_get(x_125, 0);
lean::inc(x_161);
x_162 = lean::cnstr_get(x_125, 1);
lean::inc(x_162);
if (lean::is_exclusive(x_125)) {
 lean::cnstr_release(x_125, 0);
 lean::cnstr_release(x_125, 1);
 x_163 = x_125;
} else {
 lean::dec_ref(x_125);
 x_163 = lean::box(0);
}
if (lean::is_scalar(x_163)) {
 x_164 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_164 = x_163;
}
lean::cnstr_set(x_164, 0, x_161);
lean::cnstr_set(x_164, 1, x_162);
return x_164;
}
}
}
}
else
{
uint8 x_165; 
lean::dec(x_1);
x_165 = !lean::is_exclusive(x_3);
if (x_165 == 0)
{
return x_3;
}
else
{
obj* x_166; obj* x_167; obj* x_168; 
x_166 = lean::cnstr_get(x_3, 0);
x_167 = lean::cnstr_get(x_3, 1);
lean::inc(x_167);
lean::inc(x_166);
lean::dec(x_3);
x_168 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_168, 0, x_166);
lean::cnstr_set(x_168, 1, x_167);
return x_168;
}
}
}
}
obj* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__5(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l___private_init_lean_environment_8__persistentEnvExtensionsRef;
x_4 = lean::io_ref_get(x_3, x_2);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::cnstr_get(x_4, 0);
x_7 = lean::mk_nat_obj(0u);
x_8 = l_Array_anyMAux___main___at_Lean_Compiler_mkSpecExtension___spec__6(x_1, x_6, x_7);
lean::dec(x_6);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_9 = lean::box(0);
lean::cnstr_set(x_4, 0, x_9);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
x_11 = l_Array_empty___closed__1;
lean::inc(x_10);
x_12 = lean::apply_1(x_10, x_11);
x_13 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_bind___rarg), 3, 2);
lean::closure_set(x_14, 0, x_12);
lean::closure_set(x_14, 1, x_13);
x_15 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7(x_14, x_4);
if (lean::obj_tag(x_15) == 0)
{
uint8 x_16; 
x_16 = !lean::is_exclusive(x_15);
if (x_16 == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_17 = lean::cnstr_get(x_15, 0);
lean::cnstr_set(x_15, 0, x_9);
x_18 = lean::cnstr_get(x_1, 0);
lean::inc(x_18);
x_19 = lean::cnstr_get(x_1, 2);
lean::inc(x_19);
x_20 = lean::cnstr_get(x_1, 3);
lean::inc(x_20);
x_21 = lean::cnstr_get(x_1, 4);
lean::inc(x_21);
lean::dec(x_1);
x_22 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_22, 0, x_17);
lean::cnstr_set(x_22, 1, x_18);
lean::cnstr_set(x_22, 2, x_10);
lean::cnstr_set(x_22, 3, x_19);
lean::cnstr_set(x_22, 4, x_20);
lean::cnstr_set(x_22, 5, x_21);
x_23 = lean::io_ref_get(x_3, x_15);
if (lean::obj_tag(x_23) == 0)
{
uint8 x_24; 
x_24 = !lean::is_exclusive(x_23);
if (x_24 == 0)
{
obj* x_25; obj* x_26; 
x_25 = lean::cnstr_get(x_23, 0);
lean::cnstr_set(x_23, 0, x_9);
x_26 = lean::io_ref_reset(x_3, x_23);
if (lean::obj_tag(x_26) == 0)
{
uint8 x_27; 
x_27 = !lean::is_exclusive(x_26);
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_28 = lean::cnstr_get(x_26, 0);
lean::dec(x_28);
lean::cnstr_set(x_26, 0, x_9);
x_29 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_22);
x_30 = x_22;
x_31 = lean::array_push(x_25, x_30);
x_32 = lean::io_ref_set(x_3, x_31, x_26);
if (lean::obj_tag(x_32) == 0)
{
uint8 x_33; 
x_33 = !lean::is_exclusive(x_32);
if (x_33 == 0)
{
obj* x_34; 
x_34 = lean::cnstr_get(x_32, 0);
lean::dec(x_34);
lean::cnstr_set(x_32, 0, x_22);
return x_32;
}
else
{
obj* x_35; obj* x_36; 
x_35 = lean::cnstr_get(x_32, 1);
lean::inc(x_35);
lean::dec(x_32);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_22);
lean::cnstr_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8 x_37; 
lean::dec(x_22);
x_37 = !lean::is_exclusive(x_32);
if (x_37 == 0)
{
return x_32;
}
else
{
obj* x_38; obj* x_39; obj* x_40; 
x_38 = lean::cnstr_get(x_32, 0);
x_39 = lean::cnstr_get(x_32, 1);
lean::inc(x_39);
lean::inc(x_38);
lean::dec(x_32);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_38);
lean::cnstr_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_41 = lean::cnstr_get(x_26, 1);
lean::inc(x_41);
lean::dec(x_26);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_9);
lean::cnstr_set(x_42, 1, x_41);
x_43 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_22);
x_44 = x_22;
x_45 = lean::array_push(x_25, x_44);
x_46 = lean::io_ref_set(x_3, x_45, x_42);
if (lean::obj_tag(x_46) == 0)
{
obj* x_47; obj* x_48; obj* x_49; 
x_47 = lean::cnstr_get(x_46, 1);
lean::inc(x_47);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 lean::cnstr_release(x_46, 1);
 x_48 = x_46;
} else {
 lean::dec_ref(x_46);
 x_48 = lean::box(0);
}
if (lean::is_scalar(x_48)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_48;
}
lean::cnstr_set(x_49, 0, x_22);
lean::cnstr_set(x_49, 1, x_47);
return x_49;
}
else
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_22);
x_50 = lean::cnstr_get(x_46, 0);
lean::inc(x_50);
x_51 = lean::cnstr_get(x_46, 1);
lean::inc(x_51);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 lean::cnstr_release(x_46, 1);
 x_52 = x_46;
} else {
 lean::dec_ref(x_46);
 x_52 = lean::box(0);
}
if (lean::is_scalar(x_52)) {
 x_53 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_53 = x_52;
}
lean::cnstr_set(x_53, 0, x_50);
lean::cnstr_set(x_53, 1, x_51);
return x_53;
}
}
}
else
{
uint8 x_54; 
lean::dec(x_25);
lean::dec(x_22);
x_54 = !lean::is_exclusive(x_26);
if (x_54 == 0)
{
return x_26;
}
else
{
obj* x_55; obj* x_56; obj* x_57; 
x_55 = lean::cnstr_get(x_26, 0);
x_56 = lean::cnstr_get(x_26, 1);
lean::inc(x_56);
lean::inc(x_55);
lean::dec(x_26);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_55);
lean::cnstr_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_58 = lean::cnstr_get(x_23, 0);
x_59 = lean::cnstr_get(x_23, 1);
lean::inc(x_59);
lean::inc(x_58);
lean::dec(x_23);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_9);
lean::cnstr_set(x_60, 1, x_59);
x_61 = lean::io_ref_reset(x_3, x_60);
if (lean::obj_tag(x_61) == 0)
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_62 = lean::cnstr_get(x_61, 1);
lean::inc(x_62);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_release(x_61, 0);
 lean::cnstr_release(x_61, 1);
 x_63 = x_61;
} else {
 lean::dec_ref(x_61);
 x_63 = lean::box(0);
}
if (lean::is_scalar(x_63)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_63;
}
lean::cnstr_set(x_64, 0, x_9);
lean::cnstr_set(x_64, 1, x_62);
x_65 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_22);
x_66 = x_22;
x_67 = lean::array_push(x_58, x_66);
x_68 = lean::io_ref_set(x_3, x_67, x_64);
if (lean::obj_tag(x_68) == 0)
{
obj* x_69; obj* x_70; obj* x_71; 
x_69 = lean::cnstr_get(x_68, 1);
lean::inc(x_69);
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 lean::cnstr_release(x_68, 1);
 x_70 = x_68;
} else {
 lean::dec_ref(x_68);
 x_70 = lean::box(0);
}
if (lean::is_scalar(x_70)) {
 x_71 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_71 = x_70;
}
lean::cnstr_set(x_71, 0, x_22);
lean::cnstr_set(x_71, 1, x_69);
return x_71;
}
else
{
obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
lean::dec(x_22);
x_72 = lean::cnstr_get(x_68, 0);
lean::inc(x_72);
x_73 = lean::cnstr_get(x_68, 1);
lean::inc(x_73);
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 lean::cnstr_release(x_68, 1);
 x_74 = x_68;
} else {
 lean::dec_ref(x_68);
 x_74 = lean::box(0);
}
if (lean::is_scalar(x_74)) {
 x_75 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_75 = x_74;
}
lean::cnstr_set(x_75, 0, x_72);
lean::cnstr_set(x_75, 1, x_73);
return x_75;
}
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_58);
lean::dec(x_22);
x_76 = lean::cnstr_get(x_61, 0);
lean::inc(x_76);
x_77 = lean::cnstr_get(x_61, 1);
lean::inc(x_77);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_release(x_61, 0);
 lean::cnstr_release(x_61, 1);
 x_78 = x_61;
} else {
 lean::dec_ref(x_61);
 x_78 = lean::box(0);
}
if (lean::is_scalar(x_78)) {
 x_79 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_79 = x_78;
}
lean::cnstr_set(x_79, 0, x_76);
lean::cnstr_set(x_79, 1, x_77);
return x_79;
}
}
}
else
{
uint8 x_80; 
lean::dec(x_22);
x_80 = !lean::is_exclusive(x_23);
if (x_80 == 0)
{
return x_23;
}
else
{
obj* x_81; obj* x_82; obj* x_83; 
x_81 = lean::cnstr_get(x_23, 0);
x_82 = lean::cnstr_get(x_23, 1);
lean::inc(x_82);
lean::inc(x_81);
lean::dec(x_23);
x_83 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_83, 0, x_81);
lean::cnstr_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_84 = lean::cnstr_get(x_15, 0);
x_85 = lean::cnstr_get(x_15, 1);
lean::inc(x_85);
lean::inc(x_84);
lean::dec(x_15);
x_86 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_86, 0, x_9);
lean::cnstr_set(x_86, 1, x_85);
x_87 = lean::cnstr_get(x_1, 0);
lean::inc(x_87);
x_88 = lean::cnstr_get(x_1, 2);
lean::inc(x_88);
x_89 = lean::cnstr_get(x_1, 3);
lean::inc(x_89);
x_90 = lean::cnstr_get(x_1, 4);
lean::inc(x_90);
lean::dec(x_1);
x_91 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_91, 0, x_84);
lean::cnstr_set(x_91, 1, x_87);
lean::cnstr_set(x_91, 2, x_10);
lean::cnstr_set(x_91, 3, x_88);
lean::cnstr_set(x_91, 4, x_89);
lean::cnstr_set(x_91, 5, x_90);
x_92 = lean::io_ref_get(x_3, x_86);
if (lean::obj_tag(x_92) == 0)
{
obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_93 = lean::cnstr_get(x_92, 0);
lean::inc(x_93);
x_94 = lean::cnstr_get(x_92, 1);
lean::inc(x_94);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 lean::cnstr_release(x_92, 1);
 x_95 = x_92;
} else {
 lean::dec_ref(x_92);
 x_95 = lean::box(0);
}
if (lean::is_scalar(x_95)) {
 x_96 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_96 = x_95;
}
lean::cnstr_set(x_96, 0, x_9);
lean::cnstr_set(x_96, 1, x_94);
x_97 = lean::io_ref_reset(x_3, x_96);
if (lean::obj_tag(x_97) == 0)
{
obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
x_98 = lean::cnstr_get(x_97, 1);
lean::inc(x_98);
if (lean::is_exclusive(x_97)) {
 lean::cnstr_release(x_97, 0);
 lean::cnstr_release(x_97, 1);
 x_99 = x_97;
} else {
 lean::dec_ref(x_97);
 x_99 = lean::box(0);
}
if (lean::is_scalar(x_99)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_99;
}
lean::cnstr_set(x_100, 0, x_9);
lean::cnstr_set(x_100, 1, x_98);
x_101 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_91);
x_102 = x_91;
x_103 = lean::array_push(x_93, x_102);
x_104 = lean::io_ref_set(x_3, x_103, x_100);
if (lean::obj_tag(x_104) == 0)
{
obj* x_105; obj* x_106; obj* x_107; 
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
lean::cnstr_set(x_107, 0, x_91);
lean::cnstr_set(x_107, 1, x_105);
return x_107;
}
else
{
obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
lean::dec(x_91);
x_108 = lean::cnstr_get(x_104, 0);
lean::inc(x_108);
x_109 = lean::cnstr_get(x_104, 1);
lean::inc(x_109);
if (lean::is_exclusive(x_104)) {
 lean::cnstr_release(x_104, 0);
 lean::cnstr_release(x_104, 1);
 x_110 = x_104;
} else {
 lean::dec_ref(x_104);
 x_110 = lean::box(0);
}
if (lean::is_scalar(x_110)) {
 x_111 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_111 = x_110;
}
lean::cnstr_set(x_111, 0, x_108);
lean::cnstr_set(x_111, 1, x_109);
return x_111;
}
}
else
{
obj* x_112; obj* x_113; obj* x_114; obj* x_115; 
lean::dec(x_93);
lean::dec(x_91);
x_112 = lean::cnstr_get(x_97, 0);
lean::inc(x_112);
x_113 = lean::cnstr_get(x_97, 1);
lean::inc(x_113);
if (lean::is_exclusive(x_97)) {
 lean::cnstr_release(x_97, 0);
 lean::cnstr_release(x_97, 1);
 x_114 = x_97;
} else {
 lean::dec_ref(x_97);
 x_114 = lean::box(0);
}
if (lean::is_scalar(x_114)) {
 x_115 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_115 = x_114;
}
lean::cnstr_set(x_115, 0, x_112);
lean::cnstr_set(x_115, 1, x_113);
return x_115;
}
}
else
{
obj* x_116; obj* x_117; obj* x_118; obj* x_119; 
lean::dec(x_91);
x_116 = lean::cnstr_get(x_92, 0);
lean::inc(x_116);
x_117 = lean::cnstr_get(x_92, 1);
lean::inc(x_117);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 lean::cnstr_release(x_92, 1);
 x_118 = x_92;
} else {
 lean::dec_ref(x_92);
 x_118 = lean::box(0);
}
if (lean::is_scalar(x_118)) {
 x_119 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_119 = x_118;
}
lean::cnstr_set(x_119, 0, x_116);
lean::cnstr_set(x_119, 1, x_117);
return x_119;
}
}
}
else
{
uint8 x_120; 
lean::dec(x_10);
lean::dec(x_1);
x_120 = !lean::is_exclusive(x_15);
if (x_120 == 0)
{
return x_15;
}
else
{
obj* x_121; obj* x_122; obj* x_123; 
x_121 = lean::cnstr_get(x_15, 0);
x_122 = lean::cnstr_get(x_15, 1);
lean::inc(x_122);
lean::inc(x_121);
lean::dec(x_15);
x_123 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_123, 0, x_121);
lean::cnstr_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; 
x_124 = lean::cnstr_get(x_1, 0);
lean::inc(x_124);
lean::dec(x_1);
x_125 = l_Lean_Name_toString___closed__1;
x_126 = l_Lean_Name_toStringWithSep___main(x_125, x_124);
x_127 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_128 = lean::string_append(x_127, x_126);
lean::dec(x_126);
x_129 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_130 = lean::string_append(x_128, x_129);
lean::cnstr_set_tag(x_4, 1);
lean::cnstr_set(x_4, 0, x_130);
return x_4;
}
}
else
{
obj* x_131; obj* x_132; obj* x_133; uint8 x_134; 
x_131 = lean::cnstr_get(x_4, 0);
x_132 = lean::cnstr_get(x_4, 1);
lean::inc(x_132);
lean::inc(x_131);
lean::dec(x_4);
x_133 = lean::mk_nat_obj(0u);
x_134 = l_Array_anyMAux___main___at_Lean_Compiler_mkSpecExtension___spec__6(x_1, x_131, x_133);
lean::dec(x_131);
if (x_134 == 0)
{
obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; 
x_135 = lean::box(0);
x_136 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_136, 0, x_135);
lean::cnstr_set(x_136, 1, x_132);
x_137 = lean::cnstr_get(x_1, 1);
lean::inc(x_137);
x_138 = l_Array_empty___closed__1;
lean::inc(x_137);
x_139 = lean::apply_1(x_137, x_138);
x_140 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_141 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_bind___rarg), 3, 2);
lean::closure_set(x_141, 0, x_139);
lean::closure_set(x_141, 1, x_140);
x_142 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7(x_141, x_136);
if (lean::obj_tag(x_142) == 0)
{
obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
x_143 = lean::cnstr_get(x_142, 0);
lean::inc(x_143);
x_144 = lean::cnstr_get(x_142, 1);
lean::inc(x_144);
if (lean::is_exclusive(x_142)) {
 lean::cnstr_release(x_142, 0);
 lean::cnstr_release(x_142, 1);
 x_145 = x_142;
} else {
 lean::dec_ref(x_142);
 x_145 = lean::box(0);
}
if (lean::is_scalar(x_145)) {
 x_146 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_146 = x_145;
}
lean::cnstr_set(x_146, 0, x_135);
lean::cnstr_set(x_146, 1, x_144);
x_147 = lean::cnstr_get(x_1, 0);
lean::inc(x_147);
x_148 = lean::cnstr_get(x_1, 2);
lean::inc(x_148);
x_149 = lean::cnstr_get(x_1, 3);
lean::inc(x_149);
x_150 = lean::cnstr_get(x_1, 4);
lean::inc(x_150);
lean::dec(x_1);
x_151 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_151, 0, x_143);
lean::cnstr_set(x_151, 1, x_147);
lean::cnstr_set(x_151, 2, x_137);
lean::cnstr_set(x_151, 3, x_148);
lean::cnstr_set(x_151, 4, x_149);
lean::cnstr_set(x_151, 5, x_150);
x_152 = lean::io_ref_get(x_3, x_146);
if (lean::obj_tag(x_152) == 0)
{
obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; 
x_153 = lean::cnstr_get(x_152, 0);
lean::inc(x_153);
x_154 = lean::cnstr_get(x_152, 1);
lean::inc(x_154);
if (lean::is_exclusive(x_152)) {
 lean::cnstr_release(x_152, 0);
 lean::cnstr_release(x_152, 1);
 x_155 = x_152;
} else {
 lean::dec_ref(x_152);
 x_155 = lean::box(0);
}
if (lean::is_scalar(x_155)) {
 x_156 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_156 = x_155;
}
lean::cnstr_set(x_156, 0, x_135);
lean::cnstr_set(x_156, 1, x_154);
x_157 = lean::io_ref_reset(x_3, x_156);
if (lean::obj_tag(x_157) == 0)
{
obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; 
x_158 = lean::cnstr_get(x_157, 1);
lean::inc(x_158);
if (lean::is_exclusive(x_157)) {
 lean::cnstr_release(x_157, 0);
 lean::cnstr_release(x_157, 1);
 x_159 = x_157;
} else {
 lean::dec_ref(x_157);
 x_159 = lean::box(0);
}
if (lean::is_scalar(x_159)) {
 x_160 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_160 = x_159;
}
lean::cnstr_set(x_160, 0, x_135);
lean::cnstr_set(x_160, 1, x_158);
x_161 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_151);
x_162 = x_151;
x_163 = lean::array_push(x_153, x_162);
x_164 = lean::io_ref_set(x_3, x_163, x_160);
if (lean::obj_tag(x_164) == 0)
{
obj* x_165; obj* x_166; obj* x_167; 
x_165 = lean::cnstr_get(x_164, 1);
lean::inc(x_165);
if (lean::is_exclusive(x_164)) {
 lean::cnstr_release(x_164, 0);
 lean::cnstr_release(x_164, 1);
 x_166 = x_164;
} else {
 lean::dec_ref(x_164);
 x_166 = lean::box(0);
}
if (lean::is_scalar(x_166)) {
 x_167 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_167 = x_166;
}
lean::cnstr_set(x_167, 0, x_151);
lean::cnstr_set(x_167, 1, x_165);
return x_167;
}
else
{
obj* x_168; obj* x_169; obj* x_170; obj* x_171; 
lean::dec(x_151);
x_168 = lean::cnstr_get(x_164, 0);
lean::inc(x_168);
x_169 = lean::cnstr_get(x_164, 1);
lean::inc(x_169);
if (lean::is_exclusive(x_164)) {
 lean::cnstr_release(x_164, 0);
 lean::cnstr_release(x_164, 1);
 x_170 = x_164;
} else {
 lean::dec_ref(x_164);
 x_170 = lean::box(0);
}
if (lean::is_scalar(x_170)) {
 x_171 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_171 = x_170;
}
lean::cnstr_set(x_171, 0, x_168);
lean::cnstr_set(x_171, 1, x_169);
return x_171;
}
}
else
{
obj* x_172; obj* x_173; obj* x_174; obj* x_175; 
lean::dec(x_153);
lean::dec(x_151);
x_172 = lean::cnstr_get(x_157, 0);
lean::inc(x_172);
x_173 = lean::cnstr_get(x_157, 1);
lean::inc(x_173);
if (lean::is_exclusive(x_157)) {
 lean::cnstr_release(x_157, 0);
 lean::cnstr_release(x_157, 1);
 x_174 = x_157;
} else {
 lean::dec_ref(x_157);
 x_174 = lean::box(0);
}
if (lean::is_scalar(x_174)) {
 x_175 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_175 = x_174;
}
lean::cnstr_set(x_175, 0, x_172);
lean::cnstr_set(x_175, 1, x_173);
return x_175;
}
}
else
{
obj* x_176; obj* x_177; obj* x_178; obj* x_179; 
lean::dec(x_151);
x_176 = lean::cnstr_get(x_152, 0);
lean::inc(x_176);
x_177 = lean::cnstr_get(x_152, 1);
lean::inc(x_177);
if (lean::is_exclusive(x_152)) {
 lean::cnstr_release(x_152, 0);
 lean::cnstr_release(x_152, 1);
 x_178 = x_152;
} else {
 lean::dec_ref(x_152);
 x_178 = lean::box(0);
}
if (lean::is_scalar(x_178)) {
 x_179 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_179 = x_178;
}
lean::cnstr_set(x_179, 0, x_176);
lean::cnstr_set(x_179, 1, x_177);
return x_179;
}
}
else
{
obj* x_180; obj* x_181; obj* x_182; obj* x_183; 
lean::dec(x_137);
lean::dec(x_1);
x_180 = lean::cnstr_get(x_142, 0);
lean::inc(x_180);
x_181 = lean::cnstr_get(x_142, 1);
lean::inc(x_181);
if (lean::is_exclusive(x_142)) {
 lean::cnstr_release(x_142, 0);
 lean::cnstr_release(x_142, 1);
 x_182 = x_142;
} else {
 lean::dec_ref(x_142);
 x_182 = lean::box(0);
}
if (lean::is_scalar(x_182)) {
 x_183 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_183 = x_182;
}
lean::cnstr_set(x_183, 0, x_180);
lean::cnstr_set(x_183, 1, x_181);
return x_183;
}
}
else
{
obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; 
x_184 = lean::cnstr_get(x_1, 0);
lean::inc(x_184);
lean::dec(x_1);
x_185 = l_Lean_Name_toString___closed__1;
x_186 = l_Lean_Name_toStringWithSep___main(x_185, x_184);
x_187 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_188 = lean::string_append(x_187, x_186);
lean::dec(x_186);
x_189 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_190 = lean::string_append(x_188, x_189);
x_191 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_191, 0, x_190);
lean::cnstr_set(x_191, 1, x_132);
return x_191;
}
}
}
else
{
uint8 x_192; 
lean::dec(x_1);
x_192 = !lean::is_exclusive(x_4);
if (x_192 == 0)
{
return x_4;
}
else
{
obj* x_193; obj* x_194; obj* x_195; 
x_193 = lean::cnstr_get(x_4, 0);
x_194 = lean::cnstr_get(x_4, 1);
lean::inc(x_194);
lean::inc(x_193);
lean::dec(x_4);
x_195 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_195, 0, x_193);
lean::cnstr_set(x_195, 1, x_194);
return x_195;
}
}
}
}
obj* l_Lean_registerSimplePersistentEnvExtension___at_Lean_Compiler_mkSpecExtension___spec__4(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1), 3, 1);
lean::closure_set(x_4, 0, x_1);
lean::inc(x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__2), 3, 1);
lean::closure_set(x_5, 0, x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__3), 2, 1);
lean::closure_set(x_6, 0, x_1);
x_7 = l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1;
x_8 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_8, 0, x_3);
lean::cnstr_set(x_8, 1, x_4);
lean::cnstr_set(x_8, 2, x_5);
lean::cnstr_set(x_8, 3, x_6);
lean::cnstr_set(x_8, 4, x_7);
x_9 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__5(x_8, x_2);
return x_9;
}
}
obj* l_Lean_Compiler_mkSpecExtension___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::mk_nat_obj(0u);
x_3 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__3;
x_4 = l_Array_miterateAux___main___at_Lean_Compiler_mkSpecExtension___spec__3(x_1, x_1, x_2, x_3);
x_5 = l_Lean_Compiler_SpecState_switch___main(x_4);
return x_5;
}
}
obj* _init_l_Lean_Compiler_mkSpecExtension___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_SpecState_addEntry), 2, 0);
return x_1;
}
}
obj* _init_l_Lean_Compiler_mkSpecExtension___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_mkSpecExtension___lambda__1___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_Compiler_mkSpecExtension___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Compiler_mkSpecializeAttrs___closed__4;
x_2 = l_Lean_Compiler_mkSpecExtension___closed__1;
x_3 = l_Lean_Compiler_mkSpecExtension___closed__2;
x_4 = l_Lean_regNamespacesExtension___closed__5;
x_5 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_4);
return x_5;
}
}
obj* l_Lean_Compiler_mkSpecExtension(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Compiler_mkSpecExtension___closed__3;
x_3 = l_Lean_registerSimplePersistentEnvExtension___at_Lean_Compiler_mkSpecExtension___spec__4(x_2, x_1);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Lean_Compiler_mkSpecExtension___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_Compiler_mkSpecExtension___spec__2(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Array_miterateAux___main___at_Lean_Compiler_mkSpecExtension___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_Compiler_mkSpecExtension___spec__3(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_mkStateFromImportedEntries___at_Lean_Compiler_mkSpecExtension___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_mkStateFromImportedEntries___at_Lean_Compiler_mkSpecExtension___spec__1(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_anyMAux___main___at_Lean_Compiler_mkSpecExtension___spec__6___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_Array_anyMAux___main___at_Lean_Compiler_mkSpecExtension___spec__6(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_Lean_Compiler_mkSpecExtension___lambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Compiler_mkSpecExtension___lambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Compiler_specExtension___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
}
obj* l_Lean_Compiler_specExtension___elambda__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_empty___closed__1;
return x_2;
}
}
obj* l_Lean_Compiler_specExtension___elambda__3(obj* x_1, obj* x_2) {
_start:
{
lean::inc(x_1);
return x_1;
}
}
obj* l_Lean_Compiler_specExtension___elambda__4___rarg(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 0);
lean::dec(x_3);
x_4 = l_String_splitAux___main___closed__1;
lean::cnstr_set_tag(x_1, 1);
lean::cnstr_set(x_1, 0, x_4);
return x_1;
}
else
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_6 = l_String_splitAux___main___closed__1;
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_5);
return x_7;
}
}
}
obj* l_Lean_Compiler_specExtension___elambda__4(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_specExtension___elambda__4___rarg), 1, 0);
return x_2;
}
}
obj* _init_l_Lean_Compiler_specExtension___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::mk_nat_obj(0u);
x_2 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_3 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__5;
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 2, x_3);
return x_4;
}
}
obj* _init_l_Lean_Compiler_specExtension___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_specExtension___elambda__4___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_Compiler_specExtension___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_specExtension___elambda__3___boxed), 2, 0);
return x_1;
}
}
obj* _init_l_Lean_Compiler_specExtension___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_specExtension___elambda__2___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_Compiler_specExtension___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Compiler_specExtension___elambda__1___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_Compiler_specExtension___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = l_Lean_Compiler_specExtension___closed__1;
x_2 = lean::box(0);
x_3 = l_Lean_Compiler_specExtension___closed__2;
x_4 = l_Lean_Compiler_specExtension___closed__3;
x_5 = l_Lean_Compiler_specExtension___closed__4;
x_6 = l_Lean_Compiler_specExtension___closed__5;
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
obj* l_Lean_Compiler_specExtension___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Compiler_specExtension___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Compiler_specExtension___elambda__2___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Compiler_specExtension___elambda__2(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Compiler_specExtension___elambda__3___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Compiler_specExtension___elambda__3(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Compiler_specExtension___elambda__4___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Compiler_specExtension___elambda__4(x_1);
lean::dec(x_1);
return x_2;
}
}
namespace lean {
obj* add_specialization_info_core(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
x_5 = l_Lean_Compiler_specExtension;
x_6 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_5, x_1, x_4);
return x_6;
}
}
}
obj* l_RBNode_find___main___at_Lean_Compiler_getSpecializationInfo___spec__2(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_7 = lean::cnstr_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8 x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
obj* x_10; 
lean::inc(x_6);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_6);
return x_10;
}
else
{
x_1 = x_7;
goto _start;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
obj* l_AssocList_find___main___at_Lean_Compiler_getSpecializationInfo___spec__4(obj* x_1, obj* x_2) {
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
obj* l_HashMapImp_find___at_Lean_Compiler_getSpecializationInfo___spec__3(obj* x_1, obj* x_2) {
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
x_10 = l_AssocList_find___main___at_Lean_Compiler_getSpecializationInfo___spec__4(x_2, x_9);
lean::dec(x_9);
return x_10;
}
}
obj* l_Lean_SMap_find___main___at_Lean_Compiler_getSpecializationInfo___spec__1(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = l_RBNode_find___main___at_Lean_Compiler_getSpecializationInfo___spec__2(x_5, x_2);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; 
x_7 = l_HashMapImp_find___at_Lean_Compiler_getSpecializationInfo___spec__3(x_4, x_2);
return x_7;
}
else
{
return x_6;
}
}
else
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = l_HashMapImp_find___at_Lean_Compiler_getSpecializationInfo___spec__3(x_8, x_2);
return x_9;
}
}
}
namespace lean {
obj* get_specialization_info_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_Lean_Compiler_specExtension;
x_4 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_3, x_1);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_6 = l_Lean_SMap_find___main___at_Lean_Compiler_getSpecializationInfo___spec__1(x_5, x_2);
lean::dec(x_2);
lean::dec(x_5);
return x_6;
}
}
}
obj* l_RBNode_find___main___at_Lean_Compiler_getSpecializationInfo___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___at_Lean_Compiler_getSpecializationInfo___spec__2(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_AssocList_find___main___at_Lean_Compiler_getSpecializationInfo___spec__4___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_AssocList_find___main___at_Lean_Compiler_getSpecializationInfo___spec__4(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_HashMapImp_find___at_Lean_Compiler_getSpecializationInfo___spec__3___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_HashMapImp_find___at_Lean_Compiler_getSpecializationInfo___spec__3(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_SMap_find___main___at_Lean_Compiler_getSpecializationInfo___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_SMap_find___main___at_Lean_Compiler_getSpecializationInfo___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
namespace lean {
obj* cache_specialization_core(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
x_5 = l_Lean_Compiler_specExtension;
x_6 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_5, x_1, x_4);
return x_6;
}
}
}
obj* l_RBNode_find___main___at_Lean_Compiler_getCachedSpecialization___spec__2(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_7 = lean::cnstr_get(x_1, 3);
x_8 = lean_expr_quick_lt(x_2, x_5);
if (x_8 == 0)
{
uint8 x_9; 
x_9 = lean_expr_quick_lt(x_5, x_2);
if (x_9 == 0)
{
obj* x_10; 
lean::inc(x_6);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_6);
return x_10;
}
else
{
x_1 = x_7;
goto _start;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
obj* l_AssocList_find___main___at_Lean_Compiler_getCachedSpecialization___spec__4(obj* x_1, obj* x_2) {
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
x_7 = lean_expr_eqv(x_4, x_1);
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
obj* l_HashMapImp_find___at_Lean_Compiler_getCachedSpecialization___spec__3(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; usize x_5; usize x_6; obj* x_7; usize x_8; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::array_get_size(x_3);
x_5 = lean_expr_hash(x_2);
x_6 = lean::usize_modn(x_5, x_4);
lean::dec(x_4);
x_7 = lean::box_size_t(x_6);
x_8 = lean::unbox_size_t(x_7);
lean::dec(x_7);
x_9 = lean::array_uget(x_3, x_8);
x_10 = l_AssocList_find___main___at_Lean_Compiler_getCachedSpecialization___spec__4(x_2, x_9);
lean::dec(x_9);
return x_10;
}
}
obj* l_Lean_SMap_find___main___at_Lean_Compiler_getCachedSpecialization___spec__1(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = l_RBNode_find___main___at_Lean_Compiler_getCachedSpecialization___spec__2(x_5, x_2);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; 
x_7 = l_HashMapImp_find___at_Lean_Compiler_getCachedSpecialization___spec__3(x_4, x_2);
return x_7;
}
else
{
return x_6;
}
}
else
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = l_HashMapImp_find___at_Lean_Compiler_getCachedSpecialization___spec__3(x_8, x_2);
return x_9;
}
}
}
namespace lean {
obj* get_cached_specialization_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_Lean_Compiler_specExtension;
x_4 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_3, x_1);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_6 = l_Lean_SMap_find___main___at_Lean_Compiler_getCachedSpecialization___spec__1(x_5, x_2);
lean::dec(x_2);
lean::dec(x_5);
return x_6;
}
}
}
obj* l_RBNode_find___main___at_Lean_Compiler_getCachedSpecialization___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___at_Lean_Compiler_getCachedSpecialization___spec__2(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_AssocList_find___main___at_Lean_Compiler_getCachedSpecialization___spec__4___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_AssocList_find___main___at_Lean_Compiler_getCachedSpecialization___spec__4(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_HashMapImp_find___at_Lean_Compiler_getCachedSpecialization___spec__3___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_HashMapImp_find___at_Lean_Compiler_getCachedSpecialization___spec__3(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_SMap_find___main___at_Lean_Compiler_getCachedSpecialization___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_SMap_find___main___at_Lean_Compiler_getCachedSpecialization___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* initialize_init_lean_attributes(obj*);
obj* initialize_init_lean_compiler_util(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_specialize(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_attributes(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_util(w);
if (io_result_is_error(w)) return w;
l_Lean_Compiler_SpecializeAttributeKind_Inhabited = _init_l_Lean_Compiler_SpecializeAttributeKind_Inhabited();
l_Lean_Compiler_SpecializeAttributeKind_HasBeq___closed__1 = _init_l_Lean_Compiler_SpecializeAttributeKind_HasBeq___closed__1();
lean::mark_persistent(l_Lean_Compiler_SpecializeAttributeKind_HasBeq___closed__1);
l_Lean_Compiler_SpecializeAttributeKind_HasBeq = _init_l_Lean_Compiler_SpecializeAttributeKind_HasBeq();
lean::mark_persistent(l_Lean_Compiler_SpecializeAttributeKind_HasBeq);
l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__4___closed__1 = _init_l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__4___closed__1();
lean::mark_persistent(l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_Compiler_mkSpecializeAttrs___spec__4___closed__1);
l_Lean_registerEnumAttributes___at_Lean_Compiler_mkSpecializeAttrs___spec__1___closed__1 = _init_l_Lean_registerEnumAttributes___at_Lean_Compiler_mkSpecializeAttrs___spec__1___closed__1();
lean::mark_persistent(l_Lean_registerEnumAttributes___at_Lean_Compiler_mkSpecializeAttrs___spec__1___closed__1);
l_Lean_registerEnumAttributes___at_Lean_Compiler_mkSpecializeAttrs___spec__1___closed__2 = _init_l_Lean_registerEnumAttributes___at_Lean_Compiler_mkSpecializeAttrs___spec__1___closed__2();
lean::mark_persistent(l_Lean_registerEnumAttributes___at_Lean_Compiler_mkSpecializeAttrs___spec__1___closed__2);
l_Lean_Compiler_mkSpecializeAttrs___closed__1 = _init_l_Lean_Compiler_mkSpecializeAttrs___closed__1();
lean::mark_persistent(l_Lean_Compiler_mkSpecializeAttrs___closed__1);
l_Lean_Compiler_mkSpecializeAttrs___closed__2 = _init_l_Lean_Compiler_mkSpecializeAttrs___closed__2();
lean::mark_persistent(l_Lean_Compiler_mkSpecializeAttrs___closed__2);
l_Lean_Compiler_mkSpecializeAttrs___closed__3 = _init_l_Lean_Compiler_mkSpecializeAttrs___closed__3();
lean::mark_persistent(l_Lean_Compiler_mkSpecializeAttrs___closed__3);
l_Lean_Compiler_mkSpecializeAttrs___closed__4 = _init_l_Lean_Compiler_mkSpecializeAttrs___closed__4();
lean::mark_persistent(l_Lean_Compiler_mkSpecializeAttrs___closed__4);
l_Lean_Compiler_mkSpecializeAttrs___closed__5 = _init_l_Lean_Compiler_mkSpecializeAttrs___closed__5();
lean::mark_persistent(l_Lean_Compiler_mkSpecializeAttrs___closed__5);
l_Lean_Compiler_mkSpecializeAttrs___closed__6 = _init_l_Lean_Compiler_mkSpecializeAttrs___closed__6();
lean::mark_persistent(l_Lean_Compiler_mkSpecializeAttrs___closed__6);
l_Lean_Compiler_mkSpecializeAttrs___closed__7 = _init_l_Lean_Compiler_mkSpecializeAttrs___closed__7();
lean::mark_persistent(l_Lean_Compiler_mkSpecializeAttrs___closed__7);
l_Lean_Compiler_mkSpecializeAttrs___closed__8 = _init_l_Lean_Compiler_mkSpecializeAttrs___closed__8();
lean::mark_persistent(l_Lean_Compiler_mkSpecializeAttrs___closed__8);
l_Lean_Compiler_mkSpecializeAttrs___closed__9 = _init_l_Lean_Compiler_mkSpecializeAttrs___closed__9();
lean::mark_persistent(l_Lean_Compiler_mkSpecializeAttrs___closed__9);
l_Lean_Compiler_mkSpecializeAttrs___closed__10 = _init_l_Lean_Compiler_mkSpecializeAttrs___closed__10();
lean::mark_persistent(l_Lean_Compiler_mkSpecializeAttrs___closed__10);
l_Lean_Compiler_mkSpecializeAttrs___closed__11 = _init_l_Lean_Compiler_mkSpecializeAttrs___closed__11();
lean::mark_persistent(l_Lean_Compiler_mkSpecializeAttrs___closed__11);
l_Lean_Compiler_mkSpecializeAttrs___closed__12 = _init_l_Lean_Compiler_mkSpecializeAttrs___closed__12();
lean::mark_persistent(l_Lean_Compiler_mkSpecializeAttrs___closed__12);
l_Lean_Compiler_mkSpecializeAttrs___closed__13 = _init_l_Lean_Compiler_mkSpecializeAttrs___closed__13();
lean::mark_persistent(l_Lean_Compiler_mkSpecializeAttrs___closed__13);
l_Lean_Compiler_mkSpecializeAttrs___closed__14 = _init_l_Lean_Compiler_mkSpecializeAttrs___closed__14();
lean::mark_persistent(l_Lean_Compiler_mkSpecializeAttrs___closed__14);
l_Lean_Compiler_mkSpecializeAttrs___closed__15 = _init_l_Lean_Compiler_mkSpecializeAttrs___closed__15();
lean::mark_persistent(l_Lean_Compiler_mkSpecializeAttrs___closed__15);
w = l_Lean_Compiler_mkSpecializeAttrs(w);
if (io_result_is_error(w)) return w;
l_Lean_Compiler_specializeAttrs = io_result_get_value(w);
lean::mark_persistent(l_Lean_Compiler_specializeAttrs);
l_Lean_Compiler_SpecState_Inhabited___closed__1 = _init_l_Lean_Compiler_SpecState_Inhabited___closed__1();
lean::mark_persistent(l_Lean_Compiler_SpecState_Inhabited___closed__1);
l_Lean_Compiler_SpecState_Inhabited___closed__2 = _init_l_Lean_Compiler_SpecState_Inhabited___closed__2();
lean::mark_persistent(l_Lean_Compiler_SpecState_Inhabited___closed__2);
l_Lean_Compiler_SpecState_Inhabited___closed__3 = _init_l_Lean_Compiler_SpecState_Inhabited___closed__3();
lean::mark_persistent(l_Lean_Compiler_SpecState_Inhabited___closed__3);
l_Lean_Compiler_SpecState_Inhabited___closed__4 = _init_l_Lean_Compiler_SpecState_Inhabited___closed__4();
lean::mark_persistent(l_Lean_Compiler_SpecState_Inhabited___closed__4);
l_Lean_Compiler_SpecState_Inhabited___closed__5 = _init_l_Lean_Compiler_SpecState_Inhabited___closed__5();
lean::mark_persistent(l_Lean_Compiler_SpecState_Inhabited___closed__5);
l_Lean_Compiler_SpecState_Inhabited___closed__6 = _init_l_Lean_Compiler_SpecState_Inhabited___closed__6();
lean::mark_persistent(l_Lean_Compiler_SpecState_Inhabited___closed__6);
l_Lean_Compiler_SpecState_Inhabited = _init_l_Lean_Compiler_SpecState_Inhabited();
lean::mark_persistent(l_Lean_Compiler_SpecState_Inhabited);
l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__1 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__1();
lean::mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__1);
l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__2 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__2();
lean::mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__2);
l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__3 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__3();
lean::mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__3);
l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__4 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__4();
lean::mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__4);
l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__5 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__5();
lean::mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_Compiler_mkSpecExtension___spec__7___closed__5);
l_Lean_Compiler_mkSpecExtension___closed__1 = _init_l_Lean_Compiler_mkSpecExtension___closed__1();
lean::mark_persistent(l_Lean_Compiler_mkSpecExtension___closed__1);
l_Lean_Compiler_mkSpecExtension___closed__2 = _init_l_Lean_Compiler_mkSpecExtension___closed__2();
lean::mark_persistent(l_Lean_Compiler_mkSpecExtension___closed__2);
l_Lean_Compiler_mkSpecExtension___closed__3 = _init_l_Lean_Compiler_mkSpecExtension___closed__3();
lean::mark_persistent(l_Lean_Compiler_mkSpecExtension___closed__3);
l_Lean_Compiler_specExtension___closed__1 = _init_l_Lean_Compiler_specExtension___closed__1();
lean::mark_persistent(l_Lean_Compiler_specExtension___closed__1);
l_Lean_Compiler_specExtension___closed__2 = _init_l_Lean_Compiler_specExtension___closed__2();
lean::mark_persistent(l_Lean_Compiler_specExtension___closed__2);
l_Lean_Compiler_specExtension___closed__3 = _init_l_Lean_Compiler_specExtension___closed__3();
lean::mark_persistent(l_Lean_Compiler_specExtension___closed__3);
l_Lean_Compiler_specExtension___closed__4 = _init_l_Lean_Compiler_specExtension___closed__4();
lean::mark_persistent(l_Lean_Compiler_specExtension___closed__4);
l_Lean_Compiler_specExtension___closed__5 = _init_l_Lean_Compiler_specExtension___closed__5();
lean::mark_persistent(l_Lean_Compiler_specExtension___closed__5);
l_Lean_Compiler_specExtension___closed__6 = _init_l_Lean_Compiler_specExtension___closed__6();
lean::mark_persistent(l_Lean_Compiler_specExtension___closed__6);
w = l_Lean_Compiler_mkSpecExtension(w);
if (io_result_is_error(w)) return w;
l_Lean_Compiler_specExtension = io_result_get_value(w);
lean::mark_persistent(l_Lean_Compiler_specExtension);
return w;
}

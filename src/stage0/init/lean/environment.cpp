// Lean compiler output
// Module: init.lean.environment
// Imports: init.system.io init.util init.data.bytearray.default init.lean.declaration init.lean.smap init.lean.path init.lean.localcontext
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
obj* l_Lean_EnvExtension_modifyState___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_environment_9__getEntriesFor___main___closed__1;
obj* l_Lean_Environment_getModuleIdxFor___boxed(obj*, obj*);
obj* l_unsafeCast(obj*, obj*, obj*, obj*);
obj* l_Lean_EnvExtension_setStateUnsafe___rarg___boxed(obj*, obj*, obj*);
obj* l_mkHashMap___at_Lean_Environment_Inhabited___spec__1(obj*);
obj* l___private_init_lean_environment_7__mkPersistentEnvExtensionsRef(obj*);
obj* l_Lean_namespacesExt___closed__1;
obj* l_Lean_ConstantInfo_name(obj*);
obj* l_Lean_PersistentEnvExtension_inhabited(obj*, obj*);
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
obj* lean_write_module(obj*, obj*, obj*);
obj* l_Lean_Environment_displayStats___closed__7;
obj* l_Lean_Environment_displayStats___closed__6;
obj* l_Lean_ModuleData_inhabited___closed__1;
obj* l_Lean_performModifications___boxed(obj*, obj*, obj*);
obj* l_Lean_namespacesExt___elambda__4(obj*);
uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__12___boxed(obj*, obj*, obj*, obj*, obj*);
obj* lean_environment_set_main_module(obj*, obj*);
obj* l_Lean_PersistentEnvExtension_inhabited___rarg(obj*);
uint8 l_Array_anyMAux___main___at_Lean_regNamespacesExtension___spec__6(obj*, obj*, obj*);
obj* lean_environment_main_module(obj*);
obj* l_Lean_namespacesExt___elambda__1___boxed(obj*);
obj* l_HashMapImp_find___at_Lean_Environment_find___spec__2___boxed(obj*, obj*);
obj* l_Lean_EnvExtension_modifyStateUnsafe___rarg(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__8___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Environment_displayStats___closed__4;
extern obj* l_Nat_Inhabited;
obj* l_Lean_mkStateFromImportedEntries___rarg(obj*, obj*, obj*);
obj* l_Lean_regNamespacesExtension___lambda__3(obj*);
obj* l_Lean_EnvExtension_Inhabited___rarg(obj*);
obj* l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(obj*);
extern obj* l_Array_empty___closed__1;
obj* lean_nat_sub(obj*, obj*);
obj* l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
obj* l_Lean_importModulesAux(obj*, obj*, obj*);
obj* l_Lean_Format_pretty(obj*, obj*);
obj* l_Lean_EnvExtension_getState(obj*);
obj* l_Lean_namespacesExt___elambda__2___boxed(obj*);
obj* l_Lean_isNamespace___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__9(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Environment_addAux(obj*, obj*);
obj* l_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__6___boxed(obj*);
obj* l_Lean_PersistentEnvExtension_setState___rarg(obj*, obj*, obj*);
obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
obj* l_Array_mkArray(obj*, obj*, obj*);
uint32 lean_environment_trust_level(obj*);
extern obj* l_List_repr___rarg___closed__3;
obj* l_Lean_registerSimplePersistentEnvExtension(obj*, obj*);
obj* l_HashMapImp_insert___at_Lean_Environment_addAux___spec__4(obj*, obj*, obj*);
obj* lean_environment_add_modification(obj*, obj*);
obj* l_Lean_EnvExtension_Inhabited___rarg___closed__1;
obj* l_List_lengthAux___main___rarg(obj*, obj*);
obj* l_Lean_Environment_displayStats___closed__5;
obj* l_Array_miterateAux___main___at___private_init_lean_environment_11__finalizePersistentExtensions___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_PersistentEnvExtension_getModuleEntries___rarg___boxed(obj*, obj*, obj*);
obj* lean_environment_mark_quot_init(obj*);
obj* l_Lean_namespacesExt___elambda__3(obj*, obj*);
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__9___closed__1;
obj* l_Lean_mkStateFromImportedEntries___at_Lean_regNamespacesExtension___spec__1___boxed(obj*, obj*);
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__1___boxed(obj*, obj*);
obj* l_Lean_namespacesExt___elambda__1(obj*);
obj* l_Lean_EnvExtension_getStateUnsafe___rarg(obj*, obj*);
obj* l_AssocList_replace___main___at_Lean_importModules___spec__6(obj*, obj*, obj*);
obj* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__5(obj*, obj*);
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
obj* l_Nat_foldAux___main___at_Lean_mkModuleData___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_List_toString___at_Lean_Environment_displayStats___spec__1(obj*);
obj* l_Lean_mkStateFromImportedEntries(obj*, obj*);
obj* lean_add_decl(obj*, obj*);
extern obj* l_Lean_findOLean___closed__1;
obj* l_Lean_EnvExtension_modifyStateUnsafe(obj*);
uint8 l_HashMapImp_contains___at_Lean_Environment_contains___spec__2(obj*, obj*);
obj* l_Array_anyMAux___main___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg___boxed(obj*, obj*, obj*);
obj* lean_import_modules(obj*, uint32, obj*);
obj* l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__2(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_List_reverse___rarg(obj*);
obj* l_List_toStringAux___main___at_Lean_Environment_displayStats___spec__2___boxed(obj*, obj*);
obj* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__2;
obj* l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_SMap_contains___at_Lean_Environment_contains___spec__1(obj*, obj*);
obj* l_Lean_mkEmptyEnvironment___closed__1;
obj* l_Lean_importModules___closed__1;
obj* l___private_init_lean_environment_13__registerNamePrefixes(obj*, obj*);
obj* l_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__6(obj*);
obj* l_AssocList_contains___main___at_Lean_Environment_addAux___spec__5___boxed(obj*, obj*);
obj* l_List_toArrayAux___main___rarg(obj*, obj*);
obj* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__1;
obj* l_Array_uget(obj*, obj*, usize, obj*);
obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l___private_init_lean_environment_3__getTrustLevel___boxed(obj*);
obj* l_Lean_PersistentEnvExtensionState_inhabited___rarg(obj*);
obj* l_Lean_SimplePersistentEnvExtension_getState___rarg(obj*, obj*);
obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_EnvExtension_setState(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Inhabited;
obj* l_Array_uset(obj*, obj*, usize, obj*, obj*);
obj* l_Lean_Environment_imports___boxed(obj*);
obj* l_Lean_PersistentEnvExtension_modifyState___rarg(obj*, obj*, obj*);
obj* l_List_redLength___main___rarg(obj*);
obj* l_Lean_PersistentEnvExtension_getState___rarg___boxed(obj*, obj*);
obj* l_IO_Prim_Ref_set(obj*, obj*, obj*, obj*);
obj* l_AssocList_find___main___at_Lean_Environment_find___spec__3(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__8___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__3(obj*, obj*);
uint8 l_AssocList_contains___main___at_Lean_Environment_addAux___spec__5(obj*, obj*);
obj* l_Lean_SMap_find_x27___at_Lean_Environment_find___spec__1___boxed(obj*, obj*);
extern obj* l_Lean_Options_empty;
obj* l_AssocList_find___main___at_Lean_Environment_getModuleIdxFor___spec__2___boxed(obj*, obj*);
obj* l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(obj*, obj*);
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__3___boxed(obj*);
obj* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__2(obj*, obj*, obj*);
obj* l_Lean_Environment_displayStats___closed__3;
obj* l___private_init_lean_environment_6__mkInitialExtensionStates(obj*);
obj* l_Lean_Name_quickLt___boxed(obj*, obj*);
obj* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__3(obj*, obj*);
obj* l_Lean_regNamespacesExtension___lambda__1(obj*, obj*);
obj* l_RBNode_depth___main___rarg(obj*, obj*);
obj* l_Lean_EnvExtension_setState___boxed(obj*, obj*, obj*, obj*);
obj* lean_io_initializing(obj*);
obj* l_Lean_Environment_compileDecl___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__8(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SimplePersistentEnvExtension_setState___rarg(obj*, obj*, obj*);
obj* l_Array_mkEmpty(obj*, obj*);
obj* l_Array_anyMAux___main___at_Lean_registerSimplePersistentEnvExtension___spec__2___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__2;
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__2(obj*);
uint8 l_AssocList_contains___main___at_Lean_importModules___spec__2(obj*, obj*);
obj* l_Lean_EnvExtension_setState___closed__1;
obj* lean_mk_empty_environment(uint32, obj*);
extern obj* l_Lean_Name_DecidableEq;
obj* l_Lean_SimplePersistentEnvExtension_modifyState___rarg(obj*, obj*, obj*);
obj* l_Lean_EnvExtensionEntry_inhabited;
obj* l___private_init_lean_environment_10__setImportedEntries(obj*, obj*, obj*);
obj* l_Lean_regNamespacesExtension___closed__3;
obj* l___private_init_lean_environment_9__getEntriesFor___main(obj*, obj*, obj*);
obj* l_Lean_SimplePersistentEnvExtension_getEntries___rarg(obj*, obj*);
obj* l_Lean_regModListExtension___closed__1;
obj* l_Array_toList___rarg(obj*);
obj* l_Lean_registerSimplePersistentEnvExtension___at_Lean_regNamespacesExtension___spec__4(obj*, obj*);
uint8 l_Lean_NameSet_contains(obj*, obj*);
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__1(obj*, obj*);
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__3(obj*);
obj* l_Nat_repr(obj*);
obj* l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4___boxed(obj*);
obj* l___private_init_lean_environment_12__isNamespaceName___main___boxed(obj*);
extern obj* l_List_repr___rarg___closed__2;
obj* l_Lean_EnvExtensionState_inhabited;
obj* l_Lean_regNamespacesExtension___lambda__2(obj*);
obj* l_Lean_namespacesExt___closed__3;
obj* lean_perform_serialized_modifications(obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_Environment_addAux___spec__2(obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_NameSet_insert___spec__1(obj*, obj*, obj*);
obj* l_HashMapImp_find___at_Lean_Environment_getModuleIdxFor___spec__1(obj*, obj*);
obj* l_Lean_registerEnvExtensionUnsafe___rarg(obj*, obj*, obj*);
obj* l_Lean_CPPExtensionState_inhabited;
obj* l_Lean_Environment_displayStats___closed__1;
obj* l_Lean_Environment_displayStats___closed__2;
usize lean_name_hash_usize(obj*);
obj* l_Lean_readModuleData___boxed(obj*, obj*);
obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
obj* l___private_init_lean_environment_12__isNamespaceName___boxed(obj*);
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__10(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_PersistentEnvExtension_getState___rarg(obj*, obj*);
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_registerPersistentEnvExtensionUnsafe___spec__2(obj*, obj*);
obj* l_Lean_EnvExtension_getStateUnsafe___rarg___boxed(obj*, obj*);
obj* l_Lean_registerEnvExtensionUnsafe(obj*);
obj* l_List_toStringAux___main___at_Lean_Environment_displayStats___spec__2(uint8, obj*);
obj* l_HashMapImp_insert___at_Lean_importModules___spec__1(obj*, obj*, obj*);
obj* l_Lean_SMap_switch___at_Lean_importModules___spec__11(obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_environment_10__setImportedEntries___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Environment_getModuleIdxFor(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__7___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_beqOfEq___rarg(obj*, obj*, obj*);
obj* l___private_init_lean_environment_4__mkEnvExtensionsRef(obj*);
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_regModListExtension___spec__1___closed__1;
uint8 lean_environment_quot_init(obj*);
obj* l_Lean_namespacesExt___elambda__3___boxed(obj*, obj*);
uint8 l_Array_anyMAux___main___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg(obj*, obj*, obj*);
obj* lean_display_stats(obj*, obj*);
uint8 l_Lean_Environment_isConstructor(obj*, obj*);
obj* l_Lean_regNamespacesExtension___closed__6;
obj* l_Lean_registerPersistentEnvExtension___rarg(obj*);
obj* l_Lean_Environment_Inhabited;
obj* l_Lean_Environment_Inhabited___closed__2;
obj* l_Lean_regNamespacesExtension___lambda__2___boxed(obj*);
obj* lean_string_append(obj*, obj*);
obj* l_Lean_PersistentEnvExtension_getModuleEntries(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__13___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_PersistentEnvExtensionState_inhabited(obj*, obj*);
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__3___rarg(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__13(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_namespacesExt;
extern obj* l_List_reprAux___main___rarg___closed__1;
obj* l_HashMapImp_moveEntries___main___at_Lean_importModules___spec__4(obj*, obj*, obj*);
obj* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1(obj*, obj*, obj*);
uint8 l_RBNode_isRed___rarg(obj*);
extern obj* l_ByteArray_empty;
obj* lean_save_module_data(obj*, obj*, obj*);
obj* l_Lean_EnvExtension_getState___rarg(obj*, obj*);
uint8 lean_nat_dec_lt(obj*, obj*);
obj* l_Lean_SimplePersistentEnvExtension_getState(obj*, obj*);
obj* l_Lean_SMap_find_x27___at_Lean_Environment_find___spec__1(obj*, obj*);
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
obj* l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(obj*, obj*, obj*);
obj* lean_serialize_modifications(obj*, obj*);
extern obj* l_Char_HasRepr___closed__1;
obj* l_Array_miterateAux___main___at___private_init_lean_environment_11__finalizePersistentExtensions___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_HashMapImp_moveEntries___main___at_Lean_Environment_addAux___spec__7(obj*, obj*, obj*);
obj* l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3___boxed(obj*);
obj* l_Lean_Environment_Inhabited___closed__3;
obj* l_Lean_SimplePersistentEnvExtension_getEntries(obj*, obj*);
obj* l_Lean_SimplePersistentEnvExtension_getState___rarg___boxed(obj*, obj*);
obj* l_Lean_namespacesExt___closed__4;
obj* l_Array_fget(obj*, obj*, obj*);
obj* lean_name_mk_string(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__10___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_regModListExtension___spec__1(obj*, obj*);
obj* l_Lean_registerSimplePersistentEnvExtension___rarg(obj*, obj*, obj*);
obj* l_Lean_Environment_addAndCompile(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_regNamespacesExtension___spec__3___boxed(obj*, obj*, obj*, obj*);
obj* lean_nat_add(obj*, obj*);
obj* l_Array_anyMAux___main___at_Lean_regNamespacesExtension___spec__6___boxed(obj*, obj*, obj*);
obj* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__1___rarg(obj*, obj*, obj*);
obj* l_Lean_namespacesExt___closed__2;
obj* l_Lean_regNamespacesExtension___closed__2;
obj* l_Lean_namespacesExt___elambda__4___boxed(obj*);
obj* l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__9___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_PersistentEnvExtension_getModuleEntries___rarg(obj*, obj*, obj*);
extern obj* l_RBMap_maxDepth___rarg___closed__1;
obj* l_Array_ummapAux___main___at___private_init_lean_environment_6__mkInitialExtensionStates___spec__1(obj*, obj*, obj*);
obj* l_Lean_getNamespaceSet___boxed(obj*);
obj* l_Lean_findLeanFile(obj*, obj*, obj*);
obj* l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__3;
obj* l_Array_miterateAux___main___at___private_init_lean_environment_10__setImportedEntries___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_ModuleIdx_inhabited;
uint8 lean_nat_dec_eq(obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_SimplePersistentEnvExtension_modifyState___rarg___lambda__1(obj*, obj*);
obj* l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(obj*);
obj* l_Lean_EnvExtension_setStateUnsafe___rarg(obj*, obj*, obj*);
obj* l_Lean_Environment_displayStats___closed__9;
obj* l_ExceptT_Monad___rarg___lambda__8___boxed(obj*, obj*);
obj* l_Lean_saveModuleData___boxed(obj*, obj*, obj*);
obj* l_Lean_regNamespacesExtension___closed__4;
obj* l_Array_push(obj*, obj*, obj*);
obj* lean_set_extension(obj*, obj*, obj*);
uint8 l_List_isEmpty___rarg(obj*);
obj* l_Lean_regModListExtension(obj*);
obj* l_RBNode_find___main___at_Lean_Environment_find___spec__4___boxed(obj*, obj*);
obj* l_Lean_SMap_insert___at_Lean_Environment_addAux___spec__1(obj*, obj*, obj*);
obj* l_Array_anyMAux___main___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1(obj*, obj*);
obj* l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4(obj*);
obj* l_Lean_namespacesExt___elambda__2(obj*);
obj* l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1;
obj* l_Lean_registerEnvExtension(obj*, obj*, obj*);
obj* l_Lean_importModulesAux___main(obj*, obj*, obj*);
obj* l_Lean_mkStateFromImportedEntries___at_Lean_regNamespacesExtension___spec__1(obj*, obj*);
obj* l_Lean_EnvExtension_getState___rarg___boxed(obj*, obj*);
obj* l_Lean_registerPersistentEnvExtension(obj*, obj*, obj*, obj*);
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_registerCPPExtension___spec__1(obj*, obj*);
obj* l_RBNode_find___main___at_Lean_Environment_find___spec__4(obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10(obj*, obj*, obj*, obj*);
obj* l_Lean_registerPersistentEnvExtensionUnsafe(obj*, obj*);
obj* l_AssocList_find___main___at_Lean_Environment_getModuleIdxFor___spec__2(obj*, obj*);
obj* l_Lean_mkModuleData(obj*, obj*);
obj* l_IO_Prim_mkRef(obj*, obj*, obj*);
obj* l_Lean_PersistentEnvExtension_getState(obj*, obj*);
obj* l___private_init_lean_environment_11__finalizePersistentExtensions(obj*, obj*);
obj* l_Lean_PersistentEnvExtension_setState(obj*, obj*);
obj* l___private_init_lean_environment_13__registerNamePrefixes___main(obj*, obj*);
obj* l_Lean_SMap_contains___at_Lean_Environment_contains___spec__1___boxed(obj*, obj*);
obj* l_Lean_EnvExtension_modifyState(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_regNamespacesExtension___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* lean_compile_decl(obj*, obj*, obj*);
obj* l_Nat_foldAux___main___at_Lean_mkModuleData___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_isNamespace(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_HashMapImp_find___at_Lean_Environment_getModuleIdxFor___spec__1___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_regNamespacesExtension___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_namespacesExt___closed__5;
obj* l_Array_miterateAux___main___at_Lean_regNamespacesExtension___spec__3(obj*, obj*, obj*, obj*);
obj* l_Lean_modListExtension___closed__1;
obj* l_Array_miterateAux___main___at___private_init_lean_environment_10__setImportedEntries___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_registerPersistentEnvExtensionUnsafe___spec__2___rarg(obj*, obj*, obj*);
obj* l_AssocList_mfoldl___main___at_Lean_importModules___spec__5(obj*, obj*);
obj* l_Lean_importModules___boxed(obj*, obj*, obj*);
obj* l_Lean_Environment_addDecl___boxed(obj*, obj*);
extern obj* l_NonScalar_Inhabited;
obj* l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__3;
obj* l_Lean_Environment_contains___boxed(obj*, obj*);
obj* lean_read_module_data(obj*, obj*);
obj* l_EState_bind___rarg(obj*, obj*, obj*);
obj* l_IO_println___at_HasRepr_HasEval___spec__1(obj*, obj*);
obj* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___boxed(obj*);
obj* l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5___boxed(obj*);
obj* l_Lean_namespacesExt___closed__6;
obj* l_RBNode_fold___main___at_Lean_mkModuleData___spec__2(obj*, obj*);
uint8 l_Array_anyMAux___main___at_Lean_registerSimplePersistentEnvExtension___spec__2___rarg(obj*, obj*, obj*);
obj* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4(obj*);
obj* l_Lean_Environment_Inhabited___closed__1;
obj* l_Lean_Environment_addAndCompile___boxed(obj*, obj*, obj*);
obj* l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__4;
obj* l_Lean_PersistentEnvExtension_addEntry___rarg(obj*, obj*, obj*);
obj* l_AssocList_replace___main___at_Lean_Environment_addAux___spec__9(obj*, obj*, obj*);
obj* l_IO_Prim_Ref_get(obj*, obj*, obj*);
obj* l_Lean_registerNamespace(obj*, obj*);
obj* l___private_init_lean_environment_2__isQuotInit___boxed(obj*);
uint8 l_Lean_Name_quickLt(obj*, obj*);
obj* lean_register_extension(obj*);
obj* l_Lean_SimplePersistentEnvExtension_Inhabited___rarg(obj*);
usize lean_usize_modn(usize, obj*);
obj* l_Lean_SimplePersistentEnvExtension_getEntries___rarg___boxed(obj*, obj*);
obj* l_Lean_getNamespaceSet(obj*);
obj* lean_environment_find(obj*, obj*);
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7___closed__1;
obj* l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2;
extern obj* l_HashMap_Inhabited___closed__1;
obj* l_Lean_modListExtension;
obj* l_Lean_Environment_isConstructor___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__12(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_environment_9__getEntriesFor___main___boxed(obj*, obj*, obj*);
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__2___boxed(obj*);
obj* lean_environment_add(obj*, obj*);
obj* l_Lean_EnvExtension_setStateUnsafe(obj*);
obj* l_Array_size(obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__1;
obj* l_Lean_EnvExtension_Inhabited(obj*);
obj* l_EState_pure___rarg(obj*, obj*);
obj* l_Lean_SimplePersistentEnvExtension_setState___rarg___lambda__1(obj*, obj*);
obj* l_Array_fset(obj*, obj*, obj*, obj*);
obj* l_Array_get(obj*, obj*, obj*, obj*);
obj* l_mkHashMapImp___rarg(obj*);
obj* l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__2;
obj* l_Lean_EnvExtension_getStateUnsafe(obj*);
obj* l_RBNode_setBlack___rarg(obj*);
obj* l_Lean_Environment_imports(obj*);
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7(obj*, obj*);
obj* l_AssocList_contains___main___at_Lean_importModules___spec__2___boxed(obj*, obj*);
obj* l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__1;
obj* l_Lean_SimplePersistentEnvExtension_Inhabited(obj*, obj*);
obj* l_Lean_modListExtension___closed__2;
obj* l_AssocList_find___main___at_Lean_Environment_find___spec__3___boxed(obj*, obj*);
obj* lean_get_extension(obj*, obj*);
obj* l_Lean_mkEmptyEnvironment___boxed(obj*, obj*);
obj* l_Lean_registerPersistentEnvExtension___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
extern obj* l_Lean_Name_toString___closed__1;
uint8 lean_nat_dec_le(obj*, obj*);
obj* l_Array_anyMAux___main___at_Lean_registerSimplePersistentEnvExtension___spec__2(obj*, obj*);
uint8 l_Lean_Environment_contains(obj*, obj*);
obj* l_Lean_regNamespacesExtension(obj*);
obj* l_AssocList_mfoldl___main___at_Lean_Environment_addAux___spec__8(obj*, obj*);
obj* l_Lean_PersistentEnvExtension_modifyState(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__1(obj*, obj*);
obj* lean_uint32_to_nat(uint32);
obj* l_Lean_serializeModifications___boxed(obj*, obj*);
obj* l_Lean_SimplePersistentEnvExtension_setState(obj*, obj*);
obj* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__1(obj*, obj*);
uint8 l_Lean_Format_isNil(obj*);
obj* l_Lean_PersistentEnvExtension_addEntry(obj*, obj*);
obj* l_Array_set(obj*, obj*, obj*, obj*);
obj* l_Lean_regNamespacesExtension___closed__1;
obj* l_mkHashMap___at_Lean_Environment_Inhabited___spec__3(obj*);
obj* l_HashMapImp_find___at_Lean_Environment_find___spec__2(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__8(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_namespacesExt___elambda__4___rarg(obj*);
obj* l___private_init_lean_environment_9__getEntriesFor___boxed(obj*, obj*, obj*);
obj* l_Lean_registerEnvExtension___rarg(obj*);
obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg(obj*, obj*, obj*);
obj* l_Lean_registerEnvExtension___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_environment_8__persistentEnvExtensionsRef;
obj* l_Lean_Modification_inhabited;
uint8 l___private_init_lean_environment_12__isNamespaceName___main(obj*);
obj* l_Lean_Environment_displayStats___closed__8;
obj* l_Array_miterateAux___main___at___private_init_lean_environment_10__setImportedEntries___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3(obj*);
obj* l_Lean_ModuleData_inhabited;
uint8 l___private_init_lean_environment_12__isNamespaceName(obj*);
obj* l_HashMapImp_expand___at_Lean_Environment_addAux___spec__6(obj*, obj*);
obj* l_Lean_SimplePersistentEnvExtension_modifyState(obj*, obj*);
obj* l_Lean_EnvExtension_Inhabited___rarg___lambda__1(obj*);
obj* lean_nat_mul(obj*, obj*);
obj* l___private_init_lean_environment_9__getEntriesFor(obj*, obj*, obj*);
obj* l_Lean_mkStateFromImportedEntries___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
obj* l_Lean_regNamespacesExtension___closed__5;
obj* l___private_init_lean_environment_10__setImportedEntries___boxed(obj*, obj*, obj*);
obj* l_IO_Prim_Ref_reset(obj*, obj*, obj*);
obj* l_HashMapImp_expand___at_Lean_importModules___spec__3(obj*, obj*);
extern obj* l_List_repr___rarg___closed__1;
obj* l___private_init_lean_environment_5__envExtensionsRef;
obj* l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__9(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__9___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__7(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7___closed__2;
obj* l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7___boxed(obj*);
extern obj* l_String_splitAux___main___closed__1;
obj* l_Lean_modListExtension___elambda__1(obj*);
obj* l_HashMapImp_contains___at_Lean_Environment_contains___spec__2___boxed(obj*, obj*);
obj* _init_l_Lean_EnvExtensionState_inhabited() {
_start:
{
obj* x_1; 
x_1 = l_NonScalar_Inhabited;
return x_1;
}
}
obj* _init_l_Lean_ModuleIdx_inhabited() {
_start:
{
obj* x_1; 
x_1 = l_Nat_Inhabited;
return x_1;
}
}
obj* l_mkHashMap___at_Lean_Environment_Inhabited___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
obj* l_mkHashMap___at_Lean_Environment_Inhabited___spec__3(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
obj* _init_l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Name_DecidableEq;
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_beqOfEq___rarg), 3, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
obj* _init_l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Name_quickLt___boxed), 2, 0);
return x_1;
}
}
obj* _init_l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__4() {
_start:
{
obj* x_1; uint8 x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = 1;
x_3 = l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__2;
x_4 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
obj* _init_l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2() {
_start:
{
obj* x_1; 
x_1 = l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__4;
return x_1;
}
}
obj* _init_l_Lean_Environment_Inhabited___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
obj* _init_l_Lean_Environment_Inhabited___closed__2() {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = 0;
x_2 = 0;
x_3 = lean::box(0);
x_4 = l_Array_empty___closed__1;
x_5 = lean::alloc_cnstr(0, 2, 5);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
lean::cnstr_set_uint32(x_5, sizeof(void*)*2, x_1);
lean::cnstr_set_uint8(x_5, sizeof(void*)*2 + 4, x_2);
return x_5;
}
}
obj* _init_l_Lean_Environment_Inhabited___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Environment_Inhabited___closed__1;
x_2 = l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2;
x_3 = l_Array_empty___closed__1;
x_4 = l_Lean_Environment_Inhabited___closed__2;
x_5 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_4);
return x_5;
}
}
obj* _init_l_Lean_Environment_Inhabited() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Environment_Inhabited___closed__3;
return x_1;
}
}
obj* l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(obj* x_1, obj* x_2, obj* x_3) {
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
lean::cnstr_set_uint8(x_5, sizeof(void*)*4, x_4);
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_uint8(x_1, sizeof(void*)*4);
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
x_14 = l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(x_11, x_2, x_3);
lean::cnstr_set(x_1, 3, x_14);
return x_1;
}
}
else
{
obj* x_15; 
x_15 = l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(x_8, x_2, x_3);
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
lean::cnstr_set_uint8(x_22, sizeof(void*)*4, x_6);
return x_22;
}
else
{
obj* x_23; obj* x_24; 
x_23 = l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(x_19, x_2, x_3);
x_24 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_24, 0, x_16);
lean::cnstr_set(x_24, 1, x_17);
lean::cnstr_set(x_24, 2, x_18);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_uint8(x_24, sizeof(void*)*4, x_6);
return x_24;
}
}
else
{
obj* x_25; obj* x_26; 
x_25 = l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(x_16, x_2, x_3);
x_26 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
lean::cnstr_set(x_26, 2, x_18);
lean::cnstr_set(x_26, 3, x_19);
lean::cnstr_set_uint8(x_26, sizeof(void*)*4, x_6);
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
x_34 = l_RBNode_isRed___rarg(x_31);
if (x_34 == 0)
{
obj* x_35; 
x_35 = l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(x_31, x_2, x_3);
lean::cnstr_set(x_1, 3, x_35);
return x_1;
}
else
{
obj* x_36; 
x_36 = l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(x_31, x_2, x_3);
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
lean::cnstr_set_uint8(x_36, sizeof(void*)*4, x_42);
x_43 = 1;
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_43);
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
lean::cnstr_set_uint8(x_47, sizeof(void*)*4, x_46);
x_48 = 1;
lean::cnstr_set(x_1, 3, x_47);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_48);
return x_1;
}
}
else
{
uint8 x_49; 
x_49 = lean::cnstr_get_uint8(x_38, sizeof(void*)*4);
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
lean::cnstr_set_uint8(x_38, sizeof(void*)*4, x_60);
lean::cnstr_set(x_36, 3, x_59);
lean::cnstr_set(x_36, 2, x_58);
lean::cnstr_set(x_36, 1, x_57);
lean::cnstr_set(x_36, 0, x_56);
lean::cnstr_set_uint8(x_36, sizeof(void*)*4, x_60);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_52);
lean::cnstr_set(x_1, 1, x_51);
lean::cnstr_set(x_1, 0, x_38);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_49);
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
lean::cnstr_set_uint8(x_66, sizeof(void*)*4, x_65);
lean::cnstr_set(x_36, 3, x_64);
lean::cnstr_set(x_36, 2, x_63);
lean::cnstr_set(x_36, 1, x_62);
lean::cnstr_set(x_36, 0, x_61);
lean::cnstr_set_uint8(x_36, sizeof(void*)*4, x_65);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_52);
lean::cnstr_set(x_1, 1, x_51);
lean::cnstr_set(x_1, 0, x_66);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_49);
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
lean::cnstr_set_uint8(x_75, sizeof(void*)*4, x_74);
x_76 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_76, 0, x_69);
lean::cnstr_set(x_76, 1, x_70);
lean::cnstr_set(x_76, 2, x_71);
lean::cnstr_set(x_76, 3, x_72);
lean::cnstr_set_uint8(x_76, sizeof(void*)*4, x_74);
lean::cnstr_set(x_1, 3, x_76);
lean::cnstr_set(x_1, 2, x_68);
lean::cnstr_set(x_1, 1, x_67);
lean::cnstr_set(x_1, 0, x_75);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_49);
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
lean::cnstr_set_uint8(x_36, sizeof(void*)*4, x_80);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_49);
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
lean::cnstr_set_uint8(x_84, sizeof(void*)*4, x_83);
lean::cnstr_set(x_1, 3, x_84);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
}
}
else
{
uint8 x_85; 
x_85 = lean::cnstr_get_uint8(x_37, sizeof(void*)*4);
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
lean::cnstr_set_uint8(x_37, sizeof(void*)*4, x_93);
lean::cnstr_set(x_36, 0, x_92);
lean::cnstr_set_uint8(x_36, sizeof(void*)*4, x_93);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_91);
lean::cnstr_set(x_1, 1, x_90);
lean::cnstr_set(x_1, 0, x_37);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_85);
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
lean::cnstr_set_uint8(x_99, sizeof(void*)*4, x_98);
lean::cnstr_set(x_36, 0, x_97);
lean::cnstr_set_uint8(x_36, sizeof(void*)*4, x_98);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_96);
lean::cnstr_set(x_1, 1, x_95);
lean::cnstr_set(x_1, 0, x_99);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_85);
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
lean::cnstr_set_uint8(x_109, sizeof(void*)*4, x_108);
x_110 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_110, 0, x_106);
lean::cnstr_set(x_110, 1, x_100);
lean::cnstr_set(x_110, 2, x_101);
lean::cnstr_set(x_110, 3, x_102);
lean::cnstr_set_uint8(x_110, sizeof(void*)*4, x_108);
lean::cnstr_set(x_1, 3, x_110);
lean::cnstr_set(x_1, 2, x_105);
lean::cnstr_set(x_1, 1, x_104);
lean::cnstr_set(x_1, 0, x_109);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_85);
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
lean::cnstr_set_uint8(x_36, sizeof(void*)*4, x_115);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_85);
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
lean::cnstr_set_uint8(x_119, sizeof(void*)*4, x_118);
lean::cnstr_set(x_1, 3, x_119);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
uint8 x_120; 
x_120 = lean::cnstr_get_uint8(x_111, sizeof(void*)*4);
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
lean::cnstr_set_uint8(x_111, sizeof(void*)*4, x_85);
lean::cnstr_set(x_37, 3, x_128);
lean::cnstr_set(x_37, 2, x_127);
lean::cnstr_set(x_37, 1, x_126);
lean::cnstr_set(x_37, 0, x_125);
lean::cnstr_set(x_36, 3, x_37);
lean::cnstr_set(x_36, 0, x_111);
lean::cnstr_set_uint8(x_36, sizeof(void*)*4, x_120);
return x_36;
}
else
{
obj* x_134; 
lean::dec(x_37);
lean::cnstr_set_uint8(x_111, sizeof(void*)*4, x_85);
x_134 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_134, 0, x_125);
lean::cnstr_set(x_134, 1, x_126);
lean::cnstr_set(x_134, 2, x_127);
lean::cnstr_set(x_134, 3, x_128);
lean::cnstr_set_uint8(x_134, sizeof(void*)*4, x_85);
lean::cnstr_set(x_36, 3, x_134);
lean::cnstr_set(x_36, 0, x_111);
lean::cnstr_set_uint8(x_36, sizeof(void*)*4, x_120);
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
lean::cnstr_set_uint8(x_139, sizeof(void*)*4, x_85);
if (lean::is_scalar(x_140)) {
 x_141 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_141 = x_140;
}
lean::cnstr_set(x_141, 0, x_135);
lean::cnstr_set(x_141, 1, x_136);
lean::cnstr_set(x_141, 2, x_137);
lean::cnstr_set(x_141, 3, x_138);
lean::cnstr_set_uint8(x_141, sizeof(void*)*4, x_85);
lean::cnstr_set(x_36, 3, x_141);
lean::cnstr_set(x_36, 0, x_139);
lean::cnstr_set_uint8(x_36, sizeof(void*)*4, x_120);
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
lean::cnstr_set_uint8(x_149, sizeof(void*)*4, x_85);
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_144);
lean::cnstr_set(x_151, 1, x_145);
lean::cnstr_set(x_151, 2, x_146);
lean::cnstr_set(x_151, 3, x_147);
lean::cnstr_set_uint8(x_151, sizeof(void*)*4, x_85);
x_152 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_152, 0, x_149);
lean::cnstr_set(x_152, 1, x_142);
lean::cnstr_set(x_152, 2, x_143);
lean::cnstr_set(x_152, 3, x_151);
lean::cnstr_set_uint8(x_152, sizeof(void*)*4, x_120);
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
lean::cnstr_set_uint8(x_37, sizeof(void*)*4, x_120);
x_157 = 0;
lean::cnstr_set_uint8(x_36, sizeof(void*)*4, x_157);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_120);
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
lean::cnstr_set_uint8(x_162, sizeof(void*)*4, x_120);
x_163 = 0;
lean::cnstr_set(x_36, 0, x_162);
lean::cnstr_set_uint8(x_36, sizeof(void*)*4, x_163);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_120);
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
lean::cnstr_set_uint8(x_171, sizeof(void*)*4, x_120);
x_172 = 0;
x_173 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_173, 0, x_171);
lean::cnstr_set(x_173, 1, x_164);
lean::cnstr_set(x_173, 2, x_165);
lean::cnstr_set(x_173, 3, x_111);
lean::cnstr_set_uint8(x_173, sizeof(void*)*4, x_172);
lean::cnstr_set(x_1, 3, x_173);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_120);
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
x_174 = l_RBNode_isRed___rarg(x_28);
if (x_174 == 0)
{
obj* x_175; 
x_175 = l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(x_28, x_2, x_3);
lean::cnstr_set(x_1, 0, x_175);
return x_1;
}
else
{
obj* x_176; 
x_176 = l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(x_28, x_2, x_3);
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
lean::cnstr_set_uint8(x_176, sizeof(void*)*4, x_182);
x_183 = 1;
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_183);
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
lean::cnstr_set_uint8(x_187, sizeof(void*)*4, x_186);
x_188 = 1;
lean::cnstr_set(x_1, 0, x_187);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
else
{
uint8 x_189; 
x_189 = lean::cnstr_get_uint8(x_178, sizeof(void*)*4);
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
lean::cnstr_set_uint8(x_178, sizeof(void*)*4, x_200);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_199);
lean::cnstr_set_uint8(x_176, sizeof(void*)*4, x_200);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_198);
lean::cnstr_set(x_1, 1, x_197);
lean::cnstr_set(x_1, 0, x_178);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_189);
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
lean::cnstr_set_uint8(x_206, sizeof(void*)*4, x_205);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_204);
lean::cnstr_set_uint8(x_176, sizeof(void*)*4, x_205);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_203);
lean::cnstr_set(x_1, 1, x_202);
lean::cnstr_set(x_1, 0, x_206);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_189);
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
lean::cnstr_set_uint8(x_215, sizeof(void*)*4, x_214);
x_216 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_216, 0, x_212);
lean::cnstr_set(x_216, 1, x_29);
lean::cnstr_set(x_216, 2, x_30);
lean::cnstr_set(x_216, 3, x_31);
lean::cnstr_set_uint8(x_216, sizeof(void*)*4, x_214);
lean::cnstr_set(x_1, 3, x_216);
lean::cnstr_set(x_1, 2, x_211);
lean::cnstr_set(x_1, 1, x_210);
lean::cnstr_set(x_1, 0, x_215);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_189);
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
lean::cnstr_set_uint8(x_176, sizeof(void*)*4, x_220);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_189);
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
lean::cnstr_set_uint8(x_224, sizeof(void*)*4, x_223);
lean::cnstr_set(x_1, 0, x_224);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
}
}
else
{
uint8 x_225; 
x_225 = lean::cnstr_get_uint8(x_177, sizeof(void*)*4);
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
lean::cnstr_set_uint8(x_177, sizeof(void*)*4, x_232);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_229);
lean::cnstr_set_uint8(x_176, sizeof(void*)*4, x_232);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_228);
lean::cnstr_set(x_1, 1, x_227);
lean::cnstr_set(x_1, 0, x_177);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_225);
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
lean::cnstr_set_uint8(x_238, sizeof(void*)*4, x_237);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_229);
lean::cnstr_set_uint8(x_176, sizeof(void*)*4, x_237);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_228);
lean::cnstr_set(x_1, 1, x_227);
lean::cnstr_set(x_1, 0, x_238);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_225);
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
lean::cnstr_set_uint8(x_248, sizeof(void*)*4, x_247);
x_249 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_249, 0, x_241);
lean::cnstr_set(x_249, 1, x_29);
lean::cnstr_set(x_249, 2, x_30);
lean::cnstr_set(x_249, 3, x_31);
lean::cnstr_set_uint8(x_249, sizeof(void*)*4, x_247);
lean::cnstr_set(x_1, 3, x_249);
lean::cnstr_set(x_1, 2, x_240);
lean::cnstr_set(x_1, 1, x_239);
lean::cnstr_set(x_1, 0, x_248);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_225);
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
lean::cnstr_set_uint8(x_176, sizeof(void*)*4, x_254);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_225);
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
lean::cnstr_set_uint8(x_258, sizeof(void*)*4, x_257);
lean::cnstr_set(x_1, 0, x_258);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
uint8 x_259; 
x_259 = lean::cnstr_get_uint8(x_250, sizeof(void*)*4);
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
lean::cnstr_set_uint8(x_250, sizeof(void*)*4, x_225);
lean::cnstr_set(x_177, 3, x_31);
lean::cnstr_set(x_177, 2, x_30);
lean::cnstr_set(x_177, 1, x_29);
lean::cnstr_set(x_177, 0, x_269);
lean::cnstr_set(x_176, 3, x_177);
lean::cnstr_set(x_176, 2, x_268);
lean::cnstr_set(x_176, 1, x_267);
lean::cnstr_set(x_176, 0, x_250);
lean::cnstr_set_uint8(x_176, sizeof(void*)*4, x_259);
return x_176;
}
else
{
obj* x_275; 
lean::dec(x_177);
lean::cnstr_set_uint8(x_250, sizeof(void*)*4, x_225);
x_275 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_275, 0, x_269);
lean::cnstr_set(x_275, 1, x_29);
lean::cnstr_set(x_275, 2, x_30);
lean::cnstr_set(x_275, 3, x_31);
lean::cnstr_set_uint8(x_275, sizeof(void*)*4, x_225);
lean::cnstr_set(x_176, 3, x_275);
lean::cnstr_set(x_176, 2, x_268);
lean::cnstr_set(x_176, 1, x_267);
lean::cnstr_set(x_176, 0, x_250);
lean::cnstr_set_uint8(x_176, sizeof(void*)*4, x_259);
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
lean::cnstr_set_uint8(x_280, sizeof(void*)*4, x_225);
if (lean::is_scalar(x_281)) {
 x_282 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_282 = x_281;
}
lean::cnstr_set(x_282, 0, x_279);
lean::cnstr_set(x_282, 1, x_29);
lean::cnstr_set(x_282, 2, x_30);
lean::cnstr_set(x_282, 3, x_31);
lean::cnstr_set_uint8(x_282, sizeof(void*)*4, x_225);
lean::cnstr_set(x_176, 3, x_282);
lean::cnstr_set(x_176, 2, x_278);
lean::cnstr_set(x_176, 1, x_277);
lean::cnstr_set(x_176, 0, x_280);
lean::cnstr_set_uint8(x_176, sizeof(void*)*4, x_259);
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
lean::cnstr_set_uint8(x_290, sizeof(void*)*4, x_225);
if (lean::is_scalar(x_291)) {
 x_292 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_292 = x_291;
}
lean::cnstr_set(x_292, 0, x_288);
lean::cnstr_set(x_292, 1, x_29);
lean::cnstr_set(x_292, 2, x_30);
lean::cnstr_set(x_292, 3, x_31);
lean::cnstr_set_uint8(x_292, sizeof(void*)*4, x_225);
x_293 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_293, 0, x_290);
lean::cnstr_set(x_293, 1, x_286);
lean::cnstr_set(x_293, 2, x_287);
lean::cnstr_set(x_293, 3, x_292);
lean::cnstr_set_uint8(x_293, sizeof(void*)*4, x_259);
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
lean::cnstr_set_uint8(x_177, sizeof(void*)*4, x_259);
x_298 = 0;
lean::cnstr_set_uint8(x_176, sizeof(void*)*4, x_298);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_259);
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
lean::cnstr_set_uint8(x_303, sizeof(void*)*4, x_259);
x_304 = 0;
lean::cnstr_set(x_176, 0, x_303);
lean::cnstr_set_uint8(x_176, sizeof(void*)*4, x_304);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_259);
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
lean::cnstr_set_uint8(x_312, sizeof(void*)*4, x_259);
x_313 = 0;
x_314 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_314, 0, x_312);
lean::cnstr_set(x_314, 1, x_305);
lean::cnstr_set(x_314, 2, x_306);
lean::cnstr_set(x_314, 3, x_250);
lean::cnstr_set_uint8(x_314, sizeof(void*)*4, x_313);
lean::cnstr_set(x_1, 0, x_314);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_259);
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
lean::cnstr_set_uint8(x_321, sizeof(void*)*4, x_6);
return x_321;
}
else
{
uint8 x_322; 
x_322 = l_RBNode_isRed___rarg(x_318);
if (x_322 == 0)
{
obj* x_323; obj* x_324; 
x_323 = l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(x_318, x_2, x_3);
x_324 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_324, 0, x_315);
lean::cnstr_set(x_324, 1, x_316);
lean::cnstr_set(x_324, 2, x_317);
lean::cnstr_set(x_324, 3, x_323);
lean::cnstr_set_uint8(x_324, sizeof(void*)*4, x_6);
return x_324;
}
else
{
obj* x_325; 
x_325 = l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(x_318, x_2, x_3);
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
lean::cnstr_set_uint8(x_332, sizeof(void*)*4, x_331);
x_333 = 1;
x_334 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_334, 0, x_315);
lean::cnstr_set(x_334, 1, x_316);
lean::cnstr_set(x_334, 2, x_317);
lean::cnstr_set(x_334, 3, x_332);
lean::cnstr_set_uint8(x_334, sizeof(void*)*4, x_333);
return x_334;
}
else
{
uint8 x_335; 
x_335 = lean::cnstr_get_uint8(x_327, sizeof(void*)*4);
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
lean::cnstr_set_uint8(x_345, sizeof(void*)*4, x_344);
if (lean::is_scalar(x_338)) {
 x_346 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_346 = x_338;
}
lean::cnstr_set(x_346, 0, x_339);
lean::cnstr_set(x_346, 1, x_340);
lean::cnstr_set(x_346, 2, x_341);
lean::cnstr_set(x_346, 3, x_342);
lean::cnstr_set_uint8(x_346, sizeof(void*)*4, x_344);
x_347 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_347, 0, x_345);
lean::cnstr_set(x_347, 1, x_336);
lean::cnstr_set(x_347, 2, x_337);
lean::cnstr_set(x_347, 3, x_346);
lean::cnstr_set_uint8(x_347, sizeof(void*)*4, x_335);
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
lean::cnstr_set_uint8(x_352, sizeof(void*)*4, x_351);
x_353 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_353, 0, x_315);
lean::cnstr_set(x_353, 1, x_316);
lean::cnstr_set(x_353, 2, x_317);
lean::cnstr_set(x_353, 3, x_352);
lean::cnstr_set_uint8(x_353, sizeof(void*)*4, x_335);
return x_353;
}
}
}
else
{
uint8 x_354; 
x_354 = lean::cnstr_get_uint8(x_326, sizeof(void*)*4);
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
lean::cnstr_set_uint8(x_365, sizeof(void*)*4, x_364);
if (lean::is_scalar(x_358)) {
 x_366 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_366 = x_358;
}
lean::cnstr_set(x_366, 0, x_362);
lean::cnstr_set(x_366, 1, x_355);
lean::cnstr_set(x_366, 2, x_356);
lean::cnstr_set(x_366, 3, x_357);
lean::cnstr_set_uint8(x_366, sizeof(void*)*4, x_364);
x_367 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_367, 0, x_365);
lean::cnstr_set(x_367, 1, x_360);
lean::cnstr_set(x_367, 2, x_361);
lean::cnstr_set(x_367, 3, x_366);
lean::cnstr_set_uint8(x_367, sizeof(void*)*4, x_354);
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
lean::cnstr_set_uint8(x_373, sizeof(void*)*4, x_372);
x_374 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_374, 0, x_315);
lean::cnstr_set(x_374, 1, x_316);
lean::cnstr_set(x_374, 2, x_317);
lean::cnstr_set(x_374, 3, x_373);
lean::cnstr_set_uint8(x_374, sizeof(void*)*4, x_354);
return x_374;
}
else
{
uint8 x_375; 
x_375 = lean::cnstr_get_uint8(x_368, sizeof(void*)*4);
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
lean::cnstr_set_uint8(x_384, sizeof(void*)*4, x_354);
if (lean::is_scalar(x_385)) {
 x_386 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_386 = x_385;
}
lean::cnstr_set(x_386, 0, x_379);
lean::cnstr_set(x_386, 1, x_380);
lean::cnstr_set(x_386, 2, x_381);
lean::cnstr_set(x_386, 3, x_382);
lean::cnstr_set_uint8(x_386, sizeof(void*)*4, x_354);
if (lean::is_scalar(x_378)) {
 x_387 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_387 = x_378;
}
lean::cnstr_set(x_387, 0, x_384);
lean::cnstr_set(x_387, 1, x_376);
lean::cnstr_set(x_387, 2, x_377);
lean::cnstr_set(x_387, 3, x_386);
lean::cnstr_set_uint8(x_387, sizeof(void*)*4, x_375);
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
lean::cnstr_set_uint8(x_396, sizeof(void*)*4, x_375);
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
lean::cnstr_set_uint8(x_398, sizeof(void*)*4, x_397);
x_399 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_399, 0, x_315);
lean::cnstr_set(x_399, 1, x_316);
lean::cnstr_set(x_399, 2, x_317);
lean::cnstr_set(x_399, 3, x_398);
lean::cnstr_set_uint8(x_399, sizeof(void*)*4, x_375);
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
x_400 = l_RBNode_isRed___rarg(x_315);
if (x_400 == 0)
{
obj* x_401; obj* x_402; 
x_401 = l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(x_315, x_2, x_3);
x_402 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_402, 0, x_401);
lean::cnstr_set(x_402, 1, x_316);
lean::cnstr_set(x_402, 2, x_317);
lean::cnstr_set(x_402, 3, x_318);
lean::cnstr_set_uint8(x_402, sizeof(void*)*4, x_6);
return x_402;
}
else
{
obj* x_403; 
x_403 = l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(x_315, x_2, x_3);
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
lean::cnstr_set_uint8(x_410, sizeof(void*)*4, x_409);
x_411 = 1;
x_412 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_412, 0, x_410);
lean::cnstr_set(x_412, 1, x_316);
lean::cnstr_set(x_412, 2, x_317);
lean::cnstr_set(x_412, 3, x_318);
lean::cnstr_set_uint8(x_412, sizeof(void*)*4, x_411);
return x_412;
}
else
{
uint8 x_413; 
x_413 = lean::cnstr_get_uint8(x_405, sizeof(void*)*4);
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
lean::cnstr_set_uint8(x_423, sizeof(void*)*4, x_422);
if (lean::is_scalar(x_416)) {
 x_424 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_424 = x_416;
}
lean::cnstr_set(x_424, 0, x_420);
lean::cnstr_set(x_424, 1, x_316);
lean::cnstr_set(x_424, 2, x_317);
lean::cnstr_set(x_424, 3, x_318);
lean::cnstr_set_uint8(x_424, sizeof(void*)*4, x_422);
x_425 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_425, 0, x_423);
lean::cnstr_set(x_425, 1, x_418);
lean::cnstr_set(x_425, 2, x_419);
lean::cnstr_set(x_425, 3, x_424);
lean::cnstr_set_uint8(x_425, sizeof(void*)*4, x_413);
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
lean::cnstr_set_uint8(x_430, sizeof(void*)*4, x_429);
x_431 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_431, 0, x_430);
lean::cnstr_set(x_431, 1, x_316);
lean::cnstr_set(x_431, 2, x_317);
lean::cnstr_set(x_431, 3, x_318);
lean::cnstr_set_uint8(x_431, sizeof(void*)*4, x_413);
return x_431;
}
}
}
else
{
uint8 x_432; 
x_432 = lean::cnstr_get_uint8(x_404, sizeof(void*)*4);
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
lean::cnstr_set_uint8(x_443, sizeof(void*)*4, x_442);
if (lean::is_scalar(x_436)) {
 x_444 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_444 = x_436;
}
lean::cnstr_set(x_444, 0, x_435);
lean::cnstr_set(x_444, 1, x_316);
lean::cnstr_set(x_444, 2, x_317);
lean::cnstr_set(x_444, 3, x_318);
lean::cnstr_set_uint8(x_444, sizeof(void*)*4, x_442);
x_445 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_445, 0, x_443);
lean::cnstr_set(x_445, 1, x_433);
lean::cnstr_set(x_445, 2, x_434);
lean::cnstr_set(x_445, 3, x_444);
lean::cnstr_set_uint8(x_445, sizeof(void*)*4, x_432);
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
lean::cnstr_set_uint8(x_451, sizeof(void*)*4, x_450);
x_452 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_452, 0, x_451);
lean::cnstr_set(x_452, 1, x_316);
lean::cnstr_set(x_452, 2, x_317);
lean::cnstr_set(x_452, 3, x_318);
lean::cnstr_set_uint8(x_452, sizeof(void*)*4, x_432);
return x_452;
}
else
{
uint8 x_453; 
x_453 = lean::cnstr_get_uint8(x_446, sizeof(void*)*4);
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
lean::cnstr_set_uint8(x_462, sizeof(void*)*4, x_432);
if (lean::is_scalar(x_463)) {
 x_464 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_464 = x_463;
}
lean::cnstr_set(x_464, 0, x_460);
lean::cnstr_set(x_464, 1, x_316);
lean::cnstr_set(x_464, 2, x_317);
lean::cnstr_set(x_464, 3, x_318);
lean::cnstr_set_uint8(x_464, sizeof(void*)*4, x_432);
if (lean::is_scalar(x_456)) {
 x_465 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_465 = x_456;
}
lean::cnstr_set(x_465, 0, x_462);
lean::cnstr_set(x_465, 1, x_458);
lean::cnstr_set(x_465, 2, x_459);
lean::cnstr_set(x_465, 3, x_464);
lean::cnstr_set_uint8(x_465, sizeof(void*)*4, x_453);
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
lean::cnstr_set_uint8(x_474, sizeof(void*)*4, x_453);
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
lean::cnstr_set_uint8(x_476, sizeof(void*)*4, x_475);
x_477 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_477, 0, x_476);
lean::cnstr_set(x_477, 1, x_316);
lean::cnstr_set(x_477, 2, x_317);
lean::cnstr_set(x_477, 3, x_318);
lean::cnstr_set_uint8(x_477, sizeof(void*)*4, x_453);
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
obj* l_RBNode_insert___at_Lean_Environment_addAux___spec__2(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
uint8 l_AssocList_contains___main___at_Lean_Environment_addAux___spec__5(obj* x_1, obj* x_2) {
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
obj* l_AssocList_mfoldl___main___at_Lean_Environment_addAux___spec__8(obj* x_1, obj* x_2) {
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
x_6 = lean_array_get_size(x_1);
x_7 = lean_name_hash_usize(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean::dec(x_6);
x_9 = lean::box_size_t(x_8);
x_10 = lean::unbox_size_t(x_9);
x_11 = lean_array_uget(x_1, x_10);
lean::cnstr_set(x_2, 2, x_11);
x_12 = lean::unbox_size_t(x_9);
lean::dec(x_9);
x_13 = lean_array_uset(x_1, x_12, x_2);
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
x_18 = lean_array_get_size(x_1);
x_19 = lean_name_hash_usize(x_15);
x_20 = lean_usize_modn(x_19, x_18);
lean::dec(x_18);
x_21 = lean::box_size_t(x_20);
x_22 = lean::unbox_size_t(x_21);
x_23 = lean_array_uget(x_1, x_22);
x_24 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_24, 0, x_15);
lean::cnstr_set(x_24, 1, x_16);
lean::cnstr_set(x_24, 2, x_23);
x_25 = lean::unbox_size_t(x_21);
lean::dec(x_21);
x_26 = lean_array_uset(x_1, x_25, x_24);
x_1 = x_26;
x_2 = x_17;
goto _start;
}
}
}
}
obj* l_HashMapImp_moveEntries___main___at_Lean_Environment_addAux___spec__7(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
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
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean::box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_AssocList_mfoldl___main___at_Lean_Environment_addAux___spec__8(x_3, x_6);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean_nat_add(x_1, x_10);
lean::dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
obj* l_HashMapImp_expand___at_Lean_Environment_addAux___spec__6(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean::mk_nat_obj(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean::dec(x_3);
x_6 = lean::box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean::mk_nat_obj(0u);
x_9 = l_HashMapImp_moveEntries___main___at_Lean_Environment_addAux___spec__7(x_8, x_2, x_7);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_AssocList_replace___main___at_Lean_Environment_addAux___spec__9(obj* x_1, obj* x_2, obj* x_3) {
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
x_9 = l_AssocList_replace___main___at_Lean_Environment_addAux___spec__9(x_1, x_2, x_7);
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
x_14 = l_AssocList_replace___main___at_Lean_Environment_addAux___spec__9(x_1, x_2, x_12);
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
obj* l_HashMapImp_insert___at_Lean_Environment_addAux___spec__4(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; usize x_8; usize x_9; obj* x_10; usize x_11; obj* x_12; uint8 x_13; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_name_hash_usize(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean::box_size_t(x_9);
x_11 = lean::unbox_size_t(x_10);
x_12 = lean_array_uget(x_6, x_11);
x_13 = l_AssocList_contains___main___at_Lean_Environment_addAux___spec__5(x_2, x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; usize x_17; obj* x_18; uint8 x_19; 
x_14 = lean::mk_nat_obj(1u);
x_15 = lean_nat_add(x_5, x_14);
lean::dec(x_5);
x_16 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_16, 0, x_2);
lean::cnstr_set(x_16, 1, x_3);
lean::cnstr_set(x_16, 2, x_12);
x_17 = lean::unbox_size_t(x_10);
lean::dec(x_10);
x_18 = lean_array_uset(x_6, x_17, x_16);
x_19 = lean_nat_dec_le(x_15, x_7);
lean::dec(x_7);
if (x_19 == 0)
{
obj* x_20; 
lean::free_heap_obj(x_1);
x_20 = l_HashMapImp_expand___at_Lean_Environment_addAux___spec__6(x_15, x_18);
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
x_21 = l_AssocList_replace___main___at_Lean_Environment_addAux___spec__9(x_2, x_3, x_12);
x_22 = lean::unbox_size_t(x_10);
lean::dec(x_10);
x_23 = lean_array_uset(x_6, x_22, x_21);
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
x_26 = lean_array_get_size(x_25);
x_27 = lean_name_hash_usize(x_2);
x_28 = lean_usize_modn(x_27, x_26);
x_29 = lean::box_size_t(x_28);
x_30 = lean::unbox_size_t(x_29);
x_31 = lean_array_uget(x_25, x_30);
x_32 = l_AssocList_contains___main___at_Lean_Environment_addAux___spec__5(x_2, x_31);
if (x_32 == 0)
{
obj* x_33; obj* x_34; obj* x_35; usize x_36; obj* x_37; uint8 x_38; 
x_33 = lean::mk_nat_obj(1u);
x_34 = lean_nat_add(x_24, x_33);
lean::dec(x_24);
x_35 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_35, 0, x_2);
lean::cnstr_set(x_35, 1, x_3);
lean::cnstr_set(x_35, 2, x_31);
x_36 = lean::unbox_size_t(x_29);
lean::dec(x_29);
x_37 = lean_array_uset(x_25, x_36, x_35);
x_38 = lean_nat_dec_le(x_34, x_26);
lean::dec(x_26);
if (x_38 == 0)
{
obj* x_39; 
x_39 = l_HashMapImp_expand___at_Lean_Environment_addAux___spec__6(x_34, x_37);
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
x_41 = l_AssocList_replace___main___at_Lean_Environment_addAux___spec__9(x_2, x_3, x_31);
x_42 = lean::unbox_size_t(x_29);
lean::dec(x_29);
x_43 = lean_array_uset(x_25, x_42, x_41);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_24);
lean::cnstr_set(x_44, 1, x_43);
return x_44;
}
}
}
}
obj* l_Lean_SMap_insert___at_Lean_Environment_addAux___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::cnstr_get_uint8(x_1, sizeof(void*)*2);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_1);
if (x_5 == 0)
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_1, 1);
x_7 = l_RBNode_insert___at_Lean_Environment_addAux___spec__2(x_6, x_2, x_3);
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
x_10 = l_RBNode_insert___at_Lean_Environment_addAux___spec__2(x_9, x_2, x_3);
x_11 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set_uint8(x_11, sizeof(void*)*2, x_4);
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
x_14 = l_HashMapImp_insert___at_Lean_Environment_addAux___spec__4(x_13, x_2, x_3);
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
x_17 = l_HashMapImp_insert___at_Lean_Environment_addAux___spec__4(x_15, x_2, x_3);
x_18 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_16);
lean::cnstr_set_uint8(x_18, sizeof(void*)*2, x_4);
return x_18;
}
}
}
}
obj* l_Lean_Environment_addAux(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_1, 1);
x_5 = l_Lean_ConstantInfo_name(x_2);
x_6 = l_Lean_SMap_insert___at_Lean_Environment_addAux___spec__1(x_4, x_5, x_2);
lean::cnstr_set(x_1, 1, x_6);
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
x_11 = l_Lean_ConstantInfo_name(x_2);
x_12 = l_Lean_SMap_insert___at_Lean_Environment_addAux___spec__1(x_8, x_11, x_2);
x_13 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_13, 0, x_7);
lean::cnstr_set(x_13, 1, x_12);
lean::cnstr_set(x_13, 2, x_9);
lean::cnstr_set(x_13, 3, x_10);
return x_13;
}
}
}
obj* l_AssocList_contains___main___at_Lean_Environment_addAux___spec__5___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_Environment_addAux___spec__5(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_AssocList_find___main___at_Lean_Environment_find___spec__3(obj* x_1, obj* x_2) {
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
obj* l_HashMapImp_find___at_Lean_Environment_find___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; usize x_5; usize x_6; obj* x_7; usize x_8; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_name_hash_usize(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean::dec(x_4);
x_7 = lean::box_size_t(x_6);
x_8 = lean::unbox_size_t(x_7);
lean::dec(x_7);
x_9 = lean_array_uget(x_3, x_8);
x_10 = l_AssocList_find___main___at_Lean_Environment_find___spec__3(x_2, x_9);
lean::dec(x_9);
return x_10;
}
}
obj* l_RBNode_find___main___at_Lean_Environment_find___spec__4(obj* x_1, obj* x_2) {
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
obj* l_Lean_SMap_find_x27___at_Lean_Environment_find___spec__1(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::cnstr_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = l_HashMapImp_find___at_Lean_Environment_find___spec__2(x_4, x_2);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; 
x_7 = l_RBNode_find___main___at_Lean_Environment_find___spec__4(x_5, x_2);
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
x_9 = l_HashMapImp_find___at_Lean_Environment_find___spec__2(x_8, x_2);
return x_9;
}
}
}
obj* lean_environment_find(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_Lean_SMap_find_x27___at_Lean_Environment_find___spec__1(x_3, x_2);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_AssocList_find___main___at_Lean_Environment_find___spec__3___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_AssocList_find___main___at_Lean_Environment_find___spec__3(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_HashMapImp_find___at_Lean_Environment_find___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_HashMapImp_find___at_Lean_Environment_find___spec__2(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_RBNode_find___main___at_Lean_Environment_find___spec__4___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___at_Lean_Environment_find___spec__4(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_SMap_find_x27___at_Lean_Environment_find___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_SMap_find_x27___at_Lean_Environment_find___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
uint8 l_HashMapImp_contains___at_Lean_Environment_contains___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; usize x_5; usize x_6; obj* x_7; usize x_8; obj* x_9; uint8 x_10; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_name_hash_usize(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean::dec(x_4);
x_7 = lean::box_size_t(x_6);
x_8 = lean::unbox_size_t(x_7);
lean::dec(x_7);
x_9 = lean_array_uget(x_3, x_8);
x_10 = l_AssocList_contains___main___at_Lean_Environment_addAux___spec__5(x_2, x_9);
lean::dec(x_9);
return x_10;
}
}
uint8 l_Lean_SMap_contains___at_Lean_Environment_contains___spec__1(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::cnstr_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = l_HashMapImp_contains___at_Lean_Environment_contains___spec__2(x_4, x_2);
if (x_6 == 0)
{
obj* x_7; 
x_7 = l_RBNode_find___main___at_Lean_Environment_find___spec__4(x_5, x_2);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8 x_9; 
lean::dec(x_7);
x_9 = 1;
return x_9;
}
}
else
{
uint8 x_10; 
x_10 = 1;
return x_10;
}
}
else
{
obj* x_11; uint8 x_12; 
x_11 = lean::cnstr_get(x_1, 0);
x_12 = l_HashMapImp_contains___at_Lean_Environment_contains___spec__2(x_11, x_2);
return x_12;
}
}
}
uint8 l_Lean_Environment_contains(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = l_Lean_SMap_contains___at_Lean_Environment_contains___spec__1(x_3, x_2);
return x_4;
}
}
obj* l_HashMapImp_contains___at_Lean_Environment_contains___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_HashMapImp_contains___at_Lean_Environment_contains___spec__2(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Lean_SMap_contains___at_Lean_Environment_contains___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_SMap_contains___at_Lean_Environment_contains___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Lean_Environment_contains___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_Environment_contains(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Lean_Environment_imports(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::cnstr_get(x_1, 3);
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
return x_3;
}
}
obj* l_Lean_Environment_imports___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Environment_imports(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* lean_environment_set_main_module(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; uint8 x_5; 
x_4 = lean::cnstr_get(x_1, 3);
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; 
x_6 = lean::cnstr_get(x_4, 0);
lean::dec(x_6);
lean::cnstr_set(x_4, 0, x_2);
return x_1;
}
else
{
uint32 x_7; uint8 x_8; obj* x_9; obj* x_10; 
x_7 = lean::cnstr_get_uint32(x_4, sizeof(void*)*2);
x_8 = lean::cnstr_get_uint8(x_4, sizeof(void*)*2 + 4);
x_9 = lean::cnstr_get(x_4, 1);
lean::inc(x_9);
lean::dec(x_4);
x_10 = lean::alloc_cnstr(0, 2, 5);
lean::cnstr_set(x_10, 0, x_2);
lean::cnstr_set(x_10, 1, x_9);
lean::cnstr_set_uint32(x_10, sizeof(void*)*2, x_7);
lean::cnstr_set_uint8(x_10, sizeof(void*)*2 + 4, x_8);
lean::cnstr_set(x_1, 3, x_10);
return x_1;
}
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; uint32 x_15; uint8 x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_11 = lean::cnstr_get(x_1, 3);
x_12 = lean::cnstr_get(x_1, 0);
x_13 = lean::cnstr_get(x_1, 1);
x_14 = lean::cnstr_get(x_1, 2);
lean::inc(x_11);
lean::inc(x_14);
lean::inc(x_13);
lean::inc(x_12);
lean::dec(x_1);
x_15 = lean::cnstr_get_uint32(x_11, sizeof(void*)*2);
x_16 = lean::cnstr_get_uint8(x_11, sizeof(void*)*2 + 4);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 x_18 = x_11;
} else {
 lean::dec_ref(x_11);
 x_18 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_19 = lean::alloc_cnstr(0, 2, 5);
} else {
 x_19 = x_18;
}
lean::cnstr_set(x_19, 0, x_2);
lean::cnstr_set(x_19, 1, x_17);
lean::cnstr_set_uint32(x_19, sizeof(void*)*2, x_15);
lean::cnstr_set_uint8(x_19, sizeof(void*)*2 + 4, x_16);
x_20 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_20, 0, x_12);
lean::cnstr_set(x_20, 1, x_13);
lean::cnstr_set(x_20, 2, x_14);
lean::cnstr_set(x_20, 3, x_19);
return x_20;
}
}
}
obj* lean_environment_main_module(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::cnstr_get(x_1, 3);
lean::inc(x_2);
lean::dec(x_1);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
return x_3;
}
}
obj* lean_environment_mark_quot_init(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; uint8 x_4; 
x_3 = lean::cnstr_get(x_1, 3);
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = 1;
lean::cnstr_set_uint8(x_3, sizeof(void*)*2 + 4, x_5);
return x_1;
}
else
{
uint32 x_6; obj* x_7; obj* x_8; uint8 x_9; obj* x_10; 
x_6 = lean::cnstr_get_uint32(x_3, sizeof(void*)*2);
x_7 = lean::cnstr_get(x_3, 0);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::inc(x_7);
lean::dec(x_3);
x_9 = 1;
x_10 = lean::alloc_cnstr(0, 2, 5);
lean::cnstr_set(x_10, 0, x_7);
lean::cnstr_set(x_10, 1, x_8);
lean::cnstr_set_uint32(x_10, sizeof(void*)*2, x_6);
lean::cnstr_set_uint8(x_10, sizeof(void*)*2 + 4, x_9);
lean::cnstr_set(x_1, 3, x_10);
return x_1;
}
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; uint32 x_15; obj* x_16; obj* x_17; obj* x_18; uint8 x_19; obj* x_20; obj* x_21; 
x_11 = lean::cnstr_get(x_1, 3);
x_12 = lean::cnstr_get(x_1, 0);
x_13 = lean::cnstr_get(x_1, 1);
x_14 = lean::cnstr_get(x_1, 2);
lean::inc(x_11);
lean::inc(x_14);
lean::inc(x_13);
lean::inc(x_12);
lean::dec(x_1);
x_15 = lean::cnstr_get_uint32(x_11, sizeof(void*)*2);
x_16 = lean::cnstr_get(x_11, 0);
lean::inc(x_16);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 x_18 = x_11;
} else {
 lean::dec_ref(x_11);
 x_18 = lean::box(0);
}
x_19 = 1;
if (lean::is_scalar(x_18)) {
 x_20 = lean::alloc_cnstr(0, 2, 5);
} else {
 x_20 = x_18;
}
lean::cnstr_set(x_20, 0, x_16);
lean::cnstr_set(x_20, 1, x_17);
lean::cnstr_set_uint32(x_20, sizeof(void*)*2, x_15);
lean::cnstr_set_uint8(x_20, sizeof(void*)*2 + 4, x_19);
x_21 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_21, 0, x_12);
lean::cnstr_set(x_21, 1, x_13);
lean::cnstr_set(x_21, 2, x_14);
lean::cnstr_set(x_21, 3, x_20);
return x_21;
}
}
}
uint8 lean_environment_quot_init(obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::cnstr_get(x_1, 3);
lean::inc(x_2);
lean::dec(x_1);
x_3 = lean::cnstr_get_uint8(x_2, sizeof(void*)*2 + 4);
lean::dec(x_2);
return x_3;
}
}
obj* l___private_init_lean_environment_2__isQuotInit___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean_environment_quot_init(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint32 lean_environment_trust_level(obj* x_1) {
_start:
{
obj* x_2; uint32 x_3; 
x_2 = lean::cnstr_get(x_1, 3);
lean::inc(x_2);
lean::dec(x_1);
x_3 = lean::cnstr_get_uint32(x_2, sizeof(void*)*2);
lean::dec(x_2);
return x_3;
}
}
obj* l___private_init_lean_environment_3__getTrustLevel___boxed(obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean_environment_trust_level(x_1);
x_3 = lean::box_uint32(x_2);
return x_3;
}
}
obj* l_AssocList_find___main___at_Lean_Environment_getModuleIdxFor___spec__2(obj* x_1, obj* x_2) {
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
obj* l_HashMapImp_find___at_Lean_Environment_getModuleIdxFor___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; usize x_5; usize x_6; obj* x_7; usize x_8; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_name_hash_usize(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean::dec(x_4);
x_7 = lean::box_size_t(x_6);
x_8 = lean::unbox_size_t(x_7);
lean::dec(x_7);
x_9 = lean_array_uget(x_3, x_8);
x_10 = l_AssocList_find___main___at_Lean_Environment_getModuleIdxFor___spec__2(x_2, x_9);
lean::dec(x_9);
return x_10;
}
}
obj* l_Lean_Environment_getModuleIdxFor(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = l_HashMapImp_find___at_Lean_Environment_getModuleIdxFor___spec__1(x_3, x_2);
return x_4;
}
}
obj* l_AssocList_find___main___at_Lean_Environment_getModuleIdxFor___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_AssocList_find___main___at_Lean_Environment_getModuleIdxFor___spec__2(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_HashMapImp_find___at_Lean_Environment_getModuleIdxFor___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_HashMapImp_find___at_Lean_Environment_getModuleIdxFor___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Environment_getModuleIdxFor___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Environment_getModuleIdxFor(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Lean_Environment_isConstructor(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_environment_find(x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
else
{
obj* x_5; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
lean::dec(x_3);
if (lean::obj_tag(x_5) == 6)
{
uint8 x_6; 
lean::dec(x_5);
x_6 = 1;
return x_6;
}
else
{
uint8 x_7; 
lean::dec(x_5);
x_7 = 0;
return x_7;
}
}
}
}
obj* l_Lean_Environment_isConstructor___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_Environment_isConstructor(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Lean_Environment_addDecl___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_add_decl(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Environment_compileDecl___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean_compile_decl(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Environment_addAndCompile(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean_add_decl(x_1, x_3);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::dec(x_4);
x_7 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
}
else
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_9 = lean_compile_decl(x_8, x_2, x_3);
return x_9;
}
}
}
obj* l_Lean_Environment_addAndCompile___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Environment_addAndCompile(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_EnvExtension_setStateUnsafe___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_2, 2);
x_6 = lean::cnstr_get(x_1, 0);
x_7 = l_Lean_EnvExtensionState_inhabited;
x_8 = x_3;
x_9 = lean_array_set(x_5, x_6, x_8);
lean::cnstr_set(x_2, 2, x_9);
return x_2;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_10 = lean::cnstr_get(x_2, 0);
x_11 = lean::cnstr_get(x_2, 1);
x_12 = lean::cnstr_get(x_2, 2);
x_13 = lean::cnstr_get(x_2, 3);
lean::inc(x_13);
lean::inc(x_12);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_2);
x_14 = lean::cnstr_get(x_1, 0);
x_15 = l_Lean_EnvExtensionState_inhabited;
x_16 = x_3;
x_17 = lean_array_set(x_12, x_14, x_16);
x_18 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_18, 0, x_10);
lean::cnstr_set(x_18, 1, x_11);
lean::cnstr_set(x_18, 2, x_17);
lean::cnstr_set(x_18, 3, x_13);
return x_18;
}
}
}
obj* l_Lean_EnvExtension_setStateUnsafe(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_EnvExtension_setStateUnsafe___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Lean_EnvExtension_setStateUnsafe___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_EnvExtension_setStateUnsafe___rarg(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_Lean_EnvExtension_setState___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_HashMap_Inhabited___closed__1;
x_2 = l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2;
x_3 = l_Array_empty___closed__1;
x_4 = l_Lean_Environment_Inhabited___closed__2;
x_5 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_4);
return x_5;
}
}
obj* l_Lean_EnvExtension_setState(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_EnvExtension_setState___closed__1;
return x_5;
}
}
obj* l_Lean_EnvExtension_setState___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_EnvExtension_setState(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_EnvExtension_getStateUnsafe___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_2, 2);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_5 = l_Lean_EnvExtensionState_inhabited;
x_6 = lean_array_get(x_5, x_3, x_4);
lean::dec(x_4);
x_7 = lean::cnstr_get(x_1, 2);
lean::inc(x_7);
lean::dec(x_1);
x_8 = x_6;
return x_8;
}
}
obj* l_Lean_EnvExtension_getStateUnsafe(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_EnvExtension_getStateUnsafe___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Lean_EnvExtension_getStateUnsafe___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_EnvExtension_getState___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::cnstr_get(x_1, 2);
lean::inc(x_3);
return x_3;
}
}
obj* l_Lean_EnvExtension_getState(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_EnvExtension_getState___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Lean_EnvExtension_getState___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_EnvExtension_getState___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_EnvExtension_modifyStateUnsafe___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_5 = lean::cnstr_get(x_2, 2);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_1);
return x_2;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_9 = lean_array_fget(x_5, x_6);
x_10 = lean::mk_nat_obj(0u);
x_11 = lean_array_fset(x_5, x_6, x_10);
x_12 = lean::cnstr_get(x_1, 2);
lean::inc(x_12);
lean::dec(x_1);
x_13 = x_9;
x_14 = lean::apply_1(x_3, x_13);
x_15 = l_Lean_EnvExtensionState_inhabited;
x_16 = x_14;
x_17 = lean_array_fset(x_11, x_6, x_16);
lean::dec(x_6);
lean::cnstr_set(x_2, 2, x_17);
return x_2;
}
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; uint8 x_24; 
x_18 = lean::cnstr_get(x_2, 0);
x_19 = lean::cnstr_get(x_2, 1);
x_20 = lean::cnstr_get(x_2, 2);
x_21 = lean::cnstr_get(x_2, 3);
lean::inc(x_21);
lean::inc(x_20);
lean::inc(x_19);
lean::inc(x_18);
lean::dec(x_2);
x_22 = lean::cnstr_get(x_1, 0);
lean::inc(x_22);
x_23 = lean_array_get_size(x_20);
x_24 = lean_nat_dec_lt(x_22, x_23);
lean::dec(x_23);
if (x_24 == 0)
{
obj* x_25; 
lean::dec(x_22);
lean::dec(x_3);
lean::dec(x_1);
x_25 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_25, 0, x_18);
lean::cnstr_set(x_25, 1, x_19);
lean::cnstr_set(x_25, 2, x_20);
lean::cnstr_set(x_25, 3, x_21);
return x_25;
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_26 = lean_array_fget(x_20, x_22);
x_27 = lean::mk_nat_obj(0u);
x_28 = lean_array_fset(x_20, x_22, x_27);
x_29 = lean::cnstr_get(x_1, 2);
lean::inc(x_29);
lean::dec(x_1);
x_30 = x_26;
x_31 = lean::apply_1(x_3, x_30);
x_32 = l_Lean_EnvExtensionState_inhabited;
x_33 = x_31;
x_34 = lean_array_fset(x_28, x_22, x_33);
lean::dec(x_22);
x_35 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_35, 0, x_18);
lean::cnstr_set(x_35, 1, x_19);
lean::cnstr_set(x_35, 2, x_34);
lean::cnstr_set(x_35, 3, x_21);
return x_35;
}
}
}
}
obj* l_Lean_EnvExtension_modifyStateUnsafe(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_EnvExtension_modifyStateUnsafe___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_EnvExtension_modifyState(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_EnvExtension_setState___closed__1;
return x_5;
}
}
obj* l_Lean_EnvExtension_modifyState___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_EnvExtension_modifyState(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_5;
}
}
obj* l___private_init_lean_environment_4__mkEnvExtensionsRef(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Array_empty___closed__1;
x_3 = lean_io_mk_ref(x_2, x_1);
return x_3;
}
}
obj* l_Lean_EnvExtension_Inhabited___rarg___lambda__1(obj* x_1) {
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
obj* _init_l_Lean_EnvExtension_Inhabited___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_EnvExtension_Inhabited___rarg___lambda__1), 1, 0);
return x_1;
}
}
obj* l_Lean_EnvExtension_Inhabited___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::mk_nat_obj(0u);
x_3 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
lean::cnstr_set(x_4, 2, x_1);
return x_4;
}
}
obj* l_Lean_EnvExtension_Inhabited(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_EnvExtension_Inhabited___rarg), 1, 0);
return x_2;
}
}
obj* _init_l_Lean_registerEnvExtensionUnsafe___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("failed to register environment, extensions can only be registered during initialization");
return x_1;
}
}
obj* _init_l_Lean_registerEnvExtensionUnsafe___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::mk_nat_obj(0u);
x_2 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_3 = l_Lean_EnvExtensionState_inhabited;
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 2, x_3);
return x_4;
}
}
obj* l_Lean_registerEnvExtensionUnsafe___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean_io_initializing(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; uint8 x_6; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::unbox(x_5);
lean::dec(x_5);
if (x_6 == 0)
{
uint8 x_7; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = !lean::is_exclusive(x_4);
if (x_7 == 0)
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_4, 0);
lean::dec(x_8);
x_9 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
lean::cnstr_set_tag(x_4, 1);
lean::cnstr_set(x_4, 0, x_9);
return x_4;
}
else
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::cnstr_get(x_4, 1);
lean::inc(x_10);
lean::dec(x_4);
x_11 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_4);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_14 = lean::cnstr_get(x_4, 0);
lean::dec(x_14);
x_15 = lean::box(0);
lean::cnstr_set(x_4, 0, x_15);
x_16 = l___private_init_lean_environment_5__envExtensionsRef;
x_17 = lean_io_ref_get(x_16, x_4);
if (lean::obj_tag(x_17) == 0)
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_19 = lean::cnstr_get(x_17, 0);
lean::cnstr_set(x_17, 0, x_15);
x_20 = lean_array_get_size(x_19);
lean::dec(x_19);
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_1);
x_22 = lean_io_ref_get(x_16, x_17);
if (lean::obj_tag(x_22) == 0)
{
uint8 x_23; 
x_23 = !lean::is_exclusive(x_22);
if (x_23 == 0)
{
obj* x_24; obj* x_25; 
x_24 = lean::cnstr_get(x_22, 0);
lean::cnstr_set(x_22, 0, x_15);
x_25 = lean_io_ref_reset(x_16, x_22);
if (lean::obj_tag(x_25) == 0)
{
uint8 x_26; 
x_26 = !lean::is_exclusive(x_25);
if (x_26 == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_27 = lean::cnstr_get(x_25, 0);
lean::dec(x_27);
lean::cnstr_set(x_25, 0, x_15);
x_28 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_21);
x_29 = x_21;
x_30 = lean_array_push(x_24, x_29);
x_31 = lean_io_ref_set(x_16, x_30, x_25);
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
lean::cnstr_set(x_41, 0, x_15);
lean::cnstr_set(x_41, 1, x_40);
x_42 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_21);
x_43 = x_21;
x_44 = lean_array_push(x_24, x_43);
x_45 = lean_io_ref_set(x_16, x_44, x_41);
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
lean::cnstr_set(x_59, 0, x_15);
lean::cnstr_set(x_59, 1, x_58);
x_60 = lean_io_ref_reset(x_16, x_59);
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
lean::cnstr_set(x_63, 0, x_15);
lean::cnstr_set(x_63, 1, x_61);
x_64 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_21);
x_65 = x_21;
x_66 = lean_array_push(x_57, x_65);
x_67 = lean_io_ref_set(x_16, x_66, x_63);
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
obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
x_83 = lean::cnstr_get(x_17, 0);
x_84 = lean::cnstr_get(x_17, 1);
lean::inc(x_84);
lean::inc(x_83);
lean::dec(x_17);
x_85 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_85, 0, x_15);
lean::cnstr_set(x_85, 1, x_84);
x_86 = lean_array_get_size(x_83);
lean::dec(x_83);
x_87 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_2);
lean::cnstr_set(x_87, 2, x_1);
x_88 = lean_io_ref_get(x_16, x_85);
if (lean::obj_tag(x_88) == 0)
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_89 = lean::cnstr_get(x_88, 0);
lean::inc(x_89);
x_90 = lean::cnstr_get(x_88, 1);
lean::inc(x_90);
if (lean::is_exclusive(x_88)) {
 lean::cnstr_release(x_88, 0);
 lean::cnstr_release(x_88, 1);
 x_91 = x_88;
} else {
 lean::dec_ref(x_88);
 x_91 = lean::box(0);
}
if (lean::is_scalar(x_91)) {
 x_92 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_92 = x_91;
}
lean::cnstr_set(x_92, 0, x_15);
lean::cnstr_set(x_92, 1, x_90);
x_93 = lean_io_ref_reset(x_16, x_92);
if (lean::obj_tag(x_93) == 0)
{
obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
x_94 = lean::cnstr_get(x_93, 1);
lean::inc(x_94);
if (lean::is_exclusive(x_93)) {
 lean::cnstr_release(x_93, 0);
 lean::cnstr_release(x_93, 1);
 x_95 = x_93;
} else {
 lean::dec_ref(x_93);
 x_95 = lean::box(0);
}
if (lean::is_scalar(x_95)) {
 x_96 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_96 = x_95;
}
lean::cnstr_set(x_96, 0, x_15);
lean::cnstr_set(x_96, 1, x_94);
x_97 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_87);
x_98 = x_87;
x_99 = lean_array_push(x_89, x_98);
x_100 = lean_io_ref_set(x_16, x_99, x_96);
if (lean::obj_tag(x_100) == 0)
{
obj* x_101; obj* x_102; obj* x_103; 
x_101 = lean::cnstr_get(x_100, 1);
lean::inc(x_101);
if (lean::is_exclusive(x_100)) {
 lean::cnstr_release(x_100, 0);
 lean::cnstr_release(x_100, 1);
 x_102 = x_100;
} else {
 lean::dec_ref(x_100);
 x_102 = lean::box(0);
}
if (lean::is_scalar(x_102)) {
 x_103 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_103 = x_102;
}
lean::cnstr_set(x_103, 0, x_87);
lean::cnstr_set(x_103, 1, x_101);
return x_103;
}
else
{
obj* x_104; obj* x_105; obj* x_106; obj* x_107; 
lean::dec(x_87);
x_104 = lean::cnstr_get(x_100, 0);
lean::inc(x_104);
x_105 = lean::cnstr_get(x_100, 1);
lean::inc(x_105);
if (lean::is_exclusive(x_100)) {
 lean::cnstr_release(x_100, 0);
 lean::cnstr_release(x_100, 1);
 x_106 = x_100;
} else {
 lean::dec_ref(x_100);
 x_106 = lean::box(0);
}
if (lean::is_scalar(x_106)) {
 x_107 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_107 = x_106;
}
lean::cnstr_set(x_107, 0, x_104);
lean::cnstr_set(x_107, 1, x_105);
return x_107;
}
}
else
{
obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
lean::dec(x_89);
lean::dec(x_87);
x_108 = lean::cnstr_get(x_93, 0);
lean::inc(x_108);
x_109 = lean::cnstr_get(x_93, 1);
lean::inc(x_109);
if (lean::is_exclusive(x_93)) {
 lean::cnstr_release(x_93, 0);
 lean::cnstr_release(x_93, 1);
 x_110 = x_93;
} else {
 lean::dec_ref(x_93);
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
lean::dec(x_87);
x_112 = lean::cnstr_get(x_88, 0);
lean::inc(x_112);
x_113 = lean::cnstr_get(x_88, 1);
lean::inc(x_113);
if (lean::is_exclusive(x_88)) {
 lean::cnstr_release(x_88, 0);
 lean::cnstr_release(x_88, 1);
 x_114 = x_88;
} else {
 lean::dec_ref(x_88);
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
}
else
{
uint8 x_116; 
lean::dec(x_2);
lean::dec(x_1);
x_116 = !lean::is_exclusive(x_17);
if (x_116 == 0)
{
return x_17;
}
else
{
obj* x_117; obj* x_118; obj* x_119; 
x_117 = lean::cnstr_get(x_17, 0);
x_118 = lean::cnstr_get(x_17, 1);
lean::inc(x_118);
lean::inc(x_117);
lean::dec(x_17);
x_119 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_119, 0, x_117);
lean::cnstr_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; 
x_120 = lean::cnstr_get(x_4, 1);
lean::inc(x_120);
lean::dec(x_4);
x_121 = lean::box(0);
x_122 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_122, 0, x_121);
lean::cnstr_set(x_122, 1, x_120);
x_123 = l___private_init_lean_environment_5__envExtensionsRef;
x_124 = lean_io_ref_get(x_123, x_122);
if (lean::obj_tag(x_124) == 0)
{
obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; 
x_125 = lean::cnstr_get(x_124, 0);
lean::inc(x_125);
x_126 = lean::cnstr_get(x_124, 1);
lean::inc(x_126);
if (lean::is_exclusive(x_124)) {
 lean::cnstr_release(x_124, 0);
 lean::cnstr_release(x_124, 1);
 x_127 = x_124;
} else {
 lean::dec_ref(x_124);
 x_127 = lean::box(0);
}
if (lean::is_scalar(x_127)) {
 x_128 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_128 = x_127;
}
lean::cnstr_set(x_128, 0, x_121);
lean::cnstr_set(x_128, 1, x_126);
x_129 = lean_array_get_size(x_125);
lean::dec(x_125);
x_130 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_130, 0, x_129);
lean::cnstr_set(x_130, 1, x_2);
lean::cnstr_set(x_130, 2, x_1);
x_131 = lean_io_ref_get(x_123, x_128);
if (lean::obj_tag(x_131) == 0)
{
obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; 
x_132 = lean::cnstr_get(x_131, 0);
lean::inc(x_132);
x_133 = lean::cnstr_get(x_131, 1);
lean::inc(x_133);
if (lean::is_exclusive(x_131)) {
 lean::cnstr_release(x_131, 0);
 lean::cnstr_release(x_131, 1);
 x_134 = x_131;
} else {
 lean::dec_ref(x_131);
 x_134 = lean::box(0);
}
if (lean::is_scalar(x_134)) {
 x_135 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_135 = x_134;
}
lean::cnstr_set(x_135, 0, x_121);
lean::cnstr_set(x_135, 1, x_133);
x_136 = lean_io_ref_reset(x_123, x_135);
if (lean::obj_tag(x_136) == 0)
{
obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; 
x_137 = lean::cnstr_get(x_136, 1);
lean::inc(x_137);
if (lean::is_exclusive(x_136)) {
 lean::cnstr_release(x_136, 0);
 lean::cnstr_release(x_136, 1);
 x_138 = x_136;
} else {
 lean::dec_ref(x_136);
 x_138 = lean::box(0);
}
if (lean::is_scalar(x_138)) {
 x_139 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_139 = x_138;
}
lean::cnstr_set(x_139, 0, x_121);
lean::cnstr_set(x_139, 1, x_137);
x_140 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_130);
x_141 = x_130;
x_142 = lean_array_push(x_132, x_141);
x_143 = lean_io_ref_set(x_123, x_142, x_139);
if (lean::obj_tag(x_143) == 0)
{
obj* x_144; obj* x_145; obj* x_146; 
x_144 = lean::cnstr_get(x_143, 1);
lean::inc(x_144);
if (lean::is_exclusive(x_143)) {
 lean::cnstr_release(x_143, 0);
 lean::cnstr_release(x_143, 1);
 x_145 = x_143;
} else {
 lean::dec_ref(x_143);
 x_145 = lean::box(0);
}
if (lean::is_scalar(x_145)) {
 x_146 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_146 = x_145;
}
lean::cnstr_set(x_146, 0, x_130);
lean::cnstr_set(x_146, 1, x_144);
return x_146;
}
else
{
obj* x_147; obj* x_148; obj* x_149; obj* x_150; 
lean::dec(x_130);
x_147 = lean::cnstr_get(x_143, 0);
lean::inc(x_147);
x_148 = lean::cnstr_get(x_143, 1);
lean::inc(x_148);
if (lean::is_exclusive(x_143)) {
 lean::cnstr_release(x_143, 0);
 lean::cnstr_release(x_143, 1);
 x_149 = x_143;
} else {
 lean::dec_ref(x_143);
 x_149 = lean::box(0);
}
if (lean::is_scalar(x_149)) {
 x_150 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_150 = x_149;
}
lean::cnstr_set(x_150, 0, x_147);
lean::cnstr_set(x_150, 1, x_148);
return x_150;
}
}
else
{
obj* x_151; obj* x_152; obj* x_153; obj* x_154; 
lean::dec(x_132);
lean::dec(x_130);
x_151 = lean::cnstr_get(x_136, 0);
lean::inc(x_151);
x_152 = lean::cnstr_get(x_136, 1);
lean::inc(x_152);
if (lean::is_exclusive(x_136)) {
 lean::cnstr_release(x_136, 0);
 lean::cnstr_release(x_136, 1);
 x_153 = x_136;
} else {
 lean::dec_ref(x_136);
 x_153 = lean::box(0);
}
if (lean::is_scalar(x_153)) {
 x_154 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_154 = x_153;
}
lean::cnstr_set(x_154, 0, x_151);
lean::cnstr_set(x_154, 1, x_152);
return x_154;
}
}
else
{
obj* x_155; obj* x_156; obj* x_157; obj* x_158; 
lean::dec(x_130);
x_155 = lean::cnstr_get(x_131, 0);
lean::inc(x_155);
x_156 = lean::cnstr_get(x_131, 1);
lean::inc(x_156);
if (lean::is_exclusive(x_131)) {
 lean::cnstr_release(x_131, 0);
 lean::cnstr_release(x_131, 1);
 x_157 = x_131;
} else {
 lean::dec_ref(x_131);
 x_157 = lean::box(0);
}
if (lean::is_scalar(x_157)) {
 x_158 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_158 = x_157;
}
lean::cnstr_set(x_158, 0, x_155);
lean::cnstr_set(x_158, 1, x_156);
return x_158;
}
}
else
{
obj* x_159; obj* x_160; obj* x_161; obj* x_162; 
lean::dec(x_2);
lean::dec(x_1);
x_159 = lean::cnstr_get(x_124, 0);
lean::inc(x_159);
x_160 = lean::cnstr_get(x_124, 1);
lean::inc(x_160);
if (lean::is_exclusive(x_124)) {
 lean::cnstr_release(x_124, 0);
 lean::cnstr_release(x_124, 1);
 x_161 = x_124;
} else {
 lean::dec_ref(x_124);
 x_161 = lean::box(0);
}
if (lean::is_scalar(x_161)) {
 x_162 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_162 = x_161;
}
lean::cnstr_set(x_162, 0, x_159);
lean::cnstr_set(x_162, 1, x_160);
return x_162;
}
}
}
}
else
{
uint8 x_163; 
lean::dec(x_2);
lean::dec(x_1);
x_163 = !lean::is_exclusive(x_4);
if (x_163 == 0)
{
return x_4;
}
else
{
obj* x_164; obj* x_165; obj* x_166; 
x_164 = lean::cnstr_get(x_4, 0);
x_165 = lean::cnstr_get(x_4, 1);
lean::inc(x_165);
lean::inc(x_164);
lean::dec(x_4);
x_166 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_166, 0, x_164);
lean::cnstr_set(x_166, 1, x_165);
return x_166;
}
}
}
}
obj* l_Lean_registerEnvExtensionUnsafe(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerEnvExtensionUnsafe___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_registerEnvExtension___rarg(obj* x_1) {
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
obj* l_Lean_registerEnvExtension(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerEnvExtension___rarg), 1, 0);
return x_4;
}
}
obj* l_Lean_registerEnvExtension___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_registerEnvExtension(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Array_ummapAux___main___at___private_init_lean_environment_6__mkInitialExtensionStates___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_6; 
lean::dec(x_1);
x_6 = !lean::is_exclusive(x_3);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_3, 0);
lean::dec(x_7);
x_8 = l_Array_empty___closed__1;
x_9 = x_2;
lean::cnstr_set(x_3, 0, x_9);
return x_3;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_11 = l_Array_empty___closed__1;
x_12 = x_2;
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_10);
return x_13;
}
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_14 = lean_array_fget(x_2, x_1);
x_15 = lean::box(0);
lean::inc(x_14);
x_16 = x_15;
x_17 = lean_array_fset(x_2, x_1, x_16);
x_18 = lean::cnstr_get(x_14, 1);
lean::inc(x_18);
x_19 = lean::apply_1(x_18, x_3);
if (lean::obj_tag(x_19) == 0)
{
uint8 x_20; 
x_20 = !lean::is_exclusive(x_19);
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_21 = lean::cnstr_get(x_19, 0);
lean::cnstr_set(x_19, 0, x_15);
x_22 = lean::mk_nat_obj(1u);
x_23 = lean_nat_add(x_1, x_22);
x_24 = x_21;
x_25 = lean_array_fset(x_17, x_1, x_24);
lean::dec(x_1);
x_1 = x_23;
x_2 = x_25;
x_3 = x_19;
goto _start;
}
else
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_27 = lean::cnstr_get(x_19, 0);
x_28 = lean::cnstr_get(x_19, 1);
lean::inc(x_28);
lean::inc(x_27);
lean::dec(x_19);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_15);
lean::cnstr_set(x_29, 1, x_28);
x_30 = lean::mk_nat_obj(1u);
x_31 = lean_nat_add(x_1, x_30);
x_32 = x_27;
x_33 = lean_array_fset(x_17, x_1, x_32);
lean::dec(x_1);
x_1 = x_31;
x_2 = x_33;
x_3 = x_29;
goto _start;
}
}
else
{
uint8 x_35; 
lean::dec(x_17);
lean::dec(x_14);
lean::dec(x_1);
x_35 = !lean::is_exclusive(x_19);
if (x_35 == 0)
{
return x_19;
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = lean::cnstr_get(x_19, 0);
x_37 = lean::cnstr_get(x_19, 1);
lean::inc(x_37);
lean::inc(x_36);
lean::dec(x_19);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
obj* l___private_init_lean_environment_6__mkInitialExtensionStates(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l___private_init_lean_environment_5__envExtensionsRef;
x_3 = lean_io_ref_get(x_2, x_1);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::box(0);
lean::cnstr_set(x_3, 0, x_6);
x_7 = lean::mk_nat_obj(0u);
x_8 = l_Array_ummapAux___main___at___private_init_lean_environment_6__mkInitialExtensionStates___spec__1(x_7, x_5, x_3);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_9 = lean::cnstr_get(x_3, 0);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::inc(x_9);
lean::dec(x_3);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
x_13 = lean::mk_nat_obj(0u);
x_14 = l_Array_ummapAux___main___at___private_init_lean_environment_6__mkInitialExtensionStates___spec__1(x_13, x_9, x_12);
return x_14;
}
}
else
{
uint8 x_15; 
x_15 = !lean::is_exclusive(x_3);
if (x_15 == 0)
{
return x_3;
}
else
{
obj* x_16; obj* x_17; obj* x_18; 
x_16 = lean::cnstr_get(x_3, 0);
x_17 = lean::cnstr_get(x_3, 1);
lean::inc(x_17);
lean::inc(x_16);
lean::dec(x_3);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
}
}
obj* _init_l_Lean_mkEmptyEnvironment___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("environment objects cannot be created during initialization");
return x_1;
}
}
obj* lean_mk_empty_environment(uint32 x_1, obj* x_2) {
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
x_6 = !lean::is_exclusive(x_3);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_3, 0);
lean::dec(x_7);
x_8 = lean::box(0);
lean::cnstr_set(x_3, 0, x_8);
x_9 = l___private_init_lean_environment_6__mkInitialExtensionStates(x_3);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_9);
if (x_10 == 0)
{
obj* x_11; uint8 x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_11 = lean::cnstr_get(x_9, 0);
x_12 = 0;
x_13 = lean::box(0);
x_14 = l_Array_empty___closed__1;
x_15 = lean::alloc_cnstr(0, 2, 5);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
lean::cnstr_set_uint32(x_15, sizeof(void*)*2, x_1);
lean::cnstr_set_uint8(x_15, sizeof(void*)*2 + 4, x_12);
x_16 = l_HashMap_Inhabited___closed__1;
x_17 = l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2;
x_18 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
lean::cnstr_set(x_18, 2, x_11);
lean::cnstr_set(x_18, 3, x_15);
lean::cnstr_set(x_9, 0, x_18);
return x_9;
}
else
{
obj* x_19; obj* x_20; uint8 x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_19 = lean::cnstr_get(x_9, 0);
x_20 = lean::cnstr_get(x_9, 1);
lean::inc(x_20);
lean::inc(x_19);
lean::dec(x_9);
x_21 = 0;
x_22 = lean::box(0);
x_23 = l_Array_empty___closed__1;
x_24 = lean::alloc_cnstr(0, 2, 5);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
lean::cnstr_set_uint32(x_24, sizeof(void*)*2, x_1);
lean::cnstr_set_uint8(x_24, sizeof(void*)*2 + 4, x_21);
x_25 = l_HashMap_Inhabited___closed__1;
x_26 = l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2;
x_27 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_26);
lean::cnstr_set(x_27, 2, x_19);
lean::cnstr_set(x_27, 3, x_24);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_20);
return x_28;
}
}
else
{
uint8 x_29; 
x_29 = !lean::is_exclusive(x_9);
if (x_29 == 0)
{
return x_9;
}
else
{
obj* x_30; obj* x_31; obj* x_32; 
x_30 = lean::cnstr_get(x_9, 0);
x_31 = lean::cnstr_get(x_9, 1);
lean::inc(x_31);
lean::inc(x_30);
lean::dec(x_9);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_33 = lean::cnstr_get(x_3, 1);
lean::inc(x_33);
lean::dec(x_3);
x_34 = lean::box(0);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_33);
x_36 = l___private_init_lean_environment_6__mkInitialExtensionStates(x_35);
if (lean::obj_tag(x_36) == 0)
{
obj* x_37; obj* x_38; obj* x_39; uint8 x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
x_38 = lean::cnstr_get(x_36, 1);
lean::inc(x_38);
if (lean::is_exclusive(x_36)) {
 lean::cnstr_release(x_36, 0);
 lean::cnstr_release(x_36, 1);
 x_39 = x_36;
} else {
 lean::dec_ref(x_36);
 x_39 = lean::box(0);
}
x_40 = 0;
x_41 = lean::box(0);
x_42 = l_Array_empty___closed__1;
x_43 = lean::alloc_cnstr(0, 2, 5);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_42);
lean::cnstr_set_uint32(x_43, sizeof(void*)*2, x_1);
lean::cnstr_set_uint8(x_43, sizeof(void*)*2 + 4, x_40);
x_44 = l_HashMap_Inhabited___closed__1;
x_45 = l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2;
x_46 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_46, 0, x_44);
lean::cnstr_set(x_46, 1, x_45);
lean::cnstr_set(x_46, 2, x_37);
lean::cnstr_set(x_46, 3, x_43);
if (lean::is_scalar(x_39)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_39;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_38);
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_48 = lean::cnstr_get(x_36, 0);
lean::inc(x_48);
x_49 = lean::cnstr_get(x_36, 1);
lean::inc(x_49);
if (lean::is_exclusive(x_36)) {
 lean::cnstr_release(x_36, 0);
 lean::cnstr_release(x_36, 1);
 x_50 = x_36;
} else {
 lean::dec_ref(x_36);
 x_50 = lean::box(0);
}
if (lean::is_scalar(x_50)) {
 x_51 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_51 = x_50;
}
lean::cnstr_set(x_51, 0, x_48);
lean::cnstr_set(x_51, 1, x_49);
return x_51;
}
}
}
else
{
uint8 x_52; 
x_52 = !lean::is_exclusive(x_3);
if (x_52 == 0)
{
obj* x_53; obj* x_54; 
x_53 = lean::cnstr_get(x_3, 0);
lean::dec(x_53);
x_54 = l_Lean_mkEmptyEnvironment___closed__1;
lean::cnstr_set_tag(x_3, 1);
lean::cnstr_set(x_3, 0, x_54);
return x_3;
}
else
{
obj* x_55; obj* x_56; obj* x_57; 
x_55 = lean::cnstr_get(x_3, 1);
lean::inc(x_55);
lean::dec(x_3);
x_56 = l_Lean_mkEmptyEnvironment___closed__1;
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_55);
return x_57;
}
}
}
else
{
uint8 x_58; 
x_58 = !lean::is_exclusive(x_3);
if (x_58 == 0)
{
return x_3;
}
else
{
obj* x_59; obj* x_60; obj* x_61; 
x_59 = lean::cnstr_get(x_3, 0);
x_60 = lean::cnstr_get(x_3, 1);
lean::inc(x_60);
lean::inc(x_59);
lean::dec(x_3);
x_61 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_61, 0, x_59);
lean::cnstr_set(x_61, 1, x_60);
return x_61;
}
}
}
}
obj* l_Lean_mkEmptyEnvironment___boxed(obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_4 = lean_mk_empty_environment(x_3, x_2);
return x_4;
}
}
obj* _init_l_Lean_EnvExtensionEntry_inhabited() {
_start:
{
obj* x_1; 
x_1 = l_NonScalar_Inhabited;
return x_1;
}
}
obj* l_Lean_PersistentEnvExtensionState_inhabited___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Array_empty___closed__1;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
}
}
obj* l_Lean_PersistentEnvExtensionState_inhabited(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_PersistentEnvExtensionState_inhabited___rarg), 1, 0);
return x_3;
}
}
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__1(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_2, 0);
lean::dec(x_4);
x_5 = l_String_splitAux___main___closed__1;
lean::cnstr_set_tag(x_2, 1);
lean::cnstr_set(x_2, 0, x_5);
return x_2;
}
else
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_7 = l_String_splitAux___main___closed__1;
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_6);
return x_8;
}
}
}
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_empty___closed__1;
return x_2;
}
}
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__3(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
}
obj* _init_l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__1___boxed), 2, 0);
return x_1;
}
}
obj* _init_l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_Monad___rarg___lambda__8___boxed), 2, 0);
return x_1;
}
}
obj* _init_l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__2___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__3___boxed), 1, 0);
return x_1;
}
}
obj* l_Lean_PersistentEnvExtension_inhabited___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_2 = l_Array_empty___closed__1;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_6 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
lean::cnstr_set(x_6, 2, x_3);
x_7 = lean::box(0);
x_8 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
x_9 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
x_10 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
x_11 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
x_12 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_12, 0, x_6);
lean::cnstr_set(x_12, 1, x_7);
lean::cnstr_set(x_12, 2, x_8);
lean::cnstr_set(x_12, 3, x_9);
lean::cnstr_set(x_12, 4, x_10);
lean::cnstr_set(x_12, 5, x_11);
return x_12;
}
}
obj* l_Lean_PersistentEnvExtension_inhabited(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_PersistentEnvExtension_inhabited___rarg), 1, 0);
return x_3;
}
}
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__1(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__2___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__2(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__3___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__3(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_PersistentEnvExtension_getModuleEntries___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_4, x_2);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
lean::dec(x_5);
x_7 = l_Array_empty___closed__1;
x_8 = lean_array_get(x_7, x_6, x_3);
lean::dec(x_6);
return x_8;
}
}
obj* l_Lean_PersistentEnvExtension_getModuleEntries(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_PersistentEnvExtension_getModuleEntries___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_Lean_PersistentEnvExtension_getModuleEntries___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_PersistentEnvExtension_getModuleEntries___rarg(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_PersistentEnvExtension_addEntry___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_5 = !lean::is_exclusive(x_2);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_6 = lean::cnstr_get(x_2, 2);
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
return x_2;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; uint8 x_16; 
x_10 = lean_array_fget(x_6, x_7);
x_11 = lean::mk_nat_obj(0u);
x_12 = lean_array_fset(x_6, x_7, x_11);
x_13 = lean::cnstr_get(x_4, 2);
lean::inc(x_13);
lean::dec(x_4);
x_14 = x_10;
x_15 = lean::cnstr_get(x_1, 3);
lean::inc(x_15);
lean::dec(x_1);
x_16 = !lean::is_exclusive(x_14);
if (x_16 == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_17 = lean::cnstr_get(x_14, 1);
x_18 = lean::apply_2(x_15, x_17, x_3);
lean::cnstr_set(x_14, 1, x_18);
x_19 = l_Lean_EnvExtensionState_inhabited;
x_20 = x_14;
x_21 = lean_array_fset(x_12, x_7, x_20);
lean::dec(x_7);
lean::cnstr_set(x_2, 2, x_21);
return x_2;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_22 = lean::cnstr_get(x_14, 0);
x_23 = lean::cnstr_get(x_14, 1);
lean::inc(x_23);
lean::inc(x_22);
lean::dec(x_14);
x_24 = lean::apply_2(x_15, x_23, x_3);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_22);
lean::cnstr_set(x_25, 1, x_24);
x_26 = l_Lean_EnvExtensionState_inhabited;
x_27 = x_25;
x_28 = lean_array_fset(x_12, x_7, x_27);
lean::dec(x_7);
lean::cnstr_set(x_2, 2, x_28);
return x_2;
}
}
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; uint8 x_35; 
x_29 = lean::cnstr_get(x_2, 0);
x_30 = lean::cnstr_get(x_2, 1);
x_31 = lean::cnstr_get(x_2, 2);
x_32 = lean::cnstr_get(x_2, 3);
lean::inc(x_32);
lean::inc(x_31);
lean::inc(x_30);
lean::inc(x_29);
lean::dec(x_2);
x_33 = lean::cnstr_get(x_4, 0);
lean::inc(x_33);
x_34 = lean_array_get_size(x_31);
x_35 = lean_nat_dec_lt(x_33, x_34);
lean::dec(x_34);
if (x_35 == 0)
{
obj* x_36; 
lean::dec(x_33);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_36 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_36, 0, x_29);
lean::cnstr_set(x_36, 1, x_30);
lean::cnstr_set(x_36, 2, x_31);
lean::cnstr_set(x_36, 3, x_32);
return x_36;
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_37 = lean_array_fget(x_31, x_33);
x_38 = lean::mk_nat_obj(0u);
x_39 = lean_array_fset(x_31, x_33, x_38);
x_40 = lean::cnstr_get(x_4, 2);
lean::inc(x_40);
lean::dec(x_4);
x_41 = x_37;
x_42 = lean::cnstr_get(x_1, 3);
lean::inc(x_42);
lean::dec(x_1);
x_43 = lean::cnstr_get(x_41, 0);
lean::inc(x_43);
x_44 = lean::cnstr_get(x_41, 1);
lean::inc(x_44);
if (lean::is_exclusive(x_41)) {
 lean::cnstr_release(x_41, 0);
 lean::cnstr_release(x_41, 1);
 x_45 = x_41;
} else {
 lean::dec_ref(x_41);
 x_45 = lean::box(0);
}
x_46 = lean::apply_2(x_42, x_44, x_3);
if (lean::is_scalar(x_45)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_45;
}
lean::cnstr_set(x_47, 0, x_43);
lean::cnstr_set(x_47, 1, x_46);
x_48 = l_Lean_EnvExtensionState_inhabited;
x_49 = x_47;
x_50 = lean_array_fset(x_39, x_33, x_49);
lean::dec(x_33);
x_51 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_51, 0, x_29);
lean::cnstr_set(x_51, 1, x_30);
lean::cnstr_set(x_51, 2, x_50);
lean::cnstr_set(x_51, 3, x_32);
return x_51;
}
}
}
}
obj* l_Lean_PersistentEnvExtension_addEntry(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_PersistentEnvExtension_addEntry___rarg), 3, 0);
return x_3;
}
}
obj* l_Lean_PersistentEnvExtension_getState___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_3, x_2);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_PersistentEnvExtension_getState(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_PersistentEnvExtension_getState___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_Lean_PersistentEnvExtension_getState___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_PersistentEnvExtension_getState___rarg(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_PersistentEnvExtension_setState___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = !lean::is_exclusive(x_2);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_6 = lean::cnstr_get(x_2, 2);
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_3);
return x_2;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; uint8 x_15; 
x_10 = lean_array_fget(x_6, x_7);
x_11 = lean::mk_nat_obj(0u);
x_12 = lean_array_fset(x_6, x_7, x_11);
x_13 = lean::cnstr_get(x_4, 2);
lean::inc(x_13);
lean::dec(x_4);
x_14 = x_10;
x_15 = !lean::is_exclusive(x_14);
if (x_15 == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_16 = lean::cnstr_get(x_14, 1);
lean::dec(x_16);
lean::cnstr_set(x_14, 1, x_3);
x_17 = l_Lean_EnvExtensionState_inhabited;
x_18 = x_14;
x_19 = lean_array_fset(x_12, x_7, x_18);
lean::dec(x_7);
lean::cnstr_set(x_2, 2, x_19);
return x_2;
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_20 = lean::cnstr_get(x_14, 0);
lean::inc(x_20);
lean::dec(x_14);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_3);
x_22 = l_Lean_EnvExtensionState_inhabited;
x_23 = x_21;
x_24 = lean_array_fset(x_12, x_7, x_23);
lean::dec(x_7);
lean::cnstr_set(x_2, 2, x_24);
return x_2;
}
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; uint8 x_31; 
x_25 = lean::cnstr_get(x_2, 0);
x_26 = lean::cnstr_get(x_2, 1);
x_27 = lean::cnstr_get(x_2, 2);
x_28 = lean::cnstr_get(x_2, 3);
lean::inc(x_28);
lean::inc(x_27);
lean::inc(x_26);
lean::inc(x_25);
lean::dec(x_2);
x_29 = lean::cnstr_get(x_4, 0);
lean::inc(x_29);
x_30 = lean_array_get_size(x_27);
x_31 = lean_nat_dec_lt(x_29, x_30);
lean::dec(x_30);
if (x_31 == 0)
{
obj* x_32; 
lean::dec(x_29);
lean::dec(x_4);
lean::dec(x_3);
x_32 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_32, 0, x_25);
lean::cnstr_set(x_32, 1, x_26);
lean::cnstr_set(x_32, 2, x_27);
lean::cnstr_set(x_32, 3, x_28);
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_33 = lean_array_fget(x_27, x_29);
x_34 = lean::mk_nat_obj(0u);
x_35 = lean_array_fset(x_27, x_29, x_34);
x_36 = lean::cnstr_get(x_4, 2);
lean::inc(x_36);
lean::dec(x_4);
x_37 = x_33;
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 x_39 = x_37;
} else {
 lean::dec_ref(x_37);
 x_39 = lean::box(0);
}
if (lean::is_scalar(x_39)) {
 x_40 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_40 = x_39;
}
lean::cnstr_set(x_40, 0, x_38);
lean::cnstr_set(x_40, 1, x_3);
x_41 = l_Lean_EnvExtensionState_inhabited;
x_42 = x_40;
x_43 = lean_array_fset(x_35, x_29, x_42);
lean::dec(x_29);
x_44 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_44, 0, x_25);
lean::cnstr_set(x_44, 1, x_26);
lean::cnstr_set(x_44, 2, x_43);
lean::cnstr_set(x_44, 3, x_28);
return x_44;
}
}
}
}
obj* l_Lean_PersistentEnvExtension_setState(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_PersistentEnvExtension_setState___rarg), 3, 0);
return x_3;
}
}
obj* l_Lean_PersistentEnvExtension_modifyState___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = !lean::is_exclusive(x_2);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_6 = lean::cnstr_get(x_2, 2);
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_3);
return x_2;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; uint8 x_15; 
x_10 = lean_array_fget(x_6, x_7);
x_11 = lean::mk_nat_obj(0u);
x_12 = lean_array_fset(x_6, x_7, x_11);
x_13 = lean::cnstr_get(x_4, 2);
lean::inc(x_13);
lean::dec(x_4);
x_14 = x_10;
x_15 = !lean::is_exclusive(x_14);
if (x_15 == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_16 = lean::cnstr_get(x_14, 1);
x_17 = lean::apply_1(x_3, x_16);
lean::cnstr_set(x_14, 1, x_17);
x_18 = l_Lean_EnvExtensionState_inhabited;
x_19 = x_14;
x_20 = lean_array_fset(x_12, x_7, x_19);
lean::dec(x_7);
lean::cnstr_set(x_2, 2, x_20);
return x_2;
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_21 = lean::cnstr_get(x_14, 0);
x_22 = lean::cnstr_get(x_14, 1);
lean::inc(x_22);
lean::inc(x_21);
lean::dec(x_14);
x_23 = lean::apply_1(x_3, x_22);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_21);
lean::cnstr_set(x_24, 1, x_23);
x_25 = l_Lean_EnvExtensionState_inhabited;
x_26 = x_24;
x_27 = lean_array_fset(x_12, x_7, x_26);
lean::dec(x_7);
lean::cnstr_set(x_2, 2, x_27);
return x_2;
}
}
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; uint8 x_34; 
x_28 = lean::cnstr_get(x_2, 0);
x_29 = lean::cnstr_get(x_2, 1);
x_30 = lean::cnstr_get(x_2, 2);
x_31 = lean::cnstr_get(x_2, 3);
lean::inc(x_31);
lean::inc(x_30);
lean::inc(x_29);
lean::inc(x_28);
lean::dec(x_2);
x_32 = lean::cnstr_get(x_4, 0);
lean::inc(x_32);
x_33 = lean_array_get_size(x_30);
x_34 = lean_nat_dec_lt(x_32, x_33);
lean::dec(x_33);
if (x_34 == 0)
{
obj* x_35; 
lean::dec(x_32);
lean::dec(x_4);
lean::dec(x_3);
x_35 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_35, 0, x_28);
lean::cnstr_set(x_35, 1, x_29);
lean::cnstr_set(x_35, 2, x_30);
lean::cnstr_set(x_35, 3, x_31);
return x_35;
}
else
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_36 = lean_array_fget(x_30, x_32);
x_37 = lean::mk_nat_obj(0u);
x_38 = lean_array_fset(x_30, x_32, x_37);
x_39 = lean::cnstr_get(x_4, 2);
lean::inc(x_39);
lean::dec(x_4);
x_40 = x_36;
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_42 = lean::cnstr_get(x_40, 1);
lean::inc(x_42);
if (lean::is_exclusive(x_40)) {
 lean::cnstr_release(x_40, 0);
 lean::cnstr_release(x_40, 1);
 x_43 = x_40;
} else {
 lean::dec_ref(x_40);
 x_43 = lean::box(0);
}
x_44 = lean::apply_1(x_3, x_42);
if (lean::is_scalar(x_43)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_43;
}
lean::cnstr_set(x_45, 0, x_41);
lean::cnstr_set(x_45, 1, x_44);
x_46 = l_Lean_EnvExtensionState_inhabited;
x_47 = x_45;
x_48 = lean_array_fset(x_38, x_32, x_47);
lean::dec(x_32);
x_49 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_49, 0, x_28);
lean::cnstr_set(x_49, 1, x_29);
lean::cnstr_set(x_49, 2, x_48);
lean::cnstr_set(x_49, 3, x_31);
return x_49;
}
}
}
}
obj* l_Lean_PersistentEnvExtension_modifyState(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_PersistentEnvExtension_modifyState___rarg), 3, 0);
return x_3;
}
}
obj* l___private_init_lean_environment_7__mkPersistentEnvExtensionsRef(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Array_empty___closed__1;
x_3 = lean_io_mk_ref(x_2, x_1);
return x_3;
}
}
uint8 l_Array_anyMAux___main___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
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
x_7 = lean_array_fget(x_2, x_3);
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
x_12 = lean_nat_add(x_3, x_11);
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
obj* l_Array_anyMAux___main___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_anyMAux___main___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_registerPersistentEnvExtensionUnsafe___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean_io_initializing(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; uint8 x_6; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::unbox(x_5);
lean::dec(x_5);
if (x_6 == 0)
{
uint8 x_7; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = !lean::is_exclusive(x_4);
if (x_7 == 0)
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_4, 0);
lean::dec(x_8);
x_9 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
lean::cnstr_set_tag(x_4, 1);
lean::cnstr_set(x_4, 0, x_9);
return x_4;
}
else
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::cnstr_get(x_4, 1);
lean::inc(x_10);
lean::dec(x_4);
x_11 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_4);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_14 = lean::cnstr_get(x_4, 0);
lean::dec(x_14);
x_15 = lean::box(0);
lean::cnstr_set(x_4, 0, x_15);
x_16 = l___private_init_lean_environment_5__envExtensionsRef;
x_17 = lean_io_ref_get(x_16, x_4);
if (lean::obj_tag(x_17) == 0)
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_19 = lean::cnstr_get(x_17, 0);
lean::cnstr_set(x_17, 0, x_15);
x_20 = lean_array_get_size(x_19);
lean::dec(x_19);
x_21 = l_Array_empty___closed__1;
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_1);
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_20);
lean::cnstr_set(x_23, 1, x_2);
lean::cnstr_set(x_23, 2, x_22);
x_24 = lean_io_ref_get(x_16, x_17);
if (lean::obj_tag(x_24) == 0)
{
uint8 x_25; 
x_25 = !lean::is_exclusive(x_24);
if (x_25 == 0)
{
obj* x_26; obj* x_27; 
x_26 = lean::cnstr_get(x_24, 0);
lean::cnstr_set(x_24, 0, x_15);
x_27 = lean_io_ref_reset(x_16, x_24);
if (lean::obj_tag(x_27) == 0)
{
uint8 x_28; 
x_28 = !lean::is_exclusive(x_27);
if (x_28 == 0)
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_29 = lean::cnstr_get(x_27, 0);
lean::dec(x_29);
lean::cnstr_set(x_27, 0, x_15);
x_30 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_23);
x_31 = x_23;
x_32 = lean_array_push(x_26, x_31);
x_33 = lean_io_ref_set(x_16, x_32, x_27);
if (lean::obj_tag(x_33) == 0)
{
uint8 x_34; 
x_34 = !lean::is_exclusive(x_33);
if (x_34 == 0)
{
obj* x_35; 
x_35 = lean::cnstr_get(x_33, 0);
lean::dec(x_35);
lean::cnstr_set(x_33, 0, x_23);
return x_33;
}
else
{
obj* x_36; obj* x_37; 
x_36 = lean::cnstr_get(x_33, 1);
lean::inc(x_36);
lean::dec(x_33);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_23);
lean::cnstr_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8 x_38; 
lean::dec(x_23);
x_38 = !lean::is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
obj* x_39; obj* x_40; obj* x_41; 
x_39 = lean::cnstr_get(x_33, 0);
x_40 = lean::cnstr_get(x_33, 1);
lean::inc(x_40);
lean::inc(x_39);
lean::dec(x_33);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_42 = lean::cnstr_get(x_27, 1);
lean::inc(x_42);
lean::dec(x_27);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_15);
lean::cnstr_set(x_43, 1, x_42);
x_44 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_23);
x_45 = x_23;
x_46 = lean_array_push(x_26, x_45);
x_47 = lean_io_ref_set(x_16, x_46, x_43);
if (lean::obj_tag(x_47) == 0)
{
obj* x_48; obj* x_49; obj* x_50; 
x_48 = lean::cnstr_get(x_47, 1);
lean::inc(x_48);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 x_49 = x_47;
} else {
 lean::dec_ref(x_47);
 x_49 = lean::box(0);
}
if (lean::is_scalar(x_49)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_49;
}
lean::cnstr_set(x_50, 0, x_23);
lean::cnstr_set(x_50, 1, x_48);
return x_50;
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_23);
x_51 = lean::cnstr_get(x_47, 0);
lean::inc(x_51);
x_52 = lean::cnstr_get(x_47, 1);
lean::inc(x_52);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 x_53 = x_47;
} else {
 lean::dec_ref(x_47);
 x_53 = lean::box(0);
}
if (lean::is_scalar(x_53)) {
 x_54 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_54 = x_53;
}
lean::cnstr_set(x_54, 0, x_51);
lean::cnstr_set(x_54, 1, x_52);
return x_54;
}
}
}
else
{
uint8 x_55; 
lean::dec(x_26);
lean::dec(x_23);
x_55 = !lean::is_exclusive(x_27);
if (x_55 == 0)
{
return x_27;
}
else
{
obj* x_56; obj* x_57; obj* x_58; 
x_56 = lean::cnstr_get(x_27, 0);
x_57 = lean::cnstr_get(x_27, 1);
lean::inc(x_57);
lean::inc(x_56);
lean::dec(x_27);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_59 = lean::cnstr_get(x_24, 0);
x_60 = lean::cnstr_get(x_24, 1);
lean::inc(x_60);
lean::inc(x_59);
lean::dec(x_24);
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_15);
lean::cnstr_set(x_61, 1, x_60);
x_62 = lean_io_ref_reset(x_16, x_61);
if (lean::obj_tag(x_62) == 0)
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_63 = lean::cnstr_get(x_62, 1);
lean::inc(x_63);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 lean::cnstr_release(x_62, 1);
 x_64 = x_62;
} else {
 lean::dec_ref(x_62);
 x_64 = lean::box(0);
}
if (lean::is_scalar(x_64)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_64;
}
lean::cnstr_set(x_65, 0, x_15);
lean::cnstr_set(x_65, 1, x_63);
x_66 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_23);
x_67 = x_23;
x_68 = lean_array_push(x_59, x_67);
x_69 = lean_io_ref_set(x_16, x_68, x_65);
if (lean::obj_tag(x_69) == 0)
{
obj* x_70; obj* x_71; obj* x_72; 
x_70 = lean::cnstr_get(x_69, 1);
lean::inc(x_70);
if (lean::is_exclusive(x_69)) {
 lean::cnstr_release(x_69, 0);
 lean::cnstr_release(x_69, 1);
 x_71 = x_69;
} else {
 lean::dec_ref(x_69);
 x_71 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_71;
}
lean::cnstr_set(x_72, 0, x_23);
lean::cnstr_set(x_72, 1, x_70);
return x_72;
}
else
{
obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
lean::dec(x_23);
x_73 = lean::cnstr_get(x_69, 0);
lean::inc(x_73);
x_74 = lean::cnstr_get(x_69, 1);
lean::inc(x_74);
if (lean::is_exclusive(x_69)) {
 lean::cnstr_release(x_69, 0);
 lean::cnstr_release(x_69, 1);
 x_75 = x_69;
} else {
 lean::dec_ref(x_69);
 x_75 = lean::box(0);
}
if (lean::is_scalar(x_75)) {
 x_76 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_76 = x_75;
}
lean::cnstr_set(x_76, 0, x_73);
lean::cnstr_set(x_76, 1, x_74);
return x_76;
}
}
else
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_59);
lean::dec(x_23);
x_77 = lean::cnstr_get(x_62, 0);
lean::inc(x_77);
x_78 = lean::cnstr_get(x_62, 1);
lean::inc(x_78);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 lean::cnstr_release(x_62, 1);
 x_79 = x_62;
} else {
 lean::dec_ref(x_62);
 x_79 = lean::box(0);
}
if (lean::is_scalar(x_79)) {
 x_80 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_80 = x_79;
}
lean::cnstr_set(x_80, 0, x_77);
lean::cnstr_set(x_80, 1, x_78);
return x_80;
}
}
}
else
{
uint8 x_81; 
lean::dec(x_23);
x_81 = !lean::is_exclusive(x_24);
if (x_81 == 0)
{
return x_24;
}
else
{
obj* x_82; obj* x_83; obj* x_84; 
x_82 = lean::cnstr_get(x_24, 0);
x_83 = lean::cnstr_get(x_24, 1);
lean::inc(x_83);
lean::inc(x_82);
lean::dec(x_24);
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_82);
lean::cnstr_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_85 = lean::cnstr_get(x_17, 0);
x_86 = lean::cnstr_get(x_17, 1);
lean::inc(x_86);
lean::inc(x_85);
lean::dec(x_17);
x_87 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_87, 0, x_15);
lean::cnstr_set(x_87, 1, x_86);
x_88 = lean_array_get_size(x_85);
lean::dec(x_85);
x_89 = l_Array_empty___closed__1;
x_90 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_1);
x_91 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_91, 0, x_88);
lean::cnstr_set(x_91, 1, x_2);
lean::cnstr_set(x_91, 2, x_90);
x_92 = lean_io_ref_get(x_16, x_87);
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
lean::cnstr_set(x_96, 0, x_15);
lean::cnstr_set(x_96, 1, x_94);
x_97 = lean_io_ref_reset(x_16, x_96);
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
lean::cnstr_set(x_100, 0, x_15);
lean::cnstr_set(x_100, 1, x_98);
x_101 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_91);
x_102 = x_91;
x_103 = lean_array_push(x_93, x_102);
x_104 = lean_io_ref_set(x_16, x_103, x_100);
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
lean::dec(x_2);
lean::dec(x_1);
x_120 = !lean::is_exclusive(x_17);
if (x_120 == 0)
{
return x_17;
}
else
{
obj* x_121; obj* x_122; obj* x_123; 
x_121 = lean::cnstr_get(x_17, 0);
x_122 = lean::cnstr_get(x_17, 1);
lean::inc(x_122);
lean::inc(x_121);
lean::dec(x_17);
x_123 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_123, 0, x_121);
lean::cnstr_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; 
x_124 = lean::cnstr_get(x_4, 1);
lean::inc(x_124);
lean::dec(x_4);
x_125 = lean::box(0);
x_126 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_126, 0, x_125);
lean::cnstr_set(x_126, 1, x_124);
x_127 = l___private_init_lean_environment_5__envExtensionsRef;
x_128 = lean_io_ref_get(x_127, x_126);
if (lean::obj_tag(x_128) == 0)
{
obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; 
x_129 = lean::cnstr_get(x_128, 0);
lean::inc(x_129);
x_130 = lean::cnstr_get(x_128, 1);
lean::inc(x_130);
if (lean::is_exclusive(x_128)) {
 lean::cnstr_release(x_128, 0);
 lean::cnstr_release(x_128, 1);
 x_131 = x_128;
} else {
 lean::dec_ref(x_128);
 x_131 = lean::box(0);
}
if (lean::is_scalar(x_131)) {
 x_132 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_132 = x_131;
}
lean::cnstr_set(x_132, 0, x_125);
lean::cnstr_set(x_132, 1, x_130);
x_133 = lean_array_get_size(x_129);
lean::dec(x_129);
x_134 = l_Array_empty___closed__1;
x_135 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_135, 0, x_134);
lean::cnstr_set(x_135, 1, x_1);
x_136 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_136, 0, x_133);
lean::cnstr_set(x_136, 1, x_2);
lean::cnstr_set(x_136, 2, x_135);
x_137 = lean_io_ref_get(x_127, x_132);
if (lean::obj_tag(x_137) == 0)
{
obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; 
x_138 = lean::cnstr_get(x_137, 0);
lean::inc(x_138);
x_139 = lean::cnstr_get(x_137, 1);
lean::inc(x_139);
if (lean::is_exclusive(x_137)) {
 lean::cnstr_release(x_137, 0);
 lean::cnstr_release(x_137, 1);
 x_140 = x_137;
} else {
 lean::dec_ref(x_137);
 x_140 = lean::box(0);
}
if (lean::is_scalar(x_140)) {
 x_141 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_141 = x_140;
}
lean::cnstr_set(x_141, 0, x_125);
lean::cnstr_set(x_141, 1, x_139);
x_142 = lean_io_ref_reset(x_127, x_141);
if (lean::obj_tag(x_142) == 0)
{
obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; 
x_143 = lean::cnstr_get(x_142, 1);
lean::inc(x_143);
if (lean::is_exclusive(x_142)) {
 lean::cnstr_release(x_142, 0);
 lean::cnstr_release(x_142, 1);
 x_144 = x_142;
} else {
 lean::dec_ref(x_142);
 x_144 = lean::box(0);
}
if (lean::is_scalar(x_144)) {
 x_145 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_145 = x_144;
}
lean::cnstr_set(x_145, 0, x_125);
lean::cnstr_set(x_145, 1, x_143);
x_146 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_136);
x_147 = x_136;
x_148 = lean_array_push(x_138, x_147);
x_149 = lean_io_ref_set(x_127, x_148, x_145);
if (lean::obj_tag(x_149) == 0)
{
obj* x_150; obj* x_151; obj* x_152; 
x_150 = lean::cnstr_get(x_149, 1);
lean::inc(x_150);
if (lean::is_exclusive(x_149)) {
 lean::cnstr_release(x_149, 0);
 lean::cnstr_release(x_149, 1);
 x_151 = x_149;
} else {
 lean::dec_ref(x_149);
 x_151 = lean::box(0);
}
if (lean::is_scalar(x_151)) {
 x_152 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_152 = x_151;
}
lean::cnstr_set(x_152, 0, x_136);
lean::cnstr_set(x_152, 1, x_150);
return x_152;
}
else
{
obj* x_153; obj* x_154; obj* x_155; obj* x_156; 
lean::dec(x_136);
x_153 = lean::cnstr_get(x_149, 0);
lean::inc(x_153);
x_154 = lean::cnstr_get(x_149, 1);
lean::inc(x_154);
if (lean::is_exclusive(x_149)) {
 lean::cnstr_release(x_149, 0);
 lean::cnstr_release(x_149, 1);
 x_155 = x_149;
} else {
 lean::dec_ref(x_149);
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
lean::dec(x_138);
lean::dec(x_136);
x_157 = lean::cnstr_get(x_142, 0);
lean::inc(x_157);
x_158 = lean::cnstr_get(x_142, 1);
lean::inc(x_158);
if (lean::is_exclusive(x_142)) {
 lean::cnstr_release(x_142, 0);
 lean::cnstr_release(x_142, 1);
 x_159 = x_142;
} else {
 lean::dec_ref(x_142);
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
lean::dec(x_136);
x_161 = lean::cnstr_get(x_137, 0);
lean::inc(x_161);
x_162 = lean::cnstr_get(x_137, 1);
lean::inc(x_162);
if (lean::is_exclusive(x_137)) {
 lean::cnstr_release(x_137, 0);
 lean::cnstr_release(x_137, 1);
 x_163 = x_137;
} else {
 lean::dec_ref(x_137);
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
else
{
obj* x_165; obj* x_166; obj* x_167; obj* x_168; 
lean::dec(x_2);
lean::dec(x_1);
x_165 = lean::cnstr_get(x_128, 0);
lean::inc(x_165);
x_166 = lean::cnstr_get(x_128, 1);
lean::inc(x_166);
if (lean::is_exclusive(x_128)) {
 lean::cnstr_release(x_128, 0);
 lean::cnstr_release(x_128, 1);
 x_167 = x_128;
} else {
 lean::dec_ref(x_128);
 x_167 = lean::box(0);
}
if (lean::is_scalar(x_167)) {
 x_168 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_168 = x_167;
}
lean::cnstr_set(x_168, 0, x_165);
lean::cnstr_set(x_168, 1, x_166);
return x_168;
}
}
}
}
else
{
uint8 x_169; 
lean::dec(x_2);
lean::dec(x_1);
x_169 = !lean::is_exclusive(x_4);
if (x_169 == 0)
{
return x_4;
}
else
{
obj* x_170; obj* x_171; obj* x_172; 
x_170 = lean::cnstr_get(x_4, 0);
x_171 = lean::cnstr_get(x_4, 1);
lean::inc(x_171);
lean::inc(x_170);
lean::dec(x_4);
x_172 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_172, 0, x_170);
lean::cnstr_set(x_172, 1, x_171);
return x_172;
}
}
}
}
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_registerPersistentEnvExtensionUnsafe___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerEnvExtensionUnsafe___at_Lean_registerPersistentEnvExtensionUnsafe___spec__2___rarg), 3, 0);
return x_3;
}
}
obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_3, 0);
lean::dec(x_5);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_3, 0, x_6);
return x_3;
}
else
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_3, 1);
lean::inc(x_7);
lean::dec(x_3);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_1);
lean::cnstr_set(x_8, 1, x_2);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_7);
return x_9;
}
}
}
obj* _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Array_empty___closed__1;
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__1), 3, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_EnvExtensionState_inhabited;
x_2 = l_Lean_PersistentEnvExtension_inhabited___rarg(x_1);
return x_2;
}
}
obj* _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("invalid environment extension, '");
return x_1;
}
}
obj* _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("' has already been used");
return x_1;
}
}
obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l___private_init_lean_environment_8__persistentEnvExtensionsRef;
x_5 = lean_io_ref_get(x_4, x_3);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; uint8 x_9; 
x_7 = lean::cnstr_get(x_5, 0);
x_8 = lean::mk_nat_obj(0u);
x_9 = l_Array_anyMAux___main___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg(x_2, x_7, x_8);
lean::dec(x_7);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_10 = lean::box(0);
lean::cnstr_set(x_5, 0, x_10);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
x_12 = l_Array_empty___closed__1;
lean::inc(x_11);
x_13 = lean::apply_1(x_11, x_12);
x_14 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_bind___rarg), 3, 2);
lean::closure_set(x_15, 0, x_13);
lean::closure_set(x_15, 1, x_14);
x_16 = l_Lean_registerEnvExtensionUnsafe___at_Lean_registerPersistentEnvExtensionUnsafe___spec__2___rarg(x_1, x_15, x_5);
if (lean::obj_tag(x_16) == 0)
{
uint8 x_17; 
x_17 = !lean::is_exclusive(x_16);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_18 = lean::cnstr_get(x_16, 0);
lean::cnstr_set(x_16, 0, x_10);
x_19 = lean::cnstr_get(x_2, 0);
lean::inc(x_19);
x_20 = lean::cnstr_get(x_2, 2);
lean::inc(x_20);
x_21 = lean::cnstr_get(x_2, 3);
lean::inc(x_21);
x_22 = lean::cnstr_get(x_2, 4);
lean::inc(x_22);
lean::dec(x_2);
x_23 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_23, 0, x_18);
lean::cnstr_set(x_23, 1, x_19);
lean::cnstr_set(x_23, 2, x_11);
lean::cnstr_set(x_23, 3, x_20);
lean::cnstr_set(x_23, 4, x_21);
lean::cnstr_set(x_23, 5, x_22);
x_24 = lean_io_ref_get(x_4, x_16);
if (lean::obj_tag(x_24) == 0)
{
uint8 x_25; 
x_25 = !lean::is_exclusive(x_24);
if (x_25 == 0)
{
obj* x_26; obj* x_27; 
x_26 = lean::cnstr_get(x_24, 0);
lean::cnstr_set(x_24, 0, x_10);
x_27 = lean_io_ref_reset(x_4, x_24);
if (lean::obj_tag(x_27) == 0)
{
uint8 x_28; 
x_28 = !lean::is_exclusive(x_27);
if (x_28 == 0)
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_29 = lean::cnstr_get(x_27, 0);
lean::dec(x_29);
lean::cnstr_set(x_27, 0, x_10);
x_30 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_23);
x_31 = x_23;
x_32 = lean_array_push(x_26, x_31);
x_33 = lean_io_ref_set(x_4, x_32, x_27);
if (lean::obj_tag(x_33) == 0)
{
uint8 x_34; 
x_34 = !lean::is_exclusive(x_33);
if (x_34 == 0)
{
obj* x_35; 
x_35 = lean::cnstr_get(x_33, 0);
lean::dec(x_35);
lean::cnstr_set(x_33, 0, x_23);
return x_33;
}
else
{
obj* x_36; obj* x_37; 
x_36 = lean::cnstr_get(x_33, 1);
lean::inc(x_36);
lean::dec(x_33);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_23);
lean::cnstr_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8 x_38; 
lean::dec(x_23);
x_38 = !lean::is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
obj* x_39; obj* x_40; obj* x_41; 
x_39 = lean::cnstr_get(x_33, 0);
x_40 = lean::cnstr_get(x_33, 1);
lean::inc(x_40);
lean::inc(x_39);
lean::dec(x_33);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_42 = lean::cnstr_get(x_27, 1);
lean::inc(x_42);
lean::dec(x_27);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_10);
lean::cnstr_set(x_43, 1, x_42);
x_44 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_23);
x_45 = x_23;
x_46 = lean_array_push(x_26, x_45);
x_47 = lean_io_ref_set(x_4, x_46, x_43);
if (lean::obj_tag(x_47) == 0)
{
obj* x_48; obj* x_49; obj* x_50; 
x_48 = lean::cnstr_get(x_47, 1);
lean::inc(x_48);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 x_49 = x_47;
} else {
 lean::dec_ref(x_47);
 x_49 = lean::box(0);
}
if (lean::is_scalar(x_49)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_49;
}
lean::cnstr_set(x_50, 0, x_23);
lean::cnstr_set(x_50, 1, x_48);
return x_50;
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_23);
x_51 = lean::cnstr_get(x_47, 0);
lean::inc(x_51);
x_52 = lean::cnstr_get(x_47, 1);
lean::inc(x_52);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 x_53 = x_47;
} else {
 lean::dec_ref(x_47);
 x_53 = lean::box(0);
}
if (lean::is_scalar(x_53)) {
 x_54 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_54 = x_53;
}
lean::cnstr_set(x_54, 0, x_51);
lean::cnstr_set(x_54, 1, x_52);
return x_54;
}
}
}
else
{
uint8 x_55; 
lean::dec(x_26);
lean::dec(x_23);
x_55 = !lean::is_exclusive(x_27);
if (x_55 == 0)
{
return x_27;
}
else
{
obj* x_56; obj* x_57; obj* x_58; 
x_56 = lean::cnstr_get(x_27, 0);
x_57 = lean::cnstr_get(x_27, 1);
lean::inc(x_57);
lean::inc(x_56);
lean::dec(x_27);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_59 = lean::cnstr_get(x_24, 0);
x_60 = lean::cnstr_get(x_24, 1);
lean::inc(x_60);
lean::inc(x_59);
lean::dec(x_24);
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_10);
lean::cnstr_set(x_61, 1, x_60);
x_62 = lean_io_ref_reset(x_4, x_61);
if (lean::obj_tag(x_62) == 0)
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_63 = lean::cnstr_get(x_62, 1);
lean::inc(x_63);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 lean::cnstr_release(x_62, 1);
 x_64 = x_62;
} else {
 lean::dec_ref(x_62);
 x_64 = lean::box(0);
}
if (lean::is_scalar(x_64)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_64;
}
lean::cnstr_set(x_65, 0, x_10);
lean::cnstr_set(x_65, 1, x_63);
x_66 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_23);
x_67 = x_23;
x_68 = lean_array_push(x_59, x_67);
x_69 = lean_io_ref_set(x_4, x_68, x_65);
if (lean::obj_tag(x_69) == 0)
{
obj* x_70; obj* x_71; obj* x_72; 
x_70 = lean::cnstr_get(x_69, 1);
lean::inc(x_70);
if (lean::is_exclusive(x_69)) {
 lean::cnstr_release(x_69, 0);
 lean::cnstr_release(x_69, 1);
 x_71 = x_69;
} else {
 lean::dec_ref(x_69);
 x_71 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_71;
}
lean::cnstr_set(x_72, 0, x_23);
lean::cnstr_set(x_72, 1, x_70);
return x_72;
}
else
{
obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
lean::dec(x_23);
x_73 = lean::cnstr_get(x_69, 0);
lean::inc(x_73);
x_74 = lean::cnstr_get(x_69, 1);
lean::inc(x_74);
if (lean::is_exclusive(x_69)) {
 lean::cnstr_release(x_69, 0);
 lean::cnstr_release(x_69, 1);
 x_75 = x_69;
} else {
 lean::dec_ref(x_69);
 x_75 = lean::box(0);
}
if (lean::is_scalar(x_75)) {
 x_76 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_76 = x_75;
}
lean::cnstr_set(x_76, 0, x_73);
lean::cnstr_set(x_76, 1, x_74);
return x_76;
}
}
else
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_59);
lean::dec(x_23);
x_77 = lean::cnstr_get(x_62, 0);
lean::inc(x_77);
x_78 = lean::cnstr_get(x_62, 1);
lean::inc(x_78);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 lean::cnstr_release(x_62, 1);
 x_79 = x_62;
} else {
 lean::dec_ref(x_62);
 x_79 = lean::box(0);
}
if (lean::is_scalar(x_79)) {
 x_80 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_80 = x_79;
}
lean::cnstr_set(x_80, 0, x_77);
lean::cnstr_set(x_80, 1, x_78);
return x_80;
}
}
}
else
{
uint8 x_81; 
lean::dec(x_23);
x_81 = !lean::is_exclusive(x_24);
if (x_81 == 0)
{
return x_24;
}
else
{
obj* x_82; obj* x_83; obj* x_84; 
x_82 = lean::cnstr_get(x_24, 0);
x_83 = lean::cnstr_get(x_24, 1);
lean::inc(x_83);
lean::inc(x_82);
lean::dec(x_24);
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_82);
lean::cnstr_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_85 = lean::cnstr_get(x_16, 0);
x_86 = lean::cnstr_get(x_16, 1);
lean::inc(x_86);
lean::inc(x_85);
lean::dec(x_16);
x_87 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_87, 0, x_10);
lean::cnstr_set(x_87, 1, x_86);
x_88 = lean::cnstr_get(x_2, 0);
lean::inc(x_88);
x_89 = lean::cnstr_get(x_2, 2);
lean::inc(x_89);
x_90 = lean::cnstr_get(x_2, 3);
lean::inc(x_90);
x_91 = lean::cnstr_get(x_2, 4);
lean::inc(x_91);
lean::dec(x_2);
x_92 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_92, 0, x_85);
lean::cnstr_set(x_92, 1, x_88);
lean::cnstr_set(x_92, 2, x_11);
lean::cnstr_set(x_92, 3, x_89);
lean::cnstr_set(x_92, 4, x_90);
lean::cnstr_set(x_92, 5, x_91);
x_93 = lean_io_ref_get(x_4, x_87);
if (lean::obj_tag(x_93) == 0)
{
obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
x_94 = lean::cnstr_get(x_93, 0);
lean::inc(x_94);
x_95 = lean::cnstr_get(x_93, 1);
lean::inc(x_95);
if (lean::is_exclusive(x_93)) {
 lean::cnstr_release(x_93, 0);
 lean::cnstr_release(x_93, 1);
 x_96 = x_93;
} else {
 lean::dec_ref(x_93);
 x_96 = lean::box(0);
}
if (lean::is_scalar(x_96)) {
 x_97 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_97 = x_96;
}
lean::cnstr_set(x_97, 0, x_10);
lean::cnstr_set(x_97, 1, x_95);
x_98 = lean_io_ref_reset(x_4, x_97);
if (lean::obj_tag(x_98) == 0)
{
obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; 
x_99 = lean::cnstr_get(x_98, 1);
lean::inc(x_99);
if (lean::is_exclusive(x_98)) {
 lean::cnstr_release(x_98, 0);
 lean::cnstr_release(x_98, 1);
 x_100 = x_98;
} else {
 lean::dec_ref(x_98);
 x_100 = lean::box(0);
}
if (lean::is_scalar(x_100)) {
 x_101 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_101 = x_100;
}
lean::cnstr_set(x_101, 0, x_10);
lean::cnstr_set(x_101, 1, x_99);
x_102 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_92);
x_103 = x_92;
x_104 = lean_array_push(x_94, x_103);
x_105 = lean_io_ref_set(x_4, x_104, x_101);
if (lean::obj_tag(x_105) == 0)
{
obj* x_106; obj* x_107; obj* x_108; 
x_106 = lean::cnstr_get(x_105, 1);
lean::inc(x_106);
if (lean::is_exclusive(x_105)) {
 lean::cnstr_release(x_105, 0);
 lean::cnstr_release(x_105, 1);
 x_107 = x_105;
} else {
 lean::dec_ref(x_105);
 x_107 = lean::box(0);
}
if (lean::is_scalar(x_107)) {
 x_108 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_108 = x_107;
}
lean::cnstr_set(x_108, 0, x_92);
lean::cnstr_set(x_108, 1, x_106);
return x_108;
}
else
{
obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_92);
x_109 = lean::cnstr_get(x_105, 0);
lean::inc(x_109);
x_110 = lean::cnstr_get(x_105, 1);
lean::inc(x_110);
if (lean::is_exclusive(x_105)) {
 lean::cnstr_release(x_105, 0);
 lean::cnstr_release(x_105, 1);
 x_111 = x_105;
} else {
 lean::dec_ref(x_105);
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
lean::dec(x_94);
lean::dec(x_92);
x_113 = lean::cnstr_get(x_98, 0);
lean::inc(x_113);
x_114 = lean::cnstr_get(x_98, 1);
lean::inc(x_114);
if (lean::is_exclusive(x_98)) {
 lean::cnstr_release(x_98, 0);
 lean::cnstr_release(x_98, 1);
 x_115 = x_98;
} else {
 lean::dec_ref(x_98);
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
else
{
obj* x_117; obj* x_118; obj* x_119; obj* x_120; 
lean::dec(x_92);
x_117 = lean::cnstr_get(x_93, 0);
lean::inc(x_117);
x_118 = lean::cnstr_get(x_93, 1);
lean::inc(x_118);
if (lean::is_exclusive(x_93)) {
 lean::cnstr_release(x_93, 0);
 lean::cnstr_release(x_93, 1);
 x_119 = x_93;
} else {
 lean::dec_ref(x_93);
 x_119 = lean::box(0);
}
if (lean::is_scalar(x_119)) {
 x_120 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_120 = x_119;
}
lean::cnstr_set(x_120, 0, x_117);
lean::cnstr_set(x_120, 1, x_118);
return x_120;
}
}
}
else
{
uint8 x_121; 
lean::dec(x_11);
lean::dec(x_2);
x_121 = !lean::is_exclusive(x_16);
if (x_121 == 0)
{
return x_16;
}
else
{
obj* x_122; obj* x_123; obj* x_124; 
x_122 = lean::cnstr_get(x_16, 0);
x_123 = lean::cnstr_get(x_16, 1);
lean::inc(x_123);
lean::inc(x_122);
lean::dec(x_16);
x_124 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_124, 0, x_122);
lean::cnstr_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; 
lean::dec(x_1);
x_125 = lean::cnstr_get(x_2, 0);
lean::inc(x_125);
lean::dec(x_2);
x_126 = l_Lean_Name_toString___closed__1;
x_127 = l_Lean_Name_toStringWithSep___main(x_126, x_125);
x_128 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_129 = lean_string_append(x_128, x_127);
lean::dec(x_127);
x_130 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_131 = lean_string_append(x_129, x_130);
lean::cnstr_set_tag(x_5, 1);
lean::cnstr_set(x_5, 0, x_131);
return x_5;
}
}
else
{
obj* x_132; obj* x_133; obj* x_134; uint8 x_135; 
x_132 = lean::cnstr_get(x_5, 0);
x_133 = lean::cnstr_get(x_5, 1);
lean::inc(x_133);
lean::inc(x_132);
lean::dec(x_5);
x_134 = lean::mk_nat_obj(0u);
x_135 = l_Array_anyMAux___main___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg(x_2, x_132, x_134);
lean::dec(x_132);
if (x_135 == 0)
{
obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; 
x_136 = lean::box(0);
x_137 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_137, 0, x_136);
lean::cnstr_set(x_137, 1, x_133);
x_138 = lean::cnstr_get(x_2, 1);
lean::inc(x_138);
x_139 = l_Array_empty___closed__1;
lean::inc(x_138);
x_140 = lean::apply_1(x_138, x_139);
x_141 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_142 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_bind___rarg), 3, 2);
lean::closure_set(x_142, 0, x_140);
lean::closure_set(x_142, 1, x_141);
x_143 = l_Lean_registerEnvExtensionUnsafe___at_Lean_registerPersistentEnvExtensionUnsafe___spec__2___rarg(x_1, x_142, x_137);
if (lean::obj_tag(x_143) == 0)
{
obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; 
x_144 = lean::cnstr_get(x_143, 0);
lean::inc(x_144);
x_145 = lean::cnstr_get(x_143, 1);
lean::inc(x_145);
if (lean::is_exclusive(x_143)) {
 lean::cnstr_release(x_143, 0);
 lean::cnstr_release(x_143, 1);
 x_146 = x_143;
} else {
 lean::dec_ref(x_143);
 x_146 = lean::box(0);
}
if (lean::is_scalar(x_146)) {
 x_147 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_147 = x_146;
}
lean::cnstr_set(x_147, 0, x_136);
lean::cnstr_set(x_147, 1, x_145);
x_148 = lean::cnstr_get(x_2, 0);
lean::inc(x_148);
x_149 = lean::cnstr_get(x_2, 2);
lean::inc(x_149);
x_150 = lean::cnstr_get(x_2, 3);
lean::inc(x_150);
x_151 = lean::cnstr_get(x_2, 4);
lean::inc(x_151);
lean::dec(x_2);
x_152 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_152, 0, x_144);
lean::cnstr_set(x_152, 1, x_148);
lean::cnstr_set(x_152, 2, x_138);
lean::cnstr_set(x_152, 3, x_149);
lean::cnstr_set(x_152, 4, x_150);
lean::cnstr_set(x_152, 5, x_151);
x_153 = lean_io_ref_get(x_4, x_147);
if (lean::obj_tag(x_153) == 0)
{
obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; 
x_154 = lean::cnstr_get(x_153, 0);
lean::inc(x_154);
x_155 = lean::cnstr_get(x_153, 1);
lean::inc(x_155);
if (lean::is_exclusive(x_153)) {
 lean::cnstr_release(x_153, 0);
 lean::cnstr_release(x_153, 1);
 x_156 = x_153;
} else {
 lean::dec_ref(x_153);
 x_156 = lean::box(0);
}
if (lean::is_scalar(x_156)) {
 x_157 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_157 = x_156;
}
lean::cnstr_set(x_157, 0, x_136);
lean::cnstr_set(x_157, 1, x_155);
x_158 = lean_io_ref_reset(x_4, x_157);
if (lean::obj_tag(x_158) == 0)
{
obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; 
x_159 = lean::cnstr_get(x_158, 1);
lean::inc(x_159);
if (lean::is_exclusive(x_158)) {
 lean::cnstr_release(x_158, 0);
 lean::cnstr_release(x_158, 1);
 x_160 = x_158;
} else {
 lean::dec_ref(x_158);
 x_160 = lean::box(0);
}
if (lean::is_scalar(x_160)) {
 x_161 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_161 = x_160;
}
lean::cnstr_set(x_161, 0, x_136);
lean::cnstr_set(x_161, 1, x_159);
x_162 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_152);
x_163 = x_152;
x_164 = lean_array_push(x_154, x_163);
x_165 = lean_io_ref_set(x_4, x_164, x_161);
if (lean::obj_tag(x_165) == 0)
{
obj* x_166; obj* x_167; obj* x_168; 
x_166 = lean::cnstr_get(x_165, 1);
lean::inc(x_166);
if (lean::is_exclusive(x_165)) {
 lean::cnstr_release(x_165, 0);
 lean::cnstr_release(x_165, 1);
 x_167 = x_165;
} else {
 lean::dec_ref(x_165);
 x_167 = lean::box(0);
}
if (lean::is_scalar(x_167)) {
 x_168 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_168 = x_167;
}
lean::cnstr_set(x_168, 0, x_152);
lean::cnstr_set(x_168, 1, x_166);
return x_168;
}
else
{
obj* x_169; obj* x_170; obj* x_171; obj* x_172; 
lean::dec(x_152);
x_169 = lean::cnstr_get(x_165, 0);
lean::inc(x_169);
x_170 = lean::cnstr_get(x_165, 1);
lean::inc(x_170);
if (lean::is_exclusive(x_165)) {
 lean::cnstr_release(x_165, 0);
 lean::cnstr_release(x_165, 1);
 x_171 = x_165;
} else {
 lean::dec_ref(x_165);
 x_171 = lean::box(0);
}
if (lean::is_scalar(x_171)) {
 x_172 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_172 = x_171;
}
lean::cnstr_set(x_172, 0, x_169);
lean::cnstr_set(x_172, 1, x_170);
return x_172;
}
}
else
{
obj* x_173; obj* x_174; obj* x_175; obj* x_176; 
lean::dec(x_154);
lean::dec(x_152);
x_173 = lean::cnstr_get(x_158, 0);
lean::inc(x_173);
x_174 = lean::cnstr_get(x_158, 1);
lean::inc(x_174);
if (lean::is_exclusive(x_158)) {
 lean::cnstr_release(x_158, 0);
 lean::cnstr_release(x_158, 1);
 x_175 = x_158;
} else {
 lean::dec_ref(x_158);
 x_175 = lean::box(0);
}
if (lean::is_scalar(x_175)) {
 x_176 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_176 = x_175;
}
lean::cnstr_set(x_176, 0, x_173);
lean::cnstr_set(x_176, 1, x_174);
return x_176;
}
}
else
{
obj* x_177; obj* x_178; obj* x_179; obj* x_180; 
lean::dec(x_152);
x_177 = lean::cnstr_get(x_153, 0);
lean::inc(x_177);
x_178 = lean::cnstr_get(x_153, 1);
lean::inc(x_178);
if (lean::is_exclusive(x_153)) {
 lean::cnstr_release(x_153, 0);
 lean::cnstr_release(x_153, 1);
 x_179 = x_153;
} else {
 lean::dec_ref(x_153);
 x_179 = lean::box(0);
}
if (lean::is_scalar(x_179)) {
 x_180 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_180 = x_179;
}
lean::cnstr_set(x_180, 0, x_177);
lean::cnstr_set(x_180, 1, x_178);
return x_180;
}
}
else
{
obj* x_181; obj* x_182; obj* x_183; obj* x_184; 
lean::dec(x_138);
lean::dec(x_2);
x_181 = lean::cnstr_get(x_143, 0);
lean::inc(x_181);
x_182 = lean::cnstr_get(x_143, 1);
lean::inc(x_182);
if (lean::is_exclusive(x_143)) {
 lean::cnstr_release(x_143, 0);
 lean::cnstr_release(x_143, 1);
 x_183 = x_143;
} else {
 lean::dec_ref(x_143);
 x_183 = lean::box(0);
}
if (lean::is_scalar(x_183)) {
 x_184 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_184 = x_183;
}
lean::cnstr_set(x_184, 0, x_181);
lean::cnstr_set(x_184, 1, x_182);
return x_184;
}
}
else
{
obj* x_185; obj* x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; obj* x_192; 
lean::dec(x_1);
x_185 = lean::cnstr_get(x_2, 0);
lean::inc(x_185);
lean::dec(x_2);
x_186 = l_Lean_Name_toString___closed__1;
x_187 = l_Lean_Name_toStringWithSep___main(x_186, x_185);
x_188 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_189 = lean_string_append(x_188, x_187);
lean::dec(x_187);
x_190 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_191 = lean_string_append(x_189, x_190);
x_192 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_192, 0, x_191);
lean::cnstr_set(x_192, 1, x_133);
return x_192;
}
}
}
else
{
uint8 x_193; 
lean::dec(x_2);
lean::dec(x_1);
x_193 = !lean::is_exclusive(x_5);
if (x_193 == 0)
{
return x_5;
}
else
{
obj* x_194; obj* x_195; obj* x_196; 
x_194 = lean::cnstr_get(x_5, 0);
x_195 = lean::cnstr_get(x_5, 1);
lean::inc(x_195);
lean::inc(x_194);
lean::dec(x_5);
x_196 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_196, 0, x_194);
lean::cnstr_set(x_196, 1, x_195);
return x_196;
}
}
}
}
obj* l_Lean_registerPersistentEnvExtensionUnsafe(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerPersistentEnvExtensionUnsafe___rarg), 3, 0);
return x_3;
}
}
obj* l_Array_anyMAux___main___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_Array_anyMAux___main___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_Lean_registerPersistentEnvExtension___rarg(obj* x_1) {
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
obj* l_Lean_registerPersistentEnvExtension(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerPersistentEnvExtension___rarg), 1, 0);
return x_5;
}
}
obj* l_Lean_registerPersistentEnvExtension___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_registerPersistentEnvExtension(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
lean::dec(x_1);
return x_5;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean_array_fget(x_3, x_4);
lean::inc(x_1);
x_9 = lean::apply_2(x_1, x_5, x_8);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean_nat_add(x_4, x_10);
lean::dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
lean::dec(x_1);
return x_5;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_10 = l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__1___rarg(x_1, x_8, x_8, x_9, x_5);
lean::dec(x_8);
x_11 = lean::mk_nat_obj(1u);
x_12 = lean_nat_add(x_4, x_11);
lean::dec(x_4);
x_4 = x_12;
x_5 = x_10;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__2___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_Lean_mkStateFromImportedEntries___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__2___rarg(x_1, x_3, x_3, x_4, x_2);
return x_5;
}
}
obj* l_Lean_mkStateFromImportedEntries(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_mkStateFromImportedEntries___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__2___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__2___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_mkStateFromImportedEntries___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_mkStateFromImportedEntries___rarg(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
uint8 l_Array_anyMAux___main___at_Lean_registerSimplePersistentEnvExtension___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
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
x_7 = lean_array_fget(x_2, x_3);
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
x_12 = lean_nat_add(x_3, x_11);
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
obj* l_Array_anyMAux___main___at_Lean_registerSimplePersistentEnvExtension___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_anyMAux___main___at_Lean_registerSimplePersistentEnvExtension___spec__2___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__3___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean_io_initializing(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; uint8 x_6; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::unbox(x_5);
lean::dec(x_5);
if (x_6 == 0)
{
uint8 x_7; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = !lean::is_exclusive(x_4);
if (x_7 == 0)
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_4, 0);
lean::dec(x_8);
x_9 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
lean::cnstr_set_tag(x_4, 1);
lean::cnstr_set(x_4, 0, x_9);
return x_4;
}
else
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::cnstr_get(x_4, 1);
lean::inc(x_10);
lean::dec(x_4);
x_11 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_4);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_14 = lean::cnstr_get(x_4, 0);
lean::dec(x_14);
x_15 = lean::box(0);
lean::cnstr_set(x_4, 0, x_15);
x_16 = l___private_init_lean_environment_5__envExtensionsRef;
x_17 = lean_io_ref_get(x_16, x_4);
if (lean::obj_tag(x_17) == 0)
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_19 = lean::cnstr_get(x_17, 0);
lean::cnstr_set(x_17, 0, x_15);
x_20 = lean_array_get_size(x_19);
lean::dec(x_19);
x_21 = lean::box(0);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_1);
x_23 = l_Array_empty___closed__1;
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_22);
x_25 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_25, 0, x_20);
lean::cnstr_set(x_25, 1, x_2);
lean::cnstr_set(x_25, 2, x_24);
x_26 = lean_io_ref_get(x_16, x_17);
if (lean::obj_tag(x_26) == 0)
{
uint8 x_27; 
x_27 = !lean::is_exclusive(x_26);
if (x_27 == 0)
{
obj* x_28; obj* x_29; 
x_28 = lean::cnstr_get(x_26, 0);
lean::cnstr_set(x_26, 0, x_15);
x_29 = lean_io_ref_reset(x_16, x_26);
if (lean::obj_tag(x_29) == 0)
{
uint8 x_30; 
x_30 = !lean::is_exclusive(x_29);
if (x_30 == 0)
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_31 = lean::cnstr_get(x_29, 0);
lean::dec(x_31);
lean::cnstr_set(x_29, 0, x_15);
x_32 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_25);
x_33 = x_25;
x_34 = lean_array_push(x_28, x_33);
x_35 = lean_io_ref_set(x_16, x_34, x_29);
if (lean::obj_tag(x_35) == 0)
{
uint8 x_36; 
x_36 = !lean::is_exclusive(x_35);
if (x_36 == 0)
{
obj* x_37; 
x_37 = lean::cnstr_get(x_35, 0);
lean::dec(x_37);
lean::cnstr_set(x_35, 0, x_25);
return x_35;
}
else
{
obj* x_38; obj* x_39; 
x_38 = lean::cnstr_get(x_35, 1);
lean::inc(x_38);
lean::dec(x_35);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_25);
lean::cnstr_set(x_39, 1, x_38);
return x_39;
}
}
else
{
uint8 x_40; 
lean::dec(x_25);
x_40 = !lean::is_exclusive(x_35);
if (x_40 == 0)
{
return x_35;
}
else
{
obj* x_41; obj* x_42; obj* x_43; 
x_41 = lean::cnstr_get(x_35, 0);
x_42 = lean::cnstr_get(x_35, 1);
lean::inc(x_42);
lean::inc(x_41);
lean::dec(x_35);
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
x_44 = lean::cnstr_get(x_29, 1);
lean::inc(x_44);
lean::dec(x_29);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_15);
lean::cnstr_set(x_45, 1, x_44);
x_46 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_25);
x_47 = x_25;
x_48 = lean_array_push(x_28, x_47);
x_49 = lean_io_ref_set(x_16, x_48, x_45);
if (lean::obj_tag(x_49) == 0)
{
obj* x_50; obj* x_51; obj* x_52; 
x_50 = lean::cnstr_get(x_49, 1);
lean::inc(x_50);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_release(x_49, 0);
 lean::cnstr_release(x_49, 1);
 x_51 = x_49;
} else {
 lean::dec_ref(x_49);
 x_51 = lean::box(0);
}
if (lean::is_scalar(x_51)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_51;
}
lean::cnstr_set(x_52, 0, x_25);
lean::cnstr_set(x_52, 1, x_50);
return x_52;
}
else
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_25);
x_53 = lean::cnstr_get(x_49, 0);
lean::inc(x_53);
x_54 = lean::cnstr_get(x_49, 1);
lean::inc(x_54);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_release(x_49, 0);
 lean::cnstr_release(x_49, 1);
 x_55 = x_49;
} else {
 lean::dec_ref(x_49);
 x_55 = lean::box(0);
}
if (lean::is_scalar(x_55)) {
 x_56 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_56 = x_55;
}
lean::cnstr_set(x_56, 0, x_53);
lean::cnstr_set(x_56, 1, x_54);
return x_56;
}
}
}
else
{
uint8 x_57; 
lean::dec(x_28);
lean::dec(x_25);
x_57 = !lean::is_exclusive(x_29);
if (x_57 == 0)
{
return x_29;
}
else
{
obj* x_58; obj* x_59; obj* x_60; 
x_58 = lean::cnstr_get(x_29, 0);
x_59 = lean::cnstr_get(x_29, 1);
lean::inc(x_59);
lean::inc(x_58);
lean::dec(x_29);
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_58);
lean::cnstr_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_61 = lean::cnstr_get(x_26, 0);
x_62 = lean::cnstr_get(x_26, 1);
lean::inc(x_62);
lean::inc(x_61);
lean::dec(x_26);
x_63 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_63, 0, x_15);
lean::cnstr_set(x_63, 1, x_62);
x_64 = lean_io_ref_reset(x_16, x_63);
if (lean::obj_tag(x_64) == 0)
{
obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_65 = lean::cnstr_get(x_64, 1);
lean::inc(x_65);
if (lean::is_exclusive(x_64)) {
 lean::cnstr_release(x_64, 0);
 lean::cnstr_release(x_64, 1);
 x_66 = x_64;
} else {
 lean::dec_ref(x_64);
 x_66 = lean::box(0);
}
if (lean::is_scalar(x_66)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_66;
}
lean::cnstr_set(x_67, 0, x_15);
lean::cnstr_set(x_67, 1, x_65);
x_68 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_25);
x_69 = x_25;
x_70 = lean_array_push(x_61, x_69);
x_71 = lean_io_ref_set(x_16, x_70, x_67);
if (lean::obj_tag(x_71) == 0)
{
obj* x_72; obj* x_73; obj* x_74; 
x_72 = lean::cnstr_get(x_71, 1);
lean::inc(x_72);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_release(x_71, 0);
 lean::cnstr_release(x_71, 1);
 x_73 = x_71;
} else {
 lean::dec_ref(x_71);
 x_73 = lean::box(0);
}
if (lean::is_scalar(x_73)) {
 x_74 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_74 = x_73;
}
lean::cnstr_set(x_74, 0, x_25);
lean::cnstr_set(x_74, 1, x_72);
return x_74;
}
else
{
obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
lean::dec(x_25);
x_75 = lean::cnstr_get(x_71, 0);
lean::inc(x_75);
x_76 = lean::cnstr_get(x_71, 1);
lean::inc(x_76);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_release(x_71, 0);
 lean::cnstr_release(x_71, 1);
 x_77 = x_71;
} else {
 lean::dec_ref(x_71);
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
else
{
obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
lean::dec(x_61);
lean::dec(x_25);
x_79 = lean::cnstr_get(x_64, 0);
lean::inc(x_79);
x_80 = lean::cnstr_get(x_64, 1);
lean::inc(x_80);
if (lean::is_exclusive(x_64)) {
 lean::cnstr_release(x_64, 0);
 lean::cnstr_release(x_64, 1);
 x_81 = x_64;
} else {
 lean::dec_ref(x_64);
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
}
else
{
uint8 x_83; 
lean::dec(x_25);
x_83 = !lean::is_exclusive(x_26);
if (x_83 == 0)
{
return x_26;
}
else
{
obj* x_84; obj* x_85; obj* x_86; 
x_84 = lean::cnstr_get(x_26, 0);
x_85 = lean::cnstr_get(x_26, 1);
lean::inc(x_85);
lean::inc(x_84);
lean::dec(x_26);
x_86 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_86, 0, x_84);
lean::cnstr_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; 
x_87 = lean::cnstr_get(x_17, 0);
x_88 = lean::cnstr_get(x_17, 1);
lean::inc(x_88);
lean::inc(x_87);
lean::dec(x_17);
x_89 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_89, 0, x_15);
lean::cnstr_set(x_89, 1, x_88);
x_90 = lean_array_get_size(x_87);
lean::dec(x_87);
x_91 = lean::box(0);
x_92 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_1);
x_93 = l_Array_empty___closed__1;
x_94 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_92);
x_95 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_95, 0, x_90);
lean::cnstr_set(x_95, 1, x_2);
lean::cnstr_set(x_95, 2, x_94);
x_96 = lean_io_ref_get(x_16, x_89);
if (lean::obj_tag(x_96) == 0)
{
obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_97 = lean::cnstr_get(x_96, 0);
lean::inc(x_97);
x_98 = lean::cnstr_get(x_96, 1);
lean::inc(x_98);
if (lean::is_exclusive(x_96)) {
 lean::cnstr_release(x_96, 0);
 lean::cnstr_release(x_96, 1);
 x_99 = x_96;
} else {
 lean::dec_ref(x_96);
 x_99 = lean::box(0);
}
if (lean::is_scalar(x_99)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_99;
}
lean::cnstr_set(x_100, 0, x_15);
lean::cnstr_set(x_100, 1, x_98);
x_101 = lean_io_ref_reset(x_16, x_100);
if (lean::obj_tag(x_101) == 0)
{
obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
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
lean::cnstr_set(x_104, 0, x_15);
lean::cnstr_set(x_104, 1, x_102);
x_105 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_95);
x_106 = x_95;
x_107 = lean_array_push(x_97, x_106);
x_108 = lean_io_ref_set(x_16, x_107, x_104);
if (lean::obj_tag(x_108) == 0)
{
obj* x_109; obj* x_110; obj* x_111; 
x_109 = lean::cnstr_get(x_108, 1);
lean::inc(x_109);
if (lean::is_exclusive(x_108)) {
 lean::cnstr_release(x_108, 0);
 lean::cnstr_release(x_108, 1);
 x_110 = x_108;
} else {
 lean::dec_ref(x_108);
 x_110 = lean::box(0);
}
if (lean::is_scalar(x_110)) {
 x_111 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_111 = x_110;
}
lean::cnstr_set(x_111, 0, x_95);
lean::cnstr_set(x_111, 1, x_109);
return x_111;
}
else
{
obj* x_112; obj* x_113; obj* x_114; obj* x_115; 
lean::dec(x_95);
x_112 = lean::cnstr_get(x_108, 0);
lean::inc(x_112);
x_113 = lean::cnstr_get(x_108, 1);
lean::inc(x_113);
if (lean::is_exclusive(x_108)) {
 lean::cnstr_release(x_108, 0);
 lean::cnstr_release(x_108, 1);
 x_114 = x_108;
} else {
 lean::dec_ref(x_108);
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
lean::dec(x_97);
lean::dec(x_95);
x_116 = lean::cnstr_get(x_101, 0);
lean::inc(x_116);
x_117 = lean::cnstr_get(x_101, 1);
lean::inc(x_117);
if (lean::is_exclusive(x_101)) {
 lean::cnstr_release(x_101, 0);
 lean::cnstr_release(x_101, 1);
 x_118 = x_101;
} else {
 lean::dec_ref(x_101);
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
else
{
obj* x_120; obj* x_121; obj* x_122; obj* x_123; 
lean::dec(x_95);
x_120 = lean::cnstr_get(x_96, 0);
lean::inc(x_120);
x_121 = lean::cnstr_get(x_96, 1);
lean::inc(x_121);
if (lean::is_exclusive(x_96)) {
 lean::cnstr_release(x_96, 0);
 lean::cnstr_release(x_96, 1);
 x_122 = x_96;
} else {
 lean::dec_ref(x_96);
 x_122 = lean::box(0);
}
if (lean::is_scalar(x_122)) {
 x_123 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_123 = x_122;
}
lean::cnstr_set(x_123, 0, x_120);
lean::cnstr_set(x_123, 1, x_121);
return x_123;
}
}
}
else
{
uint8 x_124; 
lean::dec(x_2);
lean::dec(x_1);
x_124 = !lean::is_exclusive(x_17);
if (x_124 == 0)
{
return x_17;
}
else
{
obj* x_125; obj* x_126; obj* x_127; 
x_125 = lean::cnstr_get(x_17, 0);
x_126 = lean::cnstr_get(x_17, 1);
lean::inc(x_126);
lean::inc(x_125);
lean::dec(x_17);
x_127 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_127, 0, x_125);
lean::cnstr_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; 
x_128 = lean::cnstr_get(x_4, 1);
lean::inc(x_128);
lean::dec(x_4);
x_129 = lean::box(0);
x_130 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_130, 0, x_129);
lean::cnstr_set(x_130, 1, x_128);
x_131 = l___private_init_lean_environment_5__envExtensionsRef;
x_132 = lean_io_ref_get(x_131, x_130);
if (lean::obj_tag(x_132) == 0)
{
obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; 
x_133 = lean::cnstr_get(x_132, 0);
lean::inc(x_133);
x_134 = lean::cnstr_get(x_132, 1);
lean::inc(x_134);
if (lean::is_exclusive(x_132)) {
 lean::cnstr_release(x_132, 0);
 lean::cnstr_release(x_132, 1);
 x_135 = x_132;
} else {
 lean::dec_ref(x_132);
 x_135 = lean::box(0);
}
if (lean::is_scalar(x_135)) {
 x_136 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_136 = x_135;
}
lean::cnstr_set(x_136, 0, x_129);
lean::cnstr_set(x_136, 1, x_134);
x_137 = lean_array_get_size(x_133);
lean::dec(x_133);
x_138 = lean::box(0);
x_139 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_139, 0, x_138);
lean::cnstr_set(x_139, 1, x_1);
x_140 = l_Array_empty___closed__1;
x_141 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_141, 0, x_140);
lean::cnstr_set(x_141, 1, x_139);
x_142 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_142, 0, x_137);
lean::cnstr_set(x_142, 1, x_2);
lean::cnstr_set(x_142, 2, x_141);
x_143 = lean_io_ref_get(x_131, x_136);
if (lean::obj_tag(x_143) == 0)
{
obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; 
x_144 = lean::cnstr_get(x_143, 0);
lean::inc(x_144);
x_145 = lean::cnstr_get(x_143, 1);
lean::inc(x_145);
if (lean::is_exclusive(x_143)) {
 lean::cnstr_release(x_143, 0);
 lean::cnstr_release(x_143, 1);
 x_146 = x_143;
} else {
 lean::dec_ref(x_143);
 x_146 = lean::box(0);
}
if (lean::is_scalar(x_146)) {
 x_147 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_147 = x_146;
}
lean::cnstr_set(x_147, 0, x_129);
lean::cnstr_set(x_147, 1, x_145);
x_148 = lean_io_ref_reset(x_131, x_147);
if (lean::obj_tag(x_148) == 0)
{
obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; 
x_149 = lean::cnstr_get(x_148, 1);
lean::inc(x_149);
if (lean::is_exclusive(x_148)) {
 lean::cnstr_release(x_148, 0);
 lean::cnstr_release(x_148, 1);
 x_150 = x_148;
} else {
 lean::dec_ref(x_148);
 x_150 = lean::box(0);
}
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_129);
lean::cnstr_set(x_151, 1, x_149);
x_152 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_142);
x_153 = x_142;
x_154 = lean_array_push(x_144, x_153);
x_155 = lean_io_ref_set(x_131, x_154, x_151);
if (lean::obj_tag(x_155) == 0)
{
obj* x_156; obj* x_157; obj* x_158; 
x_156 = lean::cnstr_get(x_155, 1);
lean::inc(x_156);
if (lean::is_exclusive(x_155)) {
 lean::cnstr_release(x_155, 0);
 lean::cnstr_release(x_155, 1);
 x_157 = x_155;
} else {
 lean::dec_ref(x_155);
 x_157 = lean::box(0);
}
if (lean::is_scalar(x_157)) {
 x_158 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_158 = x_157;
}
lean::cnstr_set(x_158, 0, x_142);
lean::cnstr_set(x_158, 1, x_156);
return x_158;
}
else
{
obj* x_159; obj* x_160; obj* x_161; obj* x_162; 
lean::dec(x_142);
x_159 = lean::cnstr_get(x_155, 0);
lean::inc(x_159);
x_160 = lean::cnstr_get(x_155, 1);
lean::inc(x_160);
if (lean::is_exclusive(x_155)) {
 lean::cnstr_release(x_155, 0);
 lean::cnstr_release(x_155, 1);
 x_161 = x_155;
} else {
 lean::dec_ref(x_155);
 x_161 = lean::box(0);
}
if (lean::is_scalar(x_161)) {
 x_162 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_162 = x_161;
}
lean::cnstr_set(x_162, 0, x_159);
lean::cnstr_set(x_162, 1, x_160);
return x_162;
}
}
else
{
obj* x_163; obj* x_164; obj* x_165; obj* x_166; 
lean::dec(x_144);
lean::dec(x_142);
x_163 = lean::cnstr_get(x_148, 0);
lean::inc(x_163);
x_164 = lean::cnstr_get(x_148, 1);
lean::inc(x_164);
if (lean::is_exclusive(x_148)) {
 lean::cnstr_release(x_148, 0);
 lean::cnstr_release(x_148, 1);
 x_165 = x_148;
} else {
 lean::dec_ref(x_148);
 x_165 = lean::box(0);
}
if (lean::is_scalar(x_165)) {
 x_166 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_166 = x_165;
}
lean::cnstr_set(x_166, 0, x_163);
lean::cnstr_set(x_166, 1, x_164);
return x_166;
}
}
else
{
obj* x_167; obj* x_168; obj* x_169; obj* x_170; 
lean::dec(x_142);
x_167 = lean::cnstr_get(x_143, 0);
lean::inc(x_167);
x_168 = lean::cnstr_get(x_143, 1);
lean::inc(x_168);
if (lean::is_exclusive(x_143)) {
 lean::cnstr_release(x_143, 0);
 lean::cnstr_release(x_143, 1);
 x_169 = x_143;
} else {
 lean::dec_ref(x_143);
 x_169 = lean::box(0);
}
if (lean::is_scalar(x_169)) {
 x_170 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_170 = x_169;
}
lean::cnstr_set(x_170, 0, x_167);
lean::cnstr_set(x_170, 1, x_168);
return x_170;
}
}
else
{
obj* x_171; obj* x_172; obj* x_173; obj* x_174; 
lean::dec(x_2);
lean::dec(x_1);
x_171 = lean::cnstr_get(x_132, 0);
lean::inc(x_171);
x_172 = lean::cnstr_get(x_132, 1);
lean::inc(x_172);
if (lean::is_exclusive(x_132)) {
 lean::cnstr_release(x_132, 0);
 lean::cnstr_release(x_132, 1);
 x_173 = x_132;
} else {
 lean::dec_ref(x_132);
 x_173 = lean::box(0);
}
if (lean::is_scalar(x_173)) {
 x_174 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_174 = x_173;
}
lean::cnstr_set(x_174, 0, x_171);
lean::cnstr_set(x_174, 1, x_172);
return x_174;
}
}
}
}
else
{
uint8 x_175; 
lean::dec(x_2);
lean::dec(x_1);
x_175 = !lean::is_exclusive(x_4);
if (x_175 == 0)
{
return x_4;
}
else
{
obj* x_176; obj* x_177; obj* x_178; 
x_176 = lean::cnstr_get(x_4, 0);
x_177 = lean::cnstr_get(x_4, 1);
lean::inc(x_177);
lean::inc(x_176);
lean::dec(x_4);
x_178 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_178, 0, x_176);
lean::cnstr_set(x_178, 1, x_177);
return x_178;
}
}
}
}
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__3(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__3___rarg), 3, 0);
return x_3;
}
}
obj* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l___private_init_lean_environment_8__persistentEnvExtensionsRef;
x_5 = lean_io_ref_get(x_4, x_3);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; uint8 x_9; 
x_7 = lean::cnstr_get(x_5, 0);
x_8 = lean::mk_nat_obj(0u);
x_9 = l_Array_anyMAux___main___at_Lean_registerSimplePersistentEnvExtension___spec__2___rarg(x_2, x_7, x_8);
lean::dec(x_7);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_10 = lean::box(0);
lean::cnstr_set(x_5, 0, x_10);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
x_12 = l_Array_empty___closed__1;
lean::inc(x_11);
x_13 = lean::apply_1(x_11, x_12);
x_14 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_bind___rarg), 3, 2);
lean::closure_set(x_15, 0, x_13);
lean::closure_set(x_15, 1, x_14);
x_16 = l_Lean_registerEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__3___rarg(x_1, x_15, x_5);
if (lean::obj_tag(x_16) == 0)
{
uint8 x_17; 
x_17 = !lean::is_exclusive(x_16);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_18 = lean::cnstr_get(x_16, 0);
lean::cnstr_set(x_16, 0, x_10);
x_19 = lean::cnstr_get(x_2, 0);
lean::inc(x_19);
x_20 = lean::cnstr_get(x_2, 2);
lean::inc(x_20);
x_21 = lean::cnstr_get(x_2, 3);
lean::inc(x_21);
x_22 = lean::cnstr_get(x_2, 4);
lean::inc(x_22);
lean::dec(x_2);
x_23 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_23, 0, x_18);
lean::cnstr_set(x_23, 1, x_19);
lean::cnstr_set(x_23, 2, x_11);
lean::cnstr_set(x_23, 3, x_20);
lean::cnstr_set(x_23, 4, x_21);
lean::cnstr_set(x_23, 5, x_22);
x_24 = lean_io_ref_get(x_4, x_16);
if (lean::obj_tag(x_24) == 0)
{
uint8 x_25; 
x_25 = !lean::is_exclusive(x_24);
if (x_25 == 0)
{
obj* x_26; obj* x_27; 
x_26 = lean::cnstr_get(x_24, 0);
lean::cnstr_set(x_24, 0, x_10);
x_27 = lean_io_ref_reset(x_4, x_24);
if (lean::obj_tag(x_27) == 0)
{
uint8 x_28; 
x_28 = !lean::is_exclusive(x_27);
if (x_28 == 0)
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_29 = lean::cnstr_get(x_27, 0);
lean::dec(x_29);
lean::cnstr_set(x_27, 0, x_10);
x_30 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_23);
x_31 = x_23;
x_32 = lean_array_push(x_26, x_31);
x_33 = lean_io_ref_set(x_4, x_32, x_27);
if (lean::obj_tag(x_33) == 0)
{
uint8 x_34; 
x_34 = !lean::is_exclusive(x_33);
if (x_34 == 0)
{
obj* x_35; 
x_35 = lean::cnstr_get(x_33, 0);
lean::dec(x_35);
lean::cnstr_set(x_33, 0, x_23);
return x_33;
}
else
{
obj* x_36; obj* x_37; 
x_36 = lean::cnstr_get(x_33, 1);
lean::inc(x_36);
lean::dec(x_33);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_23);
lean::cnstr_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8 x_38; 
lean::dec(x_23);
x_38 = !lean::is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
obj* x_39; obj* x_40; obj* x_41; 
x_39 = lean::cnstr_get(x_33, 0);
x_40 = lean::cnstr_get(x_33, 1);
lean::inc(x_40);
lean::inc(x_39);
lean::dec(x_33);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_42 = lean::cnstr_get(x_27, 1);
lean::inc(x_42);
lean::dec(x_27);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_10);
lean::cnstr_set(x_43, 1, x_42);
x_44 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_23);
x_45 = x_23;
x_46 = lean_array_push(x_26, x_45);
x_47 = lean_io_ref_set(x_4, x_46, x_43);
if (lean::obj_tag(x_47) == 0)
{
obj* x_48; obj* x_49; obj* x_50; 
x_48 = lean::cnstr_get(x_47, 1);
lean::inc(x_48);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 x_49 = x_47;
} else {
 lean::dec_ref(x_47);
 x_49 = lean::box(0);
}
if (lean::is_scalar(x_49)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_49;
}
lean::cnstr_set(x_50, 0, x_23);
lean::cnstr_set(x_50, 1, x_48);
return x_50;
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_23);
x_51 = lean::cnstr_get(x_47, 0);
lean::inc(x_51);
x_52 = lean::cnstr_get(x_47, 1);
lean::inc(x_52);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 x_53 = x_47;
} else {
 lean::dec_ref(x_47);
 x_53 = lean::box(0);
}
if (lean::is_scalar(x_53)) {
 x_54 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_54 = x_53;
}
lean::cnstr_set(x_54, 0, x_51);
lean::cnstr_set(x_54, 1, x_52);
return x_54;
}
}
}
else
{
uint8 x_55; 
lean::dec(x_26);
lean::dec(x_23);
x_55 = !lean::is_exclusive(x_27);
if (x_55 == 0)
{
return x_27;
}
else
{
obj* x_56; obj* x_57; obj* x_58; 
x_56 = lean::cnstr_get(x_27, 0);
x_57 = lean::cnstr_get(x_27, 1);
lean::inc(x_57);
lean::inc(x_56);
lean::dec(x_27);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_59 = lean::cnstr_get(x_24, 0);
x_60 = lean::cnstr_get(x_24, 1);
lean::inc(x_60);
lean::inc(x_59);
lean::dec(x_24);
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_10);
lean::cnstr_set(x_61, 1, x_60);
x_62 = lean_io_ref_reset(x_4, x_61);
if (lean::obj_tag(x_62) == 0)
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_63 = lean::cnstr_get(x_62, 1);
lean::inc(x_63);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 lean::cnstr_release(x_62, 1);
 x_64 = x_62;
} else {
 lean::dec_ref(x_62);
 x_64 = lean::box(0);
}
if (lean::is_scalar(x_64)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_64;
}
lean::cnstr_set(x_65, 0, x_10);
lean::cnstr_set(x_65, 1, x_63);
x_66 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_23);
x_67 = x_23;
x_68 = lean_array_push(x_59, x_67);
x_69 = lean_io_ref_set(x_4, x_68, x_65);
if (lean::obj_tag(x_69) == 0)
{
obj* x_70; obj* x_71; obj* x_72; 
x_70 = lean::cnstr_get(x_69, 1);
lean::inc(x_70);
if (lean::is_exclusive(x_69)) {
 lean::cnstr_release(x_69, 0);
 lean::cnstr_release(x_69, 1);
 x_71 = x_69;
} else {
 lean::dec_ref(x_69);
 x_71 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_71;
}
lean::cnstr_set(x_72, 0, x_23);
lean::cnstr_set(x_72, 1, x_70);
return x_72;
}
else
{
obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
lean::dec(x_23);
x_73 = lean::cnstr_get(x_69, 0);
lean::inc(x_73);
x_74 = lean::cnstr_get(x_69, 1);
lean::inc(x_74);
if (lean::is_exclusive(x_69)) {
 lean::cnstr_release(x_69, 0);
 lean::cnstr_release(x_69, 1);
 x_75 = x_69;
} else {
 lean::dec_ref(x_69);
 x_75 = lean::box(0);
}
if (lean::is_scalar(x_75)) {
 x_76 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_76 = x_75;
}
lean::cnstr_set(x_76, 0, x_73);
lean::cnstr_set(x_76, 1, x_74);
return x_76;
}
}
else
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_59);
lean::dec(x_23);
x_77 = lean::cnstr_get(x_62, 0);
lean::inc(x_77);
x_78 = lean::cnstr_get(x_62, 1);
lean::inc(x_78);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 lean::cnstr_release(x_62, 1);
 x_79 = x_62;
} else {
 lean::dec_ref(x_62);
 x_79 = lean::box(0);
}
if (lean::is_scalar(x_79)) {
 x_80 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_80 = x_79;
}
lean::cnstr_set(x_80, 0, x_77);
lean::cnstr_set(x_80, 1, x_78);
return x_80;
}
}
}
else
{
uint8 x_81; 
lean::dec(x_23);
x_81 = !lean::is_exclusive(x_24);
if (x_81 == 0)
{
return x_24;
}
else
{
obj* x_82; obj* x_83; obj* x_84; 
x_82 = lean::cnstr_get(x_24, 0);
x_83 = lean::cnstr_get(x_24, 1);
lean::inc(x_83);
lean::inc(x_82);
lean::dec(x_24);
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_82);
lean::cnstr_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_85 = lean::cnstr_get(x_16, 0);
x_86 = lean::cnstr_get(x_16, 1);
lean::inc(x_86);
lean::inc(x_85);
lean::dec(x_16);
x_87 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_87, 0, x_10);
lean::cnstr_set(x_87, 1, x_86);
x_88 = lean::cnstr_get(x_2, 0);
lean::inc(x_88);
x_89 = lean::cnstr_get(x_2, 2);
lean::inc(x_89);
x_90 = lean::cnstr_get(x_2, 3);
lean::inc(x_90);
x_91 = lean::cnstr_get(x_2, 4);
lean::inc(x_91);
lean::dec(x_2);
x_92 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_92, 0, x_85);
lean::cnstr_set(x_92, 1, x_88);
lean::cnstr_set(x_92, 2, x_11);
lean::cnstr_set(x_92, 3, x_89);
lean::cnstr_set(x_92, 4, x_90);
lean::cnstr_set(x_92, 5, x_91);
x_93 = lean_io_ref_get(x_4, x_87);
if (lean::obj_tag(x_93) == 0)
{
obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
x_94 = lean::cnstr_get(x_93, 0);
lean::inc(x_94);
x_95 = lean::cnstr_get(x_93, 1);
lean::inc(x_95);
if (lean::is_exclusive(x_93)) {
 lean::cnstr_release(x_93, 0);
 lean::cnstr_release(x_93, 1);
 x_96 = x_93;
} else {
 lean::dec_ref(x_93);
 x_96 = lean::box(0);
}
if (lean::is_scalar(x_96)) {
 x_97 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_97 = x_96;
}
lean::cnstr_set(x_97, 0, x_10);
lean::cnstr_set(x_97, 1, x_95);
x_98 = lean_io_ref_reset(x_4, x_97);
if (lean::obj_tag(x_98) == 0)
{
obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; 
x_99 = lean::cnstr_get(x_98, 1);
lean::inc(x_99);
if (lean::is_exclusive(x_98)) {
 lean::cnstr_release(x_98, 0);
 lean::cnstr_release(x_98, 1);
 x_100 = x_98;
} else {
 lean::dec_ref(x_98);
 x_100 = lean::box(0);
}
if (lean::is_scalar(x_100)) {
 x_101 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_101 = x_100;
}
lean::cnstr_set(x_101, 0, x_10);
lean::cnstr_set(x_101, 1, x_99);
x_102 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_92);
x_103 = x_92;
x_104 = lean_array_push(x_94, x_103);
x_105 = lean_io_ref_set(x_4, x_104, x_101);
if (lean::obj_tag(x_105) == 0)
{
obj* x_106; obj* x_107; obj* x_108; 
x_106 = lean::cnstr_get(x_105, 1);
lean::inc(x_106);
if (lean::is_exclusive(x_105)) {
 lean::cnstr_release(x_105, 0);
 lean::cnstr_release(x_105, 1);
 x_107 = x_105;
} else {
 lean::dec_ref(x_105);
 x_107 = lean::box(0);
}
if (lean::is_scalar(x_107)) {
 x_108 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_108 = x_107;
}
lean::cnstr_set(x_108, 0, x_92);
lean::cnstr_set(x_108, 1, x_106);
return x_108;
}
else
{
obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_92);
x_109 = lean::cnstr_get(x_105, 0);
lean::inc(x_109);
x_110 = lean::cnstr_get(x_105, 1);
lean::inc(x_110);
if (lean::is_exclusive(x_105)) {
 lean::cnstr_release(x_105, 0);
 lean::cnstr_release(x_105, 1);
 x_111 = x_105;
} else {
 lean::dec_ref(x_105);
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
lean::dec(x_94);
lean::dec(x_92);
x_113 = lean::cnstr_get(x_98, 0);
lean::inc(x_113);
x_114 = lean::cnstr_get(x_98, 1);
lean::inc(x_114);
if (lean::is_exclusive(x_98)) {
 lean::cnstr_release(x_98, 0);
 lean::cnstr_release(x_98, 1);
 x_115 = x_98;
} else {
 lean::dec_ref(x_98);
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
else
{
obj* x_117; obj* x_118; obj* x_119; obj* x_120; 
lean::dec(x_92);
x_117 = lean::cnstr_get(x_93, 0);
lean::inc(x_117);
x_118 = lean::cnstr_get(x_93, 1);
lean::inc(x_118);
if (lean::is_exclusive(x_93)) {
 lean::cnstr_release(x_93, 0);
 lean::cnstr_release(x_93, 1);
 x_119 = x_93;
} else {
 lean::dec_ref(x_93);
 x_119 = lean::box(0);
}
if (lean::is_scalar(x_119)) {
 x_120 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_120 = x_119;
}
lean::cnstr_set(x_120, 0, x_117);
lean::cnstr_set(x_120, 1, x_118);
return x_120;
}
}
}
else
{
uint8 x_121; 
lean::dec(x_11);
lean::dec(x_2);
x_121 = !lean::is_exclusive(x_16);
if (x_121 == 0)
{
return x_16;
}
else
{
obj* x_122; obj* x_123; obj* x_124; 
x_122 = lean::cnstr_get(x_16, 0);
x_123 = lean::cnstr_get(x_16, 1);
lean::inc(x_123);
lean::inc(x_122);
lean::dec(x_16);
x_124 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_124, 0, x_122);
lean::cnstr_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; 
lean::dec(x_1);
x_125 = lean::cnstr_get(x_2, 0);
lean::inc(x_125);
lean::dec(x_2);
x_126 = l_Lean_Name_toString___closed__1;
x_127 = l_Lean_Name_toStringWithSep___main(x_126, x_125);
x_128 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_129 = lean_string_append(x_128, x_127);
lean::dec(x_127);
x_130 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_131 = lean_string_append(x_129, x_130);
lean::cnstr_set_tag(x_5, 1);
lean::cnstr_set(x_5, 0, x_131);
return x_5;
}
}
else
{
obj* x_132; obj* x_133; obj* x_134; uint8 x_135; 
x_132 = lean::cnstr_get(x_5, 0);
x_133 = lean::cnstr_get(x_5, 1);
lean::inc(x_133);
lean::inc(x_132);
lean::dec(x_5);
x_134 = lean::mk_nat_obj(0u);
x_135 = l_Array_anyMAux___main___at_Lean_registerSimplePersistentEnvExtension___spec__2___rarg(x_2, x_132, x_134);
lean::dec(x_132);
if (x_135 == 0)
{
obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; 
x_136 = lean::box(0);
x_137 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_137, 0, x_136);
lean::cnstr_set(x_137, 1, x_133);
x_138 = lean::cnstr_get(x_2, 1);
lean::inc(x_138);
x_139 = l_Array_empty___closed__1;
lean::inc(x_138);
x_140 = lean::apply_1(x_138, x_139);
x_141 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_142 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_bind___rarg), 3, 2);
lean::closure_set(x_142, 0, x_140);
lean::closure_set(x_142, 1, x_141);
x_143 = l_Lean_registerEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__3___rarg(x_1, x_142, x_137);
if (lean::obj_tag(x_143) == 0)
{
obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; 
x_144 = lean::cnstr_get(x_143, 0);
lean::inc(x_144);
x_145 = lean::cnstr_get(x_143, 1);
lean::inc(x_145);
if (lean::is_exclusive(x_143)) {
 lean::cnstr_release(x_143, 0);
 lean::cnstr_release(x_143, 1);
 x_146 = x_143;
} else {
 lean::dec_ref(x_143);
 x_146 = lean::box(0);
}
if (lean::is_scalar(x_146)) {
 x_147 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_147 = x_146;
}
lean::cnstr_set(x_147, 0, x_136);
lean::cnstr_set(x_147, 1, x_145);
x_148 = lean::cnstr_get(x_2, 0);
lean::inc(x_148);
x_149 = lean::cnstr_get(x_2, 2);
lean::inc(x_149);
x_150 = lean::cnstr_get(x_2, 3);
lean::inc(x_150);
x_151 = lean::cnstr_get(x_2, 4);
lean::inc(x_151);
lean::dec(x_2);
x_152 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_152, 0, x_144);
lean::cnstr_set(x_152, 1, x_148);
lean::cnstr_set(x_152, 2, x_138);
lean::cnstr_set(x_152, 3, x_149);
lean::cnstr_set(x_152, 4, x_150);
lean::cnstr_set(x_152, 5, x_151);
x_153 = lean_io_ref_get(x_4, x_147);
if (lean::obj_tag(x_153) == 0)
{
obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; 
x_154 = lean::cnstr_get(x_153, 0);
lean::inc(x_154);
x_155 = lean::cnstr_get(x_153, 1);
lean::inc(x_155);
if (lean::is_exclusive(x_153)) {
 lean::cnstr_release(x_153, 0);
 lean::cnstr_release(x_153, 1);
 x_156 = x_153;
} else {
 lean::dec_ref(x_153);
 x_156 = lean::box(0);
}
if (lean::is_scalar(x_156)) {
 x_157 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_157 = x_156;
}
lean::cnstr_set(x_157, 0, x_136);
lean::cnstr_set(x_157, 1, x_155);
x_158 = lean_io_ref_reset(x_4, x_157);
if (lean::obj_tag(x_158) == 0)
{
obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; 
x_159 = lean::cnstr_get(x_158, 1);
lean::inc(x_159);
if (lean::is_exclusive(x_158)) {
 lean::cnstr_release(x_158, 0);
 lean::cnstr_release(x_158, 1);
 x_160 = x_158;
} else {
 lean::dec_ref(x_158);
 x_160 = lean::box(0);
}
if (lean::is_scalar(x_160)) {
 x_161 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_161 = x_160;
}
lean::cnstr_set(x_161, 0, x_136);
lean::cnstr_set(x_161, 1, x_159);
x_162 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_152);
x_163 = x_152;
x_164 = lean_array_push(x_154, x_163);
x_165 = lean_io_ref_set(x_4, x_164, x_161);
if (lean::obj_tag(x_165) == 0)
{
obj* x_166; obj* x_167; obj* x_168; 
x_166 = lean::cnstr_get(x_165, 1);
lean::inc(x_166);
if (lean::is_exclusive(x_165)) {
 lean::cnstr_release(x_165, 0);
 lean::cnstr_release(x_165, 1);
 x_167 = x_165;
} else {
 lean::dec_ref(x_165);
 x_167 = lean::box(0);
}
if (lean::is_scalar(x_167)) {
 x_168 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_168 = x_167;
}
lean::cnstr_set(x_168, 0, x_152);
lean::cnstr_set(x_168, 1, x_166);
return x_168;
}
else
{
obj* x_169; obj* x_170; obj* x_171; obj* x_172; 
lean::dec(x_152);
x_169 = lean::cnstr_get(x_165, 0);
lean::inc(x_169);
x_170 = lean::cnstr_get(x_165, 1);
lean::inc(x_170);
if (lean::is_exclusive(x_165)) {
 lean::cnstr_release(x_165, 0);
 lean::cnstr_release(x_165, 1);
 x_171 = x_165;
} else {
 lean::dec_ref(x_165);
 x_171 = lean::box(0);
}
if (lean::is_scalar(x_171)) {
 x_172 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_172 = x_171;
}
lean::cnstr_set(x_172, 0, x_169);
lean::cnstr_set(x_172, 1, x_170);
return x_172;
}
}
else
{
obj* x_173; obj* x_174; obj* x_175; obj* x_176; 
lean::dec(x_154);
lean::dec(x_152);
x_173 = lean::cnstr_get(x_158, 0);
lean::inc(x_173);
x_174 = lean::cnstr_get(x_158, 1);
lean::inc(x_174);
if (lean::is_exclusive(x_158)) {
 lean::cnstr_release(x_158, 0);
 lean::cnstr_release(x_158, 1);
 x_175 = x_158;
} else {
 lean::dec_ref(x_158);
 x_175 = lean::box(0);
}
if (lean::is_scalar(x_175)) {
 x_176 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_176 = x_175;
}
lean::cnstr_set(x_176, 0, x_173);
lean::cnstr_set(x_176, 1, x_174);
return x_176;
}
}
else
{
obj* x_177; obj* x_178; obj* x_179; obj* x_180; 
lean::dec(x_152);
x_177 = lean::cnstr_get(x_153, 0);
lean::inc(x_177);
x_178 = lean::cnstr_get(x_153, 1);
lean::inc(x_178);
if (lean::is_exclusive(x_153)) {
 lean::cnstr_release(x_153, 0);
 lean::cnstr_release(x_153, 1);
 x_179 = x_153;
} else {
 lean::dec_ref(x_153);
 x_179 = lean::box(0);
}
if (lean::is_scalar(x_179)) {
 x_180 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_180 = x_179;
}
lean::cnstr_set(x_180, 0, x_177);
lean::cnstr_set(x_180, 1, x_178);
return x_180;
}
}
else
{
obj* x_181; obj* x_182; obj* x_183; obj* x_184; 
lean::dec(x_138);
lean::dec(x_2);
x_181 = lean::cnstr_get(x_143, 0);
lean::inc(x_181);
x_182 = lean::cnstr_get(x_143, 1);
lean::inc(x_182);
if (lean::is_exclusive(x_143)) {
 lean::cnstr_release(x_143, 0);
 lean::cnstr_release(x_143, 1);
 x_183 = x_143;
} else {
 lean::dec_ref(x_143);
 x_183 = lean::box(0);
}
if (lean::is_scalar(x_183)) {
 x_184 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_184 = x_183;
}
lean::cnstr_set(x_184, 0, x_181);
lean::cnstr_set(x_184, 1, x_182);
return x_184;
}
}
else
{
obj* x_185; obj* x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; obj* x_192; 
lean::dec(x_1);
x_185 = lean::cnstr_get(x_2, 0);
lean::inc(x_185);
lean::dec(x_2);
x_186 = l_Lean_Name_toString___closed__1;
x_187 = l_Lean_Name_toStringWithSep___main(x_186, x_185);
x_188 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_189 = lean_string_append(x_188, x_187);
lean::dec(x_187);
x_190 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_191 = lean_string_append(x_189, x_190);
x_192 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_192, 0, x_191);
lean::cnstr_set(x_192, 1, x_133);
return x_192;
}
}
}
else
{
uint8 x_193; 
lean::dec(x_2);
lean::dec(x_1);
x_193 = !lean::is_exclusive(x_5);
if (x_193 == 0)
{
return x_5;
}
else
{
obj* x_194; obj* x_195; obj* x_196; 
x_194 = lean::cnstr_get(x_5, 0);
x_195 = lean::cnstr_get(x_5, 1);
lean::inc(x_195);
lean::inc(x_194);
lean::dec(x_5);
x_196 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_196, 0, x_194);
lean::cnstr_set(x_196, 1, x_195);
return x_196;
}
}
}
}
obj* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__1___rarg), 3, 0);
return x_3;
}
}
obj* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_3, 0);
lean::dec(x_5);
x_6 = lean::box(0);
x_7 = lean::cnstr_get(x_1, 2);
lean::inc(x_7);
lean::dec(x_1);
x_8 = lean::apply_1(x_7, x_2);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_6);
lean::cnstr_set(x_9, 1, x_8);
lean::cnstr_set(x_3, 0, x_9);
return x_3;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_11 = lean::box(0);
x_12 = lean::cnstr_get(x_1, 2);
lean::inc(x_12);
lean::dec(x_1);
x_13 = lean::apply_1(x_12, x_2);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_10);
return x_15;
}
}
}
obj* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__2(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_5);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
x_9 = lean::apply_2(x_8, x_6, x_3);
lean::cnstr_set(x_2, 1, x_9);
lean::cnstr_set(x_2, 0, x_7);
return x_2;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_2, 0);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_2);
lean::inc(x_3);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_3);
lean::cnstr_set(x_12, 1, x_10);
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
lean::dec(x_1);
x_14 = lean::apply_2(x_13, x_11, x_3);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__3(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_1, 3);
lean::inc(x_3);
lean::dec(x_1);
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_5 = l_List_reverse___rarg(x_4);
x_6 = lean::apply_1(x_3, x_5);
return x_6;
}
}
obj* _init_l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("number of local entries: ");
return x_1;
}
}
obj* _init_l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__1;
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::mk_nat_obj(0u);
x_4 = l_List_lengthAux___main___rarg(x_2, x_3);
x_5 = l_Nat_repr(x_4);
x_6 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
x_7 = 0;
x_8 = l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__2;
x_9 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_6);
lean::cnstr_set_uint8(x_9, sizeof(void*)*2, x_7);
return x_9;
}
}
obj* _init_l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___boxed), 1, 0);
return x_1;
}
}
obj* l_Lean_registerSimplePersistentEnvExtension___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::inc(x_2);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1), 3, 1);
lean::closure_set(x_5, 0, x_2);
lean::inc(x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__2), 3, 1);
lean::closure_set(x_6, 0, x_2);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__3), 2, 1);
lean::closure_set(x_7, 0, x_2);
x_8 = l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1;
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_4);
lean::cnstr_set(x_9, 1, x_5);
lean::cnstr_set(x_9, 2, x_6);
lean::cnstr_set(x_9, 3, x_7);
lean::cnstr_set(x_9, 4, x_8);
x_10 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__1___rarg(x_1, x_9, x_3);
return x_10;
}
}
obj* l_Lean_registerSimplePersistentEnvExtension(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerSimplePersistentEnvExtension___rarg), 3, 0);
return x_3;
}
}
obj* l_Array_anyMAux___main___at_Lean_registerSimplePersistentEnvExtension___spec__2___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_Array_anyMAux___main___at_Lean_registerSimplePersistentEnvExtension___spec__2___rarg(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_SimplePersistentEnvExtension_Inhabited___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::box(0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
x_4 = l_Lean_PersistentEnvExtension_inhabited___rarg(x_3);
return x_4;
}
}
obj* l_Lean_SimplePersistentEnvExtension_Inhabited(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SimplePersistentEnvExtension_Inhabited___rarg), 1, 0);
return x_3;
}
}
obj* l_Lean_SimplePersistentEnvExtension_getEntries___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_PersistentEnvExtension_getState___rarg(x_1, x_2);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_SimplePersistentEnvExtension_getEntries(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SimplePersistentEnvExtension_getEntries___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_Lean_SimplePersistentEnvExtension_getEntries___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_SimplePersistentEnvExtension_getEntries___rarg(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_SimplePersistentEnvExtension_getState___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_PersistentEnvExtension_getState___rarg(x_1, x_2);
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_SimplePersistentEnvExtension_getState(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SimplePersistentEnvExtension_getState___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_Lean_SimplePersistentEnvExtension_getState___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_SimplePersistentEnvExtension_setState___rarg___lambda__1(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; 
x_4 = lean::cnstr_get(x_2, 1);
lean::dec(x_4);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
else
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
lean::dec(x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
return x_6;
}
}
}
obj* l_Lean_SimplePersistentEnvExtension_setState___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SimplePersistentEnvExtension_setState___rarg___lambda__1), 2, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = l_Lean_PersistentEnvExtension_modifyState___rarg(x_1, x_2, x_4);
return x_5;
}
}
obj* l_Lean_SimplePersistentEnvExtension_setState(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SimplePersistentEnvExtension_setState___rarg), 3, 0);
return x_3;
}
}
obj* l_Lean_SimplePersistentEnvExtension_modifyState___rarg___lambda__1(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_2, 1);
x_5 = lean::apply_1(x_1, x_4);
lean::cnstr_set(x_2, 1, x_5);
return x_2;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::inc(x_6);
lean::dec(x_2);
x_8 = lean::apply_1(x_1, x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_6);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
}
obj* l_Lean_SimplePersistentEnvExtension_modifyState___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SimplePersistentEnvExtension_modifyState___rarg___lambda__1), 2, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = l_Lean_PersistentEnvExtension_modifyState___rarg(x_1, x_2, x_4);
return x_5;
}
}
obj* l_Lean_SimplePersistentEnvExtension_modifyState(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SimplePersistentEnvExtension_modifyState___rarg), 3, 0);
return x_3;
}
}
obj* _init_l_Lean_CPPExtensionState_inhabited() {
_start:
{
obj* x_1; 
x_1 = l_NonScalar_Inhabited;
return x_1;
}
}
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_registerCPPExtension___spec__1(obj* x_1, obj* x_2) {
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
x_8 = lean::mk_string("failed to register environment, extensions can only be registered during initialization");
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
x_10 = lean::mk_string("failed to register environment, extensions can only be registered during initialization");
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
x_16 = lean_io_ref_get(x_15, x_3);
if (lean::obj_tag(x_16) == 0)
{
uint8 x_17; 
x_17 = !lean::is_exclusive(x_16);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_18 = lean::cnstr_get(x_16, 0);
lean::cnstr_set(x_16, 0, x_14);
x_19 = lean_array_get_size(x_18);
lean::dec(x_18);
x_20 = lean::mk_nat_obj(0u);
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_1);
lean::cnstr_set(x_21, 2, x_20);
x_22 = lean_io_ref_get(x_15, x_16);
if (lean::obj_tag(x_22) == 0)
{
uint8 x_23; 
x_23 = !lean::is_exclusive(x_22);
if (x_23 == 0)
{
obj* x_24; obj* x_25; 
x_24 = lean::cnstr_get(x_22, 0);
lean::cnstr_set(x_22, 0, x_14);
x_25 = lean_io_ref_reset(x_15, x_22);
if (lean::obj_tag(x_25) == 0)
{
uint8 x_26; 
x_26 = !lean::is_exclusive(x_25);
if (x_26 == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_27 = lean::cnstr_get(x_25, 0);
lean::dec(x_27);
lean::cnstr_set(x_25, 0, x_14);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_EnvExtension_Inhabited___rarg___lambda__1), 1, 0);
x_29 = l_Lean_EnvExtensionState_inhabited;
x_30 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_30, 0, x_20);
lean::cnstr_set(x_30, 1, x_28);
lean::cnstr_set(x_30, 2, x_29);
lean::inc(x_21);
x_31 = x_21;
x_32 = lean_array_push(x_24, x_31);
x_33 = lean_io_ref_set(x_15, x_32, x_25);
if (lean::obj_tag(x_33) == 0)
{
uint8 x_34; 
x_34 = !lean::is_exclusive(x_33);
if (x_34 == 0)
{
obj* x_35; 
x_35 = lean::cnstr_get(x_33, 0);
lean::dec(x_35);
lean::cnstr_set(x_33, 0, x_21);
return x_33;
}
else
{
obj* x_36; obj* x_37; 
x_36 = lean::cnstr_get(x_33, 1);
lean::inc(x_36);
lean::dec(x_33);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_21);
lean::cnstr_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8 x_38; 
lean::dec(x_21);
x_38 = !lean::is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
obj* x_39; obj* x_40; obj* x_41; 
x_39 = lean::cnstr_get(x_33, 0);
x_40 = lean::cnstr_get(x_33, 1);
lean::inc(x_40);
lean::inc(x_39);
lean::dec(x_33);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_42 = lean::cnstr_get(x_25, 1);
lean::inc(x_42);
lean::dec(x_25);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_14);
lean::cnstr_set(x_43, 1, x_42);
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_EnvExtension_Inhabited___rarg___lambda__1), 1, 0);
x_45 = l_Lean_EnvExtensionState_inhabited;
x_46 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_46, 0, x_20);
lean::cnstr_set(x_46, 1, x_44);
lean::cnstr_set(x_46, 2, x_45);
lean::inc(x_21);
x_47 = x_21;
x_48 = lean_array_push(x_24, x_47);
x_49 = lean_io_ref_set(x_15, x_48, x_43);
if (lean::obj_tag(x_49) == 0)
{
obj* x_50; obj* x_51; obj* x_52; 
x_50 = lean::cnstr_get(x_49, 1);
lean::inc(x_50);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_release(x_49, 0);
 lean::cnstr_release(x_49, 1);
 x_51 = x_49;
} else {
 lean::dec_ref(x_49);
 x_51 = lean::box(0);
}
if (lean::is_scalar(x_51)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_51;
}
lean::cnstr_set(x_52, 0, x_21);
lean::cnstr_set(x_52, 1, x_50);
return x_52;
}
else
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_21);
x_53 = lean::cnstr_get(x_49, 0);
lean::inc(x_53);
x_54 = lean::cnstr_get(x_49, 1);
lean::inc(x_54);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_release(x_49, 0);
 lean::cnstr_release(x_49, 1);
 x_55 = x_49;
} else {
 lean::dec_ref(x_49);
 x_55 = lean::box(0);
}
if (lean::is_scalar(x_55)) {
 x_56 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_56 = x_55;
}
lean::cnstr_set(x_56, 0, x_53);
lean::cnstr_set(x_56, 1, x_54);
return x_56;
}
}
}
else
{
uint8 x_57; 
lean::dec(x_24);
lean::dec(x_21);
x_57 = !lean::is_exclusive(x_25);
if (x_57 == 0)
{
return x_25;
}
else
{
obj* x_58; obj* x_59; obj* x_60; 
x_58 = lean::cnstr_get(x_25, 0);
x_59 = lean::cnstr_get(x_25, 1);
lean::inc(x_59);
lean::inc(x_58);
lean::dec(x_25);
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_58);
lean::cnstr_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_61 = lean::cnstr_get(x_22, 0);
x_62 = lean::cnstr_get(x_22, 1);
lean::inc(x_62);
lean::inc(x_61);
lean::dec(x_22);
x_63 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_63, 0, x_14);
lean::cnstr_set(x_63, 1, x_62);
x_64 = lean_io_ref_reset(x_15, x_63);
if (lean::obj_tag(x_64) == 0)
{
obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
x_65 = lean::cnstr_get(x_64, 1);
lean::inc(x_65);
if (lean::is_exclusive(x_64)) {
 lean::cnstr_release(x_64, 0);
 lean::cnstr_release(x_64, 1);
 x_66 = x_64;
} else {
 lean::dec_ref(x_64);
 x_66 = lean::box(0);
}
if (lean::is_scalar(x_66)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_66;
}
lean::cnstr_set(x_67, 0, x_14);
lean::cnstr_set(x_67, 1, x_65);
x_68 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_EnvExtension_Inhabited___rarg___lambda__1), 1, 0);
x_69 = l_Lean_EnvExtensionState_inhabited;
x_70 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_70, 0, x_20);
lean::cnstr_set(x_70, 1, x_68);
lean::cnstr_set(x_70, 2, x_69);
lean::inc(x_21);
x_71 = x_21;
x_72 = lean_array_push(x_61, x_71);
x_73 = lean_io_ref_set(x_15, x_72, x_67);
if (lean::obj_tag(x_73) == 0)
{
obj* x_74; obj* x_75; obj* x_76; 
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
lean::cnstr_set(x_76, 0, x_21);
lean::cnstr_set(x_76, 1, x_74);
return x_76;
}
else
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_21);
x_77 = lean::cnstr_get(x_73, 0);
lean::inc(x_77);
x_78 = lean::cnstr_get(x_73, 1);
lean::inc(x_78);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_release(x_73, 0);
 lean::cnstr_release(x_73, 1);
 x_79 = x_73;
} else {
 lean::dec_ref(x_73);
 x_79 = lean::box(0);
}
if (lean::is_scalar(x_79)) {
 x_80 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_80 = x_79;
}
lean::cnstr_set(x_80, 0, x_77);
lean::cnstr_set(x_80, 1, x_78);
return x_80;
}
}
else
{
obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
lean::dec(x_61);
lean::dec(x_21);
x_81 = lean::cnstr_get(x_64, 0);
lean::inc(x_81);
x_82 = lean::cnstr_get(x_64, 1);
lean::inc(x_82);
if (lean::is_exclusive(x_64)) {
 lean::cnstr_release(x_64, 0);
 lean::cnstr_release(x_64, 1);
 x_83 = x_64;
} else {
 lean::dec_ref(x_64);
 x_83 = lean::box(0);
}
if (lean::is_scalar(x_83)) {
 x_84 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_84 = x_83;
}
lean::cnstr_set(x_84, 0, x_81);
lean::cnstr_set(x_84, 1, x_82);
return x_84;
}
}
}
else
{
uint8 x_85; 
lean::dec(x_21);
x_85 = !lean::is_exclusive(x_22);
if (x_85 == 0)
{
return x_22;
}
else
{
obj* x_86; obj* x_87; obj* x_88; 
x_86 = lean::cnstr_get(x_22, 0);
x_87 = lean::cnstr_get(x_22, 1);
lean::inc(x_87);
lean::inc(x_86);
lean::dec(x_22);
x_88 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_88, 0, x_86);
lean::cnstr_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_89 = lean::cnstr_get(x_16, 0);
x_90 = lean::cnstr_get(x_16, 1);
lean::inc(x_90);
lean::inc(x_89);
lean::dec(x_16);
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_14);
lean::cnstr_set(x_91, 1, x_90);
x_92 = lean_array_get_size(x_89);
lean::dec(x_89);
x_93 = lean::mk_nat_obj(0u);
x_94 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_94, 0, x_92);
lean::cnstr_set(x_94, 1, x_1);
lean::cnstr_set(x_94, 2, x_93);
x_95 = lean_io_ref_get(x_15, x_91);
if (lean::obj_tag(x_95) == 0)
{
obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
x_96 = lean::cnstr_get(x_95, 0);
lean::inc(x_96);
x_97 = lean::cnstr_get(x_95, 1);
lean::inc(x_97);
if (lean::is_exclusive(x_95)) {
 lean::cnstr_release(x_95, 0);
 lean::cnstr_release(x_95, 1);
 x_98 = x_95;
} else {
 lean::dec_ref(x_95);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_98)) {
 x_99 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_99 = x_98;
}
lean::cnstr_set(x_99, 0, x_14);
lean::cnstr_set(x_99, 1, x_97);
x_100 = lean_io_ref_reset(x_15, x_99);
if (lean::obj_tag(x_100) == 0)
{
obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
x_101 = lean::cnstr_get(x_100, 1);
lean::inc(x_101);
if (lean::is_exclusive(x_100)) {
 lean::cnstr_release(x_100, 0);
 lean::cnstr_release(x_100, 1);
 x_102 = x_100;
} else {
 lean::dec_ref(x_100);
 x_102 = lean::box(0);
}
if (lean::is_scalar(x_102)) {
 x_103 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_103 = x_102;
}
lean::cnstr_set(x_103, 0, x_14);
lean::cnstr_set(x_103, 1, x_101);
x_104 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_EnvExtension_Inhabited___rarg___lambda__1), 1, 0);
x_105 = l_Lean_EnvExtensionState_inhabited;
x_106 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_106, 0, x_93);
lean::cnstr_set(x_106, 1, x_104);
lean::cnstr_set(x_106, 2, x_105);
lean::inc(x_94);
x_107 = x_94;
x_108 = lean_array_push(x_96, x_107);
x_109 = lean_io_ref_set(x_15, x_108, x_103);
if (lean::obj_tag(x_109) == 0)
{
obj* x_110; obj* x_111; obj* x_112; 
x_110 = lean::cnstr_get(x_109, 1);
lean::inc(x_110);
if (lean::is_exclusive(x_109)) {
 lean::cnstr_release(x_109, 0);
 lean::cnstr_release(x_109, 1);
 x_111 = x_109;
} else {
 lean::dec_ref(x_109);
 x_111 = lean::box(0);
}
if (lean::is_scalar(x_111)) {
 x_112 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_112 = x_111;
}
lean::cnstr_set(x_112, 0, x_94);
lean::cnstr_set(x_112, 1, x_110);
return x_112;
}
else
{
obj* x_113; obj* x_114; obj* x_115; obj* x_116; 
lean::dec(x_94);
x_113 = lean::cnstr_get(x_109, 0);
lean::inc(x_113);
x_114 = lean::cnstr_get(x_109, 1);
lean::inc(x_114);
if (lean::is_exclusive(x_109)) {
 lean::cnstr_release(x_109, 0);
 lean::cnstr_release(x_109, 1);
 x_115 = x_109;
} else {
 lean::dec_ref(x_109);
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
else
{
obj* x_117; obj* x_118; obj* x_119; obj* x_120; 
lean::dec(x_96);
lean::dec(x_94);
x_117 = lean::cnstr_get(x_100, 0);
lean::inc(x_117);
x_118 = lean::cnstr_get(x_100, 1);
lean::inc(x_118);
if (lean::is_exclusive(x_100)) {
 lean::cnstr_release(x_100, 0);
 lean::cnstr_release(x_100, 1);
 x_119 = x_100;
} else {
 lean::dec_ref(x_100);
 x_119 = lean::box(0);
}
if (lean::is_scalar(x_119)) {
 x_120 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_120 = x_119;
}
lean::cnstr_set(x_120, 0, x_117);
lean::cnstr_set(x_120, 1, x_118);
return x_120;
}
}
else
{
obj* x_121; obj* x_122; obj* x_123; obj* x_124; 
lean::dec(x_94);
x_121 = lean::cnstr_get(x_95, 0);
lean::inc(x_121);
x_122 = lean::cnstr_get(x_95, 1);
lean::inc(x_122);
if (lean::is_exclusive(x_95)) {
 lean::cnstr_release(x_95, 0);
 lean::cnstr_release(x_95, 1);
 x_123 = x_95;
} else {
 lean::dec_ref(x_95);
 x_123 = lean::box(0);
}
if (lean::is_scalar(x_123)) {
 x_124 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_124 = x_123;
}
lean::cnstr_set(x_124, 0, x_121);
lean::cnstr_set(x_124, 1, x_122);
return x_124;
}
}
}
else
{
uint8 x_125; 
lean::dec(x_1);
x_125 = !lean::is_exclusive(x_16);
if (x_125 == 0)
{
return x_16;
}
else
{
obj* x_126; obj* x_127; obj* x_128; 
x_126 = lean::cnstr_get(x_16, 0);
x_127 = lean::cnstr_get(x_16, 1);
lean::inc(x_127);
lean::inc(x_126);
lean::dec(x_16);
x_128 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_128, 0, x_126);
lean::cnstr_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
x_129 = lean::cnstr_get(x_3, 1);
lean::inc(x_129);
lean::dec(x_3);
x_130 = lean::box(0);
x_131 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_131, 0, x_130);
lean::cnstr_set(x_131, 1, x_129);
x_132 = l___private_init_lean_environment_5__envExtensionsRef;
x_133 = lean_io_ref_get(x_132, x_131);
if (lean::obj_tag(x_133) == 0)
{
obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; 
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
lean::cnstr_set(x_137, 0, x_130);
lean::cnstr_set(x_137, 1, x_135);
x_138 = lean_array_get_size(x_134);
lean::dec(x_134);
x_139 = lean::mk_nat_obj(0u);
x_140 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_140, 0, x_138);
lean::cnstr_set(x_140, 1, x_1);
lean::cnstr_set(x_140, 2, x_139);
x_141 = lean_io_ref_get(x_132, x_137);
if (lean::obj_tag(x_141) == 0)
{
obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; 
x_142 = lean::cnstr_get(x_141, 0);
lean::inc(x_142);
x_143 = lean::cnstr_get(x_141, 1);
lean::inc(x_143);
if (lean::is_exclusive(x_141)) {
 lean::cnstr_release(x_141, 0);
 lean::cnstr_release(x_141, 1);
 x_144 = x_141;
} else {
 lean::dec_ref(x_141);
 x_144 = lean::box(0);
}
if (lean::is_scalar(x_144)) {
 x_145 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_145 = x_144;
}
lean::cnstr_set(x_145, 0, x_130);
lean::cnstr_set(x_145, 1, x_143);
x_146 = lean_io_ref_reset(x_132, x_145);
if (lean::obj_tag(x_146) == 0)
{
obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; 
x_147 = lean::cnstr_get(x_146, 1);
lean::inc(x_147);
if (lean::is_exclusive(x_146)) {
 lean::cnstr_release(x_146, 0);
 lean::cnstr_release(x_146, 1);
 x_148 = x_146;
} else {
 lean::dec_ref(x_146);
 x_148 = lean::box(0);
}
if (lean::is_scalar(x_148)) {
 x_149 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_149 = x_148;
}
lean::cnstr_set(x_149, 0, x_130);
lean::cnstr_set(x_149, 1, x_147);
x_150 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_EnvExtension_Inhabited___rarg___lambda__1), 1, 0);
x_151 = l_Lean_EnvExtensionState_inhabited;
x_152 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_152, 0, x_139);
lean::cnstr_set(x_152, 1, x_150);
lean::cnstr_set(x_152, 2, x_151);
lean::inc(x_140);
x_153 = x_140;
x_154 = lean_array_push(x_142, x_153);
x_155 = lean_io_ref_set(x_132, x_154, x_149);
if (lean::obj_tag(x_155) == 0)
{
obj* x_156; obj* x_157; obj* x_158; 
x_156 = lean::cnstr_get(x_155, 1);
lean::inc(x_156);
if (lean::is_exclusive(x_155)) {
 lean::cnstr_release(x_155, 0);
 lean::cnstr_release(x_155, 1);
 x_157 = x_155;
} else {
 lean::dec_ref(x_155);
 x_157 = lean::box(0);
}
if (lean::is_scalar(x_157)) {
 x_158 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_158 = x_157;
}
lean::cnstr_set(x_158, 0, x_140);
lean::cnstr_set(x_158, 1, x_156);
return x_158;
}
else
{
obj* x_159; obj* x_160; obj* x_161; obj* x_162; 
lean::dec(x_140);
x_159 = lean::cnstr_get(x_155, 0);
lean::inc(x_159);
x_160 = lean::cnstr_get(x_155, 1);
lean::inc(x_160);
if (lean::is_exclusive(x_155)) {
 lean::cnstr_release(x_155, 0);
 lean::cnstr_release(x_155, 1);
 x_161 = x_155;
} else {
 lean::dec_ref(x_155);
 x_161 = lean::box(0);
}
if (lean::is_scalar(x_161)) {
 x_162 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_162 = x_161;
}
lean::cnstr_set(x_162, 0, x_159);
lean::cnstr_set(x_162, 1, x_160);
return x_162;
}
}
else
{
obj* x_163; obj* x_164; obj* x_165; obj* x_166; 
lean::dec(x_142);
lean::dec(x_140);
x_163 = lean::cnstr_get(x_146, 0);
lean::inc(x_163);
x_164 = lean::cnstr_get(x_146, 1);
lean::inc(x_164);
if (lean::is_exclusive(x_146)) {
 lean::cnstr_release(x_146, 0);
 lean::cnstr_release(x_146, 1);
 x_165 = x_146;
} else {
 lean::dec_ref(x_146);
 x_165 = lean::box(0);
}
if (lean::is_scalar(x_165)) {
 x_166 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_166 = x_165;
}
lean::cnstr_set(x_166, 0, x_163);
lean::cnstr_set(x_166, 1, x_164);
return x_166;
}
}
else
{
obj* x_167; obj* x_168; obj* x_169; obj* x_170; 
lean::dec(x_140);
x_167 = lean::cnstr_get(x_141, 0);
lean::inc(x_167);
x_168 = lean::cnstr_get(x_141, 1);
lean::inc(x_168);
if (lean::is_exclusive(x_141)) {
 lean::cnstr_release(x_141, 0);
 lean::cnstr_release(x_141, 1);
 x_169 = x_141;
} else {
 lean::dec_ref(x_141);
 x_169 = lean::box(0);
}
if (lean::is_scalar(x_169)) {
 x_170 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_170 = x_169;
}
lean::cnstr_set(x_170, 0, x_167);
lean::cnstr_set(x_170, 1, x_168);
return x_170;
}
}
else
{
obj* x_171; obj* x_172; obj* x_173; obj* x_174; 
lean::dec(x_1);
x_171 = lean::cnstr_get(x_133, 0);
lean::inc(x_171);
x_172 = lean::cnstr_get(x_133, 1);
lean::inc(x_172);
if (lean::is_exclusive(x_133)) {
 lean::cnstr_release(x_133, 0);
 lean::cnstr_release(x_133, 1);
 x_173 = x_133;
} else {
 lean::dec_ref(x_133);
 x_173 = lean::box(0);
}
if (lean::is_scalar(x_173)) {
 x_174 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_174 = x_173;
}
lean::cnstr_set(x_174, 0, x_171);
lean::cnstr_set(x_174, 1, x_172);
return x_174;
}
}
}
}
else
{
uint8 x_175; 
lean::dec(x_1);
x_175 = !lean::is_exclusive(x_3);
if (x_175 == 0)
{
return x_3;
}
else
{
obj* x_176; obj* x_177; obj* x_178; 
x_176 = lean::cnstr_get(x_3, 0);
x_177 = lean::cnstr_get(x_3, 1);
lean::inc(x_177);
lean::inc(x_176);
lean::dec(x_3);
x_178 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_178, 0, x_176);
lean::cnstr_set(x_178, 1, x_177);
return x_178;
}
}
}
}
obj* lean_register_extension(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_pure___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::box(0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_3);
x_5 = l_Lean_registerEnvExtensionUnsafe___at_Lean_registerCPPExtension___spec__1(x_2, x_4);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
lean::dec(x_5);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
else
{
obj* x_9; 
lean::dec(x_5);
x_9 = lean::box(0);
return x_9;
}
}
}
obj* lean_set_extension(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::box(0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_4);
x_6 = l___private_init_lean_environment_5__envExtensionsRef;
x_7 = lean_io_ref_get(x_6, x_5);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::mk_nat_obj(0u);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_EnvExtension_Inhabited___rarg___lambda__1), 1, 0);
x_11 = l_Lean_EnvExtensionState_inhabited;
x_12 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_12, 0, x_9);
lean::cnstr_set(x_12, 1, x_10);
lean::cnstr_set(x_12, 2, x_11);
x_13 = lean_array_get(x_12, x_8, x_2);
lean::dec(x_2);
lean::dec(x_8);
x_14 = l_Lean_EnvExtension_setStateUnsafe___rarg(x_13, x_1, x_3);
lean::dec(x_13);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
return x_15;
}
else
{
obj* x_16; 
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_16 = lean::box(0);
return x_16;
}
}
}
obj* lean_get_extension(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::box(0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_3);
x_5 = l___private_init_lean_environment_5__envExtensionsRef;
x_6 = lean_io_ref_get(x_5, x_4);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::mk_nat_obj(0u);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_EnvExtension_Inhabited___rarg___lambda__1), 1, 0);
x_10 = l_Lean_EnvExtensionState_inhabited;
x_11 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_9);
lean::cnstr_set(x_11, 2, x_10);
x_12 = lean_array_get(x_11, x_7, x_2);
lean::dec(x_2);
lean::dec(x_7);
x_13 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_12, x_1);
lean::dec(x_1);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
else
{
obj* x_15; 
lean::dec(x_6);
lean::dec(x_2);
lean::dec(x_1);
x_15 = lean::box(0);
return x_15;
}
}
}
obj* _init_l_Lean_Modification_inhabited() {
_start:
{
obj* x_1; 
x_1 = l_NonScalar_Inhabited;
return x_1;
}
}
obj* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_regModListExtension___spec__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
}
}
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_regModListExtension___spec__1(obj* x_1, obj* x_2) {
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
x_16 = lean_io_ref_get(x_15, x_3);
if (lean::obj_tag(x_16) == 0)
{
uint8 x_17; 
x_17 = !lean::is_exclusive(x_16);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_18 = lean::cnstr_get(x_16, 0);
lean::cnstr_set(x_16, 0, x_14);
x_19 = lean_array_get_size(x_18);
lean::dec(x_18);
x_20 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regModListExtension___spec__1___closed__1;
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_1);
lean::cnstr_set(x_21, 2, x_20);
x_22 = lean_io_ref_get(x_15, x_16);
if (lean::obj_tag(x_22) == 0)
{
uint8 x_23; 
x_23 = !lean::is_exclusive(x_22);
if (x_23 == 0)
{
obj* x_24; obj* x_25; 
x_24 = lean::cnstr_get(x_22, 0);
lean::cnstr_set(x_22, 0, x_14);
x_25 = lean_io_ref_reset(x_15, x_22);
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
x_30 = lean_array_push(x_24, x_29);
x_31 = lean_io_ref_set(x_15, x_30, x_25);
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
x_44 = lean_array_push(x_24, x_43);
x_45 = lean_io_ref_set(x_15, x_44, x_41);
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
x_60 = lean_io_ref_reset(x_15, x_59);
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
x_66 = lean_array_push(x_57, x_65);
x_67 = lean_io_ref_set(x_15, x_66, x_63);
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
x_86 = lean_array_get_size(x_83);
lean::dec(x_83);
x_87 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regModListExtension___spec__1___closed__1;
x_88 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_88, 0, x_86);
lean::cnstr_set(x_88, 1, x_1);
lean::cnstr_set(x_88, 2, x_87);
x_89 = lean_io_ref_get(x_15, x_85);
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
x_94 = lean_io_ref_reset(x_15, x_93);
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
x_100 = lean_array_push(x_90, x_99);
x_101 = lean_io_ref_set(x_15, x_100, x_97);
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
x_125 = lean_io_ref_get(x_124, x_123);
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
x_130 = lean_array_get_size(x_126);
lean::dec(x_126);
x_131 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regModListExtension___spec__1___closed__1;
x_132 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_132, 0, x_130);
lean::cnstr_set(x_132, 1, x_1);
lean::cnstr_set(x_132, 2, x_131);
x_133 = lean_io_ref_get(x_124, x_129);
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
x_138 = lean_io_ref_reset(x_124, x_137);
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
x_144 = lean_array_push(x_134, x_143);
x_145 = lean_io_ref_set(x_124, x_144, x_141);
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
obj* _init_l_Lean_regModListExtension___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_pure___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_regModListExtension(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_regModListExtension___closed__1;
x_3 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regModListExtension___spec__1(x_2, x_1);
return x_3;
}
}
obj* l_Lean_modListExtension___elambda__1(obj* x_1) {
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
obj* _init_l_Lean_modListExtension___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_modListExtension___elambda__1), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_modListExtension___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::mk_nat_obj(0u);
x_2 = l_Lean_modListExtension___closed__1;
x_3 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regModListExtension___spec__1___closed__1;
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 2, x_3);
return x_4;
}
}
obj* lean_environment_add_modification(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_1, 2);
x_5 = l_Lean_modListExtension;
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
lean::dec(x_6);
lean::dec(x_2);
return x_1;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_9 = lean_array_fget(x_4, x_6);
x_10 = lean::mk_nat_obj(0u);
x_11 = lean_array_fset(x_4, x_6, x_10);
x_12 = lean::cnstr_get(x_5, 2);
lean::inc(x_12);
x_13 = x_9;
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_2);
lean::cnstr_set(x_14, 1, x_13);
x_15 = l_Lean_EnvExtensionState_inhabited;
x_16 = x_14;
x_17 = lean_array_fset(x_11, x_6, x_16);
lean::dec(x_6);
lean::cnstr_set(x_1, 2, x_17);
return x_1;
}
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; uint8 x_25; 
x_18 = lean::cnstr_get(x_1, 0);
x_19 = lean::cnstr_get(x_1, 1);
x_20 = lean::cnstr_get(x_1, 2);
x_21 = lean::cnstr_get(x_1, 3);
lean::inc(x_21);
lean::inc(x_20);
lean::inc(x_19);
lean::inc(x_18);
lean::dec(x_1);
x_22 = l_Lean_modListExtension;
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
x_24 = lean_array_get_size(x_20);
x_25 = lean_nat_dec_lt(x_23, x_24);
lean::dec(x_24);
if (x_25 == 0)
{
obj* x_26; 
lean::dec(x_23);
lean::dec(x_2);
x_26 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_26, 0, x_18);
lean::cnstr_set(x_26, 1, x_19);
lean::cnstr_set(x_26, 2, x_20);
lean::cnstr_set(x_26, 3, x_21);
return x_26;
}
else
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_27 = lean_array_fget(x_20, x_23);
x_28 = lean::mk_nat_obj(0u);
x_29 = lean_array_fset(x_20, x_23, x_28);
x_30 = lean::cnstr_get(x_22, 2);
lean::inc(x_30);
x_31 = x_27;
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_2);
lean::cnstr_set(x_32, 1, x_31);
x_33 = l_Lean_EnvExtensionState_inhabited;
x_34 = x_32;
x_35 = lean_array_fset(x_29, x_23, x_34);
lean::dec(x_23);
x_36 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_36, 0, x_18);
lean::cnstr_set(x_36, 1, x_19);
lean::cnstr_set(x_36, 2, x_35);
lean::cnstr_set(x_36, 3, x_21);
return x_36;
}
}
}
}
obj* l_Lean_serializeModifications___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_serialize_modifications(x_1, x_2);
return x_3;
}
}
obj* l_Lean_performModifications___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean_perform_serialized_modifications(x_1, x_2, x_3);
return x_4;
}
}
obj* _init_l_Lean_ModuleData_inhabited___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_ByteArray_empty;
x_3 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_1);
lean::cnstr_set(x_3, 3, x_2);
return x_3;
}
}
obj* _init_l_Lean_ModuleData_inhabited() {
_start:
{
obj* x_1; 
x_1 = l_Lean_ModuleData_inhabited___closed__1;
return x_1;
}
}
obj* l_Lean_saveModuleData___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean_save_module_data(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_readModuleData___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_read_module_data(x_1, x_2);
return x_3;
}
}
obj* l_Nat_foldAux___main___at_Lean_mkModuleData___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::mk_nat_obj(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean_nat_sub(x_4, x_8);
x_10 = lean_nat_sub(x_3, x_4);
lean::dec(x_4);
x_11 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_12 = lean_array_get(x_11, x_2, x_10);
lean::dec(x_10);
lean::inc(x_12);
x_13 = l_Lean_PersistentEnvExtension_getState___rarg(x_12, x_1);
x_14 = lean::cnstr_get(x_12, 4);
lean::inc(x_14);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
x_16 = lean::apply_1(x_14, x_13);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean_array_push(x_5, x_17);
x_4 = x_9;
x_5 = x_18;
goto _start;
}
else
{
lean::dec(x_4);
return x_5;
}
}
}
obj* l_RBNode_fold___main___at_Lean_mkModuleData___spec__2(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_2, 2);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_2, 3);
lean::inc(x_5);
lean::dec(x_2);
x_6 = l_RBNode_fold___main___at_Lean_mkModuleData___spec__2(x_1, x_3);
x_7 = lean_array_push(x_6, x_4);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
obj* l_Lean_mkModuleData(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l___private_init_lean_environment_8__persistentEnvExtensionsRef;
x_4 = lean_io_ref_get(x_3, x_2);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_4, 0);
x_7 = lean::box(0);
lean::cnstr_set(x_4, 0, x_7);
x_8 = lean_array_get_size(x_6);
x_9 = l_Array_empty___closed__1;
lean::inc(x_8);
x_10 = l_Nat_foldAux___main___at_Lean_mkModuleData___spec__1(x_1, x_6, x_8, x_8, x_9);
lean::dec(x_8);
lean::dec(x_6);
x_11 = l_Lean_modListExtension;
x_12 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_11, x_1);
x_13 = lean_serialize_modifications(x_12, x_4);
if (lean::obj_tag(x_13) == 0)
{
uint8 x_14; 
x_14 = !lean::is_exclusive(x_13);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_15 = lean::cnstr_get(x_13, 0);
x_16 = lean::cnstr_get(x_1, 3);
lean::inc(x_16);
x_17 = lean::cnstr_get(x_16, 1);
lean::inc(x_17);
lean::dec(x_16);
x_18 = lean::cnstr_get(x_1, 1);
lean::inc(x_18);
lean::dec(x_1);
x_19 = lean::cnstr_get(x_18, 1);
lean::inc(x_19);
lean::dec(x_18);
x_20 = l_RBNode_fold___main___at_Lean_mkModuleData___spec__2(x_9, x_19);
x_21 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_21, 0, x_17);
lean::cnstr_set(x_21, 1, x_20);
lean::cnstr_set(x_21, 2, x_10);
lean::cnstr_set(x_21, 3, x_15);
lean::cnstr_set(x_13, 0, x_21);
return x_13;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_22 = lean::cnstr_get(x_13, 0);
x_23 = lean::cnstr_get(x_13, 1);
lean::inc(x_23);
lean::inc(x_22);
lean::dec(x_13);
x_24 = lean::cnstr_get(x_1, 3);
lean::inc(x_24);
x_25 = lean::cnstr_get(x_24, 1);
lean::inc(x_25);
lean::dec(x_24);
x_26 = lean::cnstr_get(x_1, 1);
lean::inc(x_26);
lean::dec(x_1);
x_27 = lean::cnstr_get(x_26, 1);
lean::inc(x_27);
lean::dec(x_26);
x_28 = l_RBNode_fold___main___at_Lean_mkModuleData___spec__2(x_9, x_27);
x_29 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_29, 0, x_25);
lean::cnstr_set(x_29, 1, x_28);
lean::cnstr_set(x_29, 2, x_10);
lean::cnstr_set(x_29, 3, x_22);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_23);
return x_30;
}
}
else
{
uint8 x_31; 
lean::dec(x_10);
lean::dec(x_1);
x_31 = !lean::is_exclusive(x_13);
if (x_31 == 0)
{
return x_13;
}
else
{
obj* x_32; obj* x_33; obj* x_34; 
x_32 = lean::cnstr_get(x_13, 0);
x_33 = lean::cnstr_get(x_13, 1);
lean::inc(x_33);
lean::inc(x_32);
lean::dec(x_13);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_35 = lean::cnstr_get(x_4, 0);
x_36 = lean::cnstr_get(x_4, 1);
lean::inc(x_36);
lean::inc(x_35);
lean::dec(x_4);
x_37 = lean::box(0);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_36);
x_39 = lean_array_get_size(x_35);
x_40 = l_Array_empty___closed__1;
lean::inc(x_39);
x_41 = l_Nat_foldAux___main___at_Lean_mkModuleData___spec__1(x_1, x_35, x_39, x_39, x_40);
lean::dec(x_39);
lean::dec(x_35);
x_42 = l_Lean_modListExtension;
x_43 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_42, x_1);
x_44 = lean_serialize_modifications(x_43, x_38);
if (lean::obj_tag(x_44) == 0)
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_45 = lean::cnstr_get(x_44, 0);
lean::inc(x_45);
x_46 = lean::cnstr_get(x_44, 1);
lean::inc(x_46);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 lean::cnstr_release(x_44, 1);
 x_47 = x_44;
} else {
 lean::dec_ref(x_44);
 x_47 = lean::box(0);
}
x_48 = lean::cnstr_get(x_1, 3);
lean::inc(x_48);
x_49 = lean::cnstr_get(x_48, 1);
lean::inc(x_49);
lean::dec(x_48);
x_50 = lean::cnstr_get(x_1, 1);
lean::inc(x_50);
lean::dec(x_1);
x_51 = lean::cnstr_get(x_50, 1);
lean::inc(x_51);
lean::dec(x_50);
x_52 = l_RBNode_fold___main___at_Lean_mkModuleData___spec__2(x_40, x_51);
x_53 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_53, 0, x_49);
lean::cnstr_set(x_53, 1, x_52);
lean::cnstr_set(x_53, 2, x_41);
lean::cnstr_set(x_53, 3, x_45);
if (lean::is_scalar(x_47)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_47;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_46);
return x_54;
}
else
{
obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
lean::dec(x_41);
lean::dec(x_1);
x_55 = lean::cnstr_get(x_44, 0);
lean::inc(x_55);
x_56 = lean::cnstr_get(x_44, 1);
lean::inc(x_56);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 lean::cnstr_release(x_44, 1);
 x_57 = x_44;
} else {
 lean::dec_ref(x_44);
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
else
{
uint8 x_59; 
lean::dec(x_1);
x_59 = !lean::is_exclusive(x_4);
if (x_59 == 0)
{
return x_4;
}
else
{
obj* x_60; obj* x_61; obj* x_62; 
x_60 = lean::cnstr_get(x_4, 0);
x_61 = lean::cnstr_get(x_4, 1);
lean::inc(x_61);
lean::inc(x_60);
lean::dec(x_4);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_60);
lean::cnstr_set(x_62, 1, x_61);
return x_62;
}
}
}
}
obj* l_Nat_foldAux___main___at_Lean_mkModuleData___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Nat_foldAux___main___at_Lean_mkModuleData___spec__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* lean_write_module(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_mkModuleData(x_1, x_3);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_4, 0);
x_7 = lean::box(0);
lean::cnstr_set(x_4, 0, x_7);
x_8 = lean_save_module_data(x_2, x_6, x_4);
lean::dec(x_2);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_4, 0);
x_10 = lean::cnstr_get(x_4, 1);
lean::inc(x_10);
lean::inc(x_9);
lean::dec(x_4);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
x_13 = lean_save_module_data(x_2, x_9, x_12);
lean::dec(x_2);
return x_13;
}
}
else
{
uint8 x_14; 
lean::dec(x_2);
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
obj* l_Lean_importModulesAux___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; 
x_5 = lean::cnstr_get(x_3, 0);
lean::dec(x_5);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
else
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_2);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::dec(x_1);
x_10 = lean::cnstr_get(x_2, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
x_12 = l_Lean_NameSet_contains(x_10, x_8);
if (x_12 == 0)
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_2);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_14 = lean::cnstr_get(x_2, 1);
lean::dec(x_14);
x_15 = lean::cnstr_get(x_2, 0);
lean::dec(x_15);
x_16 = lean::box(0);
lean::inc(x_8);
x_17 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_10, x_8, x_16);
x_18 = l_Lean_findOLean___closed__1;
x_19 = l_Lean_findLeanFile(x_8, x_18, x_3);
if (lean::obj_tag(x_19) == 0)
{
uint8 x_20; 
x_20 = !lean::is_exclusive(x_19);
if (x_20 == 0)
{
obj* x_21; obj* x_22; 
x_21 = lean::cnstr_get(x_19, 0);
lean::cnstr_set(x_19, 0, x_16);
x_22 = lean_read_module_data(x_21, x_19);
lean::dec(x_21);
if (lean::obj_tag(x_22) == 0)
{
uint8 x_23; 
x_23 = !lean::is_exclusive(x_22);
if (x_23 == 0)
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_24 = lean::cnstr_get(x_22, 0);
lean::cnstr_set(x_22, 0, x_16);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_26 = l_Array_toList___rarg(x_25);
lean::dec(x_25);
lean::cnstr_set(x_2, 0, x_17);
x_27 = l_Lean_importModulesAux___main(x_26, x_2, x_22);
if (lean::obj_tag(x_27) == 0)
{
uint8 x_28; 
x_28 = !lean::is_exclusive(x_27);
if (x_28 == 0)
{
obj* x_29; uint8 x_30; 
x_29 = lean::cnstr_get(x_27, 0);
lean::cnstr_set(x_27, 0, x_16);
x_30 = !lean::is_exclusive(x_29);
if (x_30 == 0)
{
obj* x_31; obj* x_32; 
x_31 = lean::cnstr_get(x_29, 1);
x_32 = lean_array_push(x_31, x_24);
lean::cnstr_set(x_29, 1, x_32);
x_1 = x_9;
x_2 = x_29;
x_3 = x_27;
goto _start;
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_34 = lean::cnstr_get(x_29, 0);
x_35 = lean::cnstr_get(x_29, 1);
lean::inc(x_35);
lean::inc(x_34);
lean::dec(x_29);
x_36 = lean_array_push(x_35, x_24);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_34);
lean::cnstr_set(x_37, 1, x_36);
x_1 = x_9;
x_2 = x_37;
x_3 = x_27;
goto _start;
}
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_39 = lean::cnstr_get(x_27, 0);
x_40 = lean::cnstr_get(x_27, 1);
lean::inc(x_40);
lean::inc(x_39);
lean::dec(x_27);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_16);
lean::cnstr_set(x_41, 1, x_40);
x_42 = lean::cnstr_get(x_39, 0);
lean::inc(x_42);
x_43 = lean::cnstr_get(x_39, 1);
lean::inc(x_43);
if (lean::is_exclusive(x_39)) {
 lean::cnstr_release(x_39, 0);
 lean::cnstr_release(x_39, 1);
 x_44 = x_39;
} else {
 lean::dec_ref(x_39);
 x_44 = lean::box(0);
}
x_45 = lean_array_push(x_43, x_24);
if (lean::is_scalar(x_44)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_44;
}
lean::cnstr_set(x_46, 0, x_42);
lean::cnstr_set(x_46, 1, x_45);
x_1 = x_9;
x_2 = x_46;
x_3 = x_41;
goto _start;
}
}
else
{
uint8 x_48; 
lean::dec(x_24);
lean::dec(x_9);
x_48 = !lean::is_exclusive(x_27);
if (x_48 == 0)
{
return x_27;
}
else
{
obj* x_49; obj* x_50; obj* x_51; 
x_49 = lean::cnstr_get(x_27, 0);
x_50 = lean::cnstr_get(x_27, 1);
lean::inc(x_50);
lean::inc(x_49);
lean::dec(x_27);
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_49);
lean::cnstr_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_52 = lean::cnstr_get(x_22, 0);
x_53 = lean::cnstr_get(x_22, 1);
lean::inc(x_53);
lean::inc(x_52);
lean::dec(x_22);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_16);
lean::cnstr_set(x_54, 1, x_53);
x_55 = lean::cnstr_get(x_52, 0);
lean::inc(x_55);
x_56 = l_Array_toList___rarg(x_55);
lean::dec(x_55);
lean::cnstr_set(x_2, 0, x_17);
x_57 = l_Lean_importModulesAux___main(x_56, x_2, x_54);
if (lean::obj_tag(x_57) == 0)
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
x_59 = lean::cnstr_get(x_57, 1);
lean::inc(x_59);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 lean::cnstr_release(x_57, 1);
 x_60 = x_57;
} else {
 lean::dec_ref(x_57);
 x_60 = lean::box(0);
}
if (lean::is_scalar(x_60)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_60;
}
lean::cnstr_set(x_61, 0, x_16);
lean::cnstr_set(x_61, 1, x_59);
x_62 = lean::cnstr_get(x_58, 0);
lean::inc(x_62);
x_63 = lean::cnstr_get(x_58, 1);
lean::inc(x_63);
if (lean::is_exclusive(x_58)) {
 lean::cnstr_release(x_58, 0);
 lean::cnstr_release(x_58, 1);
 x_64 = x_58;
} else {
 lean::dec_ref(x_58);
 x_64 = lean::box(0);
}
x_65 = lean_array_push(x_63, x_52);
if (lean::is_scalar(x_64)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_64;
}
lean::cnstr_set(x_66, 0, x_62);
lean::cnstr_set(x_66, 1, x_65);
x_1 = x_9;
x_2 = x_66;
x_3 = x_61;
goto _start;
}
else
{
obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
lean::dec(x_52);
lean::dec(x_9);
x_68 = lean::cnstr_get(x_57, 0);
lean::inc(x_68);
x_69 = lean::cnstr_get(x_57, 1);
lean::inc(x_69);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 lean::cnstr_release(x_57, 1);
 x_70 = x_57;
} else {
 lean::dec_ref(x_57);
 x_70 = lean::box(0);
}
if (lean::is_scalar(x_70)) {
 x_71 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_71 = x_70;
}
lean::cnstr_set(x_71, 0, x_68);
lean::cnstr_set(x_71, 1, x_69);
return x_71;
}
}
}
else
{
uint8 x_72; 
lean::dec(x_17);
lean::free_heap_obj(x_2);
lean::dec(x_11);
lean::dec(x_9);
x_72 = !lean::is_exclusive(x_22);
if (x_72 == 0)
{
return x_22;
}
else
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = lean::cnstr_get(x_22, 0);
x_74 = lean::cnstr_get(x_22, 1);
lean::inc(x_74);
lean::inc(x_73);
lean::dec(x_22);
x_75 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_75, 0, x_73);
lean::cnstr_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
x_76 = lean::cnstr_get(x_19, 0);
x_77 = lean::cnstr_get(x_19, 1);
lean::inc(x_77);
lean::inc(x_76);
lean::dec(x_19);
x_78 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_78, 0, x_16);
lean::cnstr_set(x_78, 1, x_77);
x_79 = lean_read_module_data(x_76, x_78);
lean::dec(x_76);
if (lean::obj_tag(x_79) == 0)
{
obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
x_80 = lean::cnstr_get(x_79, 0);
lean::inc(x_80);
x_81 = lean::cnstr_get(x_79, 1);
lean::inc(x_81);
if (lean::is_exclusive(x_79)) {
 lean::cnstr_release(x_79, 0);
 lean::cnstr_release(x_79, 1);
 x_82 = x_79;
} else {
 lean::dec_ref(x_79);
 x_82 = lean::box(0);
}
if (lean::is_scalar(x_82)) {
 x_83 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_83 = x_82;
}
lean::cnstr_set(x_83, 0, x_16);
lean::cnstr_set(x_83, 1, x_81);
x_84 = lean::cnstr_get(x_80, 0);
lean::inc(x_84);
x_85 = l_Array_toList___rarg(x_84);
lean::dec(x_84);
lean::cnstr_set(x_2, 0, x_17);
x_86 = l_Lean_importModulesAux___main(x_85, x_2, x_83);
if (lean::obj_tag(x_86) == 0)
{
obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_87 = lean::cnstr_get(x_86, 0);
lean::inc(x_87);
x_88 = lean::cnstr_get(x_86, 1);
lean::inc(x_88);
if (lean::is_exclusive(x_86)) {
 lean::cnstr_release(x_86, 0);
 lean::cnstr_release(x_86, 1);
 x_89 = x_86;
} else {
 lean::dec_ref(x_86);
 x_89 = lean::box(0);
}
if (lean::is_scalar(x_89)) {
 x_90 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_90 = x_89;
}
lean::cnstr_set(x_90, 0, x_16);
lean::cnstr_set(x_90, 1, x_88);
x_91 = lean::cnstr_get(x_87, 0);
lean::inc(x_91);
x_92 = lean::cnstr_get(x_87, 1);
lean::inc(x_92);
if (lean::is_exclusive(x_87)) {
 lean::cnstr_release(x_87, 0);
 lean::cnstr_release(x_87, 1);
 x_93 = x_87;
} else {
 lean::dec_ref(x_87);
 x_93 = lean::box(0);
}
x_94 = lean_array_push(x_92, x_80);
if (lean::is_scalar(x_93)) {
 x_95 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_95 = x_93;
}
lean::cnstr_set(x_95, 0, x_91);
lean::cnstr_set(x_95, 1, x_94);
x_1 = x_9;
x_2 = x_95;
x_3 = x_90;
goto _start;
}
else
{
obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
lean::dec(x_80);
lean::dec(x_9);
x_97 = lean::cnstr_get(x_86, 0);
lean::inc(x_97);
x_98 = lean::cnstr_get(x_86, 1);
lean::inc(x_98);
if (lean::is_exclusive(x_86)) {
 lean::cnstr_release(x_86, 0);
 lean::cnstr_release(x_86, 1);
 x_99 = x_86;
} else {
 lean::dec_ref(x_86);
 x_99 = lean::box(0);
}
if (lean::is_scalar(x_99)) {
 x_100 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_100 = x_99;
}
lean::cnstr_set(x_100, 0, x_97);
lean::cnstr_set(x_100, 1, x_98);
return x_100;
}
}
else
{
obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
lean::dec(x_17);
lean::free_heap_obj(x_2);
lean::dec(x_11);
lean::dec(x_9);
x_101 = lean::cnstr_get(x_79, 0);
lean::inc(x_101);
x_102 = lean::cnstr_get(x_79, 1);
lean::inc(x_102);
if (lean::is_exclusive(x_79)) {
 lean::cnstr_release(x_79, 0);
 lean::cnstr_release(x_79, 1);
 x_103 = x_79;
} else {
 lean::dec_ref(x_79);
 x_103 = lean::box(0);
}
if (lean::is_scalar(x_103)) {
 x_104 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_104 = x_103;
}
lean::cnstr_set(x_104, 0, x_101);
lean::cnstr_set(x_104, 1, x_102);
return x_104;
}
}
}
else
{
uint8 x_105; 
lean::dec(x_17);
lean::free_heap_obj(x_2);
lean::dec(x_11);
lean::dec(x_9);
x_105 = !lean::is_exclusive(x_19);
if (x_105 == 0)
{
return x_19;
}
else
{
obj* x_106; obj* x_107; obj* x_108; 
x_106 = lean::cnstr_get(x_19, 0);
x_107 = lean::cnstr_get(x_19, 1);
lean::inc(x_107);
lean::inc(x_106);
lean::dec(x_19);
x_108 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_108, 0, x_106);
lean::cnstr_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_2);
x_109 = lean::box(0);
lean::inc(x_8);
x_110 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_10, x_8, x_109);
x_111 = l_Lean_findOLean___closed__1;
x_112 = l_Lean_findLeanFile(x_8, x_111, x_3);
if (lean::obj_tag(x_112) == 0)
{
obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; 
x_113 = lean::cnstr_get(x_112, 0);
lean::inc(x_113);
x_114 = lean::cnstr_get(x_112, 1);
lean::inc(x_114);
if (lean::is_exclusive(x_112)) {
 lean::cnstr_release(x_112, 0);
 lean::cnstr_release(x_112, 1);
 x_115 = x_112;
} else {
 lean::dec_ref(x_112);
 x_115 = lean::box(0);
}
if (lean::is_scalar(x_115)) {
 x_116 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_116 = x_115;
}
lean::cnstr_set(x_116, 0, x_109);
lean::cnstr_set(x_116, 1, x_114);
x_117 = lean_read_module_data(x_113, x_116);
lean::dec(x_113);
if (lean::obj_tag(x_117) == 0)
{
obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; 
x_118 = lean::cnstr_get(x_117, 0);
lean::inc(x_118);
x_119 = lean::cnstr_get(x_117, 1);
lean::inc(x_119);
if (lean::is_exclusive(x_117)) {
 lean::cnstr_release(x_117, 0);
 lean::cnstr_release(x_117, 1);
 x_120 = x_117;
} else {
 lean::dec_ref(x_117);
 x_120 = lean::box(0);
}
if (lean::is_scalar(x_120)) {
 x_121 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_121 = x_120;
}
lean::cnstr_set(x_121, 0, x_109);
lean::cnstr_set(x_121, 1, x_119);
x_122 = lean::cnstr_get(x_118, 0);
lean::inc(x_122);
x_123 = l_Array_toList___rarg(x_122);
lean::dec(x_122);
x_124 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_124, 0, x_110);
lean::cnstr_set(x_124, 1, x_11);
x_125 = l_Lean_importModulesAux___main(x_123, x_124, x_121);
if (lean::obj_tag(x_125) == 0)
{
obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
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
lean::cnstr_set(x_129, 0, x_109);
lean::cnstr_set(x_129, 1, x_127);
x_130 = lean::cnstr_get(x_126, 0);
lean::inc(x_130);
x_131 = lean::cnstr_get(x_126, 1);
lean::inc(x_131);
if (lean::is_exclusive(x_126)) {
 lean::cnstr_release(x_126, 0);
 lean::cnstr_release(x_126, 1);
 x_132 = x_126;
} else {
 lean::dec_ref(x_126);
 x_132 = lean::box(0);
}
x_133 = lean_array_push(x_131, x_118);
if (lean::is_scalar(x_132)) {
 x_134 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_134 = x_132;
}
lean::cnstr_set(x_134, 0, x_130);
lean::cnstr_set(x_134, 1, x_133);
x_1 = x_9;
x_2 = x_134;
x_3 = x_129;
goto _start;
}
else
{
obj* x_136; obj* x_137; obj* x_138; obj* x_139; 
lean::dec(x_118);
lean::dec(x_9);
x_136 = lean::cnstr_get(x_125, 0);
lean::inc(x_136);
x_137 = lean::cnstr_get(x_125, 1);
lean::inc(x_137);
if (lean::is_exclusive(x_125)) {
 lean::cnstr_release(x_125, 0);
 lean::cnstr_release(x_125, 1);
 x_138 = x_125;
} else {
 lean::dec_ref(x_125);
 x_138 = lean::box(0);
}
if (lean::is_scalar(x_138)) {
 x_139 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_139 = x_138;
}
lean::cnstr_set(x_139, 0, x_136);
lean::cnstr_set(x_139, 1, x_137);
return x_139;
}
}
else
{
obj* x_140; obj* x_141; obj* x_142; obj* x_143; 
lean::dec(x_110);
lean::dec(x_11);
lean::dec(x_9);
x_140 = lean::cnstr_get(x_117, 0);
lean::inc(x_140);
x_141 = lean::cnstr_get(x_117, 1);
lean::inc(x_141);
if (lean::is_exclusive(x_117)) {
 lean::cnstr_release(x_117, 0);
 lean::cnstr_release(x_117, 1);
 x_142 = x_117;
} else {
 lean::dec_ref(x_117);
 x_142 = lean::box(0);
}
if (lean::is_scalar(x_142)) {
 x_143 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_143 = x_142;
}
lean::cnstr_set(x_143, 0, x_140);
lean::cnstr_set(x_143, 1, x_141);
return x_143;
}
}
else
{
obj* x_144; obj* x_145; obj* x_146; obj* x_147; 
lean::dec(x_110);
lean::dec(x_11);
lean::dec(x_9);
x_144 = lean::cnstr_get(x_112, 0);
lean::inc(x_144);
x_145 = lean::cnstr_get(x_112, 1);
lean::inc(x_145);
if (lean::is_exclusive(x_112)) {
 lean::cnstr_release(x_112, 0);
 lean::cnstr_release(x_112, 1);
 x_146 = x_112;
} else {
 lean::dec_ref(x_112);
 x_146 = lean::box(0);
}
if (lean::is_scalar(x_146)) {
 x_147 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_147 = x_146;
}
lean::cnstr_set(x_147, 0, x_144);
lean::cnstr_set(x_147, 1, x_145);
return x_147;
}
}
}
else
{
lean::dec(x_11);
lean::dec(x_10);
lean::dec(x_8);
x_1 = x_9;
goto _start;
}
}
}
}
obj* l_Lean_importModulesAux(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_importModulesAux___main(x_1, x_2, x_3);
return x_4;
}
}
obj* _init_l___private_init_lean_environment_9__getEntriesFor___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Inhabited;
x_2 = l_Array_empty___closed__1;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l___private_init_lean_environment_9__getEntriesFor___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::cnstr_get(x_1, 2);
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_7; 
lean::dec(x_3);
x_7 = l_Array_empty___closed__1;
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; uint8 x_11; 
x_8 = l___private_init_lean_environment_9__getEntriesFor___main___closed__1;
x_9 = lean_array_get(x_8, x_4, x_3);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_11 = lean_name_dec_eq(x_10, x_2);
lean::dec(x_10);
if (x_11 == 0)
{
obj* x_12; obj* x_13; 
lean::dec(x_9);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean_nat_add(x_3, x_12);
lean::dec(x_3);
x_3 = x_13;
goto _start;
}
else
{
obj* x_15; 
lean::dec(x_3);
x_15 = lean::cnstr_get(x_9, 1);
lean::inc(x_15);
lean::dec(x_9);
return x_15;
}
}
}
}
obj* l___private_init_lean_environment_9__getEntriesFor___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_environment_9__getEntriesFor___main(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_environment_9__getEntriesFor(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_environment_9__getEntriesFor___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_lean_environment_9__getEntriesFor___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_environment_9__getEntriesFor(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_environment_10__setImportedEntries___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
return x_5;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
x_10 = lean::mk_nat_obj(0u);
x_11 = l___private_init_lean_environment_9__getEntriesFor___main(x_2, x_9, x_10);
lean::dec(x_9);
x_12 = lean::cnstr_get(x_8, 0);
lean::inc(x_12);
lean::dec(x_8);
x_13 = !lean::is_exclusive(x_5);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; uint8 x_17; obj* x_18; obj* x_19; 
x_14 = lean::cnstr_get(x_5, 2);
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
x_16 = lean_array_get_size(x_14);
x_17 = lean_nat_dec_lt(x_15, x_16);
lean::dec(x_16);
x_18 = lean::mk_nat_obj(1u);
x_19 = lean_nat_add(x_4, x_18);
lean::dec(x_4);
if (x_17 == 0)
{
lean::dec(x_15);
lean::dec(x_12);
lean::dec(x_11);
x_4 = x_19;
goto _start;
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; uint8 x_25; 
x_21 = lean_array_fget(x_14, x_15);
x_22 = lean_array_fset(x_14, x_15, x_10);
x_23 = lean::cnstr_get(x_12, 2);
lean::inc(x_23);
lean::dec(x_12);
x_24 = x_21;
x_25 = !lean::is_exclusive(x_24);
if (x_25 == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_26 = lean::cnstr_get(x_24, 0);
x_27 = lean_array_push(x_26, x_11);
lean::cnstr_set(x_24, 0, x_27);
x_28 = l_Lean_EnvExtensionState_inhabited;
x_29 = x_24;
x_30 = lean_array_fset(x_22, x_15, x_29);
lean::dec(x_15);
lean::cnstr_set(x_5, 2, x_30);
x_4 = x_19;
goto _start;
}
else
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_32 = lean::cnstr_get(x_24, 0);
x_33 = lean::cnstr_get(x_24, 1);
lean::inc(x_33);
lean::inc(x_32);
lean::dec(x_24);
x_34 = lean_array_push(x_32, x_11);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_33);
x_36 = l_Lean_EnvExtensionState_inhabited;
x_37 = x_35;
x_38 = lean_array_fset(x_22, x_15, x_37);
lean::dec(x_15);
lean::cnstr_set(x_5, 2, x_38);
x_4 = x_19;
goto _start;
}
}
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; uint8 x_46; obj* x_47; obj* x_48; 
x_40 = lean::cnstr_get(x_5, 0);
x_41 = lean::cnstr_get(x_5, 1);
x_42 = lean::cnstr_get(x_5, 2);
x_43 = lean::cnstr_get(x_5, 3);
lean::inc(x_43);
lean::inc(x_42);
lean::inc(x_41);
lean::inc(x_40);
lean::dec(x_5);
x_44 = lean::cnstr_get(x_12, 0);
lean::inc(x_44);
x_45 = lean_array_get_size(x_42);
x_46 = lean_nat_dec_lt(x_44, x_45);
lean::dec(x_45);
x_47 = lean::mk_nat_obj(1u);
x_48 = lean_nat_add(x_4, x_47);
lean::dec(x_4);
if (x_46 == 0)
{
obj* x_49; 
lean::dec(x_44);
lean::dec(x_12);
lean::dec(x_11);
x_49 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_49, 0, x_40);
lean::cnstr_set(x_49, 1, x_41);
lean::cnstr_set(x_49, 2, x_42);
lean::cnstr_set(x_49, 3, x_43);
x_4 = x_48;
x_5 = x_49;
goto _start;
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_51 = lean_array_fget(x_42, x_44);
x_52 = lean_array_fset(x_42, x_44, x_10);
x_53 = lean::cnstr_get(x_12, 2);
lean::inc(x_53);
lean::dec(x_12);
x_54 = x_51;
x_55 = lean::cnstr_get(x_54, 0);
lean::inc(x_55);
x_56 = lean::cnstr_get(x_54, 1);
lean::inc(x_56);
if (lean::is_exclusive(x_54)) {
 lean::cnstr_release(x_54, 0);
 lean::cnstr_release(x_54, 1);
 x_57 = x_54;
} else {
 lean::dec_ref(x_54);
 x_57 = lean::box(0);
}
x_58 = lean_array_push(x_55, x_11);
if (lean::is_scalar(x_57)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_57;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_56);
x_60 = l_Lean_EnvExtensionState_inhabited;
x_61 = x_59;
x_62 = lean_array_fset(x_52, x_44, x_61);
lean::dec(x_44);
x_63 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_63, 0, x_40);
lean::cnstr_set(x_63, 1, x_41);
lean::cnstr_set(x_63, 2, x_62);
lean::cnstr_set(x_63, 3, x_43);
x_4 = x_48;
x_5 = x_63;
goto _start;
}
}
}
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_environment_10__setImportedEntries___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
return x_5;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean::mk_nat_obj(0u);
x_10 = l_Array_miterateAux___main___at___private_init_lean_environment_10__setImportedEntries___spec__1(x_2, x_8, x_2, x_9, x_5);
lean::dec(x_8);
x_11 = lean::mk_nat_obj(1u);
x_12 = lean_nat_add(x_4, x_11);
lean::dec(x_4);
x_4 = x_12;
x_5 = x_10;
goto _start;
}
}
}
obj* l___private_init_lean_environment_10__setImportedEntries(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l___private_init_lean_environment_8__persistentEnvExtensionsRef;
x_5 = lean_io_ref_get(x_4, x_3);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_5, 0);
x_8 = lean::mk_nat_obj(0u);
x_9 = l_Array_miterateAux___main___at___private_init_lean_environment_10__setImportedEntries___spec__2(x_2, x_7, x_2, x_8, x_1);
lean::dec(x_7);
lean::cnstr_set(x_5, 0, x_9);
return x_5;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_5, 0);
x_11 = lean::cnstr_get(x_5, 1);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_5);
x_12 = lean::mk_nat_obj(0u);
x_13 = l_Array_miterateAux___main___at___private_init_lean_environment_10__setImportedEntries___spec__2(x_2, x_10, x_2, x_12, x_1);
lean::dec(x_10);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_11);
return x_14;
}
}
else
{
uint8 x_15; 
lean::dec(x_1);
x_15 = !lean::is_exclusive(x_5);
if (x_15 == 0)
{
return x_5;
}
else
{
obj* x_16; obj* x_17; obj* x_18; 
x_16 = lean::cnstr_get(x_5, 0);
x_17 = lean::cnstr_get(x_5, 1);
lean::inc(x_17);
lean::inc(x_16);
lean::dec(x_5);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_environment_10__setImportedEntries___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at___private_init_lean_environment_10__setImportedEntries___spec__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_environment_10__setImportedEntries___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at___private_init_lean_environment_10__setImportedEntries___spec__2(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l___private_init_lean_environment_10__setImportedEntries___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_environment_10__setImportedEntries(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_environment_11__finalizePersistentExtensions___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
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
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; 
x_12 = lean_array_fget(x_2, x_3);
x_13 = lean::mk_nat_obj(1u);
x_14 = lean_nat_add(x_3, x_13);
lean::dec(x_3);
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
lean::inc(x_15);
x_16 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_15, x_4);
x_17 = lean::cnstr_get(x_12, 2);
lean::inc(x_17);
lean::dec(x_12);
x_18 = !lean::is_exclusive(x_16);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; 
x_19 = lean::cnstr_get(x_16, 0);
x_20 = lean::cnstr_get(x_16, 1);
lean::dec(x_20);
lean::inc(x_19);
x_21 = lean::apply_2(x_17, x_19, x_5);
if (lean::obj_tag(x_21) == 0)
{
uint8 x_22; 
x_22 = !lean::is_exclusive(x_21);
if (x_22 == 0)
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = lean::cnstr_get(x_21, 0);
lean::cnstr_set(x_16, 1, x_23);
x_24 = l_Lean_EnvExtension_setStateUnsafe___rarg(x_15, x_4, x_16);
lean::dec(x_15);
x_25 = lean::box(0);
lean::cnstr_set(x_21, 0, x_25);
x_3 = x_14;
x_4 = x_24;
x_5 = x_21;
goto _start;
}
else
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_27 = lean::cnstr_get(x_21, 0);
x_28 = lean::cnstr_get(x_21, 1);
lean::inc(x_28);
lean::inc(x_27);
lean::dec(x_21);
lean::cnstr_set(x_16, 1, x_27);
x_29 = l_Lean_EnvExtension_setStateUnsafe___rarg(x_15, x_4, x_16);
lean::dec(x_15);
x_30 = lean::box(0);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_28);
x_3 = x_14;
x_4 = x_29;
x_5 = x_31;
goto _start;
}
}
else
{
uint8 x_33; 
lean::free_heap_obj(x_16);
lean::dec(x_19);
lean::dec(x_15);
lean::dec(x_14);
lean::dec(x_4);
x_33 = !lean::is_exclusive(x_21);
if (x_33 == 0)
{
return x_21;
}
else
{
obj* x_34; obj* x_35; obj* x_36; 
x_34 = lean::cnstr_get(x_21, 0);
x_35 = lean::cnstr_get(x_21, 1);
lean::inc(x_35);
lean::inc(x_34);
lean::dec(x_21);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
obj* x_37; obj* x_38; 
x_37 = lean::cnstr_get(x_16, 0);
lean::inc(x_37);
lean::dec(x_16);
lean::inc(x_37);
x_38 = lean::apply_2(x_17, x_37, x_5);
if (lean::obj_tag(x_38) == 0)
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_40 = lean::cnstr_get(x_38, 1);
lean::inc(x_40);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 lean::cnstr_release(x_38, 1);
 x_41 = x_38;
} else {
 lean::dec_ref(x_38);
 x_41 = lean::box(0);
}
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_37);
lean::cnstr_set(x_42, 1, x_39);
x_43 = l_Lean_EnvExtension_setStateUnsafe___rarg(x_15, x_4, x_42);
lean::dec(x_15);
x_44 = lean::box(0);
if (lean::is_scalar(x_41)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_41;
}
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_40);
x_3 = x_14;
x_4 = x_43;
x_5 = x_45;
goto _start;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
lean::dec(x_37);
lean::dec(x_15);
lean::dec(x_14);
lean::dec(x_4);
x_47 = lean::cnstr_get(x_38, 0);
lean::inc(x_47);
x_48 = lean::cnstr_get(x_38, 1);
lean::inc(x_48);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 lean::cnstr_release(x_38, 1);
 x_49 = x_38;
} else {
 lean::dec_ref(x_38);
 x_49 = lean::box(0);
}
if (lean::is_scalar(x_49)) {
 x_50 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_50 = x_49;
}
lean::cnstr_set(x_50, 0, x_47);
lean::cnstr_set(x_50, 1, x_48);
return x_50;
}
}
}
}
}
obj* l___private_init_lean_environment_11__finalizePersistentExtensions(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l___private_init_lean_environment_8__persistentEnvExtensionsRef;
x_4 = lean_io_ref_get(x_3, x_2);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_4, 0);
x_7 = lean::box(0);
lean::cnstr_set(x_4, 0, x_7);
x_8 = lean::mk_nat_obj(0u);
x_9 = l_Array_miterateAux___main___at___private_init_lean_environment_11__finalizePersistentExtensions___spec__1(x_6, x_6, x_8, x_1, x_4);
lean::dec(x_6);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_4, 0);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_4);
x_12 = lean::box(0);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
x_14 = lean::mk_nat_obj(0u);
x_15 = l_Array_miterateAux___main___at___private_init_lean_environment_11__finalizePersistentExtensions___spec__1(x_10, x_10, x_14, x_1, x_13);
lean::dec(x_10);
return x_15;
}
}
else
{
uint8 x_16; 
lean::dec(x_1);
x_16 = !lean::is_exclusive(x_4);
if (x_16 == 0)
{
return x_4;
}
else
{
obj* x_17; obj* x_18; obj* x_19; 
x_17 = lean::cnstr_get(x_4, 0);
x_18 = lean::cnstr_get(x_4, 1);
lean::inc(x_18);
lean::inc(x_17);
lean::dec(x_4);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
}
}
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_environment_11__finalizePersistentExtensions___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at___private_init_lean_environment_11__finalizePersistentExtensions___spec__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
uint8 l_AssocList_contains___main___at_Lean_importModules___spec__2(obj* x_1, obj* x_2) {
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
obj* l_AssocList_mfoldl___main___at_Lean_importModules___spec__5(obj* x_1, obj* x_2) {
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
x_6 = lean_array_get_size(x_1);
x_7 = lean_name_hash_usize(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean::dec(x_6);
x_9 = lean::box_size_t(x_8);
x_10 = lean::unbox_size_t(x_9);
x_11 = lean_array_uget(x_1, x_10);
lean::cnstr_set(x_2, 2, x_11);
x_12 = lean::unbox_size_t(x_9);
lean::dec(x_9);
x_13 = lean_array_uset(x_1, x_12, x_2);
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
x_18 = lean_array_get_size(x_1);
x_19 = lean_name_hash_usize(x_15);
x_20 = lean_usize_modn(x_19, x_18);
lean::dec(x_18);
x_21 = lean::box_size_t(x_20);
x_22 = lean::unbox_size_t(x_21);
x_23 = lean_array_uget(x_1, x_22);
x_24 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_24, 0, x_15);
lean::cnstr_set(x_24, 1, x_16);
lean::cnstr_set(x_24, 2, x_23);
x_25 = lean::unbox_size_t(x_21);
lean::dec(x_21);
x_26 = lean_array_uset(x_1, x_25, x_24);
x_1 = x_26;
x_2 = x_17;
goto _start;
}
}
}
}
obj* l_HashMapImp_moveEntries___main___at_Lean_importModules___spec__4(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
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
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean::box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_AssocList_mfoldl___main___at_Lean_importModules___spec__5(x_3, x_6);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean_nat_add(x_1, x_10);
lean::dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
obj* l_HashMapImp_expand___at_Lean_importModules___spec__3(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean::mk_nat_obj(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean::dec(x_3);
x_6 = lean::box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean::mk_nat_obj(0u);
x_9 = l_HashMapImp_moveEntries___main___at_Lean_importModules___spec__4(x_8, x_2, x_7);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_AssocList_replace___main___at_Lean_importModules___spec__6(obj* x_1, obj* x_2, obj* x_3) {
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
x_9 = l_AssocList_replace___main___at_Lean_importModules___spec__6(x_1, x_2, x_7);
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
x_14 = l_AssocList_replace___main___at_Lean_importModules___spec__6(x_1, x_2, x_12);
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
obj* l_HashMapImp_insert___at_Lean_importModules___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; usize x_8; usize x_9; obj* x_10; usize x_11; obj* x_12; uint8 x_13; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_name_hash_usize(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean::box_size_t(x_9);
x_11 = lean::unbox_size_t(x_10);
x_12 = lean_array_uget(x_6, x_11);
x_13 = l_AssocList_contains___main___at_Lean_importModules___spec__2(x_2, x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; usize x_17; obj* x_18; uint8 x_19; 
x_14 = lean::mk_nat_obj(1u);
x_15 = lean_nat_add(x_5, x_14);
lean::dec(x_5);
x_16 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_16, 0, x_2);
lean::cnstr_set(x_16, 1, x_3);
lean::cnstr_set(x_16, 2, x_12);
x_17 = lean::unbox_size_t(x_10);
lean::dec(x_10);
x_18 = lean_array_uset(x_6, x_17, x_16);
x_19 = lean_nat_dec_le(x_15, x_7);
lean::dec(x_7);
if (x_19 == 0)
{
obj* x_20; 
lean::free_heap_obj(x_1);
x_20 = l_HashMapImp_expand___at_Lean_importModules___spec__3(x_15, x_18);
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
x_21 = l_AssocList_replace___main___at_Lean_importModules___spec__6(x_2, x_3, x_12);
x_22 = lean::unbox_size_t(x_10);
lean::dec(x_10);
x_23 = lean_array_uset(x_6, x_22, x_21);
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
x_26 = lean_array_get_size(x_25);
x_27 = lean_name_hash_usize(x_2);
x_28 = lean_usize_modn(x_27, x_26);
x_29 = lean::box_size_t(x_28);
x_30 = lean::unbox_size_t(x_29);
x_31 = lean_array_uget(x_25, x_30);
x_32 = l_AssocList_contains___main___at_Lean_importModules___spec__2(x_2, x_31);
if (x_32 == 0)
{
obj* x_33; obj* x_34; obj* x_35; usize x_36; obj* x_37; uint8 x_38; 
x_33 = lean::mk_nat_obj(1u);
x_34 = lean_nat_add(x_24, x_33);
lean::dec(x_24);
x_35 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_35, 0, x_2);
lean::cnstr_set(x_35, 1, x_3);
lean::cnstr_set(x_35, 2, x_31);
x_36 = lean::unbox_size_t(x_29);
lean::dec(x_29);
x_37 = lean_array_uset(x_25, x_36, x_35);
x_38 = lean_nat_dec_le(x_34, x_26);
lean::dec(x_26);
if (x_38 == 0)
{
obj* x_39; 
x_39 = l_HashMapImp_expand___at_Lean_importModules___spec__3(x_34, x_37);
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
x_41 = l_AssocList_replace___main___at_Lean_importModules___spec__6(x_2, x_3, x_31);
x_42 = lean::unbox_size_t(x_29);
lean::dec(x_29);
x_43 = lean_array_uset(x_25, x_42, x_41);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_24);
lean::cnstr_set(x_44, 1, x_43);
return x_44;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__7(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; uint8 x_9; 
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_6, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
lean::dec(x_6);
lean::dec(x_3);
return x_7;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean_array_fget(x_5, x_6);
x_11 = l_Lean_ConstantInfo_name(x_10);
lean::dec(x_10);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean_nat_add(x_6, x_12);
lean::dec(x_6);
lean::inc(x_3);
x_14 = l_HashMapImp_insert___at_Lean_importModules___spec__1(x_7, x_11, x_3);
x_6 = x_13;
x_7 = x_14;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__8(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
return x_5;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
x_10 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_11 = l_Array_miterateAux___main___at_Lean_importModules___spec__7(x_1, x_2, x_4, x_8, x_9, x_10, x_5);
lean::dec(x_9);
lean::dec(x_8);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean_nat_add(x_4, x_12);
lean::dec(x_4);
x_4 = x_13;
x_5 = x_11;
goto _start;
}
}
}
obj* _init_l_Array_miterateAux___main___at_Lean_importModules___spec__9___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("import failed, environment already contains '");
return x_1;
}
}
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__9(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_lt(x_4, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
uint8 x_9; 
lean::dec(x_4);
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
obj* x_13; obj* x_14; obj* x_15; obj* x_16; uint8 x_17; 
x_13 = lean_array_fget(x_3, x_4);
x_14 = lean::mk_nat_obj(1u);
x_15 = lean_nat_add(x_4, x_14);
lean::dec(x_4);
x_16 = l_Lean_ConstantInfo_name(x_13);
x_17 = l_Lean_SMap_contains___at_Lean_Environment_contains___spec__1(x_5, x_16);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_6);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; 
x_19 = lean::cnstr_get(x_6, 0);
lean::dec(x_19);
x_20 = l_Lean_SMap_insert___at_Lean_Environment_addAux___spec__1(x_5, x_16, x_13);
x_21 = lean::box(0);
lean::cnstr_set(x_6, 0, x_21);
x_4 = x_15;
x_5 = x_20;
goto _start;
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_23 = lean::cnstr_get(x_6, 1);
lean::inc(x_23);
lean::dec(x_6);
x_24 = l_Lean_SMap_insert___at_Lean_Environment_addAux___spec__1(x_5, x_16, x_13);
x_25 = lean::box(0);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_23);
x_4 = x_15;
x_5 = x_24;
x_6 = x_26;
goto _start;
}
}
else
{
uint8 x_28; 
lean::dec(x_15);
lean::dec(x_13);
lean::dec(x_5);
x_28 = !lean::is_exclusive(x_6);
if (x_28 == 0)
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_29 = lean::cnstr_get(x_6, 0);
lean::dec(x_29);
x_30 = l_Lean_Name_toString___closed__1;
x_31 = l_Lean_Name_toStringWithSep___main(x_30, x_16);
x_32 = l_Array_miterateAux___main___at_Lean_importModules___spec__9___closed__1;
x_33 = lean_string_append(x_32, x_31);
lean::dec(x_31);
x_34 = l_Char_HasRepr___closed__1;
x_35 = lean_string_append(x_33, x_34);
lean::cnstr_set_tag(x_6, 1);
lean::cnstr_set(x_6, 0, x_35);
return x_6;
}
else
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_36 = lean::cnstr_get(x_6, 1);
lean::inc(x_36);
lean::dec(x_6);
x_37 = l_Lean_Name_toString___closed__1;
x_38 = l_Lean_Name_toStringWithSep___main(x_37, x_16);
x_39 = l_Array_miterateAux___main___at_Lean_importModules___spec__9___closed__1;
x_40 = lean_string_append(x_39, x_38);
lean::dec(x_38);
x_41 = l_Char_HasRepr___closed__1;
x_42 = lean_string_append(x_40, x_41);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_36);
return x_43;
}
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__10(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_lt(x_4, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
uint8 x_9; 
lean::dec(x_4);
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
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_13 = lean_array_fget(x_3, x_4);
x_14 = lean::mk_nat_obj(1u);
x_15 = lean_nat_add(x_4, x_14);
lean::dec(x_4);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
x_17 = lean::mk_nat_obj(0u);
x_18 = l_Array_miterateAux___main___at_Lean_importModules___spec__9(x_2, x_13, x_16, x_17, x_5, x_6);
lean::dec(x_16);
lean::dec(x_13);
if (lean::obj_tag(x_18) == 0)
{
uint8 x_19; 
x_19 = !lean::is_exclusive(x_18);
if (x_19 == 0)
{
obj* x_20; obj* x_21; 
x_20 = lean::cnstr_get(x_18, 0);
x_21 = lean::box(0);
lean::cnstr_set(x_18, 0, x_21);
x_4 = x_15;
x_5 = x_20;
x_6 = x_18;
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
x_4 = x_15;
x_5 = x_23;
x_6 = x_26;
goto _start;
}
}
else
{
uint8 x_28; 
lean::dec(x_15);
x_28 = !lean::is_exclusive(x_18);
if (x_28 == 0)
{
return x_18;
}
else
{
obj* x_29; obj* x_30; obj* x_31; 
x_29 = lean::cnstr_get(x_18, 0);
x_30 = lean::cnstr_get(x_18, 1);
lean::inc(x_30);
lean::inc(x_29);
lean::dec(x_18);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
obj* l_Lean_SMap_switch___at_Lean_importModules___spec__11(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = lean::cnstr_get_uint8(x_1, sizeof(void*)*2);
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
lean::cnstr_set_uint8(x_1, sizeof(void*)*2, x_4);
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
lean::cnstr_set_uint8(x_8, sizeof(void*)*2, x_7);
return x_8;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__12(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
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
x_12 = lean_array_fget(x_2, x_3);
x_13 = lean::mk_nat_obj(1u);
x_14 = lean_nat_add(x_3, x_13);
lean::dec(x_3);
x_15 = lean::cnstr_get(x_12, 3);
lean::inc(x_15);
lean::dec(x_12);
x_16 = lean_perform_serialized_modifications(x_4, x_15, x_5);
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
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__13(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
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
x_12 = lean_array_fget(x_2, x_3);
x_13 = lean::mk_nat_obj(1u);
x_14 = lean_nat_add(x_3, x_13);
lean::dec(x_3);
x_15 = lean::cnstr_get(x_12, 3);
lean::inc(x_15);
lean::dec(x_12);
x_16 = lean_perform_serialized_modifications(x_4, x_15, x_5);
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
obj* _init_l_Lean_importModules___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Array_empty___closed__1;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* lean_import_modules(obj* x_1, uint32 x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_importModules___closed__1;
lean::inc(x_1);
x_5 = l_Lean_importModulesAux___main(x_1, x_4, x_3);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_7 = lean::cnstr_get(x_5, 0);
x_8 = lean::box(0);
lean::cnstr_set(x_5, 0, x_8);
x_9 = lean::cnstr_get(x_7, 1);
lean::inc(x_9);
lean::dec(x_7);
x_10 = l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__1;
x_11 = lean::mk_nat_obj(0u);
x_12 = l_HashMap_Inhabited___closed__1;
x_13 = l_Array_miterateAux___main___at_Lean_importModules___spec__8(x_9, x_10, x_9, x_11, x_12);
x_14 = l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2;
x_15 = l_Array_miterateAux___main___at_Lean_importModules___spec__10(x_9, x_10, x_9, x_11, x_14, x_5);
if (lean::obj_tag(x_15) == 0)
{
uint8 x_16; 
x_16 = !lean::is_exclusive(x_15);
if (x_16 == 0)
{
obj* x_17; obj* x_18; obj* x_19; 
x_17 = lean::cnstr_get(x_15, 0);
lean::cnstr_set(x_15, 0, x_8);
x_18 = l_Lean_SMap_switch___at_Lean_importModules___spec__11(x_17);
x_19 = l___private_init_lean_environment_6__mkInitialExtensionStates(x_15);
if (lean::obj_tag(x_19) == 0)
{
uint8 x_20; 
x_20 = !lean::is_exclusive(x_19);
if (x_20 == 0)
{
obj* x_21; uint8 x_22; obj* x_23; obj* x_24; obj* x_25; 
x_21 = lean::cnstr_get(x_19, 0);
lean::cnstr_set(x_19, 0, x_8);
x_22 = l_List_isEmpty___rarg(x_1);
x_23 = l_List_redLength___main___rarg(x_1);
x_24 = lean_mk_empty_array_with_capacity(x_23);
lean::dec(x_23);
x_25 = l_List_toArrayAux___main___rarg(x_1, x_24);
if (x_22 == 0)
{
uint8 x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_26 = 1;
x_27 = lean::box(0);
x_28 = lean::alloc_cnstr(0, 2, 5);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_25);
lean::cnstr_set_uint32(x_28, sizeof(void*)*2, x_2);
lean::cnstr_set_uint8(x_28, sizeof(void*)*2 + 4, x_26);
x_29 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_29, 0, x_13);
lean::cnstr_set(x_29, 1, x_18);
lean::cnstr_set(x_29, 2, x_21);
lean::cnstr_set(x_29, 3, x_28);
x_30 = l___private_init_lean_environment_10__setImportedEntries(x_29, x_9, x_19);
if (lean::obj_tag(x_30) == 0)
{
uint8 x_31; 
x_31 = !lean::is_exclusive(x_30);
if (x_31 == 0)
{
obj* x_32; obj* x_33; 
x_32 = lean::cnstr_get(x_30, 0);
lean::cnstr_set(x_30, 0, x_8);
x_33 = l___private_init_lean_environment_11__finalizePersistentExtensions(x_32, x_30);
if (lean::obj_tag(x_33) == 0)
{
uint8 x_34; 
x_34 = !lean::is_exclusive(x_33);
if (x_34 == 0)
{
obj* x_35; obj* x_36; 
x_35 = lean::cnstr_get(x_33, 0);
lean::cnstr_set(x_33, 0, x_8);
x_36 = l_Array_miterateAux___main___at_Lean_importModules___spec__12(x_9, x_9, x_11, x_35, x_33);
lean::dec(x_9);
if (lean::obj_tag(x_36) == 0)
{
uint8 x_37; 
x_37 = !lean::is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
obj* x_38; obj* x_39; obj* x_40; 
x_38 = lean::cnstr_get(x_36, 0);
x_39 = lean::cnstr_get(x_36, 1);
lean::inc(x_39);
lean::inc(x_38);
lean::dec(x_36);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_38);
lean::cnstr_set(x_40, 1, x_39);
return x_40;
}
}
else
{
uint8 x_41; 
x_41 = !lean::is_exclusive(x_36);
if (x_41 == 0)
{
return x_36;
}
else
{
obj* x_42; obj* x_43; obj* x_44; 
x_42 = lean::cnstr_get(x_36, 0);
x_43 = lean::cnstr_get(x_36, 1);
lean::inc(x_43);
lean::inc(x_42);
lean::dec(x_36);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_42);
lean::cnstr_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_45 = lean::cnstr_get(x_33, 0);
x_46 = lean::cnstr_get(x_33, 1);
lean::inc(x_46);
lean::inc(x_45);
lean::dec(x_33);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_8);
lean::cnstr_set(x_47, 1, x_46);
x_48 = l_Array_miterateAux___main___at_Lean_importModules___spec__12(x_9, x_9, x_11, x_45, x_47);
lean::dec(x_9);
if (lean::obj_tag(x_48) == 0)
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
x_50 = lean::cnstr_get(x_48, 1);
lean::inc(x_50);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_release(x_48, 0);
 lean::cnstr_release(x_48, 1);
 x_51 = x_48;
} else {
 lean::dec_ref(x_48);
 x_51 = lean::box(0);
}
if (lean::is_scalar(x_51)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_51;
}
lean::cnstr_set(x_52, 0, x_49);
lean::cnstr_set(x_52, 1, x_50);
return x_52;
}
else
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_53 = lean::cnstr_get(x_48, 0);
lean::inc(x_53);
x_54 = lean::cnstr_get(x_48, 1);
lean::inc(x_54);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_release(x_48, 0);
 lean::cnstr_release(x_48, 1);
 x_55 = x_48;
} else {
 lean::dec_ref(x_48);
 x_55 = lean::box(0);
}
if (lean::is_scalar(x_55)) {
 x_56 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_56 = x_55;
}
lean::cnstr_set(x_56, 0, x_53);
lean::cnstr_set(x_56, 1, x_54);
return x_56;
}
}
}
else
{
uint8 x_57; 
lean::dec(x_9);
x_57 = !lean::is_exclusive(x_33);
if (x_57 == 0)
{
return x_33;
}
else
{
obj* x_58; obj* x_59; obj* x_60; 
x_58 = lean::cnstr_get(x_33, 0);
x_59 = lean::cnstr_get(x_33, 1);
lean::inc(x_59);
lean::inc(x_58);
lean::dec(x_33);
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_58);
lean::cnstr_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_61 = lean::cnstr_get(x_30, 0);
x_62 = lean::cnstr_get(x_30, 1);
lean::inc(x_62);
lean::inc(x_61);
lean::dec(x_30);
x_63 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_63, 0, x_8);
lean::cnstr_set(x_63, 1, x_62);
x_64 = l___private_init_lean_environment_11__finalizePersistentExtensions(x_61, x_63);
if (lean::obj_tag(x_64) == 0)
{
obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_65 = lean::cnstr_get(x_64, 0);
lean::inc(x_65);
x_66 = lean::cnstr_get(x_64, 1);
lean::inc(x_66);
if (lean::is_exclusive(x_64)) {
 lean::cnstr_release(x_64, 0);
 lean::cnstr_release(x_64, 1);
 x_67 = x_64;
} else {
 lean::dec_ref(x_64);
 x_67 = lean::box(0);
}
if (lean::is_scalar(x_67)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_67;
}
lean::cnstr_set(x_68, 0, x_8);
lean::cnstr_set(x_68, 1, x_66);
x_69 = l_Array_miterateAux___main___at_Lean_importModules___spec__12(x_9, x_9, x_11, x_65, x_68);
lean::dec(x_9);
if (lean::obj_tag(x_69) == 0)
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
x_71 = lean::cnstr_get(x_69, 1);
lean::inc(x_71);
if (lean::is_exclusive(x_69)) {
 lean::cnstr_release(x_69, 0);
 lean::cnstr_release(x_69, 1);
 x_72 = x_69;
} else {
 lean::dec_ref(x_69);
 x_72 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_70);
lean::cnstr_set(x_73, 1, x_71);
return x_73;
}
else
{
obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
x_74 = lean::cnstr_get(x_69, 0);
lean::inc(x_74);
x_75 = lean::cnstr_get(x_69, 1);
lean::inc(x_75);
if (lean::is_exclusive(x_69)) {
 lean::cnstr_release(x_69, 0);
 lean::cnstr_release(x_69, 1);
 x_76 = x_69;
} else {
 lean::dec_ref(x_69);
 x_76 = lean::box(0);
}
if (lean::is_scalar(x_76)) {
 x_77 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_77 = x_76;
}
lean::cnstr_set(x_77, 0, x_74);
lean::cnstr_set(x_77, 1, x_75);
return x_77;
}
}
else
{
obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
lean::dec(x_9);
x_78 = lean::cnstr_get(x_64, 0);
lean::inc(x_78);
x_79 = lean::cnstr_get(x_64, 1);
lean::inc(x_79);
if (lean::is_exclusive(x_64)) {
 lean::cnstr_release(x_64, 0);
 lean::cnstr_release(x_64, 1);
 x_80 = x_64;
} else {
 lean::dec_ref(x_64);
 x_80 = lean::box(0);
}
if (lean::is_scalar(x_80)) {
 x_81 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_81 = x_80;
}
lean::cnstr_set(x_81, 0, x_78);
lean::cnstr_set(x_81, 1, x_79);
return x_81;
}
}
}
else
{
uint8 x_82; 
lean::dec(x_9);
x_82 = !lean::is_exclusive(x_30);
if (x_82 == 0)
{
return x_30;
}
else
{
obj* x_83; obj* x_84; obj* x_85; 
x_83 = lean::cnstr_get(x_30, 0);
x_84 = lean::cnstr_get(x_30, 1);
lean::inc(x_84);
lean::inc(x_83);
lean::dec(x_30);
x_85 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_85, 0, x_83);
lean::cnstr_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8 x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; 
x_86 = 0;
x_87 = lean::box(0);
x_88 = lean::alloc_cnstr(0, 2, 5);
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_25);
lean::cnstr_set_uint32(x_88, sizeof(void*)*2, x_2);
lean::cnstr_set_uint8(x_88, sizeof(void*)*2 + 4, x_86);
x_89 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_89, 0, x_13);
lean::cnstr_set(x_89, 1, x_18);
lean::cnstr_set(x_89, 2, x_21);
lean::cnstr_set(x_89, 3, x_88);
x_90 = l___private_init_lean_environment_10__setImportedEntries(x_89, x_9, x_19);
if (lean::obj_tag(x_90) == 0)
{
uint8 x_91; 
x_91 = !lean::is_exclusive(x_90);
if (x_91 == 0)
{
obj* x_92; obj* x_93; 
x_92 = lean::cnstr_get(x_90, 0);
lean::cnstr_set(x_90, 0, x_8);
x_93 = l___private_init_lean_environment_11__finalizePersistentExtensions(x_92, x_90);
if (lean::obj_tag(x_93) == 0)
{
uint8 x_94; 
x_94 = !lean::is_exclusive(x_93);
if (x_94 == 0)
{
obj* x_95; obj* x_96; 
x_95 = lean::cnstr_get(x_93, 0);
lean::cnstr_set(x_93, 0, x_8);
x_96 = l_Array_miterateAux___main___at_Lean_importModules___spec__13(x_9, x_9, x_11, x_95, x_93);
lean::dec(x_9);
if (lean::obj_tag(x_96) == 0)
{
uint8 x_97; 
x_97 = !lean::is_exclusive(x_96);
if (x_97 == 0)
{
return x_96;
}
else
{
obj* x_98; obj* x_99; obj* x_100; 
x_98 = lean::cnstr_get(x_96, 0);
x_99 = lean::cnstr_get(x_96, 1);
lean::inc(x_99);
lean::inc(x_98);
lean::dec(x_96);
x_100 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_100, 0, x_98);
lean::cnstr_set(x_100, 1, x_99);
return x_100;
}
}
else
{
uint8 x_101; 
x_101 = !lean::is_exclusive(x_96);
if (x_101 == 0)
{
return x_96;
}
else
{
obj* x_102; obj* x_103; obj* x_104; 
x_102 = lean::cnstr_get(x_96, 0);
x_103 = lean::cnstr_get(x_96, 1);
lean::inc(x_103);
lean::inc(x_102);
lean::dec(x_96);
x_104 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_104, 0, x_102);
lean::cnstr_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
x_105 = lean::cnstr_get(x_93, 0);
x_106 = lean::cnstr_get(x_93, 1);
lean::inc(x_106);
lean::inc(x_105);
lean::dec(x_93);
x_107 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_107, 0, x_8);
lean::cnstr_set(x_107, 1, x_106);
x_108 = l_Array_miterateAux___main___at_Lean_importModules___spec__13(x_9, x_9, x_11, x_105, x_107);
lean::dec(x_9);
if (lean::obj_tag(x_108) == 0)
{
obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
x_109 = lean::cnstr_get(x_108, 0);
lean::inc(x_109);
x_110 = lean::cnstr_get(x_108, 1);
lean::inc(x_110);
if (lean::is_exclusive(x_108)) {
 lean::cnstr_release(x_108, 0);
 lean::cnstr_release(x_108, 1);
 x_111 = x_108;
} else {
 lean::dec_ref(x_108);
 x_111 = lean::box(0);
}
if (lean::is_scalar(x_111)) {
 x_112 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_112 = x_111;
}
lean::cnstr_set(x_112, 0, x_109);
lean::cnstr_set(x_112, 1, x_110);
return x_112;
}
else
{
obj* x_113; obj* x_114; obj* x_115; obj* x_116; 
x_113 = lean::cnstr_get(x_108, 0);
lean::inc(x_113);
x_114 = lean::cnstr_get(x_108, 1);
lean::inc(x_114);
if (lean::is_exclusive(x_108)) {
 lean::cnstr_release(x_108, 0);
 lean::cnstr_release(x_108, 1);
 x_115 = x_108;
} else {
 lean::dec_ref(x_108);
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
lean::dec(x_9);
x_117 = !lean::is_exclusive(x_93);
if (x_117 == 0)
{
return x_93;
}
else
{
obj* x_118; obj* x_119; obj* x_120; 
x_118 = lean::cnstr_get(x_93, 0);
x_119 = lean::cnstr_get(x_93, 1);
lean::inc(x_119);
lean::inc(x_118);
lean::dec(x_93);
x_120 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_120, 0, x_118);
lean::cnstr_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
obj* x_121; obj* x_122; obj* x_123; obj* x_124; 
x_121 = lean::cnstr_get(x_90, 0);
x_122 = lean::cnstr_get(x_90, 1);
lean::inc(x_122);
lean::inc(x_121);
lean::dec(x_90);
x_123 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_123, 0, x_8);
lean::cnstr_set(x_123, 1, x_122);
x_124 = l___private_init_lean_environment_11__finalizePersistentExtensions(x_121, x_123);
if (lean::obj_tag(x_124) == 0)
{
obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; 
x_125 = lean::cnstr_get(x_124, 0);
lean::inc(x_125);
x_126 = lean::cnstr_get(x_124, 1);
lean::inc(x_126);
if (lean::is_exclusive(x_124)) {
 lean::cnstr_release(x_124, 0);
 lean::cnstr_release(x_124, 1);
 x_127 = x_124;
} else {
 lean::dec_ref(x_124);
 x_127 = lean::box(0);
}
if (lean::is_scalar(x_127)) {
 x_128 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_128 = x_127;
}
lean::cnstr_set(x_128, 0, x_8);
lean::cnstr_set(x_128, 1, x_126);
x_129 = l_Array_miterateAux___main___at_Lean_importModules___spec__13(x_9, x_9, x_11, x_125, x_128);
lean::dec(x_9);
if (lean::obj_tag(x_129) == 0)
{
obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
x_130 = lean::cnstr_get(x_129, 0);
lean::inc(x_130);
x_131 = lean::cnstr_get(x_129, 1);
lean::inc(x_131);
if (lean::is_exclusive(x_129)) {
 lean::cnstr_release(x_129, 0);
 lean::cnstr_release(x_129, 1);
 x_132 = x_129;
} else {
 lean::dec_ref(x_129);
 x_132 = lean::box(0);
}
if (lean::is_scalar(x_132)) {
 x_133 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_133 = x_132;
}
lean::cnstr_set(x_133, 0, x_130);
lean::cnstr_set(x_133, 1, x_131);
return x_133;
}
else
{
obj* x_134; obj* x_135; obj* x_136; obj* x_137; 
x_134 = lean::cnstr_get(x_129, 0);
lean::inc(x_134);
x_135 = lean::cnstr_get(x_129, 1);
lean::inc(x_135);
if (lean::is_exclusive(x_129)) {
 lean::cnstr_release(x_129, 0);
 lean::cnstr_release(x_129, 1);
 x_136 = x_129;
} else {
 lean::dec_ref(x_129);
 x_136 = lean::box(0);
}
if (lean::is_scalar(x_136)) {
 x_137 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_137 = x_136;
}
lean::cnstr_set(x_137, 0, x_134);
lean::cnstr_set(x_137, 1, x_135);
return x_137;
}
}
else
{
obj* x_138; obj* x_139; obj* x_140; obj* x_141; 
lean::dec(x_9);
x_138 = lean::cnstr_get(x_124, 0);
lean::inc(x_138);
x_139 = lean::cnstr_get(x_124, 1);
lean::inc(x_139);
if (lean::is_exclusive(x_124)) {
 lean::cnstr_release(x_124, 0);
 lean::cnstr_release(x_124, 1);
 x_140 = x_124;
} else {
 lean::dec_ref(x_124);
 x_140 = lean::box(0);
}
if (lean::is_scalar(x_140)) {
 x_141 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_141 = x_140;
}
lean::cnstr_set(x_141, 0, x_138);
lean::cnstr_set(x_141, 1, x_139);
return x_141;
}
}
}
else
{
uint8 x_142; 
lean::dec(x_9);
x_142 = !lean::is_exclusive(x_90);
if (x_142 == 0)
{
return x_90;
}
else
{
obj* x_143; obj* x_144; obj* x_145; 
x_143 = lean::cnstr_get(x_90, 0);
x_144 = lean::cnstr_get(x_90, 1);
lean::inc(x_144);
lean::inc(x_143);
lean::dec(x_90);
x_145 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_145, 0, x_143);
lean::cnstr_set(x_145, 1, x_144);
return x_145;
}
}
}
}
else
{
obj* x_146; obj* x_147; obj* x_148; uint8 x_149; obj* x_150; obj* x_151; obj* x_152; 
x_146 = lean::cnstr_get(x_19, 0);
x_147 = lean::cnstr_get(x_19, 1);
lean::inc(x_147);
lean::inc(x_146);
lean::dec(x_19);
x_148 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_148, 0, x_8);
lean::cnstr_set(x_148, 1, x_147);
x_149 = l_List_isEmpty___rarg(x_1);
x_150 = l_List_redLength___main___rarg(x_1);
x_151 = lean_mk_empty_array_with_capacity(x_150);
lean::dec(x_150);
x_152 = l_List_toArrayAux___main___rarg(x_1, x_151);
if (x_149 == 0)
{
uint8 x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; 
x_153 = 1;
x_154 = lean::box(0);
x_155 = lean::alloc_cnstr(0, 2, 5);
lean::cnstr_set(x_155, 0, x_154);
lean::cnstr_set(x_155, 1, x_152);
lean::cnstr_set_uint32(x_155, sizeof(void*)*2, x_2);
lean::cnstr_set_uint8(x_155, sizeof(void*)*2 + 4, x_153);
x_156 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_156, 0, x_13);
lean::cnstr_set(x_156, 1, x_18);
lean::cnstr_set(x_156, 2, x_146);
lean::cnstr_set(x_156, 3, x_155);
x_157 = l___private_init_lean_environment_10__setImportedEntries(x_156, x_9, x_148);
if (lean::obj_tag(x_157) == 0)
{
obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; 
x_158 = lean::cnstr_get(x_157, 0);
lean::inc(x_158);
x_159 = lean::cnstr_get(x_157, 1);
lean::inc(x_159);
if (lean::is_exclusive(x_157)) {
 lean::cnstr_release(x_157, 0);
 lean::cnstr_release(x_157, 1);
 x_160 = x_157;
} else {
 lean::dec_ref(x_157);
 x_160 = lean::box(0);
}
if (lean::is_scalar(x_160)) {
 x_161 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_161 = x_160;
}
lean::cnstr_set(x_161, 0, x_8);
lean::cnstr_set(x_161, 1, x_159);
x_162 = l___private_init_lean_environment_11__finalizePersistentExtensions(x_158, x_161);
if (lean::obj_tag(x_162) == 0)
{
obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; 
x_163 = lean::cnstr_get(x_162, 0);
lean::inc(x_163);
x_164 = lean::cnstr_get(x_162, 1);
lean::inc(x_164);
if (lean::is_exclusive(x_162)) {
 lean::cnstr_release(x_162, 0);
 lean::cnstr_release(x_162, 1);
 x_165 = x_162;
} else {
 lean::dec_ref(x_162);
 x_165 = lean::box(0);
}
if (lean::is_scalar(x_165)) {
 x_166 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_166 = x_165;
}
lean::cnstr_set(x_166, 0, x_8);
lean::cnstr_set(x_166, 1, x_164);
x_167 = l_Array_miterateAux___main___at_Lean_importModules___spec__12(x_9, x_9, x_11, x_163, x_166);
lean::dec(x_9);
if (lean::obj_tag(x_167) == 0)
{
obj* x_168; obj* x_169; obj* x_170; obj* x_171; 
x_168 = lean::cnstr_get(x_167, 0);
lean::inc(x_168);
x_169 = lean::cnstr_get(x_167, 1);
lean::inc(x_169);
if (lean::is_exclusive(x_167)) {
 lean::cnstr_release(x_167, 0);
 lean::cnstr_release(x_167, 1);
 x_170 = x_167;
} else {
 lean::dec_ref(x_167);
 x_170 = lean::box(0);
}
if (lean::is_scalar(x_170)) {
 x_171 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_171 = x_170;
}
lean::cnstr_set(x_171, 0, x_168);
lean::cnstr_set(x_171, 1, x_169);
return x_171;
}
else
{
obj* x_172; obj* x_173; obj* x_174; obj* x_175; 
x_172 = lean::cnstr_get(x_167, 0);
lean::inc(x_172);
x_173 = lean::cnstr_get(x_167, 1);
lean::inc(x_173);
if (lean::is_exclusive(x_167)) {
 lean::cnstr_release(x_167, 0);
 lean::cnstr_release(x_167, 1);
 x_174 = x_167;
} else {
 lean::dec_ref(x_167);
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
lean::dec(x_9);
x_176 = lean::cnstr_get(x_162, 0);
lean::inc(x_176);
x_177 = lean::cnstr_get(x_162, 1);
lean::inc(x_177);
if (lean::is_exclusive(x_162)) {
 lean::cnstr_release(x_162, 0);
 lean::cnstr_release(x_162, 1);
 x_178 = x_162;
} else {
 lean::dec_ref(x_162);
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
lean::dec(x_9);
x_180 = lean::cnstr_get(x_157, 0);
lean::inc(x_180);
x_181 = lean::cnstr_get(x_157, 1);
lean::inc(x_181);
if (lean::is_exclusive(x_157)) {
 lean::cnstr_release(x_157, 0);
 lean::cnstr_release(x_157, 1);
 x_182 = x_157;
} else {
 lean::dec_ref(x_157);
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
uint8 x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; 
x_184 = 0;
x_185 = lean::box(0);
x_186 = lean::alloc_cnstr(0, 2, 5);
lean::cnstr_set(x_186, 0, x_185);
lean::cnstr_set(x_186, 1, x_152);
lean::cnstr_set_uint32(x_186, sizeof(void*)*2, x_2);
lean::cnstr_set_uint8(x_186, sizeof(void*)*2 + 4, x_184);
x_187 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_187, 0, x_13);
lean::cnstr_set(x_187, 1, x_18);
lean::cnstr_set(x_187, 2, x_146);
lean::cnstr_set(x_187, 3, x_186);
x_188 = l___private_init_lean_environment_10__setImportedEntries(x_187, x_9, x_148);
if (lean::obj_tag(x_188) == 0)
{
obj* x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; 
x_189 = lean::cnstr_get(x_188, 0);
lean::inc(x_189);
x_190 = lean::cnstr_get(x_188, 1);
lean::inc(x_190);
if (lean::is_exclusive(x_188)) {
 lean::cnstr_release(x_188, 0);
 lean::cnstr_release(x_188, 1);
 x_191 = x_188;
} else {
 lean::dec_ref(x_188);
 x_191 = lean::box(0);
}
if (lean::is_scalar(x_191)) {
 x_192 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_192 = x_191;
}
lean::cnstr_set(x_192, 0, x_8);
lean::cnstr_set(x_192, 1, x_190);
x_193 = l___private_init_lean_environment_11__finalizePersistentExtensions(x_189, x_192);
if (lean::obj_tag(x_193) == 0)
{
obj* x_194; obj* x_195; obj* x_196; obj* x_197; obj* x_198; 
x_194 = lean::cnstr_get(x_193, 0);
lean::inc(x_194);
x_195 = lean::cnstr_get(x_193, 1);
lean::inc(x_195);
if (lean::is_exclusive(x_193)) {
 lean::cnstr_release(x_193, 0);
 lean::cnstr_release(x_193, 1);
 x_196 = x_193;
} else {
 lean::dec_ref(x_193);
 x_196 = lean::box(0);
}
if (lean::is_scalar(x_196)) {
 x_197 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_197 = x_196;
}
lean::cnstr_set(x_197, 0, x_8);
lean::cnstr_set(x_197, 1, x_195);
x_198 = l_Array_miterateAux___main___at_Lean_importModules___spec__13(x_9, x_9, x_11, x_194, x_197);
lean::dec(x_9);
if (lean::obj_tag(x_198) == 0)
{
obj* x_199; obj* x_200; obj* x_201; obj* x_202; 
x_199 = lean::cnstr_get(x_198, 0);
lean::inc(x_199);
x_200 = lean::cnstr_get(x_198, 1);
lean::inc(x_200);
if (lean::is_exclusive(x_198)) {
 lean::cnstr_release(x_198, 0);
 lean::cnstr_release(x_198, 1);
 x_201 = x_198;
} else {
 lean::dec_ref(x_198);
 x_201 = lean::box(0);
}
if (lean::is_scalar(x_201)) {
 x_202 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_202 = x_201;
}
lean::cnstr_set(x_202, 0, x_199);
lean::cnstr_set(x_202, 1, x_200);
return x_202;
}
else
{
obj* x_203; obj* x_204; obj* x_205; obj* x_206; 
x_203 = lean::cnstr_get(x_198, 0);
lean::inc(x_203);
x_204 = lean::cnstr_get(x_198, 1);
lean::inc(x_204);
if (lean::is_exclusive(x_198)) {
 lean::cnstr_release(x_198, 0);
 lean::cnstr_release(x_198, 1);
 x_205 = x_198;
} else {
 lean::dec_ref(x_198);
 x_205 = lean::box(0);
}
if (lean::is_scalar(x_205)) {
 x_206 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_206 = x_205;
}
lean::cnstr_set(x_206, 0, x_203);
lean::cnstr_set(x_206, 1, x_204);
return x_206;
}
}
else
{
obj* x_207; obj* x_208; obj* x_209; obj* x_210; 
lean::dec(x_9);
x_207 = lean::cnstr_get(x_193, 0);
lean::inc(x_207);
x_208 = lean::cnstr_get(x_193, 1);
lean::inc(x_208);
if (lean::is_exclusive(x_193)) {
 lean::cnstr_release(x_193, 0);
 lean::cnstr_release(x_193, 1);
 x_209 = x_193;
} else {
 lean::dec_ref(x_193);
 x_209 = lean::box(0);
}
if (lean::is_scalar(x_209)) {
 x_210 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_210 = x_209;
}
lean::cnstr_set(x_210, 0, x_207);
lean::cnstr_set(x_210, 1, x_208);
return x_210;
}
}
else
{
obj* x_211; obj* x_212; obj* x_213; obj* x_214; 
lean::dec(x_9);
x_211 = lean::cnstr_get(x_188, 0);
lean::inc(x_211);
x_212 = lean::cnstr_get(x_188, 1);
lean::inc(x_212);
if (lean::is_exclusive(x_188)) {
 lean::cnstr_release(x_188, 0);
 lean::cnstr_release(x_188, 1);
 x_213 = x_188;
} else {
 lean::dec_ref(x_188);
 x_213 = lean::box(0);
}
if (lean::is_scalar(x_213)) {
 x_214 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_214 = x_213;
}
lean::cnstr_set(x_214, 0, x_211);
lean::cnstr_set(x_214, 1, x_212);
return x_214;
}
}
}
}
else
{
uint8 x_215; 
lean::dec(x_18);
lean::dec(x_13);
lean::dec(x_9);
lean::dec(x_1);
x_215 = !lean::is_exclusive(x_19);
if (x_215 == 0)
{
return x_19;
}
else
{
obj* x_216; obj* x_217; obj* x_218; 
x_216 = lean::cnstr_get(x_19, 0);
x_217 = lean::cnstr_get(x_19, 1);
lean::inc(x_217);
lean::inc(x_216);
lean::dec(x_19);
x_218 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_218, 0, x_216);
lean::cnstr_set(x_218, 1, x_217);
return x_218;
}
}
}
else
{
obj* x_219; obj* x_220; obj* x_221; obj* x_222; obj* x_223; 
x_219 = lean::cnstr_get(x_15, 0);
x_220 = lean::cnstr_get(x_15, 1);
lean::inc(x_220);
lean::inc(x_219);
lean::dec(x_15);
x_221 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_221, 0, x_8);
lean::cnstr_set(x_221, 1, x_220);
x_222 = l_Lean_SMap_switch___at_Lean_importModules___spec__11(x_219);
x_223 = l___private_init_lean_environment_6__mkInitialExtensionStates(x_221);
if (lean::obj_tag(x_223) == 0)
{
obj* x_224; obj* x_225; obj* x_226; obj* x_227; uint8 x_228; obj* x_229; obj* x_230; obj* x_231; 
x_224 = lean::cnstr_get(x_223, 0);
lean::inc(x_224);
x_225 = lean::cnstr_get(x_223, 1);
lean::inc(x_225);
if (lean::is_exclusive(x_223)) {
 lean::cnstr_release(x_223, 0);
 lean::cnstr_release(x_223, 1);
 x_226 = x_223;
} else {
 lean::dec_ref(x_223);
 x_226 = lean::box(0);
}
if (lean::is_scalar(x_226)) {
 x_227 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_227 = x_226;
}
lean::cnstr_set(x_227, 0, x_8);
lean::cnstr_set(x_227, 1, x_225);
x_228 = l_List_isEmpty___rarg(x_1);
x_229 = l_List_redLength___main___rarg(x_1);
x_230 = lean_mk_empty_array_with_capacity(x_229);
lean::dec(x_229);
x_231 = l_List_toArrayAux___main___rarg(x_1, x_230);
if (x_228 == 0)
{
uint8 x_232; obj* x_233; obj* x_234; obj* x_235; obj* x_236; 
x_232 = 1;
x_233 = lean::box(0);
x_234 = lean::alloc_cnstr(0, 2, 5);
lean::cnstr_set(x_234, 0, x_233);
lean::cnstr_set(x_234, 1, x_231);
lean::cnstr_set_uint32(x_234, sizeof(void*)*2, x_2);
lean::cnstr_set_uint8(x_234, sizeof(void*)*2 + 4, x_232);
x_235 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_235, 0, x_13);
lean::cnstr_set(x_235, 1, x_222);
lean::cnstr_set(x_235, 2, x_224);
lean::cnstr_set(x_235, 3, x_234);
x_236 = l___private_init_lean_environment_10__setImportedEntries(x_235, x_9, x_227);
if (lean::obj_tag(x_236) == 0)
{
obj* x_237; obj* x_238; obj* x_239; obj* x_240; obj* x_241; 
x_237 = lean::cnstr_get(x_236, 0);
lean::inc(x_237);
x_238 = lean::cnstr_get(x_236, 1);
lean::inc(x_238);
if (lean::is_exclusive(x_236)) {
 lean::cnstr_release(x_236, 0);
 lean::cnstr_release(x_236, 1);
 x_239 = x_236;
} else {
 lean::dec_ref(x_236);
 x_239 = lean::box(0);
}
if (lean::is_scalar(x_239)) {
 x_240 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_240 = x_239;
}
lean::cnstr_set(x_240, 0, x_8);
lean::cnstr_set(x_240, 1, x_238);
x_241 = l___private_init_lean_environment_11__finalizePersistentExtensions(x_237, x_240);
if (lean::obj_tag(x_241) == 0)
{
obj* x_242; obj* x_243; obj* x_244; obj* x_245; obj* x_246; 
x_242 = lean::cnstr_get(x_241, 0);
lean::inc(x_242);
x_243 = lean::cnstr_get(x_241, 1);
lean::inc(x_243);
if (lean::is_exclusive(x_241)) {
 lean::cnstr_release(x_241, 0);
 lean::cnstr_release(x_241, 1);
 x_244 = x_241;
} else {
 lean::dec_ref(x_241);
 x_244 = lean::box(0);
}
if (lean::is_scalar(x_244)) {
 x_245 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_245 = x_244;
}
lean::cnstr_set(x_245, 0, x_8);
lean::cnstr_set(x_245, 1, x_243);
x_246 = l_Array_miterateAux___main___at_Lean_importModules___spec__12(x_9, x_9, x_11, x_242, x_245);
lean::dec(x_9);
if (lean::obj_tag(x_246) == 0)
{
obj* x_247; obj* x_248; obj* x_249; obj* x_250; 
x_247 = lean::cnstr_get(x_246, 0);
lean::inc(x_247);
x_248 = lean::cnstr_get(x_246, 1);
lean::inc(x_248);
if (lean::is_exclusive(x_246)) {
 lean::cnstr_release(x_246, 0);
 lean::cnstr_release(x_246, 1);
 x_249 = x_246;
} else {
 lean::dec_ref(x_246);
 x_249 = lean::box(0);
}
if (lean::is_scalar(x_249)) {
 x_250 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_250 = x_249;
}
lean::cnstr_set(x_250, 0, x_247);
lean::cnstr_set(x_250, 1, x_248);
return x_250;
}
else
{
obj* x_251; obj* x_252; obj* x_253; obj* x_254; 
x_251 = lean::cnstr_get(x_246, 0);
lean::inc(x_251);
x_252 = lean::cnstr_get(x_246, 1);
lean::inc(x_252);
if (lean::is_exclusive(x_246)) {
 lean::cnstr_release(x_246, 0);
 lean::cnstr_release(x_246, 1);
 x_253 = x_246;
} else {
 lean::dec_ref(x_246);
 x_253 = lean::box(0);
}
if (lean::is_scalar(x_253)) {
 x_254 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_254 = x_253;
}
lean::cnstr_set(x_254, 0, x_251);
lean::cnstr_set(x_254, 1, x_252);
return x_254;
}
}
else
{
obj* x_255; obj* x_256; obj* x_257; obj* x_258; 
lean::dec(x_9);
x_255 = lean::cnstr_get(x_241, 0);
lean::inc(x_255);
x_256 = lean::cnstr_get(x_241, 1);
lean::inc(x_256);
if (lean::is_exclusive(x_241)) {
 lean::cnstr_release(x_241, 0);
 lean::cnstr_release(x_241, 1);
 x_257 = x_241;
} else {
 lean::dec_ref(x_241);
 x_257 = lean::box(0);
}
if (lean::is_scalar(x_257)) {
 x_258 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_258 = x_257;
}
lean::cnstr_set(x_258, 0, x_255);
lean::cnstr_set(x_258, 1, x_256);
return x_258;
}
}
else
{
obj* x_259; obj* x_260; obj* x_261; obj* x_262; 
lean::dec(x_9);
x_259 = lean::cnstr_get(x_236, 0);
lean::inc(x_259);
x_260 = lean::cnstr_get(x_236, 1);
lean::inc(x_260);
if (lean::is_exclusive(x_236)) {
 lean::cnstr_release(x_236, 0);
 lean::cnstr_release(x_236, 1);
 x_261 = x_236;
} else {
 lean::dec_ref(x_236);
 x_261 = lean::box(0);
}
if (lean::is_scalar(x_261)) {
 x_262 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_262 = x_261;
}
lean::cnstr_set(x_262, 0, x_259);
lean::cnstr_set(x_262, 1, x_260);
return x_262;
}
}
else
{
uint8 x_263; obj* x_264; obj* x_265; obj* x_266; obj* x_267; 
x_263 = 0;
x_264 = lean::box(0);
x_265 = lean::alloc_cnstr(0, 2, 5);
lean::cnstr_set(x_265, 0, x_264);
lean::cnstr_set(x_265, 1, x_231);
lean::cnstr_set_uint32(x_265, sizeof(void*)*2, x_2);
lean::cnstr_set_uint8(x_265, sizeof(void*)*2 + 4, x_263);
x_266 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_266, 0, x_13);
lean::cnstr_set(x_266, 1, x_222);
lean::cnstr_set(x_266, 2, x_224);
lean::cnstr_set(x_266, 3, x_265);
x_267 = l___private_init_lean_environment_10__setImportedEntries(x_266, x_9, x_227);
if (lean::obj_tag(x_267) == 0)
{
obj* x_268; obj* x_269; obj* x_270; obj* x_271; obj* x_272; 
x_268 = lean::cnstr_get(x_267, 0);
lean::inc(x_268);
x_269 = lean::cnstr_get(x_267, 1);
lean::inc(x_269);
if (lean::is_exclusive(x_267)) {
 lean::cnstr_release(x_267, 0);
 lean::cnstr_release(x_267, 1);
 x_270 = x_267;
} else {
 lean::dec_ref(x_267);
 x_270 = lean::box(0);
}
if (lean::is_scalar(x_270)) {
 x_271 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_271 = x_270;
}
lean::cnstr_set(x_271, 0, x_8);
lean::cnstr_set(x_271, 1, x_269);
x_272 = l___private_init_lean_environment_11__finalizePersistentExtensions(x_268, x_271);
if (lean::obj_tag(x_272) == 0)
{
obj* x_273; obj* x_274; obj* x_275; obj* x_276; obj* x_277; 
x_273 = lean::cnstr_get(x_272, 0);
lean::inc(x_273);
x_274 = lean::cnstr_get(x_272, 1);
lean::inc(x_274);
if (lean::is_exclusive(x_272)) {
 lean::cnstr_release(x_272, 0);
 lean::cnstr_release(x_272, 1);
 x_275 = x_272;
} else {
 lean::dec_ref(x_272);
 x_275 = lean::box(0);
}
if (lean::is_scalar(x_275)) {
 x_276 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_276 = x_275;
}
lean::cnstr_set(x_276, 0, x_8);
lean::cnstr_set(x_276, 1, x_274);
x_277 = l_Array_miterateAux___main___at_Lean_importModules___spec__13(x_9, x_9, x_11, x_273, x_276);
lean::dec(x_9);
if (lean::obj_tag(x_277) == 0)
{
obj* x_278; obj* x_279; obj* x_280; obj* x_281; 
x_278 = lean::cnstr_get(x_277, 0);
lean::inc(x_278);
x_279 = lean::cnstr_get(x_277, 1);
lean::inc(x_279);
if (lean::is_exclusive(x_277)) {
 lean::cnstr_release(x_277, 0);
 lean::cnstr_release(x_277, 1);
 x_280 = x_277;
} else {
 lean::dec_ref(x_277);
 x_280 = lean::box(0);
}
if (lean::is_scalar(x_280)) {
 x_281 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_281 = x_280;
}
lean::cnstr_set(x_281, 0, x_278);
lean::cnstr_set(x_281, 1, x_279);
return x_281;
}
else
{
obj* x_282; obj* x_283; obj* x_284; obj* x_285; 
x_282 = lean::cnstr_get(x_277, 0);
lean::inc(x_282);
x_283 = lean::cnstr_get(x_277, 1);
lean::inc(x_283);
if (lean::is_exclusive(x_277)) {
 lean::cnstr_release(x_277, 0);
 lean::cnstr_release(x_277, 1);
 x_284 = x_277;
} else {
 lean::dec_ref(x_277);
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
lean::dec(x_9);
x_286 = lean::cnstr_get(x_272, 0);
lean::inc(x_286);
x_287 = lean::cnstr_get(x_272, 1);
lean::inc(x_287);
if (lean::is_exclusive(x_272)) {
 lean::cnstr_release(x_272, 0);
 lean::cnstr_release(x_272, 1);
 x_288 = x_272;
} else {
 lean::dec_ref(x_272);
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
else
{
obj* x_290; obj* x_291; obj* x_292; obj* x_293; 
lean::dec(x_9);
x_290 = lean::cnstr_get(x_267, 0);
lean::inc(x_290);
x_291 = lean::cnstr_get(x_267, 1);
lean::inc(x_291);
if (lean::is_exclusive(x_267)) {
 lean::cnstr_release(x_267, 0);
 lean::cnstr_release(x_267, 1);
 x_292 = x_267;
} else {
 lean::dec_ref(x_267);
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
}
else
{
obj* x_294; obj* x_295; obj* x_296; obj* x_297; 
lean::dec(x_222);
lean::dec(x_13);
lean::dec(x_9);
lean::dec(x_1);
x_294 = lean::cnstr_get(x_223, 0);
lean::inc(x_294);
x_295 = lean::cnstr_get(x_223, 1);
lean::inc(x_295);
if (lean::is_exclusive(x_223)) {
 lean::cnstr_release(x_223, 0);
 lean::cnstr_release(x_223, 1);
 x_296 = x_223;
} else {
 lean::dec_ref(x_223);
 x_296 = lean::box(0);
}
if (lean::is_scalar(x_296)) {
 x_297 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_297 = x_296;
}
lean::cnstr_set(x_297, 0, x_294);
lean::cnstr_set(x_297, 1, x_295);
return x_297;
}
}
}
else
{
uint8 x_298; 
lean::dec(x_13);
lean::dec(x_9);
lean::dec(x_1);
x_298 = !lean::is_exclusive(x_15);
if (x_298 == 0)
{
return x_15;
}
else
{
obj* x_299; obj* x_300; obj* x_301; 
x_299 = lean::cnstr_get(x_15, 0);
x_300 = lean::cnstr_get(x_15, 1);
lean::inc(x_300);
lean::inc(x_299);
lean::dec(x_15);
x_301 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_301, 0, x_299);
lean::cnstr_set(x_301, 1, x_300);
return x_301;
}
}
}
else
{
obj* x_302; obj* x_303; obj* x_304; obj* x_305; obj* x_306; obj* x_307; obj* x_308; obj* x_309; obj* x_310; obj* x_311; obj* x_312; 
x_302 = lean::cnstr_get(x_5, 0);
x_303 = lean::cnstr_get(x_5, 1);
lean::inc(x_303);
lean::inc(x_302);
lean::dec(x_5);
x_304 = lean::box(0);
x_305 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_305, 0, x_304);
lean::cnstr_set(x_305, 1, x_303);
x_306 = lean::cnstr_get(x_302, 1);
lean::inc(x_306);
lean::dec(x_302);
x_307 = l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__1;
x_308 = lean::mk_nat_obj(0u);
x_309 = l_HashMap_Inhabited___closed__1;
x_310 = l_Array_miterateAux___main___at_Lean_importModules___spec__8(x_306, x_307, x_306, x_308, x_309);
x_311 = l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2;
x_312 = l_Array_miterateAux___main___at_Lean_importModules___spec__10(x_306, x_307, x_306, x_308, x_311, x_305);
if (lean::obj_tag(x_312) == 0)
{
obj* x_313; obj* x_314; obj* x_315; obj* x_316; obj* x_317; obj* x_318; 
x_313 = lean::cnstr_get(x_312, 0);
lean::inc(x_313);
x_314 = lean::cnstr_get(x_312, 1);
lean::inc(x_314);
if (lean::is_exclusive(x_312)) {
 lean::cnstr_release(x_312, 0);
 lean::cnstr_release(x_312, 1);
 x_315 = x_312;
} else {
 lean::dec_ref(x_312);
 x_315 = lean::box(0);
}
if (lean::is_scalar(x_315)) {
 x_316 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_316 = x_315;
}
lean::cnstr_set(x_316, 0, x_304);
lean::cnstr_set(x_316, 1, x_314);
x_317 = l_Lean_SMap_switch___at_Lean_importModules___spec__11(x_313);
x_318 = l___private_init_lean_environment_6__mkInitialExtensionStates(x_316);
if (lean::obj_tag(x_318) == 0)
{
obj* x_319; obj* x_320; obj* x_321; obj* x_322; uint8 x_323; obj* x_324; obj* x_325; obj* x_326; 
x_319 = lean::cnstr_get(x_318, 0);
lean::inc(x_319);
x_320 = lean::cnstr_get(x_318, 1);
lean::inc(x_320);
if (lean::is_exclusive(x_318)) {
 lean::cnstr_release(x_318, 0);
 lean::cnstr_release(x_318, 1);
 x_321 = x_318;
} else {
 lean::dec_ref(x_318);
 x_321 = lean::box(0);
}
if (lean::is_scalar(x_321)) {
 x_322 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_322 = x_321;
}
lean::cnstr_set(x_322, 0, x_304);
lean::cnstr_set(x_322, 1, x_320);
x_323 = l_List_isEmpty___rarg(x_1);
x_324 = l_List_redLength___main___rarg(x_1);
x_325 = lean_mk_empty_array_with_capacity(x_324);
lean::dec(x_324);
x_326 = l_List_toArrayAux___main___rarg(x_1, x_325);
if (x_323 == 0)
{
uint8 x_327; obj* x_328; obj* x_329; obj* x_330; obj* x_331; 
x_327 = 1;
x_328 = lean::box(0);
x_329 = lean::alloc_cnstr(0, 2, 5);
lean::cnstr_set(x_329, 0, x_328);
lean::cnstr_set(x_329, 1, x_326);
lean::cnstr_set_uint32(x_329, sizeof(void*)*2, x_2);
lean::cnstr_set_uint8(x_329, sizeof(void*)*2 + 4, x_327);
x_330 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_330, 0, x_310);
lean::cnstr_set(x_330, 1, x_317);
lean::cnstr_set(x_330, 2, x_319);
lean::cnstr_set(x_330, 3, x_329);
x_331 = l___private_init_lean_environment_10__setImportedEntries(x_330, x_306, x_322);
if (lean::obj_tag(x_331) == 0)
{
obj* x_332; obj* x_333; obj* x_334; obj* x_335; obj* x_336; 
x_332 = lean::cnstr_get(x_331, 0);
lean::inc(x_332);
x_333 = lean::cnstr_get(x_331, 1);
lean::inc(x_333);
if (lean::is_exclusive(x_331)) {
 lean::cnstr_release(x_331, 0);
 lean::cnstr_release(x_331, 1);
 x_334 = x_331;
} else {
 lean::dec_ref(x_331);
 x_334 = lean::box(0);
}
if (lean::is_scalar(x_334)) {
 x_335 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_335 = x_334;
}
lean::cnstr_set(x_335, 0, x_304);
lean::cnstr_set(x_335, 1, x_333);
x_336 = l___private_init_lean_environment_11__finalizePersistentExtensions(x_332, x_335);
if (lean::obj_tag(x_336) == 0)
{
obj* x_337; obj* x_338; obj* x_339; obj* x_340; obj* x_341; 
x_337 = lean::cnstr_get(x_336, 0);
lean::inc(x_337);
x_338 = lean::cnstr_get(x_336, 1);
lean::inc(x_338);
if (lean::is_exclusive(x_336)) {
 lean::cnstr_release(x_336, 0);
 lean::cnstr_release(x_336, 1);
 x_339 = x_336;
} else {
 lean::dec_ref(x_336);
 x_339 = lean::box(0);
}
if (lean::is_scalar(x_339)) {
 x_340 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_340 = x_339;
}
lean::cnstr_set(x_340, 0, x_304);
lean::cnstr_set(x_340, 1, x_338);
x_341 = l_Array_miterateAux___main___at_Lean_importModules___spec__12(x_306, x_306, x_308, x_337, x_340);
lean::dec(x_306);
if (lean::obj_tag(x_341) == 0)
{
obj* x_342; obj* x_343; obj* x_344; obj* x_345; 
x_342 = lean::cnstr_get(x_341, 0);
lean::inc(x_342);
x_343 = lean::cnstr_get(x_341, 1);
lean::inc(x_343);
if (lean::is_exclusive(x_341)) {
 lean::cnstr_release(x_341, 0);
 lean::cnstr_release(x_341, 1);
 x_344 = x_341;
} else {
 lean::dec_ref(x_341);
 x_344 = lean::box(0);
}
if (lean::is_scalar(x_344)) {
 x_345 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_345 = x_344;
}
lean::cnstr_set(x_345, 0, x_342);
lean::cnstr_set(x_345, 1, x_343);
return x_345;
}
else
{
obj* x_346; obj* x_347; obj* x_348; obj* x_349; 
x_346 = lean::cnstr_get(x_341, 0);
lean::inc(x_346);
x_347 = lean::cnstr_get(x_341, 1);
lean::inc(x_347);
if (lean::is_exclusive(x_341)) {
 lean::cnstr_release(x_341, 0);
 lean::cnstr_release(x_341, 1);
 x_348 = x_341;
} else {
 lean::dec_ref(x_341);
 x_348 = lean::box(0);
}
if (lean::is_scalar(x_348)) {
 x_349 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_349 = x_348;
}
lean::cnstr_set(x_349, 0, x_346);
lean::cnstr_set(x_349, 1, x_347);
return x_349;
}
}
else
{
obj* x_350; obj* x_351; obj* x_352; obj* x_353; 
lean::dec(x_306);
x_350 = lean::cnstr_get(x_336, 0);
lean::inc(x_350);
x_351 = lean::cnstr_get(x_336, 1);
lean::inc(x_351);
if (lean::is_exclusive(x_336)) {
 lean::cnstr_release(x_336, 0);
 lean::cnstr_release(x_336, 1);
 x_352 = x_336;
} else {
 lean::dec_ref(x_336);
 x_352 = lean::box(0);
}
if (lean::is_scalar(x_352)) {
 x_353 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_353 = x_352;
}
lean::cnstr_set(x_353, 0, x_350);
lean::cnstr_set(x_353, 1, x_351);
return x_353;
}
}
else
{
obj* x_354; obj* x_355; obj* x_356; obj* x_357; 
lean::dec(x_306);
x_354 = lean::cnstr_get(x_331, 0);
lean::inc(x_354);
x_355 = lean::cnstr_get(x_331, 1);
lean::inc(x_355);
if (lean::is_exclusive(x_331)) {
 lean::cnstr_release(x_331, 0);
 lean::cnstr_release(x_331, 1);
 x_356 = x_331;
} else {
 lean::dec_ref(x_331);
 x_356 = lean::box(0);
}
if (lean::is_scalar(x_356)) {
 x_357 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_357 = x_356;
}
lean::cnstr_set(x_357, 0, x_354);
lean::cnstr_set(x_357, 1, x_355);
return x_357;
}
}
else
{
uint8 x_358; obj* x_359; obj* x_360; obj* x_361; obj* x_362; 
x_358 = 0;
x_359 = lean::box(0);
x_360 = lean::alloc_cnstr(0, 2, 5);
lean::cnstr_set(x_360, 0, x_359);
lean::cnstr_set(x_360, 1, x_326);
lean::cnstr_set_uint32(x_360, sizeof(void*)*2, x_2);
lean::cnstr_set_uint8(x_360, sizeof(void*)*2 + 4, x_358);
x_361 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_361, 0, x_310);
lean::cnstr_set(x_361, 1, x_317);
lean::cnstr_set(x_361, 2, x_319);
lean::cnstr_set(x_361, 3, x_360);
x_362 = l___private_init_lean_environment_10__setImportedEntries(x_361, x_306, x_322);
if (lean::obj_tag(x_362) == 0)
{
obj* x_363; obj* x_364; obj* x_365; obj* x_366; obj* x_367; 
x_363 = lean::cnstr_get(x_362, 0);
lean::inc(x_363);
x_364 = lean::cnstr_get(x_362, 1);
lean::inc(x_364);
if (lean::is_exclusive(x_362)) {
 lean::cnstr_release(x_362, 0);
 lean::cnstr_release(x_362, 1);
 x_365 = x_362;
} else {
 lean::dec_ref(x_362);
 x_365 = lean::box(0);
}
if (lean::is_scalar(x_365)) {
 x_366 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_366 = x_365;
}
lean::cnstr_set(x_366, 0, x_304);
lean::cnstr_set(x_366, 1, x_364);
x_367 = l___private_init_lean_environment_11__finalizePersistentExtensions(x_363, x_366);
if (lean::obj_tag(x_367) == 0)
{
obj* x_368; obj* x_369; obj* x_370; obj* x_371; obj* x_372; 
x_368 = lean::cnstr_get(x_367, 0);
lean::inc(x_368);
x_369 = lean::cnstr_get(x_367, 1);
lean::inc(x_369);
if (lean::is_exclusive(x_367)) {
 lean::cnstr_release(x_367, 0);
 lean::cnstr_release(x_367, 1);
 x_370 = x_367;
} else {
 lean::dec_ref(x_367);
 x_370 = lean::box(0);
}
if (lean::is_scalar(x_370)) {
 x_371 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_371 = x_370;
}
lean::cnstr_set(x_371, 0, x_304);
lean::cnstr_set(x_371, 1, x_369);
x_372 = l_Array_miterateAux___main___at_Lean_importModules___spec__13(x_306, x_306, x_308, x_368, x_371);
lean::dec(x_306);
if (lean::obj_tag(x_372) == 0)
{
obj* x_373; obj* x_374; obj* x_375; obj* x_376; 
x_373 = lean::cnstr_get(x_372, 0);
lean::inc(x_373);
x_374 = lean::cnstr_get(x_372, 1);
lean::inc(x_374);
if (lean::is_exclusive(x_372)) {
 lean::cnstr_release(x_372, 0);
 lean::cnstr_release(x_372, 1);
 x_375 = x_372;
} else {
 lean::dec_ref(x_372);
 x_375 = lean::box(0);
}
if (lean::is_scalar(x_375)) {
 x_376 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_376 = x_375;
}
lean::cnstr_set(x_376, 0, x_373);
lean::cnstr_set(x_376, 1, x_374);
return x_376;
}
else
{
obj* x_377; obj* x_378; obj* x_379; obj* x_380; 
x_377 = lean::cnstr_get(x_372, 0);
lean::inc(x_377);
x_378 = lean::cnstr_get(x_372, 1);
lean::inc(x_378);
if (lean::is_exclusive(x_372)) {
 lean::cnstr_release(x_372, 0);
 lean::cnstr_release(x_372, 1);
 x_379 = x_372;
} else {
 lean::dec_ref(x_372);
 x_379 = lean::box(0);
}
if (lean::is_scalar(x_379)) {
 x_380 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_380 = x_379;
}
lean::cnstr_set(x_380, 0, x_377);
lean::cnstr_set(x_380, 1, x_378);
return x_380;
}
}
else
{
obj* x_381; obj* x_382; obj* x_383; obj* x_384; 
lean::dec(x_306);
x_381 = lean::cnstr_get(x_367, 0);
lean::inc(x_381);
x_382 = lean::cnstr_get(x_367, 1);
lean::inc(x_382);
if (lean::is_exclusive(x_367)) {
 lean::cnstr_release(x_367, 0);
 lean::cnstr_release(x_367, 1);
 x_383 = x_367;
} else {
 lean::dec_ref(x_367);
 x_383 = lean::box(0);
}
if (lean::is_scalar(x_383)) {
 x_384 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_384 = x_383;
}
lean::cnstr_set(x_384, 0, x_381);
lean::cnstr_set(x_384, 1, x_382);
return x_384;
}
}
else
{
obj* x_385; obj* x_386; obj* x_387; obj* x_388; 
lean::dec(x_306);
x_385 = lean::cnstr_get(x_362, 0);
lean::inc(x_385);
x_386 = lean::cnstr_get(x_362, 1);
lean::inc(x_386);
if (lean::is_exclusive(x_362)) {
 lean::cnstr_release(x_362, 0);
 lean::cnstr_release(x_362, 1);
 x_387 = x_362;
} else {
 lean::dec_ref(x_362);
 x_387 = lean::box(0);
}
if (lean::is_scalar(x_387)) {
 x_388 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_388 = x_387;
}
lean::cnstr_set(x_388, 0, x_385);
lean::cnstr_set(x_388, 1, x_386);
return x_388;
}
}
}
else
{
obj* x_389; obj* x_390; obj* x_391; obj* x_392; 
lean::dec(x_317);
lean::dec(x_310);
lean::dec(x_306);
lean::dec(x_1);
x_389 = lean::cnstr_get(x_318, 0);
lean::inc(x_389);
x_390 = lean::cnstr_get(x_318, 1);
lean::inc(x_390);
if (lean::is_exclusive(x_318)) {
 lean::cnstr_release(x_318, 0);
 lean::cnstr_release(x_318, 1);
 x_391 = x_318;
} else {
 lean::dec_ref(x_318);
 x_391 = lean::box(0);
}
if (lean::is_scalar(x_391)) {
 x_392 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_392 = x_391;
}
lean::cnstr_set(x_392, 0, x_389);
lean::cnstr_set(x_392, 1, x_390);
return x_392;
}
}
else
{
obj* x_393; obj* x_394; obj* x_395; obj* x_396; 
lean::dec(x_310);
lean::dec(x_306);
lean::dec(x_1);
x_393 = lean::cnstr_get(x_312, 0);
lean::inc(x_393);
x_394 = lean::cnstr_get(x_312, 1);
lean::inc(x_394);
if (lean::is_exclusive(x_312)) {
 lean::cnstr_release(x_312, 0);
 lean::cnstr_release(x_312, 1);
 x_395 = x_312;
} else {
 lean::dec_ref(x_312);
 x_395 = lean::box(0);
}
if (lean::is_scalar(x_395)) {
 x_396 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_396 = x_395;
}
lean::cnstr_set(x_396, 0, x_393);
lean::cnstr_set(x_396, 1, x_394);
return x_396;
}
}
}
else
{
uint8 x_397; 
lean::dec(x_1);
x_397 = !lean::is_exclusive(x_5);
if (x_397 == 0)
{
return x_5;
}
else
{
obj* x_398; obj* x_399; obj* x_400; 
x_398 = lean::cnstr_get(x_5, 0);
x_399 = lean::cnstr_get(x_5, 1);
lean::inc(x_399);
lean::inc(x_398);
lean::dec(x_5);
x_400 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_400, 0, x_398);
lean::cnstr_set(x_400, 1, x_399);
return x_400;
}
}
}
}
obj* l_AssocList_contains___main___at_Lean_importModules___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_importModules___spec__2(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__7___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Array_miterateAux___main___at_Lean_importModules___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_8;
}
}
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__8___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_importModules___spec__8(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__9___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_miterateAux___main___at_Lean_importModules___spec__9(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
}
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__10___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_miterateAux___main___at_Lean_importModules___spec__10(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
}
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__12___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_importModules___spec__12(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__13___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_importModules___spec__13(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Lean_importModules___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_5 = lean_import_modules(x_1, x_4, x_3);
return x_5;
}
}
obj* l_Array_miterateAux___main___at_Lean_regNamespacesExtension___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
return x_4;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean::box(0);
x_9 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_4, x_7, x_8);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean_nat_add(x_3, x_10);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_9;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_Lean_regNamespacesExtension___spec__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
return x_4;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean::mk_nat_obj(0u);
x_9 = l_Array_miterateAux___main___at_Lean_regNamespacesExtension___spec__2(x_7, x_7, x_8, x_4);
lean::dec(x_7);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean_nat_add(x_3, x_10);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_9;
goto _start;
}
}
}
obj* l_Lean_mkStateFromImportedEntries___at_Lean_regNamespacesExtension___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l_Array_miterateAux___main___at_Lean_regNamespacesExtension___spec__3(x_2, x_2, x_3, x_1);
return x_4;
}
}
uint8 l_Array_anyMAux___main___at_Lean_regNamespacesExtension___spec__6(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
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
x_7 = lean_array_fget(x_2, x_3);
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
x_12 = lean_nat_add(x_3, x_11);
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
obj* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7___closed__1;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7(obj* x_1, obj* x_2) {
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
x_16 = lean_io_ref_get(x_15, x_3);
if (lean::obj_tag(x_16) == 0)
{
uint8 x_17; 
x_17 = !lean::is_exclusive(x_16);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_18 = lean::cnstr_get(x_16, 0);
lean::cnstr_set(x_16, 0, x_14);
x_19 = lean_array_get_size(x_18);
lean::dec(x_18);
x_20 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7___closed__2;
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_1);
lean::cnstr_set(x_21, 2, x_20);
x_22 = lean_io_ref_get(x_15, x_16);
if (lean::obj_tag(x_22) == 0)
{
uint8 x_23; 
x_23 = !lean::is_exclusive(x_22);
if (x_23 == 0)
{
obj* x_24; obj* x_25; 
x_24 = lean::cnstr_get(x_22, 0);
lean::cnstr_set(x_22, 0, x_14);
x_25 = lean_io_ref_reset(x_15, x_22);
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
x_30 = lean_array_push(x_24, x_29);
x_31 = lean_io_ref_set(x_15, x_30, x_25);
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
x_44 = lean_array_push(x_24, x_43);
x_45 = lean_io_ref_set(x_15, x_44, x_41);
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
x_60 = lean_io_ref_reset(x_15, x_59);
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
x_66 = lean_array_push(x_57, x_65);
x_67 = lean_io_ref_set(x_15, x_66, x_63);
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
x_86 = lean_array_get_size(x_83);
lean::dec(x_83);
x_87 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7___closed__2;
x_88 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_88, 0, x_86);
lean::cnstr_set(x_88, 1, x_1);
lean::cnstr_set(x_88, 2, x_87);
x_89 = lean_io_ref_get(x_15, x_85);
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
x_94 = lean_io_ref_reset(x_15, x_93);
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
x_100 = lean_array_push(x_90, x_99);
x_101 = lean_io_ref_set(x_15, x_100, x_97);
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
x_125 = lean_io_ref_get(x_124, x_123);
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
x_130 = lean_array_get_size(x_126);
lean::dec(x_126);
x_131 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7___closed__2;
x_132 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_132, 0, x_130);
lean::cnstr_set(x_132, 1, x_1);
lean::cnstr_set(x_132, 2, x_131);
x_133 = lean_io_ref_get(x_124, x_129);
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
x_138 = lean_io_ref_reset(x_124, x_137);
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
x_144 = lean_array_push(x_134, x_143);
x_145 = lean_io_ref_set(x_124, x_144, x_141);
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
obj* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__5(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l___private_init_lean_environment_8__persistentEnvExtensionsRef;
x_4 = lean_io_ref_get(x_3, x_2);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::cnstr_get(x_4, 0);
x_7 = lean::mk_nat_obj(0u);
x_8 = l_Array_anyMAux___main___at_Lean_regNamespacesExtension___spec__6(x_1, x_6, x_7);
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
x_15 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7(x_14, x_4);
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
x_23 = lean_io_ref_get(x_3, x_15);
if (lean::obj_tag(x_23) == 0)
{
uint8 x_24; 
x_24 = !lean::is_exclusive(x_23);
if (x_24 == 0)
{
obj* x_25; obj* x_26; 
x_25 = lean::cnstr_get(x_23, 0);
lean::cnstr_set(x_23, 0, x_9);
x_26 = lean_io_ref_reset(x_3, x_23);
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
x_31 = lean_array_push(x_25, x_30);
x_32 = lean_io_ref_set(x_3, x_31, x_26);
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
x_45 = lean_array_push(x_25, x_44);
x_46 = lean_io_ref_set(x_3, x_45, x_42);
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
x_61 = lean_io_ref_reset(x_3, x_60);
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
x_67 = lean_array_push(x_58, x_66);
x_68 = lean_io_ref_set(x_3, x_67, x_64);
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
x_92 = lean_io_ref_get(x_3, x_86);
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
x_97 = lean_io_ref_reset(x_3, x_96);
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
x_103 = lean_array_push(x_93, x_102);
x_104 = lean_io_ref_set(x_3, x_103, x_100);
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
x_128 = lean_string_append(x_127, x_126);
lean::dec(x_126);
x_129 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_130 = lean_string_append(x_128, x_129);
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
x_134 = l_Array_anyMAux___main___at_Lean_regNamespacesExtension___spec__6(x_1, x_131, x_133);
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
x_142 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7(x_141, x_136);
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
x_152 = lean_io_ref_get(x_3, x_146);
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
x_157 = lean_io_ref_reset(x_3, x_156);
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
x_163 = lean_array_push(x_153, x_162);
x_164 = lean_io_ref_set(x_3, x_163, x_160);
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
x_188 = lean_string_append(x_187, x_186);
lean::dec(x_186);
x_189 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_190 = lean_string_append(x_188, x_189);
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
obj* l_Lean_registerSimplePersistentEnvExtension___at_Lean_regNamespacesExtension___spec__4(obj* x_1, obj* x_2) {
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
x_9 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__5(x_8, x_2);
return x_9;
}
}
obj* l_Lean_regNamespacesExtension___lambda__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_regNamespacesExtension___lambda__2(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::box(0);
x_3 = lean::mk_nat_obj(0u);
x_4 = l_Array_miterateAux___main___at_Lean_regNamespacesExtension___spec__3(x_1, x_1, x_3, x_2);
return x_4;
}
}
obj* l_Lean_regNamespacesExtension___lambda__3(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_List_redLength___main___rarg(x_1);
x_3 = lean_mk_empty_array_with_capacity(x_2);
lean::dec(x_2);
x_4 = l_List_toArrayAux___main___rarg(x_1, x_3);
return x_4;
}
}
obj* _init_l_Lean_regNamespacesExtension___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("namespaces");
return x_1;
}
}
obj* _init_l_Lean_regNamespacesExtension___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_regNamespacesExtension___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_regNamespacesExtension___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_regNamespacesExtension___lambda__1), 2, 0);
return x_1;
}
}
obj* _init_l_Lean_regNamespacesExtension___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_regNamespacesExtension___lambda__2___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_regNamespacesExtension___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_regNamespacesExtension___lambda__3), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_regNamespacesExtension___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_regNamespacesExtension___closed__2;
x_2 = l_Lean_regNamespacesExtension___closed__3;
x_3 = l_Lean_regNamespacesExtension___closed__4;
x_4 = l_Lean_regNamespacesExtension___closed__5;
x_5 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_4);
return x_5;
}
}
obj* l_Lean_regNamespacesExtension(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_regNamespacesExtension___closed__6;
x_3 = l_Lean_registerSimplePersistentEnvExtension___at_Lean_regNamespacesExtension___spec__4(x_2, x_1);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Lean_regNamespacesExtension___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_regNamespacesExtension___spec__2(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Array_miterateAux___main___at_Lean_regNamespacesExtension___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_regNamespacesExtension___spec__3(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_mkStateFromImportedEntries___at_Lean_regNamespacesExtension___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_mkStateFromImportedEntries___at_Lean_regNamespacesExtension___spec__1(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_anyMAux___main___at_Lean_regNamespacesExtension___spec__6___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_Array_anyMAux___main___at_Lean_regNamespacesExtension___spec__6(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_Lean_regNamespacesExtension___lambda__2___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_regNamespacesExtension___lambda__2(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_namespacesExt___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
}
obj* l_Lean_namespacesExt___elambda__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_empty___closed__1;
return x_2;
}
}
obj* l_Lean_namespacesExt___elambda__3(obj* x_1, obj* x_2) {
_start:
{
lean::inc(x_1);
return x_1;
}
}
obj* l_Lean_namespacesExt___elambda__4___rarg(obj* x_1) {
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
obj* l_Lean_namespacesExt___elambda__4(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_namespacesExt___elambda__4___rarg), 1, 0);
return x_2;
}
}
obj* _init_l_Lean_namespacesExt___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::mk_nat_obj(0u);
x_2 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_3 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7___closed__2;
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 2, x_3);
return x_4;
}
}
obj* _init_l_Lean_namespacesExt___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_namespacesExt___elambda__4___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_namespacesExt___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_namespacesExt___elambda__3___boxed), 2, 0);
return x_1;
}
}
obj* _init_l_Lean_namespacesExt___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_namespacesExt___elambda__2___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_namespacesExt___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_namespacesExt___elambda__1___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_namespacesExt___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = l_Lean_namespacesExt___closed__1;
x_2 = lean::box(0);
x_3 = l_Lean_namespacesExt___closed__2;
x_4 = l_Lean_namespacesExt___closed__3;
x_5 = l_Lean_namespacesExt___closed__4;
x_6 = l_Lean_namespacesExt___closed__5;
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
obj* l_Lean_namespacesExt___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_namespacesExt___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_namespacesExt___elambda__2___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_namespacesExt___elambda__2(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_namespacesExt___elambda__3___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_namespacesExt___elambda__3(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_namespacesExt___elambda__4___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_namespacesExt___elambda__4(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_registerNamespace(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = l_Lean_namespacesExt;
x_4 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_3, x_1);
x_5 = l_Lean_NameSet_contains(x_4, x_2);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_6; 
x_6 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_3, x_1, x_2);
return x_6;
}
else
{
lean::dec(x_2);
return x_1;
}
}
}
uint8 l_Lean_isNamespace(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = l_Lean_namespacesExt;
x_4 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_3, x_1);
x_5 = l_Lean_NameSet_contains(x_4, x_2);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_isNamespace___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_isNamespace(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Lean_getNamespaceSet(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_namespacesExt;
x_3 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_2, x_1);
return x_3;
}
}
obj* l_Lean_getNamespaceSet___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_getNamespaceSet(x_1);
lean::dec(x_1);
return x_2;
}
}
uint8 l___private_init_lean_environment_12__isNamespaceName___main(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 1)
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::box(0);
x_4 = lean_name_dec_eq(x_2, x_3);
if (x_4 == 0)
{
x_1 = x_2;
goto _start;
}
else
{
uint8 x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8 x_7; 
x_7 = 0;
return x_7;
}
}
}
obj* l___private_init_lean_environment_12__isNamespaceName___main___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l___private_init_lean_environment_12__isNamespaceName___main(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l___private_init_lean_environment_12__isNamespaceName(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l___private_init_lean_environment_12__isNamespaceName___main(x_1);
return x_2;
}
}
obj* l___private_init_lean_environment_12__isNamespaceName___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l___private_init_lean_environment_12__isNamespaceName(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l___private_init_lean_environment_13__registerNamePrefixes___main(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 1)
{
obj* x_3; uint8 x_4; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_4 = l___private_init_lean_environment_12__isNamespaceName___main(x_3);
if (x_4 == 0)
{
lean::dec(x_3);
return x_1;
}
else
{
obj* x_5; 
lean::inc(x_3);
x_5 = l_Lean_registerNamespace(x_1, x_3);
x_1 = x_5;
x_2 = x_3;
goto _start;
}
}
else
{
lean::dec(x_2);
return x_1;
}
}
}
obj* l___private_init_lean_environment_13__registerNamePrefixes(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_environment_13__registerNamePrefixes___main(x_1, x_2);
return x_3;
}
}
obj* lean_environment_add(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_Lean_ConstantInfo_name(x_2);
x_4 = l___private_init_lean_environment_13__registerNamePrefixes___main(x_1, x_3);
x_5 = l_Lean_Environment_addAux(x_4, x_2);
return x_5;
}
}
obj* l_List_toStringAux___main___at_Lean_Environment_displayStats___spec__2(uint8 x_1, obj* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = l_String_splitAux___main___closed__1;
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_6 = l_Lean_Name_toString___closed__1;
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_4);
x_8 = l_List_reprAux___main___rarg___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean::dec(x_7);
x_10 = l_List_toStringAux___main___at_Lean_Environment_displayStats___spec__2(x_1, x_5);
x_11 = lean_string_append(x_9, x_10);
lean::dec(x_10);
return x_11;
}
}
else
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_12; 
x_12 = l_String_splitAux___main___closed__1;
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; uint8 x_17; obj* x_18; obj* x_19; 
x_13 = lean::cnstr_get(x_2, 0);
lean::inc(x_13);
x_14 = lean::cnstr_get(x_2, 1);
lean::inc(x_14);
lean::dec(x_2);
x_15 = l_Lean_Name_toString___closed__1;
x_16 = l_Lean_Name_toStringWithSep___main(x_15, x_13);
x_17 = 0;
x_18 = l_List_toStringAux___main___at_Lean_Environment_displayStats___spec__2(x_17, x_14);
x_19 = lean_string_append(x_16, x_18);
lean::dec(x_18);
return x_19;
}
}
}
}
obj* l_List_toString___at_Lean_Environment_displayStats___spec__1(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_List_repr___rarg___closed__1;
return x_2;
}
else
{
uint8 x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = 1;
x_4 = l_List_toStringAux___main___at_Lean_Environment_displayStats___spec__2(x_3, x_1);
x_5 = l_List_repr___rarg___closed__2;
x_6 = lean_string_append(x_5, x_4);
lean::dec(x_4);
x_7 = l_List_repr___rarg___closed__3;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
}
}
obj* l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::mk_nat_obj(0u);
x_5 = l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(x_4, x_3);
x_6 = lean::cnstr_get(x_2, 0);
x_7 = lean_nat_add(x_6, x_5);
lean::dec(x_5);
return x_7;
}
}
obj* l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::mk_nat_obj(0u);
x_5 = l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(x_4, x_3);
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_5);
return x_7;
}
}
obj* l_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__6(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::cnstr_get(x_1, 1);
x_3 = lean_array_get_size(x_2);
return x_3;
}
}
obj* l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = l_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__6(x_2);
return x_3;
}
}
obj* l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::cnstr_get(x_1, 1);
x_3 = l_RBMap_maxDepth___rarg___closed__1;
x_4 = l_RBNode_depth___main___rarg(x_3, x_2);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__8(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
return x_5;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean_array_get_size(x_8);
lean::dec(x_8);
x_10 = lean_nat_add(x_5, x_9);
lean::dec(x_9);
lean::dec(x_5);
x_11 = lean::mk_nat_obj(1u);
x_12 = lean_nat_add(x_4, x_11);
lean::dec(x_4);
x_4 = x_12;
x_5 = x_10;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__9(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
return x_5;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean_array_get_size(x_8);
lean::dec(x_8);
x_10 = lean_nat_add(x_5, x_9);
lean::dec(x_9);
lean::dec(x_5);
x_11 = lean::mk_nat_obj(1u);
x_12 = lean_nat_add(x_4, x_11);
lean::dec(x_4);
x_4 = x_12;
x_5 = x_10;
goto _start;
}
}
}
obj* _init_l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("extension '");
return x_1;
}
}
obj* _init_l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("  ");
return x_1;
}
}
obj* _init_l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("  number of imported entries: ");
return x_1;
}
}
obj* l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
uint8 x_7; 
lean::dec(x_3);
x_7 = !lean::is_exclusive(x_4);
if (x_7 == 0)
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_4, 0);
lean::dec(x_8);
x_9 = lean::box(0);
lean::cnstr_set(x_4, 0, x_9);
return x_4;
}
else
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::cnstr_get(x_4, 1);
lean::inc(x_10);
lean::dec(x_4);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
return x_12;
}
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_13 = lean_array_fget(x_2, x_3);
x_14 = lean::mk_nat_obj(1u);
x_15 = lean_nat_add(x_3, x_14);
lean::dec(x_3);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
x_17 = l_Lean_Name_toString___closed__1;
x_18 = l_Lean_Name_toStringWithSep___main(x_17, x_16);
x_19 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean::dec(x_18);
x_21 = l_Char_HasRepr___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_IO_println___at_HasRepr_HasEval___spec__1(x_22, x_4);
lean::dec(x_22);
if (lean::obj_tag(x_23) == 0)
{
uint8 x_24; 
x_24 = !lean::is_exclusive(x_23);
if (x_24 == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; uint8 x_32; 
x_25 = lean::cnstr_get(x_23, 0);
lean::dec(x_25);
x_26 = lean::box(0);
lean::cnstr_set(x_23, 0, x_26);
x_27 = lean::cnstr_get(x_13, 0);
lean::inc(x_27);
x_28 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_27, x_1);
x_29 = lean::cnstr_get(x_13, 5);
lean::inc(x_29);
x_30 = lean::cnstr_get(x_28, 1);
lean::inc(x_30);
x_31 = lean::apply_1(x_29, x_30);
x_32 = l_Lean_Format_isNil(x_31);
if (x_32 == 0)
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_33 = lean::mk_nat_obj(2u);
x_34 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_31);
x_35 = l_Lean_Options_empty;
x_36 = l_Lean_Format_pretty(x_34, x_35);
x_37 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__2;
x_38 = lean_string_append(x_37, x_36);
lean::dec(x_36);
x_39 = l_IO_println___at_HasRepr_HasEval___spec__1(x_38, x_23);
lean::dec(x_38);
if (lean::obj_tag(x_39) == 0)
{
uint8 x_40; 
x_40 = !lean::is_exclusive(x_39);
if (x_40 == 0)
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_41 = lean::cnstr_get(x_39, 0);
lean::dec(x_41);
lean::cnstr_set(x_39, 0, x_26);
x_42 = lean::cnstr_get(x_28, 0);
lean::inc(x_42);
lean::dec(x_28);
x_43 = lean::mk_nat_obj(0u);
x_44 = l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__8(x_1, x_13, x_42, x_43, x_43);
lean::dec(x_42);
lean::dec(x_13);
x_45 = l_Nat_repr(x_44);
x_46 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__3;
x_47 = lean_string_append(x_46, x_45);
lean::dec(x_45);
x_48 = l_IO_println___at_HasRepr_HasEval___spec__1(x_47, x_39);
lean::dec(x_47);
if (lean::obj_tag(x_48) == 0)
{
uint8 x_49; 
x_49 = !lean::is_exclusive(x_48);
if (x_49 == 0)
{
obj* x_50; 
x_50 = lean::cnstr_get(x_48, 0);
lean::dec(x_50);
lean::cnstr_set(x_48, 0, x_26);
x_3 = x_15;
x_4 = x_48;
goto _start;
}
else
{
obj* x_52; obj* x_53; 
x_52 = lean::cnstr_get(x_48, 1);
lean::inc(x_52);
lean::dec(x_48);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_26);
lean::cnstr_set(x_53, 1, x_52);
x_3 = x_15;
x_4 = x_53;
goto _start;
}
}
else
{
uint8 x_55; 
lean::dec(x_15);
x_55 = !lean::is_exclusive(x_48);
if (x_55 == 0)
{
return x_48;
}
else
{
obj* x_56; obj* x_57; obj* x_58; 
x_56 = lean::cnstr_get(x_48, 0);
x_57 = lean::cnstr_get(x_48, 1);
lean::inc(x_57);
lean::inc(x_56);
lean::dec(x_48);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_59 = lean::cnstr_get(x_39, 1);
lean::inc(x_59);
lean::dec(x_39);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_26);
lean::cnstr_set(x_60, 1, x_59);
x_61 = lean::cnstr_get(x_28, 0);
lean::inc(x_61);
lean::dec(x_28);
x_62 = lean::mk_nat_obj(0u);
x_63 = l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__8(x_1, x_13, x_61, x_62, x_62);
lean::dec(x_61);
lean::dec(x_13);
x_64 = l_Nat_repr(x_63);
x_65 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__3;
x_66 = lean_string_append(x_65, x_64);
lean::dec(x_64);
x_67 = l_IO_println___at_HasRepr_HasEval___spec__1(x_66, x_60);
lean::dec(x_66);
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
lean::cnstr_set(x_70, 0, x_26);
lean::cnstr_set(x_70, 1, x_68);
x_3 = x_15;
x_4 = x_70;
goto _start;
}
else
{
obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
lean::dec(x_15);
x_72 = lean::cnstr_get(x_67, 0);
lean::inc(x_72);
x_73 = lean::cnstr_get(x_67, 1);
lean::inc(x_73);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_release(x_67, 0);
 lean::cnstr_release(x_67, 1);
 x_74 = x_67;
} else {
 lean::dec_ref(x_67);
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
}
else
{
uint8 x_76; 
lean::dec(x_28);
lean::dec(x_15);
lean::dec(x_13);
x_76 = !lean::is_exclusive(x_39);
if (x_76 == 0)
{
return x_39;
}
else
{
obj* x_77; obj* x_78; obj* x_79; 
x_77 = lean::cnstr_get(x_39, 0);
x_78 = lean::cnstr_get(x_39, 1);
lean::inc(x_78);
lean::inc(x_77);
lean::dec(x_39);
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_77);
lean::cnstr_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
lean::dec(x_31);
x_80 = lean::cnstr_get(x_28, 0);
lean::inc(x_80);
lean::dec(x_28);
x_81 = lean::mk_nat_obj(0u);
x_82 = l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__9(x_1, x_13, x_80, x_81, x_81);
lean::dec(x_80);
lean::dec(x_13);
x_83 = l_Nat_repr(x_82);
x_84 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__3;
x_85 = lean_string_append(x_84, x_83);
lean::dec(x_83);
x_86 = l_IO_println___at_HasRepr_HasEval___spec__1(x_85, x_23);
lean::dec(x_85);
if (lean::obj_tag(x_86) == 0)
{
uint8 x_87; 
x_87 = !lean::is_exclusive(x_86);
if (x_87 == 0)
{
obj* x_88; 
x_88 = lean::cnstr_get(x_86, 0);
lean::dec(x_88);
lean::cnstr_set(x_86, 0, x_26);
x_3 = x_15;
x_4 = x_86;
goto _start;
}
else
{
obj* x_90; obj* x_91; 
x_90 = lean::cnstr_get(x_86, 1);
lean::inc(x_90);
lean::dec(x_86);
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_26);
lean::cnstr_set(x_91, 1, x_90);
x_3 = x_15;
x_4 = x_91;
goto _start;
}
}
else
{
uint8 x_93; 
lean::dec(x_15);
x_93 = !lean::is_exclusive(x_86);
if (x_93 == 0)
{
return x_86;
}
else
{
obj* x_94; obj* x_95; obj* x_96; 
x_94 = lean::cnstr_get(x_86, 0);
x_95 = lean::cnstr_get(x_86, 1);
lean::inc(x_95);
lean::inc(x_94);
lean::dec(x_86);
x_96 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_96, 0, x_94);
lean::cnstr_set(x_96, 1, x_95);
return x_96;
}
}
}
}
else
{
obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; uint8 x_105; 
x_97 = lean::cnstr_get(x_23, 1);
lean::inc(x_97);
lean::dec(x_23);
x_98 = lean::box(0);
x_99 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_99, 0, x_98);
lean::cnstr_set(x_99, 1, x_97);
x_100 = lean::cnstr_get(x_13, 0);
lean::inc(x_100);
x_101 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_100, x_1);
x_102 = lean::cnstr_get(x_13, 5);
lean::inc(x_102);
x_103 = lean::cnstr_get(x_101, 1);
lean::inc(x_103);
x_104 = lean::apply_1(x_102, x_103);
x_105 = l_Lean_Format_isNil(x_104);
if (x_105 == 0)
{
obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
x_106 = lean::mk_nat_obj(2u);
x_107 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_107, 0, x_106);
lean::cnstr_set(x_107, 1, x_104);
x_108 = l_Lean_Options_empty;
x_109 = l_Lean_Format_pretty(x_107, x_108);
x_110 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__2;
x_111 = lean_string_append(x_110, x_109);
lean::dec(x_109);
x_112 = l_IO_println___at_HasRepr_HasEval___spec__1(x_111, x_99);
lean::dec(x_111);
if (lean::obj_tag(x_112) == 0)
{
obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; 
x_113 = lean::cnstr_get(x_112, 1);
lean::inc(x_113);
if (lean::is_exclusive(x_112)) {
 lean::cnstr_release(x_112, 0);
 lean::cnstr_release(x_112, 1);
 x_114 = x_112;
} else {
 lean::dec_ref(x_112);
 x_114 = lean::box(0);
}
if (lean::is_scalar(x_114)) {
 x_115 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_115 = x_114;
}
lean::cnstr_set(x_115, 0, x_98);
lean::cnstr_set(x_115, 1, x_113);
x_116 = lean::cnstr_get(x_101, 0);
lean::inc(x_116);
lean::dec(x_101);
x_117 = lean::mk_nat_obj(0u);
x_118 = l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__8(x_1, x_13, x_116, x_117, x_117);
lean::dec(x_116);
lean::dec(x_13);
x_119 = l_Nat_repr(x_118);
x_120 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__3;
x_121 = lean_string_append(x_120, x_119);
lean::dec(x_119);
x_122 = l_IO_println___at_HasRepr_HasEval___spec__1(x_121, x_115);
lean::dec(x_121);
if (lean::obj_tag(x_122) == 0)
{
obj* x_123; obj* x_124; obj* x_125; 
x_123 = lean::cnstr_get(x_122, 1);
lean::inc(x_123);
if (lean::is_exclusive(x_122)) {
 lean::cnstr_release(x_122, 0);
 lean::cnstr_release(x_122, 1);
 x_124 = x_122;
} else {
 lean::dec_ref(x_122);
 x_124 = lean::box(0);
}
if (lean::is_scalar(x_124)) {
 x_125 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_125 = x_124;
}
lean::cnstr_set(x_125, 0, x_98);
lean::cnstr_set(x_125, 1, x_123);
x_3 = x_15;
x_4 = x_125;
goto _start;
}
else
{
obj* x_127; obj* x_128; obj* x_129; obj* x_130; 
lean::dec(x_15);
x_127 = lean::cnstr_get(x_122, 0);
lean::inc(x_127);
x_128 = lean::cnstr_get(x_122, 1);
lean::inc(x_128);
if (lean::is_exclusive(x_122)) {
 lean::cnstr_release(x_122, 0);
 lean::cnstr_release(x_122, 1);
 x_129 = x_122;
} else {
 lean::dec_ref(x_122);
 x_129 = lean::box(0);
}
if (lean::is_scalar(x_129)) {
 x_130 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_130 = x_129;
}
lean::cnstr_set(x_130, 0, x_127);
lean::cnstr_set(x_130, 1, x_128);
return x_130;
}
}
else
{
obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
lean::dec(x_101);
lean::dec(x_15);
lean::dec(x_13);
x_131 = lean::cnstr_get(x_112, 0);
lean::inc(x_131);
x_132 = lean::cnstr_get(x_112, 1);
lean::inc(x_132);
if (lean::is_exclusive(x_112)) {
 lean::cnstr_release(x_112, 0);
 lean::cnstr_release(x_112, 1);
 x_133 = x_112;
} else {
 lean::dec_ref(x_112);
 x_133 = lean::box(0);
}
if (lean::is_scalar(x_133)) {
 x_134 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_134 = x_133;
}
lean::cnstr_set(x_134, 0, x_131);
lean::cnstr_set(x_134, 1, x_132);
return x_134;
}
}
else
{
obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; 
lean::dec(x_104);
x_135 = lean::cnstr_get(x_101, 0);
lean::inc(x_135);
lean::dec(x_101);
x_136 = lean::mk_nat_obj(0u);
x_137 = l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__9(x_1, x_13, x_135, x_136, x_136);
lean::dec(x_135);
lean::dec(x_13);
x_138 = l_Nat_repr(x_137);
x_139 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__3;
x_140 = lean_string_append(x_139, x_138);
lean::dec(x_138);
x_141 = l_IO_println___at_HasRepr_HasEval___spec__1(x_140, x_99);
lean::dec(x_140);
if (lean::obj_tag(x_141) == 0)
{
obj* x_142; obj* x_143; obj* x_144; 
x_142 = lean::cnstr_get(x_141, 1);
lean::inc(x_142);
if (lean::is_exclusive(x_141)) {
 lean::cnstr_release(x_141, 0);
 lean::cnstr_release(x_141, 1);
 x_143 = x_141;
} else {
 lean::dec_ref(x_141);
 x_143 = lean::box(0);
}
if (lean::is_scalar(x_143)) {
 x_144 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_144 = x_143;
}
lean::cnstr_set(x_144, 0, x_98);
lean::cnstr_set(x_144, 1, x_142);
x_3 = x_15;
x_4 = x_144;
goto _start;
}
else
{
obj* x_146; obj* x_147; obj* x_148; obj* x_149; 
lean::dec(x_15);
x_146 = lean::cnstr_get(x_141, 0);
lean::inc(x_146);
x_147 = lean::cnstr_get(x_141, 1);
lean::inc(x_147);
if (lean::is_exclusive(x_141)) {
 lean::cnstr_release(x_141, 0);
 lean::cnstr_release(x_141, 1);
 x_148 = x_141;
} else {
 lean::dec_ref(x_141);
 x_148 = lean::box(0);
}
if (lean::is_scalar(x_148)) {
 x_149 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_149 = x_148;
}
lean::cnstr_set(x_149, 0, x_146);
lean::cnstr_set(x_149, 1, x_147);
return x_149;
}
}
}
}
else
{
uint8 x_150; 
lean::dec(x_15);
lean::dec(x_13);
x_150 = !lean::is_exclusive(x_23);
if (x_150 == 0)
{
return x_23;
}
else
{
obj* x_151; obj* x_152; obj* x_153; 
x_151 = lean::cnstr_get(x_23, 0);
x_152 = lean::cnstr_get(x_23, 1);
lean::inc(x_152);
lean::inc(x_151);
lean::dec(x_23);
x_153 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_153, 0, x_151);
lean::cnstr_set(x_153, 1, x_152);
return x_153;
}
}
}
}
}
obj* _init_l_Lean_Environment_displayStats___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("direct imports:                        ");
return x_1;
}
}
obj* _init_l_Lean_Environment_displayStats___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("number of imported modules:            ");
return x_1;
}
}
obj* _init_l_Lean_Environment_displayStats___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("number of consts:                      ");
return x_1;
}
}
obj* _init_l_Lean_Environment_displayStats___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("number of imported consts:             ");
return x_1;
}
}
obj* _init_l_Lean_Environment_displayStats___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("number of local consts:                ");
return x_1;
}
}
obj* _init_l_Lean_Environment_displayStats___closed__6() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("number of buckets for imported consts: ");
return x_1;
}
}
obj* _init_l_Lean_Environment_displayStats___closed__7() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("map depth for local consts:            ");
return x_1;
}
}
obj* _init_l_Lean_Environment_displayStats___closed__8() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("trust level:                           ");
return x_1;
}
}
obj* _init_l_Lean_Environment_displayStats___closed__9() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("number of extensions:                  ");
return x_1;
}
}
obj* lean_display_stats(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l___private_init_lean_environment_8__persistentEnvExtensionsRef;
x_4 = lean_io_ref_get(x_3, x_2);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_6 = lean::cnstr_get(x_4, 0);
x_7 = lean::box(0);
lean::cnstr_set(x_4, 0, x_7);
x_8 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_9 = lean::mk_nat_obj(0u);
x_10 = lean_array_get(x_8, x_6, x_9);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
lean::dec(x_10);
x_12 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_11, x_1);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
lean::dec(x_12);
x_14 = lean_array_get_size(x_13);
lean::dec(x_13);
x_15 = lean::cnstr_get(x_1, 3);
lean::inc(x_15);
x_16 = lean::cnstr_get(x_15, 1);
lean::inc(x_16);
x_17 = l_Array_toList___rarg(x_16);
lean::dec(x_16);
x_18 = l_List_toString___at_Lean_Environment_displayStats___spec__1(x_17);
x_19 = l_Lean_Environment_displayStats___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean::dec(x_18);
x_21 = l_IO_println___at_HasRepr_HasEval___spec__1(x_20, x_4);
lean::dec(x_20);
if (lean::obj_tag(x_21) == 0)
{
uint8 x_22; 
x_22 = !lean::is_exclusive(x_21);
if (x_22 == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_23 = lean::cnstr_get(x_21, 0);
lean::dec(x_23);
lean::cnstr_set(x_21, 0, x_7);
x_24 = l_Nat_repr(x_14);
x_25 = l_Lean_Environment_displayStats___closed__2;
x_26 = lean_string_append(x_25, x_24);
lean::dec(x_24);
x_27 = l_IO_println___at_HasRepr_HasEval___spec__1(x_26, x_21);
lean::dec(x_26);
if (lean::obj_tag(x_27) == 0)
{
uint8 x_28; 
x_28 = !lean::is_exclusive(x_27);
if (x_28 == 0)
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_29 = lean::cnstr_get(x_27, 0);
lean::dec(x_29);
lean::cnstr_set(x_27, 0, x_7);
x_30 = lean::cnstr_get(x_1, 1);
lean::inc(x_30);
x_31 = l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3(x_30);
x_32 = l_Nat_repr(x_31);
x_33 = l_Lean_Environment_displayStats___closed__3;
x_34 = lean_string_append(x_33, x_32);
lean::dec(x_32);
x_35 = l_IO_println___at_HasRepr_HasEval___spec__1(x_34, x_27);
lean::dec(x_34);
if (lean::obj_tag(x_35) == 0)
{
uint8 x_36; 
x_36 = !lean::is_exclusive(x_35);
if (x_36 == 0)
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_37 = lean::cnstr_get(x_35, 0);
lean::dec(x_37);
lean::cnstr_set(x_35, 0, x_7);
x_38 = l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4(x_30);
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_40 = l_Nat_repr(x_39);
x_41 = l_Lean_Environment_displayStats___closed__4;
x_42 = lean_string_append(x_41, x_40);
lean::dec(x_40);
x_43 = l_IO_println___at_HasRepr_HasEval___spec__1(x_42, x_35);
lean::dec(x_42);
if (lean::obj_tag(x_43) == 0)
{
uint8 x_44; 
x_44 = !lean::is_exclusive(x_43);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_45 = lean::cnstr_get(x_43, 0);
lean::dec(x_45);
lean::cnstr_set(x_43, 0, x_7);
x_46 = lean::cnstr_get(x_38, 1);
lean::inc(x_46);
lean::dec(x_38);
x_47 = l_Nat_repr(x_46);
x_48 = l_Lean_Environment_displayStats___closed__5;
x_49 = lean_string_append(x_48, x_47);
lean::dec(x_47);
x_50 = l_IO_println___at_HasRepr_HasEval___spec__1(x_49, x_43);
lean::dec(x_49);
if (lean::obj_tag(x_50) == 0)
{
uint8 x_51; 
x_51 = !lean::is_exclusive(x_50);
if (x_51 == 0)
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_52 = lean::cnstr_get(x_50, 0);
lean::dec(x_52);
lean::cnstr_set(x_50, 0, x_7);
x_53 = l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(x_30);
x_54 = l_Nat_repr(x_53);
x_55 = l_Lean_Environment_displayStats___closed__6;
x_56 = lean_string_append(x_55, x_54);
lean::dec(x_54);
x_57 = l_IO_println___at_HasRepr_HasEval___spec__1(x_56, x_50);
lean::dec(x_56);
if (lean::obj_tag(x_57) == 0)
{
uint8 x_58; 
x_58 = !lean::is_exclusive(x_57);
if (x_58 == 0)
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_59 = lean::cnstr_get(x_57, 0);
lean::dec(x_59);
lean::cnstr_set(x_57, 0, x_7);
x_60 = l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(x_30);
lean::dec(x_30);
x_61 = l_Nat_repr(x_60);
x_62 = l_Lean_Environment_displayStats___closed__7;
x_63 = lean_string_append(x_62, x_61);
lean::dec(x_61);
x_64 = l_IO_println___at_HasRepr_HasEval___spec__1(x_63, x_57);
lean::dec(x_63);
if (lean::obj_tag(x_64) == 0)
{
uint8 x_65; 
x_65 = !lean::is_exclusive(x_64);
if (x_65 == 0)
{
obj* x_66; uint32 x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
x_66 = lean::cnstr_get(x_64, 0);
lean::dec(x_66);
lean::cnstr_set(x_64, 0, x_7);
x_67 = lean::cnstr_get_uint32(x_15, sizeof(void*)*2);
lean::dec(x_15);
x_68 = lean_uint32_to_nat(x_67);
x_69 = l_Nat_repr(x_68);
x_70 = l_Lean_Environment_displayStats___closed__8;
x_71 = lean_string_append(x_70, x_69);
lean::dec(x_69);
x_72 = l_IO_println___at_HasRepr_HasEval___spec__1(x_71, x_64);
lean::dec(x_71);
if (lean::obj_tag(x_72) == 0)
{
uint8 x_73; 
x_73 = !lean::is_exclusive(x_72);
if (x_73 == 0)
{
obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_74 = lean::cnstr_get(x_72, 0);
lean::dec(x_74);
lean::cnstr_set(x_72, 0, x_7);
x_75 = lean::cnstr_get(x_1, 2);
lean::inc(x_75);
x_76 = lean_array_get_size(x_75);
lean::dec(x_75);
x_77 = l_Nat_repr(x_76);
x_78 = l_Lean_Environment_displayStats___closed__9;
x_79 = lean_string_append(x_78, x_77);
lean::dec(x_77);
x_80 = l_IO_println___at_HasRepr_HasEval___spec__1(x_79, x_72);
lean::dec(x_79);
if (lean::obj_tag(x_80) == 0)
{
uint8 x_81; 
x_81 = !lean::is_exclusive(x_80);
if (x_81 == 0)
{
obj* x_82; obj* x_83; 
x_82 = lean::cnstr_get(x_80, 0);
lean::dec(x_82);
lean::cnstr_set(x_80, 0, x_7);
x_83 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10(x_1, x_6, x_9, x_80);
lean::dec(x_6);
lean::dec(x_1);
if (lean::obj_tag(x_83) == 0)
{
uint8 x_84; 
x_84 = !lean::is_exclusive(x_83);
if (x_84 == 0)
{
obj* x_85; 
x_85 = lean::cnstr_get(x_83, 0);
lean::dec(x_85);
lean::cnstr_set(x_83, 0, x_7);
return x_83;
}
else
{
obj* x_86; obj* x_87; 
x_86 = lean::cnstr_get(x_83, 1);
lean::inc(x_86);
lean::dec(x_83);
x_87 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_87, 0, x_7);
lean::cnstr_set(x_87, 1, x_86);
return x_87;
}
}
else
{
uint8 x_88; 
x_88 = !lean::is_exclusive(x_83);
if (x_88 == 0)
{
return x_83;
}
else
{
obj* x_89; obj* x_90; obj* x_91; 
x_89 = lean::cnstr_get(x_83, 0);
x_90 = lean::cnstr_get(x_83, 1);
lean::inc(x_90);
lean::inc(x_89);
lean::dec(x_83);
x_91 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_91, 0, x_89);
lean::cnstr_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
obj* x_92; obj* x_93; obj* x_94; 
x_92 = lean::cnstr_get(x_80, 1);
lean::inc(x_92);
lean::dec(x_80);
x_93 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_93, 0, x_7);
lean::cnstr_set(x_93, 1, x_92);
x_94 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10(x_1, x_6, x_9, x_93);
lean::dec(x_6);
lean::dec(x_1);
if (lean::obj_tag(x_94) == 0)
{
obj* x_95; obj* x_96; obj* x_97; 
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
lean::cnstr_set(x_97, 0, x_7);
lean::cnstr_set(x_97, 1, x_95);
return x_97;
}
else
{
obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_98 = lean::cnstr_get(x_94, 0);
lean::inc(x_98);
x_99 = lean::cnstr_get(x_94, 1);
lean::inc(x_99);
if (lean::is_exclusive(x_94)) {
 lean::cnstr_release(x_94, 0);
 lean::cnstr_release(x_94, 1);
 x_100 = x_94;
} else {
 lean::dec_ref(x_94);
 x_100 = lean::box(0);
}
if (lean::is_scalar(x_100)) {
 x_101 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_101 = x_100;
}
lean::cnstr_set(x_101, 0, x_98);
lean::cnstr_set(x_101, 1, x_99);
return x_101;
}
}
}
else
{
uint8 x_102; 
lean::dec(x_6);
lean::dec(x_1);
x_102 = !lean::is_exclusive(x_80);
if (x_102 == 0)
{
return x_80;
}
else
{
obj* x_103; obj* x_104; obj* x_105; 
x_103 = lean::cnstr_get(x_80, 0);
x_104 = lean::cnstr_get(x_80, 1);
lean::inc(x_104);
lean::inc(x_103);
lean::dec(x_80);
x_105 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_105, 0, x_103);
lean::cnstr_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
x_106 = lean::cnstr_get(x_72, 1);
lean::inc(x_106);
lean::dec(x_72);
x_107 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_107, 0, x_7);
lean::cnstr_set(x_107, 1, x_106);
x_108 = lean::cnstr_get(x_1, 2);
lean::inc(x_108);
x_109 = lean_array_get_size(x_108);
lean::dec(x_108);
x_110 = l_Nat_repr(x_109);
x_111 = l_Lean_Environment_displayStats___closed__9;
x_112 = lean_string_append(x_111, x_110);
lean::dec(x_110);
x_113 = l_IO_println___at_HasRepr_HasEval___spec__1(x_112, x_107);
lean::dec(x_112);
if (lean::obj_tag(x_113) == 0)
{
obj* x_114; obj* x_115; obj* x_116; obj* x_117; 
x_114 = lean::cnstr_get(x_113, 1);
lean::inc(x_114);
if (lean::is_exclusive(x_113)) {
 lean::cnstr_release(x_113, 0);
 lean::cnstr_release(x_113, 1);
 x_115 = x_113;
} else {
 lean::dec_ref(x_113);
 x_115 = lean::box(0);
}
if (lean::is_scalar(x_115)) {
 x_116 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_116 = x_115;
}
lean::cnstr_set(x_116, 0, x_7);
lean::cnstr_set(x_116, 1, x_114);
x_117 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10(x_1, x_6, x_9, x_116);
lean::dec(x_6);
lean::dec(x_1);
if (lean::obj_tag(x_117) == 0)
{
obj* x_118; obj* x_119; obj* x_120; 
x_118 = lean::cnstr_get(x_117, 1);
lean::inc(x_118);
if (lean::is_exclusive(x_117)) {
 lean::cnstr_release(x_117, 0);
 lean::cnstr_release(x_117, 1);
 x_119 = x_117;
} else {
 lean::dec_ref(x_117);
 x_119 = lean::box(0);
}
if (lean::is_scalar(x_119)) {
 x_120 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_120 = x_119;
}
lean::cnstr_set(x_120, 0, x_7);
lean::cnstr_set(x_120, 1, x_118);
return x_120;
}
else
{
obj* x_121; obj* x_122; obj* x_123; obj* x_124; 
x_121 = lean::cnstr_get(x_117, 0);
lean::inc(x_121);
x_122 = lean::cnstr_get(x_117, 1);
lean::inc(x_122);
if (lean::is_exclusive(x_117)) {
 lean::cnstr_release(x_117, 0);
 lean::cnstr_release(x_117, 1);
 x_123 = x_117;
} else {
 lean::dec_ref(x_117);
 x_123 = lean::box(0);
}
if (lean::is_scalar(x_123)) {
 x_124 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_124 = x_123;
}
lean::cnstr_set(x_124, 0, x_121);
lean::cnstr_set(x_124, 1, x_122);
return x_124;
}
}
else
{
obj* x_125; obj* x_126; obj* x_127; obj* x_128; 
lean::dec(x_6);
lean::dec(x_1);
x_125 = lean::cnstr_get(x_113, 0);
lean::inc(x_125);
x_126 = lean::cnstr_get(x_113, 1);
lean::inc(x_126);
if (lean::is_exclusive(x_113)) {
 lean::cnstr_release(x_113, 0);
 lean::cnstr_release(x_113, 1);
 x_127 = x_113;
} else {
 lean::dec_ref(x_113);
 x_127 = lean::box(0);
}
if (lean::is_scalar(x_127)) {
 x_128 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_128 = x_127;
}
lean::cnstr_set(x_128, 0, x_125);
lean::cnstr_set(x_128, 1, x_126);
return x_128;
}
}
}
else
{
uint8 x_129; 
lean::dec(x_6);
lean::dec(x_1);
x_129 = !lean::is_exclusive(x_72);
if (x_129 == 0)
{
return x_72;
}
else
{
obj* x_130; obj* x_131; obj* x_132; 
x_130 = lean::cnstr_get(x_72, 0);
x_131 = lean::cnstr_get(x_72, 1);
lean::inc(x_131);
lean::inc(x_130);
lean::dec(x_72);
x_132 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_132, 0, x_130);
lean::cnstr_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
obj* x_133; obj* x_134; uint32 x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; 
x_133 = lean::cnstr_get(x_64, 1);
lean::inc(x_133);
lean::dec(x_64);
x_134 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_134, 0, x_7);
lean::cnstr_set(x_134, 1, x_133);
x_135 = lean::cnstr_get_uint32(x_15, sizeof(void*)*2);
lean::dec(x_15);
x_136 = lean_uint32_to_nat(x_135);
x_137 = l_Nat_repr(x_136);
x_138 = l_Lean_Environment_displayStats___closed__8;
x_139 = lean_string_append(x_138, x_137);
lean::dec(x_137);
x_140 = l_IO_println___at_HasRepr_HasEval___spec__1(x_139, x_134);
lean::dec(x_139);
if (lean::obj_tag(x_140) == 0)
{
obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; 
x_141 = lean::cnstr_get(x_140, 1);
lean::inc(x_141);
if (lean::is_exclusive(x_140)) {
 lean::cnstr_release(x_140, 0);
 lean::cnstr_release(x_140, 1);
 x_142 = x_140;
} else {
 lean::dec_ref(x_140);
 x_142 = lean::box(0);
}
if (lean::is_scalar(x_142)) {
 x_143 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_143 = x_142;
}
lean::cnstr_set(x_143, 0, x_7);
lean::cnstr_set(x_143, 1, x_141);
x_144 = lean::cnstr_get(x_1, 2);
lean::inc(x_144);
x_145 = lean_array_get_size(x_144);
lean::dec(x_144);
x_146 = l_Nat_repr(x_145);
x_147 = l_Lean_Environment_displayStats___closed__9;
x_148 = lean_string_append(x_147, x_146);
lean::dec(x_146);
x_149 = l_IO_println___at_HasRepr_HasEval___spec__1(x_148, x_143);
lean::dec(x_148);
if (lean::obj_tag(x_149) == 0)
{
obj* x_150; obj* x_151; obj* x_152; obj* x_153; 
x_150 = lean::cnstr_get(x_149, 1);
lean::inc(x_150);
if (lean::is_exclusive(x_149)) {
 lean::cnstr_release(x_149, 0);
 lean::cnstr_release(x_149, 1);
 x_151 = x_149;
} else {
 lean::dec_ref(x_149);
 x_151 = lean::box(0);
}
if (lean::is_scalar(x_151)) {
 x_152 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_152 = x_151;
}
lean::cnstr_set(x_152, 0, x_7);
lean::cnstr_set(x_152, 1, x_150);
x_153 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10(x_1, x_6, x_9, x_152);
lean::dec(x_6);
lean::dec(x_1);
if (lean::obj_tag(x_153) == 0)
{
obj* x_154; obj* x_155; obj* x_156; 
x_154 = lean::cnstr_get(x_153, 1);
lean::inc(x_154);
if (lean::is_exclusive(x_153)) {
 lean::cnstr_release(x_153, 0);
 lean::cnstr_release(x_153, 1);
 x_155 = x_153;
} else {
 lean::dec_ref(x_153);
 x_155 = lean::box(0);
}
if (lean::is_scalar(x_155)) {
 x_156 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_156 = x_155;
}
lean::cnstr_set(x_156, 0, x_7);
lean::cnstr_set(x_156, 1, x_154);
return x_156;
}
else
{
obj* x_157; obj* x_158; obj* x_159; obj* x_160; 
x_157 = lean::cnstr_get(x_153, 0);
lean::inc(x_157);
x_158 = lean::cnstr_get(x_153, 1);
lean::inc(x_158);
if (lean::is_exclusive(x_153)) {
 lean::cnstr_release(x_153, 0);
 lean::cnstr_release(x_153, 1);
 x_159 = x_153;
} else {
 lean::dec_ref(x_153);
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
lean::dec(x_6);
lean::dec(x_1);
x_161 = lean::cnstr_get(x_149, 0);
lean::inc(x_161);
x_162 = lean::cnstr_get(x_149, 1);
lean::inc(x_162);
if (lean::is_exclusive(x_149)) {
 lean::cnstr_release(x_149, 0);
 lean::cnstr_release(x_149, 1);
 x_163 = x_149;
} else {
 lean::dec_ref(x_149);
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
else
{
obj* x_165; obj* x_166; obj* x_167; obj* x_168; 
lean::dec(x_6);
lean::dec(x_1);
x_165 = lean::cnstr_get(x_140, 0);
lean::inc(x_165);
x_166 = lean::cnstr_get(x_140, 1);
lean::inc(x_166);
if (lean::is_exclusive(x_140)) {
 lean::cnstr_release(x_140, 0);
 lean::cnstr_release(x_140, 1);
 x_167 = x_140;
} else {
 lean::dec_ref(x_140);
 x_167 = lean::box(0);
}
if (lean::is_scalar(x_167)) {
 x_168 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_168 = x_167;
}
lean::cnstr_set(x_168, 0, x_165);
lean::cnstr_set(x_168, 1, x_166);
return x_168;
}
}
}
else
{
uint8 x_169; 
lean::dec(x_15);
lean::dec(x_6);
lean::dec(x_1);
x_169 = !lean::is_exclusive(x_64);
if (x_169 == 0)
{
return x_64;
}
else
{
obj* x_170; obj* x_171; obj* x_172; 
x_170 = lean::cnstr_get(x_64, 0);
x_171 = lean::cnstr_get(x_64, 1);
lean::inc(x_171);
lean::inc(x_170);
lean::dec(x_64);
x_172 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_172, 0, x_170);
lean::cnstr_set(x_172, 1, x_171);
return x_172;
}
}
}
else
{
obj* x_173; obj* x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; 
x_173 = lean::cnstr_get(x_57, 1);
lean::inc(x_173);
lean::dec(x_57);
x_174 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_174, 0, x_7);
lean::cnstr_set(x_174, 1, x_173);
x_175 = l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(x_30);
lean::dec(x_30);
x_176 = l_Nat_repr(x_175);
x_177 = l_Lean_Environment_displayStats___closed__7;
x_178 = lean_string_append(x_177, x_176);
lean::dec(x_176);
x_179 = l_IO_println___at_HasRepr_HasEval___spec__1(x_178, x_174);
lean::dec(x_178);
if (lean::obj_tag(x_179) == 0)
{
obj* x_180; obj* x_181; obj* x_182; uint32 x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; 
x_180 = lean::cnstr_get(x_179, 1);
lean::inc(x_180);
if (lean::is_exclusive(x_179)) {
 lean::cnstr_release(x_179, 0);
 lean::cnstr_release(x_179, 1);
 x_181 = x_179;
} else {
 lean::dec_ref(x_179);
 x_181 = lean::box(0);
}
if (lean::is_scalar(x_181)) {
 x_182 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_182 = x_181;
}
lean::cnstr_set(x_182, 0, x_7);
lean::cnstr_set(x_182, 1, x_180);
x_183 = lean::cnstr_get_uint32(x_15, sizeof(void*)*2);
lean::dec(x_15);
x_184 = lean_uint32_to_nat(x_183);
x_185 = l_Nat_repr(x_184);
x_186 = l_Lean_Environment_displayStats___closed__8;
x_187 = lean_string_append(x_186, x_185);
lean::dec(x_185);
x_188 = l_IO_println___at_HasRepr_HasEval___spec__1(x_187, x_182);
lean::dec(x_187);
if (lean::obj_tag(x_188) == 0)
{
obj* x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; obj* x_196; obj* x_197; 
x_189 = lean::cnstr_get(x_188, 1);
lean::inc(x_189);
if (lean::is_exclusive(x_188)) {
 lean::cnstr_release(x_188, 0);
 lean::cnstr_release(x_188, 1);
 x_190 = x_188;
} else {
 lean::dec_ref(x_188);
 x_190 = lean::box(0);
}
if (lean::is_scalar(x_190)) {
 x_191 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_191 = x_190;
}
lean::cnstr_set(x_191, 0, x_7);
lean::cnstr_set(x_191, 1, x_189);
x_192 = lean::cnstr_get(x_1, 2);
lean::inc(x_192);
x_193 = lean_array_get_size(x_192);
lean::dec(x_192);
x_194 = l_Nat_repr(x_193);
x_195 = l_Lean_Environment_displayStats___closed__9;
x_196 = lean_string_append(x_195, x_194);
lean::dec(x_194);
x_197 = l_IO_println___at_HasRepr_HasEval___spec__1(x_196, x_191);
lean::dec(x_196);
if (lean::obj_tag(x_197) == 0)
{
obj* x_198; obj* x_199; obj* x_200; obj* x_201; 
x_198 = lean::cnstr_get(x_197, 1);
lean::inc(x_198);
if (lean::is_exclusive(x_197)) {
 lean::cnstr_release(x_197, 0);
 lean::cnstr_release(x_197, 1);
 x_199 = x_197;
} else {
 lean::dec_ref(x_197);
 x_199 = lean::box(0);
}
if (lean::is_scalar(x_199)) {
 x_200 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_200 = x_199;
}
lean::cnstr_set(x_200, 0, x_7);
lean::cnstr_set(x_200, 1, x_198);
x_201 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10(x_1, x_6, x_9, x_200);
lean::dec(x_6);
lean::dec(x_1);
if (lean::obj_tag(x_201) == 0)
{
obj* x_202; obj* x_203; obj* x_204; 
x_202 = lean::cnstr_get(x_201, 1);
lean::inc(x_202);
if (lean::is_exclusive(x_201)) {
 lean::cnstr_release(x_201, 0);
 lean::cnstr_release(x_201, 1);
 x_203 = x_201;
} else {
 lean::dec_ref(x_201);
 x_203 = lean::box(0);
}
if (lean::is_scalar(x_203)) {
 x_204 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_204 = x_203;
}
lean::cnstr_set(x_204, 0, x_7);
lean::cnstr_set(x_204, 1, x_202);
return x_204;
}
else
{
obj* x_205; obj* x_206; obj* x_207; obj* x_208; 
x_205 = lean::cnstr_get(x_201, 0);
lean::inc(x_205);
x_206 = lean::cnstr_get(x_201, 1);
lean::inc(x_206);
if (lean::is_exclusive(x_201)) {
 lean::cnstr_release(x_201, 0);
 lean::cnstr_release(x_201, 1);
 x_207 = x_201;
} else {
 lean::dec_ref(x_201);
 x_207 = lean::box(0);
}
if (lean::is_scalar(x_207)) {
 x_208 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_208 = x_207;
}
lean::cnstr_set(x_208, 0, x_205);
lean::cnstr_set(x_208, 1, x_206);
return x_208;
}
}
else
{
obj* x_209; obj* x_210; obj* x_211; obj* x_212; 
lean::dec(x_6);
lean::dec(x_1);
x_209 = lean::cnstr_get(x_197, 0);
lean::inc(x_209);
x_210 = lean::cnstr_get(x_197, 1);
lean::inc(x_210);
if (lean::is_exclusive(x_197)) {
 lean::cnstr_release(x_197, 0);
 lean::cnstr_release(x_197, 1);
 x_211 = x_197;
} else {
 lean::dec_ref(x_197);
 x_211 = lean::box(0);
}
if (lean::is_scalar(x_211)) {
 x_212 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_212 = x_211;
}
lean::cnstr_set(x_212, 0, x_209);
lean::cnstr_set(x_212, 1, x_210);
return x_212;
}
}
else
{
obj* x_213; obj* x_214; obj* x_215; obj* x_216; 
lean::dec(x_6);
lean::dec(x_1);
x_213 = lean::cnstr_get(x_188, 0);
lean::inc(x_213);
x_214 = lean::cnstr_get(x_188, 1);
lean::inc(x_214);
if (lean::is_exclusive(x_188)) {
 lean::cnstr_release(x_188, 0);
 lean::cnstr_release(x_188, 1);
 x_215 = x_188;
} else {
 lean::dec_ref(x_188);
 x_215 = lean::box(0);
}
if (lean::is_scalar(x_215)) {
 x_216 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_216 = x_215;
}
lean::cnstr_set(x_216, 0, x_213);
lean::cnstr_set(x_216, 1, x_214);
return x_216;
}
}
else
{
obj* x_217; obj* x_218; obj* x_219; obj* x_220; 
lean::dec(x_15);
lean::dec(x_6);
lean::dec(x_1);
x_217 = lean::cnstr_get(x_179, 0);
lean::inc(x_217);
x_218 = lean::cnstr_get(x_179, 1);
lean::inc(x_218);
if (lean::is_exclusive(x_179)) {
 lean::cnstr_release(x_179, 0);
 lean::cnstr_release(x_179, 1);
 x_219 = x_179;
} else {
 lean::dec_ref(x_179);
 x_219 = lean::box(0);
}
if (lean::is_scalar(x_219)) {
 x_220 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_220 = x_219;
}
lean::cnstr_set(x_220, 0, x_217);
lean::cnstr_set(x_220, 1, x_218);
return x_220;
}
}
}
else
{
uint8 x_221; 
lean::dec(x_30);
lean::dec(x_15);
lean::dec(x_6);
lean::dec(x_1);
x_221 = !lean::is_exclusive(x_57);
if (x_221 == 0)
{
return x_57;
}
else
{
obj* x_222; obj* x_223; obj* x_224; 
x_222 = lean::cnstr_get(x_57, 0);
x_223 = lean::cnstr_get(x_57, 1);
lean::inc(x_223);
lean::inc(x_222);
lean::dec(x_57);
x_224 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_224, 0, x_222);
lean::cnstr_set(x_224, 1, x_223);
return x_224;
}
}
}
else
{
obj* x_225; obj* x_226; obj* x_227; obj* x_228; obj* x_229; obj* x_230; obj* x_231; 
x_225 = lean::cnstr_get(x_50, 1);
lean::inc(x_225);
lean::dec(x_50);
x_226 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_226, 0, x_7);
lean::cnstr_set(x_226, 1, x_225);
x_227 = l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(x_30);
x_228 = l_Nat_repr(x_227);
x_229 = l_Lean_Environment_displayStats___closed__6;
x_230 = lean_string_append(x_229, x_228);
lean::dec(x_228);
x_231 = l_IO_println___at_HasRepr_HasEval___spec__1(x_230, x_226);
lean::dec(x_230);
if (lean::obj_tag(x_231) == 0)
{
obj* x_232; obj* x_233; obj* x_234; obj* x_235; obj* x_236; obj* x_237; obj* x_238; obj* x_239; 
x_232 = lean::cnstr_get(x_231, 1);
lean::inc(x_232);
if (lean::is_exclusive(x_231)) {
 lean::cnstr_release(x_231, 0);
 lean::cnstr_release(x_231, 1);
 x_233 = x_231;
} else {
 lean::dec_ref(x_231);
 x_233 = lean::box(0);
}
if (lean::is_scalar(x_233)) {
 x_234 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_234 = x_233;
}
lean::cnstr_set(x_234, 0, x_7);
lean::cnstr_set(x_234, 1, x_232);
x_235 = l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(x_30);
lean::dec(x_30);
x_236 = l_Nat_repr(x_235);
x_237 = l_Lean_Environment_displayStats___closed__7;
x_238 = lean_string_append(x_237, x_236);
lean::dec(x_236);
x_239 = l_IO_println___at_HasRepr_HasEval___spec__1(x_238, x_234);
lean::dec(x_238);
if (lean::obj_tag(x_239) == 0)
{
obj* x_240; obj* x_241; obj* x_242; uint32 x_243; obj* x_244; obj* x_245; obj* x_246; obj* x_247; obj* x_248; 
x_240 = lean::cnstr_get(x_239, 1);
lean::inc(x_240);
if (lean::is_exclusive(x_239)) {
 lean::cnstr_release(x_239, 0);
 lean::cnstr_release(x_239, 1);
 x_241 = x_239;
} else {
 lean::dec_ref(x_239);
 x_241 = lean::box(0);
}
if (lean::is_scalar(x_241)) {
 x_242 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_242 = x_241;
}
lean::cnstr_set(x_242, 0, x_7);
lean::cnstr_set(x_242, 1, x_240);
x_243 = lean::cnstr_get_uint32(x_15, sizeof(void*)*2);
lean::dec(x_15);
x_244 = lean_uint32_to_nat(x_243);
x_245 = l_Nat_repr(x_244);
x_246 = l_Lean_Environment_displayStats___closed__8;
x_247 = lean_string_append(x_246, x_245);
lean::dec(x_245);
x_248 = l_IO_println___at_HasRepr_HasEval___spec__1(x_247, x_242);
lean::dec(x_247);
if (lean::obj_tag(x_248) == 0)
{
obj* x_249; obj* x_250; obj* x_251; obj* x_252; obj* x_253; obj* x_254; obj* x_255; obj* x_256; obj* x_257; 
x_249 = lean::cnstr_get(x_248, 1);
lean::inc(x_249);
if (lean::is_exclusive(x_248)) {
 lean::cnstr_release(x_248, 0);
 lean::cnstr_release(x_248, 1);
 x_250 = x_248;
} else {
 lean::dec_ref(x_248);
 x_250 = lean::box(0);
}
if (lean::is_scalar(x_250)) {
 x_251 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_251 = x_250;
}
lean::cnstr_set(x_251, 0, x_7);
lean::cnstr_set(x_251, 1, x_249);
x_252 = lean::cnstr_get(x_1, 2);
lean::inc(x_252);
x_253 = lean_array_get_size(x_252);
lean::dec(x_252);
x_254 = l_Nat_repr(x_253);
x_255 = l_Lean_Environment_displayStats___closed__9;
x_256 = lean_string_append(x_255, x_254);
lean::dec(x_254);
x_257 = l_IO_println___at_HasRepr_HasEval___spec__1(x_256, x_251);
lean::dec(x_256);
if (lean::obj_tag(x_257) == 0)
{
obj* x_258; obj* x_259; obj* x_260; obj* x_261; 
x_258 = lean::cnstr_get(x_257, 1);
lean::inc(x_258);
if (lean::is_exclusive(x_257)) {
 lean::cnstr_release(x_257, 0);
 lean::cnstr_release(x_257, 1);
 x_259 = x_257;
} else {
 lean::dec_ref(x_257);
 x_259 = lean::box(0);
}
if (lean::is_scalar(x_259)) {
 x_260 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_260 = x_259;
}
lean::cnstr_set(x_260, 0, x_7);
lean::cnstr_set(x_260, 1, x_258);
x_261 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10(x_1, x_6, x_9, x_260);
lean::dec(x_6);
lean::dec(x_1);
if (lean::obj_tag(x_261) == 0)
{
obj* x_262; obj* x_263; obj* x_264; 
x_262 = lean::cnstr_get(x_261, 1);
lean::inc(x_262);
if (lean::is_exclusive(x_261)) {
 lean::cnstr_release(x_261, 0);
 lean::cnstr_release(x_261, 1);
 x_263 = x_261;
} else {
 lean::dec_ref(x_261);
 x_263 = lean::box(0);
}
if (lean::is_scalar(x_263)) {
 x_264 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_264 = x_263;
}
lean::cnstr_set(x_264, 0, x_7);
lean::cnstr_set(x_264, 1, x_262);
return x_264;
}
else
{
obj* x_265; obj* x_266; obj* x_267; obj* x_268; 
x_265 = lean::cnstr_get(x_261, 0);
lean::inc(x_265);
x_266 = lean::cnstr_get(x_261, 1);
lean::inc(x_266);
if (lean::is_exclusive(x_261)) {
 lean::cnstr_release(x_261, 0);
 lean::cnstr_release(x_261, 1);
 x_267 = x_261;
} else {
 lean::dec_ref(x_261);
 x_267 = lean::box(0);
}
if (lean::is_scalar(x_267)) {
 x_268 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_268 = x_267;
}
lean::cnstr_set(x_268, 0, x_265);
lean::cnstr_set(x_268, 1, x_266);
return x_268;
}
}
else
{
obj* x_269; obj* x_270; obj* x_271; obj* x_272; 
lean::dec(x_6);
lean::dec(x_1);
x_269 = lean::cnstr_get(x_257, 0);
lean::inc(x_269);
x_270 = lean::cnstr_get(x_257, 1);
lean::inc(x_270);
if (lean::is_exclusive(x_257)) {
 lean::cnstr_release(x_257, 0);
 lean::cnstr_release(x_257, 1);
 x_271 = x_257;
} else {
 lean::dec_ref(x_257);
 x_271 = lean::box(0);
}
if (lean::is_scalar(x_271)) {
 x_272 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_272 = x_271;
}
lean::cnstr_set(x_272, 0, x_269);
lean::cnstr_set(x_272, 1, x_270);
return x_272;
}
}
else
{
obj* x_273; obj* x_274; obj* x_275; obj* x_276; 
lean::dec(x_6);
lean::dec(x_1);
x_273 = lean::cnstr_get(x_248, 0);
lean::inc(x_273);
x_274 = lean::cnstr_get(x_248, 1);
lean::inc(x_274);
if (lean::is_exclusive(x_248)) {
 lean::cnstr_release(x_248, 0);
 lean::cnstr_release(x_248, 1);
 x_275 = x_248;
} else {
 lean::dec_ref(x_248);
 x_275 = lean::box(0);
}
if (lean::is_scalar(x_275)) {
 x_276 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_276 = x_275;
}
lean::cnstr_set(x_276, 0, x_273);
lean::cnstr_set(x_276, 1, x_274);
return x_276;
}
}
else
{
obj* x_277; obj* x_278; obj* x_279; obj* x_280; 
lean::dec(x_15);
lean::dec(x_6);
lean::dec(x_1);
x_277 = lean::cnstr_get(x_239, 0);
lean::inc(x_277);
x_278 = lean::cnstr_get(x_239, 1);
lean::inc(x_278);
if (lean::is_exclusive(x_239)) {
 lean::cnstr_release(x_239, 0);
 lean::cnstr_release(x_239, 1);
 x_279 = x_239;
} else {
 lean::dec_ref(x_239);
 x_279 = lean::box(0);
}
if (lean::is_scalar(x_279)) {
 x_280 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_280 = x_279;
}
lean::cnstr_set(x_280, 0, x_277);
lean::cnstr_set(x_280, 1, x_278);
return x_280;
}
}
else
{
obj* x_281; obj* x_282; obj* x_283; obj* x_284; 
lean::dec(x_30);
lean::dec(x_15);
lean::dec(x_6);
lean::dec(x_1);
x_281 = lean::cnstr_get(x_231, 0);
lean::inc(x_281);
x_282 = lean::cnstr_get(x_231, 1);
lean::inc(x_282);
if (lean::is_exclusive(x_231)) {
 lean::cnstr_release(x_231, 0);
 lean::cnstr_release(x_231, 1);
 x_283 = x_231;
} else {
 lean::dec_ref(x_231);
 x_283 = lean::box(0);
}
if (lean::is_scalar(x_283)) {
 x_284 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_284 = x_283;
}
lean::cnstr_set(x_284, 0, x_281);
lean::cnstr_set(x_284, 1, x_282);
return x_284;
}
}
}
else
{
uint8 x_285; 
lean::dec(x_30);
lean::dec(x_15);
lean::dec(x_6);
lean::dec(x_1);
x_285 = !lean::is_exclusive(x_50);
if (x_285 == 0)
{
return x_50;
}
else
{
obj* x_286; obj* x_287; obj* x_288; 
x_286 = lean::cnstr_get(x_50, 0);
x_287 = lean::cnstr_get(x_50, 1);
lean::inc(x_287);
lean::inc(x_286);
lean::dec(x_50);
x_288 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_288, 0, x_286);
lean::cnstr_set(x_288, 1, x_287);
return x_288;
}
}
}
else
{
obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; obj* x_294; obj* x_295; 
x_289 = lean::cnstr_get(x_43, 1);
lean::inc(x_289);
lean::dec(x_43);
x_290 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_290, 0, x_7);
lean::cnstr_set(x_290, 1, x_289);
x_291 = lean::cnstr_get(x_38, 1);
lean::inc(x_291);
lean::dec(x_38);
x_292 = l_Nat_repr(x_291);
x_293 = l_Lean_Environment_displayStats___closed__5;
x_294 = lean_string_append(x_293, x_292);
lean::dec(x_292);
x_295 = l_IO_println___at_HasRepr_HasEval___spec__1(x_294, x_290);
lean::dec(x_294);
if (lean::obj_tag(x_295) == 0)
{
obj* x_296; obj* x_297; obj* x_298; obj* x_299; obj* x_300; obj* x_301; obj* x_302; obj* x_303; 
x_296 = lean::cnstr_get(x_295, 1);
lean::inc(x_296);
if (lean::is_exclusive(x_295)) {
 lean::cnstr_release(x_295, 0);
 lean::cnstr_release(x_295, 1);
 x_297 = x_295;
} else {
 lean::dec_ref(x_295);
 x_297 = lean::box(0);
}
if (lean::is_scalar(x_297)) {
 x_298 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_298 = x_297;
}
lean::cnstr_set(x_298, 0, x_7);
lean::cnstr_set(x_298, 1, x_296);
x_299 = l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(x_30);
x_300 = l_Nat_repr(x_299);
x_301 = l_Lean_Environment_displayStats___closed__6;
x_302 = lean_string_append(x_301, x_300);
lean::dec(x_300);
x_303 = l_IO_println___at_HasRepr_HasEval___spec__1(x_302, x_298);
lean::dec(x_302);
if (lean::obj_tag(x_303) == 0)
{
obj* x_304; obj* x_305; obj* x_306; obj* x_307; obj* x_308; obj* x_309; obj* x_310; obj* x_311; 
x_304 = lean::cnstr_get(x_303, 1);
lean::inc(x_304);
if (lean::is_exclusive(x_303)) {
 lean::cnstr_release(x_303, 0);
 lean::cnstr_release(x_303, 1);
 x_305 = x_303;
} else {
 lean::dec_ref(x_303);
 x_305 = lean::box(0);
}
if (lean::is_scalar(x_305)) {
 x_306 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_306 = x_305;
}
lean::cnstr_set(x_306, 0, x_7);
lean::cnstr_set(x_306, 1, x_304);
x_307 = l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(x_30);
lean::dec(x_30);
x_308 = l_Nat_repr(x_307);
x_309 = l_Lean_Environment_displayStats___closed__7;
x_310 = lean_string_append(x_309, x_308);
lean::dec(x_308);
x_311 = l_IO_println___at_HasRepr_HasEval___spec__1(x_310, x_306);
lean::dec(x_310);
if (lean::obj_tag(x_311) == 0)
{
obj* x_312; obj* x_313; obj* x_314; uint32 x_315; obj* x_316; obj* x_317; obj* x_318; obj* x_319; obj* x_320; 
x_312 = lean::cnstr_get(x_311, 1);
lean::inc(x_312);
if (lean::is_exclusive(x_311)) {
 lean::cnstr_release(x_311, 0);
 lean::cnstr_release(x_311, 1);
 x_313 = x_311;
} else {
 lean::dec_ref(x_311);
 x_313 = lean::box(0);
}
if (lean::is_scalar(x_313)) {
 x_314 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_314 = x_313;
}
lean::cnstr_set(x_314, 0, x_7);
lean::cnstr_set(x_314, 1, x_312);
x_315 = lean::cnstr_get_uint32(x_15, sizeof(void*)*2);
lean::dec(x_15);
x_316 = lean_uint32_to_nat(x_315);
x_317 = l_Nat_repr(x_316);
x_318 = l_Lean_Environment_displayStats___closed__8;
x_319 = lean_string_append(x_318, x_317);
lean::dec(x_317);
x_320 = l_IO_println___at_HasRepr_HasEval___spec__1(x_319, x_314);
lean::dec(x_319);
if (lean::obj_tag(x_320) == 0)
{
obj* x_321; obj* x_322; obj* x_323; obj* x_324; obj* x_325; obj* x_326; obj* x_327; obj* x_328; obj* x_329; 
x_321 = lean::cnstr_get(x_320, 1);
lean::inc(x_321);
if (lean::is_exclusive(x_320)) {
 lean::cnstr_release(x_320, 0);
 lean::cnstr_release(x_320, 1);
 x_322 = x_320;
} else {
 lean::dec_ref(x_320);
 x_322 = lean::box(0);
}
if (lean::is_scalar(x_322)) {
 x_323 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_323 = x_322;
}
lean::cnstr_set(x_323, 0, x_7);
lean::cnstr_set(x_323, 1, x_321);
x_324 = lean::cnstr_get(x_1, 2);
lean::inc(x_324);
x_325 = lean_array_get_size(x_324);
lean::dec(x_324);
x_326 = l_Nat_repr(x_325);
x_327 = l_Lean_Environment_displayStats___closed__9;
x_328 = lean_string_append(x_327, x_326);
lean::dec(x_326);
x_329 = l_IO_println___at_HasRepr_HasEval___spec__1(x_328, x_323);
lean::dec(x_328);
if (lean::obj_tag(x_329) == 0)
{
obj* x_330; obj* x_331; obj* x_332; obj* x_333; 
x_330 = lean::cnstr_get(x_329, 1);
lean::inc(x_330);
if (lean::is_exclusive(x_329)) {
 lean::cnstr_release(x_329, 0);
 lean::cnstr_release(x_329, 1);
 x_331 = x_329;
} else {
 lean::dec_ref(x_329);
 x_331 = lean::box(0);
}
if (lean::is_scalar(x_331)) {
 x_332 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_332 = x_331;
}
lean::cnstr_set(x_332, 0, x_7);
lean::cnstr_set(x_332, 1, x_330);
x_333 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10(x_1, x_6, x_9, x_332);
lean::dec(x_6);
lean::dec(x_1);
if (lean::obj_tag(x_333) == 0)
{
obj* x_334; obj* x_335; obj* x_336; 
x_334 = lean::cnstr_get(x_333, 1);
lean::inc(x_334);
if (lean::is_exclusive(x_333)) {
 lean::cnstr_release(x_333, 0);
 lean::cnstr_release(x_333, 1);
 x_335 = x_333;
} else {
 lean::dec_ref(x_333);
 x_335 = lean::box(0);
}
if (lean::is_scalar(x_335)) {
 x_336 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_336 = x_335;
}
lean::cnstr_set(x_336, 0, x_7);
lean::cnstr_set(x_336, 1, x_334);
return x_336;
}
else
{
obj* x_337; obj* x_338; obj* x_339; obj* x_340; 
x_337 = lean::cnstr_get(x_333, 0);
lean::inc(x_337);
x_338 = lean::cnstr_get(x_333, 1);
lean::inc(x_338);
if (lean::is_exclusive(x_333)) {
 lean::cnstr_release(x_333, 0);
 lean::cnstr_release(x_333, 1);
 x_339 = x_333;
} else {
 lean::dec_ref(x_333);
 x_339 = lean::box(0);
}
if (lean::is_scalar(x_339)) {
 x_340 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_340 = x_339;
}
lean::cnstr_set(x_340, 0, x_337);
lean::cnstr_set(x_340, 1, x_338);
return x_340;
}
}
else
{
obj* x_341; obj* x_342; obj* x_343; obj* x_344; 
lean::dec(x_6);
lean::dec(x_1);
x_341 = lean::cnstr_get(x_329, 0);
lean::inc(x_341);
x_342 = lean::cnstr_get(x_329, 1);
lean::inc(x_342);
if (lean::is_exclusive(x_329)) {
 lean::cnstr_release(x_329, 0);
 lean::cnstr_release(x_329, 1);
 x_343 = x_329;
} else {
 lean::dec_ref(x_329);
 x_343 = lean::box(0);
}
if (lean::is_scalar(x_343)) {
 x_344 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_344 = x_343;
}
lean::cnstr_set(x_344, 0, x_341);
lean::cnstr_set(x_344, 1, x_342);
return x_344;
}
}
else
{
obj* x_345; obj* x_346; obj* x_347; obj* x_348; 
lean::dec(x_6);
lean::dec(x_1);
x_345 = lean::cnstr_get(x_320, 0);
lean::inc(x_345);
x_346 = lean::cnstr_get(x_320, 1);
lean::inc(x_346);
if (lean::is_exclusive(x_320)) {
 lean::cnstr_release(x_320, 0);
 lean::cnstr_release(x_320, 1);
 x_347 = x_320;
} else {
 lean::dec_ref(x_320);
 x_347 = lean::box(0);
}
if (lean::is_scalar(x_347)) {
 x_348 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_348 = x_347;
}
lean::cnstr_set(x_348, 0, x_345);
lean::cnstr_set(x_348, 1, x_346);
return x_348;
}
}
else
{
obj* x_349; obj* x_350; obj* x_351; obj* x_352; 
lean::dec(x_15);
lean::dec(x_6);
lean::dec(x_1);
x_349 = lean::cnstr_get(x_311, 0);
lean::inc(x_349);
x_350 = lean::cnstr_get(x_311, 1);
lean::inc(x_350);
if (lean::is_exclusive(x_311)) {
 lean::cnstr_release(x_311, 0);
 lean::cnstr_release(x_311, 1);
 x_351 = x_311;
} else {
 lean::dec_ref(x_311);
 x_351 = lean::box(0);
}
if (lean::is_scalar(x_351)) {
 x_352 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_352 = x_351;
}
lean::cnstr_set(x_352, 0, x_349);
lean::cnstr_set(x_352, 1, x_350);
return x_352;
}
}
else
{
obj* x_353; obj* x_354; obj* x_355; obj* x_356; 
lean::dec(x_30);
lean::dec(x_15);
lean::dec(x_6);
lean::dec(x_1);
x_353 = lean::cnstr_get(x_303, 0);
lean::inc(x_353);
x_354 = lean::cnstr_get(x_303, 1);
lean::inc(x_354);
if (lean::is_exclusive(x_303)) {
 lean::cnstr_release(x_303, 0);
 lean::cnstr_release(x_303, 1);
 x_355 = x_303;
} else {
 lean::dec_ref(x_303);
 x_355 = lean::box(0);
}
if (lean::is_scalar(x_355)) {
 x_356 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_356 = x_355;
}
lean::cnstr_set(x_356, 0, x_353);
lean::cnstr_set(x_356, 1, x_354);
return x_356;
}
}
else
{
obj* x_357; obj* x_358; obj* x_359; obj* x_360; 
lean::dec(x_30);
lean::dec(x_15);
lean::dec(x_6);
lean::dec(x_1);
x_357 = lean::cnstr_get(x_295, 0);
lean::inc(x_357);
x_358 = lean::cnstr_get(x_295, 1);
lean::inc(x_358);
if (lean::is_exclusive(x_295)) {
 lean::cnstr_release(x_295, 0);
 lean::cnstr_release(x_295, 1);
 x_359 = x_295;
} else {
 lean::dec_ref(x_295);
 x_359 = lean::box(0);
}
if (lean::is_scalar(x_359)) {
 x_360 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_360 = x_359;
}
lean::cnstr_set(x_360, 0, x_357);
lean::cnstr_set(x_360, 1, x_358);
return x_360;
}
}
}
else
{
uint8 x_361; 
lean::dec(x_38);
lean::dec(x_30);
lean::dec(x_15);
lean::dec(x_6);
lean::dec(x_1);
x_361 = !lean::is_exclusive(x_43);
if (x_361 == 0)
{
return x_43;
}
else
{
obj* x_362; obj* x_363; obj* x_364; 
x_362 = lean::cnstr_get(x_43, 0);
x_363 = lean::cnstr_get(x_43, 1);
lean::inc(x_363);
lean::inc(x_362);
lean::dec(x_43);
x_364 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_364, 0, x_362);
lean::cnstr_set(x_364, 1, x_363);
return x_364;
}
}
}
else
{
obj* x_365; obj* x_366; obj* x_367; obj* x_368; obj* x_369; obj* x_370; obj* x_371; obj* x_372; 
x_365 = lean::cnstr_get(x_35, 1);
lean::inc(x_365);
lean::dec(x_35);
x_366 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_366, 0, x_7);
lean::cnstr_set(x_366, 1, x_365);
x_367 = l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4(x_30);
x_368 = lean::cnstr_get(x_367, 0);
lean::inc(x_368);
x_369 = l_Nat_repr(x_368);
x_370 = l_Lean_Environment_displayStats___closed__4;
x_371 = lean_string_append(x_370, x_369);
lean::dec(x_369);
x_372 = l_IO_println___at_HasRepr_HasEval___spec__1(x_371, x_366);
lean::dec(x_371);
if (lean::obj_tag(x_372) == 0)
{
obj* x_373; obj* x_374; obj* x_375; obj* x_376; obj* x_377; obj* x_378; obj* x_379; obj* x_380; 
x_373 = lean::cnstr_get(x_372, 1);
lean::inc(x_373);
if (lean::is_exclusive(x_372)) {
 lean::cnstr_release(x_372, 0);
 lean::cnstr_release(x_372, 1);
 x_374 = x_372;
} else {
 lean::dec_ref(x_372);
 x_374 = lean::box(0);
}
if (lean::is_scalar(x_374)) {
 x_375 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_375 = x_374;
}
lean::cnstr_set(x_375, 0, x_7);
lean::cnstr_set(x_375, 1, x_373);
x_376 = lean::cnstr_get(x_367, 1);
lean::inc(x_376);
lean::dec(x_367);
x_377 = l_Nat_repr(x_376);
x_378 = l_Lean_Environment_displayStats___closed__5;
x_379 = lean_string_append(x_378, x_377);
lean::dec(x_377);
x_380 = l_IO_println___at_HasRepr_HasEval___spec__1(x_379, x_375);
lean::dec(x_379);
if (lean::obj_tag(x_380) == 0)
{
obj* x_381; obj* x_382; obj* x_383; obj* x_384; obj* x_385; obj* x_386; obj* x_387; obj* x_388; 
x_381 = lean::cnstr_get(x_380, 1);
lean::inc(x_381);
if (lean::is_exclusive(x_380)) {
 lean::cnstr_release(x_380, 0);
 lean::cnstr_release(x_380, 1);
 x_382 = x_380;
} else {
 lean::dec_ref(x_380);
 x_382 = lean::box(0);
}
if (lean::is_scalar(x_382)) {
 x_383 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_383 = x_382;
}
lean::cnstr_set(x_383, 0, x_7);
lean::cnstr_set(x_383, 1, x_381);
x_384 = l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(x_30);
x_385 = l_Nat_repr(x_384);
x_386 = l_Lean_Environment_displayStats___closed__6;
x_387 = lean_string_append(x_386, x_385);
lean::dec(x_385);
x_388 = l_IO_println___at_HasRepr_HasEval___spec__1(x_387, x_383);
lean::dec(x_387);
if (lean::obj_tag(x_388) == 0)
{
obj* x_389; obj* x_390; obj* x_391; obj* x_392; obj* x_393; obj* x_394; obj* x_395; obj* x_396; 
x_389 = lean::cnstr_get(x_388, 1);
lean::inc(x_389);
if (lean::is_exclusive(x_388)) {
 lean::cnstr_release(x_388, 0);
 lean::cnstr_release(x_388, 1);
 x_390 = x_388;
} else {
 lean::dec_ref(x_388);
 x_390 = lean::box(0);
}
if (lean::is_scalar(x_390)) {
 x_391 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_391 = x_390;
}
lean::cnstr_set(x_391, 0, x_7);
lean::cnstr_set(x_391, 1, x_389);
x_392 = l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(x_30);
lean::dec(x_30);
x_393 = l_Nat_repr(x_392);
x_394 = l_Lean_Environment_displayStats___closed__7;
x_395 = lean_string_append(x_394, x_393);
lean::dec(x_393);
x_396 = l_IO_println___at_HasRepr_HasEval___spec__1(x_395, x_391);
lean::dec(x_395);
if (lean::obj_tag(x_396) == 0)
{
obj* x_397; obj* x_398; obj* x_399; uint32 x_400; obj* x_401; obj* x_402; obj* x_403; obj* x_404; obj* x_405; 
x_397 = lean::cnstr_get(x_396, 1);
lean::inc(x_397);
if (lean::is_exclusive(x_396)) {
 lean::cnstr_release(x_396, 0);
 lean::cnstr_release(x_396, 1);
 x_398 = x_396;
} else {
 lean::dec_ref(x_396);
 x_398 = lean::box(0);
}
if (lean::is_scalar(x_398)) {
 x_399 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_399 = x_398;
}
lean::cnstr_set(x_399, 0, x_7);
lean::cnstr_set(x_399, 1, x_397);
x_400 = lean::cnstr_get_uint32(x_15, sizeof(void*)*2);
lean::dec(x_15);
x_401 = lean_uint32_to_nat(x_400);
x_402 = l_Nat_repr(x_401);
x_403 = l_Lean_Environment_displayStats___closed__8;
x_404 = lean_string_append(x_403, x_402);
lean::dec(x_402);
x_405 = l_IO_println___at_HasRepr_HasEval___spec__1(x_404, x_399);
lean::dec(x_404);
if (lean::obj_tag(x_405) == 0)
{
obj* x_406; obj* x_407; obj* x_408; obj* x_409; obj* x_410; obj* x_411; obj* x_412; obj* x_413; obj* x_414; 
x_406 = lean::cnstr_get(x_405, 1);
lean::inc(x_406);
if (lean::is_exclusive(x_405)) {
 lean::cnstr_release(x_405, 0);
 lean::cnstr_release(x_405, 1);
 x_407 = x_405;
} else {
 lean::dec_ref(x_405);
 x_407 = lean::box(0);
}
if (lean::is_scalar(x_407)) {
 x_408 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_408 = x_407;
}
lean::cnstr_set(x_408, 0, x_7);
lean::cnstr_set(x_408, 1, x_406);
x_409 = lean::cnstr_get(x_1, 2);
lean::inc(x_409);
x_410 = lean_array_get_size(x_409);
lean::dec(x_409);
x_411 = l_Nat_repr(x_410);
x_412 = l_Lean_Environment_displayStats___closed__9;
x_413 = lean_string_append(x_412, x_411);
lean::dec(x_411);
x_414 = l_IO_println___at_HasRepr_HasEval___spec__1(x_413, x_408);
lean::dec(x_413);
if (lean::obj_tag(x_414) == 0)
{
obj* x_415; obj* x_416; obj* x_417; obj* x_418; 
x_415 = lean::cnstr_get(x_414, 1);
lean::inc(x_415);
if (lean::is_exclusive(x_414)) {
 lean::cnstr_release(x_414, 0);
 lean::cnstr_release(x_414, 1);
 x_416 = x_414;
} else {
 lean::dec_ref(x_414);
 x_416 = lean::box(0);
}
if (lean::is_scalar(x_416)) {
 x_417 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_417 = x_416;
}
lean::cnstr_set(x_417, 0, x_7);
lean::cnstr_set(x_417, 1, x_415);
x_418 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10(x_1, x_6, x_9, x_417);
lean::dec(x_6);
lean::dec(x_1);
if (lean::obj_tag(x_418) == 0)
{
obj* x_419; obj* x_420; obj* x_421; 
x_419 = lean::cnstr_get(x_418, 1);
lean::inc(x_419);
if (lean::is_exclusive(x_418)) {
 lean::cnstr_release(x_418, 0);
 lean::cnstr_release(x_418, 1);
 x_420 = x_418;
} else {
 lean::dec_ref(x_418);
 x_420 = lean::box(0);
}
if (lean::is_scalar(x_420)) {
 x_421 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_421 = x_420;
}
lean::cnstr_set(x_421, 0, x_7);
lean::cnstr_set(x_421, 1, x_419);
return x_421;
}
else
{
obj* x_422; obj* x_423; obj* x_424; obj* x_425; 
x_422 = lean::cnstr_get(x_418, 0);
lean::inc(x_422);
x_423 = lean::cnstr_get(x_418, 1);
lean::inc(x_423);
if (lean::is_exclusive(x_418)) {
 lean::cnstr_release(x_418, 0);
 lean::cnstr_release(x_418, 1);
 x_424 = x_418;
} else {
 lean::dec_ref(x_418);
 x_424 = lean::box(0);
}
if (lean::is_scalar(x_424)) {
 x_425 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_425 = x_424;
}
lean::cnstr_set(x_425, 0, x_422);
lean::cnstr_set(x_425, 1, x_423);
return x_425;
}
}
else
{
obj* x_426; obj* x_427; obj* x_428; obj* x_429; 
lean::dec(x_6);
lean::dec(x_1);
x_426 = lean::cnstr_get(x_414, 0);
lean::inc(x_426);
x_427 = lean::cnstr_get(x_414, 1);
lean::inc(x_427);
if (lean::is_exclusive(x_414)) {
 lean::cnstr_release(x_414, 0);
 lean::cnstr_release(x_414, 1);
 x_428 = x_414;
} else {
 lean::dec_ref(x_414);
 x_428 = lean::box(0);
}
if (lean::is_scalar(x_428)) {
 x_429 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_429 = x_428;
}
lean::cnstr_set(x_429, 0, x_426);
lean::cnstr_set(x_429, 1, x_427);
return x_429;
}
}
else
{
obj* x_430; obj* x_431; obj* x_432; obj* x_433; 
lean::dec(x_6);
lean::dec(x_1);
x_430 = lean::cnstr_get(x_405, 0);
lean::inc(x_430);
x_431 = lean::cnstr_get(x_405, 1);
lean::inc(x_431);
if (lean::is_exclusive(x_405)) {
 lean::cnstr_release(x_405, 0);
 lean::cnstr_release(x_405, 1);
 x_432 = x_405;
} else {
 lean::dec_ref(x_405);
 x_432 = lean::box(0);
}
if (lean::is_scalar(x_432)) {
 x_433 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_433 = x_432;
}
lean::cnstr_set(x_433, 0, x_430);
lean::cnstr_set(x_433, 1, x_431);
return x_433;
}
}
else
{
obj* x_434; obj* x_435; obj* x_436; obj* x_437; 
lean::dec(x_15);
lean::dec(x_6);
lean::dec(x_1);
x_434 = lean::cnstr_get(x_396, 0);
lean::inc(x_434);
x_435 = lean::cnstr_get(x_396, 1);
lean::inc(x_435);
if (lean::is_exclusive(x_396)) {
 lean::cnstr_release(x_396, 0);
 lean::cnstr_release(x_396, 1);
 x_436 = x_396;
} else {
 lean::dec_ref(x_396);
 x_436 = lean::box(0);
}
if (lean::is_scalar(x_436)) {
 x_437 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_437 = x_436;
}
lean::cnstr_set(x_437, 0, x_434);
lean::cnstr_set(x_437, 1, x_435);
return x_437;
}
}
else
{
obj* x_438; obj* x_439; obj* x_440; obj* x_441; 
lean::dec(x_30);
lean::dec(x_15);
lean::dec(x_6);
lean::dec(x_1);
x_438 = lean::cnstr_get(x_388, 0);
lean::inc(x_438);
x_439 = lean::cnstr_get(x_388, 1);
lean::inc(x_439);
if (lean::is_exclusive(x_388)) {
 lean::cnstr_release(x_388, 0);
 lean::cnstr_release(x_388, 1);
 x_440 = x_388;
} else {
 lean::dec_ref(x_388);
 x_440 = lean::box(0);
}
if (lean::is_scalar(x_440)) {
 x_441 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_441 = x_440;
}
lean::cnstr_set(x_441, 0, x_438);
lean::cnstr_set(x_441, 1, x_439);
return x_441;
}
}
else
{
obj* x_442; obj* x_443; obj* x_444; obj* x_445; 
lean::dec(x_30);
lean::dec(x_15);
lean::dec(x_6);
lean::dec(x_1);
x_442 = lean::cnstr_get(x_380, 0);
lean::inc(x_442);
x_443 = lean::cnstr_get(x_380, 1);
lean::inc(x_443);
if (lean::is_exclusive(x_380)) {
 lean::cnstr_release(x_380, 0);
 lean::cnstr_release(x_380, 1);
 x_444 = x_380;
} else {
 lean::dec_ref(x_380);
 x_444 = lean::box(0);
}
if (lean::is_scalar(x_444)) {
 x_445 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_445 = x_444;
}
lean::cnstr_set(x_445, 0, x_442);
lean::cnstr_set(x_445, 1, x_443);
return x_445;
}
}
else
{
obj* x_446; obj* x_447; obj* x_448; obj* x_449; 
lean::dec(x_367);
lean::dec(x_30);
lean::dec(x_15);
lean::dec(x_6);
lean::dec(x_1);
x_446 = lean::cnstr_get(x_372, 0);
lean::inc(x_446);
x_447 = lean::cnstr_get(x_372, 1);
lean::inc(x_447);
if (lean::is_exclusive(x_372)) {
 lean::cnstr_release(x_372, 0);
 lean::cnstr_release(x_372, 1);
 x_448 = x_372;
} else {
 lean::dec_ref(x_372);
 x_448 = lean::box(0);
}
if (lean::is_scalar(x_448)) {
 x_449 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_449 = x_448;
}
lean::cnstr_set(x_449, 0, x_446);
lean::cnstr_set(x_449, 1, x_447);
return x_449;
}
}
}
else
{
uint8 x_450; 
lean::dec(x_30);
lean::dec(x_15);
lean::dec(x_6);
lean::dec(x_1);
x_450 = !lean::is_exclusive(x_35);
if (x_450 == 0)
{
return x_35;
}
else
{
obj* x_451; obj* x_452; obj* x_453; 
x_451 = lean::cnstr_get(x_35, 0);
x_452 = lean::cnstr_get(x_35, 1);
lean::inc(x_452);
lean::inc(x_451);
lean::dec(x_35);
x_453 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_453, 0, x_451);
lean::cnstr_set(x_453, 1, x_452);
return x_453;
}
}
}
else
{
obj* x_454; obj* x_455; obj* x_456; obj* x_457; obj* x_458; obj* x_459; obj* x_460; obj* x_461; 
x_454 = lean::cnstr_get(x_27, 1);
lean::inc(x_454);
lean::dec(x_27);
x_455 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_455, 0, x_7);
lean::cnstr_set(x_455, 1, x_454);
x_456 = lean::cnstr_get(x_1, 1);
lean::inc(x_456);
x_457 = l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3(x_456);
x_458 = l_Nat_repr(x_457);
x_459 = l_Lean_Environment_displayStats___closed__3;
x_460 = lean_string_append(x_459, x_458);
lean::dec(x_458);
x_461 = l_IO_println___at_HasRepr_HasEval___spec__1(x_460, x_455);
lean::dec(x_460);
if (lean::obj_tag(x_461) == 0)
{
obj* x_462; obj* x_463; obj* x_464; obj* x_465; obj* x_466; obj* x_467; obj* x_468; obj* x_469; obj* x_470; 
x_462 = lean::cnstr_get(x_461, 1);
lean::inc(x_462);
if (lean::is_exclusive(x_461)) {
 lean::cnstr_release(x_461, 0);
 lean::cnstr_release(x_461, 1);
 x_463 = x_461;
} else {
 lean::dec_ref(x_461);
 x_463 = lean::box(0);
}
if (lean::is_scalar(x_463)) {
 x_464 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_464 = x_463;
}
lean::cnstr_set(x_464, 0, x_7);
lean::cnstr_set(x_464, 1, x_462);
x_465 = l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4(x_456);
x_466 = lean::cnstr_get(x_465, 0);
lean::inc(x_466);
x_467 = l_Nat_repr(x_466);
x_468 = l_Lean_Environment_displayStats___closed__4;
x_469 = lean_string_append(x_468, x_467);
lean::dec(x_467);
x_470 = l_IO_println___at_HasRepr_HasEval___spec__1(x_469, x_464);
lean::dec(x_469);
if (lean::obj_tag(x_470) == 0)
{
obj* x_471; obj* x_472; obj* x_473; obj* x_474; obj* x_475; obj* x_476; obj* x_477; obj* x_478; 
x_471 = lean::cnstr_get(x_470, 1);
lean::inc(x_471);
if (lean::is_exclusive(x_470)) {
 lean::cnstr_release(x_470, 0);
 lean::cnstr_release(x_470, 1);
 x_472 = x_470;
} else {
 lean::dec_ref(x_470);
 x_472 = lean::box(0);
}
if (lean::is_scalar(x_472)) {
 x_473 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_473 = x_472;
}
lean::cnstr_set(x_473, 0, x_7);
lean::cnstr_set(x_473, 1, x_471);
x_474 = lean::cnstr_get(x_465, 1);
lean::inc(x_474);
lean::dec(x_465);
x_475 = l_Nat_repr(x_474);
x_476 = l_Lean_Environment_displayStats___closed__5;
x_477 = lean_string_append(x_476, x_475);
lean::dec(x_475);
x_478 = l_IO_println___at_HasRepr_HasEval___spec__1(x_477, x_473);
lean::dec(x_477);
if (lean::obj_tag(x_478) == 0)
{
obj* x_479; obj* x_480; obj* x_481; obj* x_482; obj* x_483; obj* x_484; obj* x_485; obj* x_486; 
x_479 = lean::cnstr_get(x_478, 1);
lean::inc(x_479);
if (lean::is_exclusive(x_478)) {
 lean::cnstr_release(x_478, 0);
 lean::cnstr_release(x_478, 1);
 x_480 = x_478;
} else {
 lean::dec_ref(x_478);
 x_480 = lean::box(0);
}
if (lean::is_scalar(x_480)) {
 x_481 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_481 = x_480;
}
lean::cnstr_set(x_481, 0, x_7);
lean::cnstr_set(x_481, 1, x_479);
x_482 = l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(x_456);
x_483 = l_Nat_repr(x_482);
x_484 = l_Lean_Environment_displayStats___closed__6;
x_485 = lean_string_append(x_484, x_483);
lean::dec(x_483);
x_486 = l_IO_println___at_HasRepr_HasEval___spec__1(x_485, x_481);
lean::dec(x_485);
if (lean::obj_tag(x_486) == 0)
{
obj* x_487; obj* x_488; obj* x_489; obj* x_490; obj* x_491; obj* x_492; obj* x_493; obj* x_494; 
x_487 = lean::cnstr_get(x_486, 1);
lean::inc(x_487);
if (lean::is_exclusive(x_486)) {
 lean::cnstr_release(x_486, 0);
 lean::cnstr_release(x_486, 1);
 x_488 = x_486;
} else {
 lean::dec_ref(x_486);
 x_488 = lean::box(0);
}
if (lean::is_scalar(x_488)) {
 x_489 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_489 = x_488;
}
lean::cnstr_set(x_489, 0, x_7);
lean::cnstr_set(x_489, 1, x_487);
x_490 = l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(x_456);
lean::dec(x_456);
x_491 = l_Nat_repr(x_490);
x_492 = l_Lean_Environment_displayStats___closed__7;
x_493 = lean_string_append(x_492, x_491);
lean::dec(x_491);
x_494 = l_IO_println___at_HasRepr_HasEval___spec__1(x_493, x_489);
lean::dec(x_493);
if (lean::obj_tag(x_494) == 0)
{
obj* x_495; obj* x_496; obj* x_497; uint32 x_498; obj* x_499; obj* x_500; obj* x_501; obj* x_502; obj* x_503; 
x_495 = lean::cnstr_get(x_494, 1);
lean::inc(x_495);
if (lean::is_exclusive(x_494)) {
 lean::cnstr_release(x_494, 0);
 lean::cnstr_release(x_494, 1);
 x_496 = x_494;
} else {
 lean::dec_ref(x_494);
 x_496 = lean::box(0);
}
if (lean::is_scalar(x_496)) {
 x_497 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_497 = x_496;
}
lean::cnstr_set(x_497, 0, x_7);
lean::cnstr_set(x_497, 1, x_495);
x_498 = lean::cnstr_get_uint32(x_15, sizeof(void*)*2);
lean::dec(x_15);
x_499 = lean_uint32_to_nat(x_498);
x_500 = l_Nat_repr(x_499);
x_501 = l_Lean_Environment_displayStats___closed__8;
x_502 = lean_string_append(x_501, x_500);
lean::dec(x_500);
x_503 = l_IO_println___at_HasRepr_HasEval___spec__1(x_502, x_497);
lean::dec(x_502);
if (lean::obj_tag(x_503) == 0)
{
obj* x_504; obj* x_505; obj* x_506; obj* x_507; obj* x_508; obj* x_509; obj* x_510; obj* x_511; obj* x_512; 
x_504 = lean::cnstr_get(x_503, 1);
lean::inc(x_504);
if (lean::is_exclusive(x_503)) {
 lean::cnstr_release(x_503, 0);
 lean::cnstr_release(x_503, 1);
 x_505 = x_503;
} else {
 lean::dec_ref(x_503);
 x_505 = lean::box(0);
}
if (lean::is_scalar(x_505)) {
 x_506 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_506 = x_505;
}
lean::cnstr_set(x_506, 0, x_7);
lean::cnstr_set(x_506, 1, x_504);
x_507 = lean::cnstr_get(x_1, 2);
lean::inc(x_507);
x_508 = lean_array_get_size(x_507);
lean::dec(x_507);
x_509 = l_Nat_repr(x_508);
x_510 = l_Lean_Environment_displayStats___closed__9;
x_511 = lean_string_append(x_510, x_509);
lean::dec(x_509);
x_512 = l_IO_println___at_HasRepr_HasEval___spec__1(x_511, x_506);
lean::dec(x_511);
if (lean::obj_tag(x_512) == 0)
{
obj* x_513; obj* x_514; obj* x_515; obj* x_516; 
x_513 = lean::cnstr_get(x_512, 1);
lean::inc(x_513);
if (lean::is_exclusive(x_512)) {
 lean::cnstr_release(x_512, 0);
 lean::cnstr_release(x_512, 1);
 x_514 = x_512;
} else {
 lean::dec_ref(x_512);
 x_514 = lean::box(0);
}
if (lean::is_scalar(x_514)) {
 x_515 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_515 = x_514;
}
lean::cnstr_set(x_515, 0, x_7);
lean::cnstr_set(x_515, 1, x_513);
x_516 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10(x_1, x_6, x_9, x_515);
lean::dec(x_6);
lean::dec(x_1);
if (lean::obj_tag(x_516) == 0)
{
obj* x_517; obj* x_518; obj* x_519; 
x_517 = lean::cnstr_get(x_516, 1);
lean::inc(x_517);
if (lean::is_exclusive(x_516)) {
 lean::cnstr_release(x_516, 0);
 lean::cnstr_release(x_516, 1);
 x_518 = x_516;
} else {
 lean::dec_ref(x_516);
 x_518 = lean::box(0);
}
if (lean::is_scalar(x_518)) {
 x_519 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_519 = x_518;
}
lean::cnstr_set(x_519, 0, x_7);
lean::cnstr_set(x_519, 1, x_517);
return x_519;
}
else
{
obj* x_520; obj* x_521; obj* x_522; obj* x_523; 
x_520 = lean::cnstr_get(x_516, 0);
lean::inc(x_520);
x_521 = lean::cnstr_get(x_516, 1);
lean::inc(x_521);
if (lean::is_exclusive(x_516)) {
 lean::cnstr_release(x_516, 0);
 lean::cnstr_release(x_516, 1);
 x_522 = x_516;
} else {
 lean::dec_ref(x_516);
 x_522 = lean::box(0);
}
if (lean::is_scalar(x_522)) {
 x_523 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_523 = x_522;
}
lean::cnstr_set(x_523, 0, x_520);
lean::cnstr_set(x_523, 1, x_521);
return x_523;
}
}
else
{
obj* x_524; obj* x_525; obj* x_526; obj* x_527; 
lean::dec(x_6);
lean::dec(x_1);
x_524 = lean::cnstr_get(x_512, 0);
lean::inc(x_524);
x_525 = lean::cnstr_get(x_512, 1);
lean::inc(x_525);
if (lean::is_exclusive(x_512)) {
 lean::cnstr_release(x_512, 0);
 lean::cnstr_release(x_512, 1);
 x_526 = x_512;
} else {
 lean::dec_ref(x_512);
 x_526 = lean::box(0);
}
if (lean::is_scalar(x_526)) {
 x_527 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_527 = x_526;
}
lean::cnstr_set(x_527, 0, x_524);
lean::cnstr_set(x_527, 1, x_525);
return x_527;
}
}
else
{
obj* x_528; obj* x_529; obj* x_530; obj* x_531; 
lean::dec(x_6);
lean::dec(x_1);
x_528 = lean::cnstr_get(x_503, 0);
lean::inc(x_528);
x_529 = lean::cnstr_get(x_503, 1);
lean::inc(x_529);
if (lean::is_exclusive(x_503)) {
 lean::cnstr_release(x_503, 0);
 lean::cnstr_release(x_503, 1);
 x_530 = x_503;
} else {
 lean::dec_ref(x_503);
 x_530 = lean::box(0);
}
if (lean::is_scalar(x_530)) {
 x_531 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_531 = x_530;
}
lean::cnstr_set(x_531, 0, x_528);
lean::cnstr_set(x_531, 1, x_529);
return x_531;
}
}
else
{
obj* x_532; obj* x_533; obj* x_534; obj* x_535; 
lean::dec(x_15);
lean::dec(x_6);
lean::dec(x_1);
x_532 = lean::cnstr_get(x_494, 0);
lean::inc(x_532);
x_533 = lean::cnstr_get(x_494, 1);
lean::inc(x_533);
if (lean::is_exclusive(x_494)) {
 lean::cnstr_release(x_494, 0);
 lean::cnstr_release(x_494, 1);
 x_534 = x_494;
} else {
 lean::dec_ref(x_494);
 x_534 = lean::box(0);
}
if (lean::is_scalar(x_534)) {
 x_535 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_535 = x_534;
}
lean::cnstr_set(x_535, 0, x_532);
lean::cnstr_set(x_535, 1, x_533);
return x_535;
}
}
else
{
obj* x_536; obj* x_537; obj* x_538; obj* x_539; 
lean::dec(x_456);
lean::dec(x_15);
lean::dec(x_6);
lean::dec(x_1);
x_536 = lean::cnstr_get(x_486, 0);
lean::inc(x_536);
x_537 = lean::cnstr_get(x_486, 1);
lean::inc(x_537);
if (lean::is_exclusive(x_486)) {
 lean::cnstr_release(x_486, 0);
 lean::cnstr_release(x_486, 1);
 x_538 = x_486;
} else {
 lean::dec_ref(x_486);
 x_538 = lean::box(0);
}
if (lean::is_scalar(x_538)) {
 x_539 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_539 = x_538;
}
lean::cnstr_set(x_539, 0, x_536);
lean::cnstr_set(x_539, 1, x_537);
return x_539;
}
}
else
{
obj* x_540; obj* x_541; obj* x_542; obj* x_543; 
lean::dec(x_456);
lean::dec(x_15);
lean::dec(x_6);
lean::dec(x_1);
x_540 = lean::cnstr_get(x_478, 0);
lean::inc(x_540);
x_541 = lean::cnstr_get(x_478, 1);
lean::inc(x_541);
if (lean::is_exclusive(x_478)) {
 lean::cnstr_release(x_478, 0);
 lean::cnstr_release(x_478, 1);
 x_542 = x_478;
} else {
 lean::dec_ref(x_478);
 x_542 = lean::box(0);
}
if (lean::is_scalar(x_542)) {
 x_543 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_543 = x_542;
}
lean::cnstr_set(x_543, 0, x_540);
lean::cnstr_set(x_543, 1, x_541);
return x_543;
}
}
else
{
obj* x_544; obj* x_545; obj* x_546; obj* x_547; 
lean::dec(x_465);
lean::dec(x_456);
lean::dec(x_15);
lean::dec(x_6);
lean::dec(x_1);
x_544 = lean::cnstr_get(x_470, 0);
lean::inc(x_544);
x_545 = lean::cnstr_get(x_470, 1);
lean::inc(x_545);
if (lean::is_exclusive(x_470)) {
 lean::cnstr_release(x_470, 0);
 lean::cnstr_release(x_470, 1);
 x_546 = x_470;
} else {
 lean::dec_ref(x_470);
 x_546 = lean::box(0);
}
if (lean::is_scalar(x_546)) {
 x_547 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_547 = x_546;
}
lean::cnstr_set(x_547, 0, x_544);
lean::cnstr_set(x_547, 1, x_545);
return x_547;
}
}
else
{
obj* x_548; obj* x_549; obj* x_550; obj* x_551; 
lean::dec(x_456);
lean::dec(x_15);
lean::dec(x_6);
lean::dec(x_1);
x_548 = lean::cnstr_get(x_461, 0);
lean::inc(x_548);
x_549 = lean::cnstr_get(x_461, 1);
lean::inc(x_549);
if (lean::is_exclusive(x_461)) {
 lean::cnstr_release(x_461, 0);
 lean::cnstr_release(x_461, 1);
 x_550 = x_461;
} else {
 lean::dec_ref(x_461);
 x_550 = lean::box(0);
}
if (lean::is_scalar(x_550)) {
 x_551 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_551 = x_550;
}
lean::cnstr_set(x_551, 0, x_548);
lean::cnstr_set(x_551, 1, x_549);
return x_551;
}
}
}
else
{
uint8 x_552; 
lean::dec(x_15);
lean::dec(x_6);
lean::dec(x_1);
x_552 = !lean::is_exclusive(x_27);
if (x_552 == 0)
{
return x_27;
}
else
{
obj* x_553; obj* x_554; obj* x_555; 
x_553 = lean::cnstr_get(x_27, 0);
x_554 = lean::cnstr_get(x_27, 1);
lean::inc(x_554);
lean::inc(x_553);
lean::dec(x_27);
x_555 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_555, 0, x_553);
lean::cnstr_set(x_555, 1, x_554);
return x_555;
}
}
}
else
{
obj* x_556; obj* x_557; obj* x_558; obj* x_559; obj* x_560; obj* x_561; 
x_556 = lean::cnstr_get(x_21, 1);
lean::inc(x_556);
lean::dec(x_21);
x_557 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_557, 0, x_7);
lean::cnstr_set(x_557, 1, x_556);
x_558 = l_Nat_repr(x_14);
x_559 = l_Lean_Environment_displayStats___closed__2;
x_560 = lean_string_append(x_559, x_558);
lean::dec(x_558);
x_561 = l_IO_println___at_HasRepr_HasEval___spec__1(x_560, x_557);
lean::dec(x_560);
if (lean::obj_tag(x_561) == 0)
{
obj* x_562; obj* x_563; obj* x_564; obj* x_565; obj* x_566; obj* x_567; obj* x_568; obj* x_569; obj* x_570; 
x_562 = lean::cnstr_get(x_561, 1);
lean::inc(x_562);
if (lean::is_exclusive(x_561)) {
 lean::cnstr_release(x_561, 0);
 lean::cnstr_release(x_561, 1);
 x_563 = x_561;
} else {
 lean::dec_ref(x_561);
 x_563 = lean::box(0);
}
if (lean::is_scalar(x_563)) {
 x_564 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_564 = x_563;
}
lean::cnstr_set(x_564, 0, x_7);
lean::cnstr_set(x_564, 1, x_562);
x_565 = lean::cnstr_get(x_1, 1);
lean::inc(x_565);
x_566 = l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3(x_565);
x_567 = l_Nat_repr(x_566);
x_568 = l_Lean_Environment_displayStats___closed__3;
x_569 = lean_string_append(x_568, x_567);
lean::dec(x_567);
x_570 = l_IO_println___at_HasRepr_HasEval___spec__1(x_569, x_564);
lean::dec(x_569);
if (lean::obj_tag(x_570) == 0)
{
obj* x_571; obj* x_572; obj* x_573; obj* x_574; obj* x_575; obj* x_576; obj* x_577; obj* x_578; obj* x_579; 
x_571 = lean::cnstr_get(x_570, 1);
lean::inc(x_571);
if (lean::is_exclusive(x_570)) {
 lean::cnstr_release(x_570, 0);
 lean::cnstr_release(x_570, 1);
 x_572 = x_570;
} else {
 lean::dec_ref(x_570);
 x_572 = lean::box(0);
}
if (lean::is_scalar(x_572)) {
 x_573 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_573 = x_572;
}
lean::cnstr_set(x_573, 0, x_7);
lean::cnstr_set(x_573, 1, x_571);
x_574 = l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4(x_565);
x_575 = lean::cnstr_get(x_574, 0);
lean::inc(x_575);
x_576 = l_Nat_repr(x_575);
x_577 = l_Lean_Environment_displayStats___closed__4;
x_578 = lean_string_append(x_577, x_576);
lean::dec(x_576);
x_579 = l_IO_println___at_HasRepr_HasEval___spec__1(x_578, x_573);
lean::dec(x_578);
if (lean::obj_tag(x_579) == 0)
{
obj* x_580; obj* x_581; obj* x_582; obj* x_583; obj* x_584; obj* x_585; obj* x_586; obj* x_587; 
x_580 = lean::cnstr_get(x_579, 1);
lean::inc(x_580);
if (lean::is_exclusive(x_579)) {
 lean::cnstr_release(x_579, 0);
 lean::cnstr_release(x_579, 1);
 x_581 = x_579;
} else {
 lean::dec_ref(x_579);
 x_581 = lean::box(0);
}
if (lean::is_scalar(x_581)) {
 x_582 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_582 = x_581;
}
lean::cnstr_set(x_582, 0, x_7);
lean::cnstr_set(x_582, 1, x_580);
x_583 = lean::cnstr_get(x_574, 1);
lean::inc(x_583);
lean::dec(x_574);
x_584 = l_Nat_repr(x_583);
x_585 = l_Lean_Environment_displayStats___closed__5;
x_586 = lean_string_append(x_585, x_584);
lean::dec(x_584);
x_587 = l_IO_println___at_HasRepr_HasEval___spec__1(x_586, x_582);
lean::dec(x_586);
if (lean::obj_tag(x_587) == 0)
{
obj* x_588; obj* x_589; obj* x_590; obj* x_591; obj* x_592; obj* x_593; obj* x_594; obj* x_595; 
x_588 = lean::cnstr_get(x_587, 1);
lean::inc(x_588);
if (lean::is_exclusive(x_587)) {
 lean::cnstr_release(x_587, 0);
 lean::cnstr_release(x_587, 1);
 x_589 = x_587;
} else {
 lean::dec_ref(x_587);
 x_589 = lean::box(0);
}
if (lean::is_scalar(x_589)) {
 x_590 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_590 = x_589;
}
lean::cnstr_set(x_590, 0, x_7);
lean::cnstr_set(x_590, 1, x_588);
x_591 = l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(x_565);
x_592 = l_Nat_repr(x_591);
x_593 = l_Lean_Environment_displayStats___closed__6;
x_594 = lean_string_append(x_593, x_592);
lean::dec(x_592);
x_595 = l_IO_println___at_HasRepr_HasEval___spec__1(x_594, x_590);
lean::dec(x_594);
if (lean::obj_tag(x_595) == 0)
{
obj* x_596; obj* x_597; obj* x_598; obj* x_599; obj* x_600; obj* x_601; obj* x_602; obj* x_603; 
x_596 = lean::cnstr_get(x_595, 1);
lean::inc(x_596);
if (lean::is_exclusive(x_595)) {
 lean::cnstr_release(x_595, 0);
 lean::cnstr_release(x_595, 1);
 x_597 = x_595;
} else {
 lean::dec_ref(x_595);
 x_597 = lean::box(0);
}
if (lean::is_scalar(x_597)) {
 x_598 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_598 = x_597;
}
lean::cnstr_set(x_598, 0, x_7);
lean::cnstr_set(x_598, 1, x_596);
x_599 = l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(x_565);
lean::dec(x_565);
x_600 = l_Nat_repr(x_599);
x_601 = l_Lean_Environment_displayStats___closed__7;
x_602 = lean_string_append(x_601, x_600);
lean::dec(x_600);
x_603 = l_IO_println___at_HasRepr_HasEval___spec__1(x_602, x_598);
lean::dec(x_602);
if (lean::obj_tag(x_603) == 0)
{
obj* x_604; obj* x_605; obj* x_606; uint32 x_607; obj* x_608; obj* x_609; obj* x_610; obj* x_611; obj* x_612; 
x_604 = lean::cnstr_get(x_603, 1);
lean::inc(x_604);
if (lean::is_exclusive(x_603)) {
 lean::cnstr_release(x_603, 0);
 lean::cnstr_release(x_603, 1);
 x_605 = x_603;
} else {
 lean::dec_ref(x_603);
 x_605 = lean::box(0);
}
if (lean::is_scalar(x_605)) {
 x_606 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_606 = x_605;
}
lean::cnstr_set(x_606, 0, x_7);
lean::cnstr_set(x_606, 1, x_604);
x_607 = lean::cnstr_get_uint32(x_15, sizeof(void*)*2);
lean::dec(x_15);
x_608 = lean_uint32_to_nat(x_607);
x_609 = l_Nat_repr(x_608);
x_610 = l_Lean_Environment_displayStats___closed__8;
x_611 = lean_string_append(x_610, x_609);
lean::dec(x_609);
x_612 = l_IO_println___at_HasRepr_HasEval___spec__1(x_611, x_606);
lean::dec(x_611);
if (lean::obj_tag(x_612) == 0)
{
obj* x_613; obj* x_614; obj* x_615; obj* x_616; obj* x_617; obj* x_618; obj* x_619; obj* x_620; obj* x_621; 
x_613 = lean::cnstr_get(x_612, 1);
lean::inc(x_613);
if (lean::is_exclusive(x_612)) {
 lean::cnstr_release(x_612, 0);
 lean::cnstr_release(x_612, 1);
 x_614 = x_612;
} else {
 lean::dec_ref(x_612);
 x_614 = lean::box(0);
}
if (lean::is_scalar(x_614)) {
 x_615 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_615 = x_614;
}
lean::cnstr_set(x_615, 0, x_7);
lean::cnstr_set(x_615, 1, x_613);
x_616 = lean::cnstr_get(x_1, 2);
lean::inc(x_616);
x_617 = lean_array_get_size(x_616);
lean::dec(x_616);
x_618 = l_Nat_repr(x_617);
x_619 = l_Lean_Environment_displayStats___closed__9;
x_620 = lean_string_append(x_619, x_618);
lean::dec(x_618);
x_621 = l_IO_println___at_HasRepr_HasEval___spec__1(x_620, x_615);
lean::dec(x_620);
if (lean::obj_tag(x_621) == 0)
{
obj* x_622; obj* x_623; obj* x_624; obj* x_625; 
x_622 = lean::cnstr_get(x_621, 1);
lean::inc(x_622);
if (lean::is_exclusive(x_621)) {
 lean::cnstr_release(x_621, 0);
 lean::cnstr_release(x_621, 1);
 x_623 = x_621;
} else {
 lean::dec_ref(x_621);
 x_623 = lean::box(0);
}
if (lean::is_scalar(x_623)) {
 x_624 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_624 = x_623;
}
lean::cnstr_set(x_624, 0, x_7);
lean::cnstr_set(x_624, 1, x_622);
x_625 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10(x_1, x_6, x_9, x_624);
lean::dec(x_6);
lean::dec(x_1);
if (lean::obj_tag(x_625) == 0)
{
obj* x_626; obj* x_627; obj* x_628; 
x_626 = lean::cnstr_get(x_625, 1);
lean::inc(x_626);
if (lean::is_exclusive(x_625)) {
 lean::cnstr_release(x_625, 0);
 lean::cnstr_release(x_625, 1);
 x_627 = x_625;
} else {
 lean::dec_ref(x_625);
 x_627 = lean::box(0);
}
if (lean::is_scalar(x_627)) {
 x_628 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_628 = x_627;
}
lean::cnstr_set(x_628, 0, x_7);
lean::cnstr_set(x_628, 1, x_626);
return x_628;
}
else
{
obj* x_629; obj* x_630; obj* x_631; obj* x_632; 
x_629 = lean::cnstr_get(x_625, 0);
lean::inc(x_629);
x_630 = lean::cnstr_get(x_625, 1);
lean::inc(x_630);
if (lean::is_exclusive(x_625)) {
 lean::cnstr_release(x_625, 0);
 lean::cnstr_release(x_625, 1);
 x_631 = x_625;
} else {
 lean::dec_ref(x_625);
 x_631 = lean::box(0);
}
if (lean::is_scalar(x_631)) {
 x_632 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_632 = x_631;
}
lean::cnstr_set(x_632, 0, x_629);
lean::cnstr_set(x_632, 1, x_630);
return x_632;
}
}
else
{
obj* x_633; obj* x_634; obj* x_635; obj* x_636; 
lean::dec(x_6);
lean::dec(x_1);
x_633 = lean::cnstr_get(x_621, 0);
lean::inc(x_633);
x_634 = lean::cnstr_get(x_621, 1);
lean::inc(x_634);
if (lean::is_exclusive(x_621)) {
 lean::cnstr_release(x_621, 0);
 lean::cnstr_release(x_621, 1);
 x_635 = x_621;
} else {
 lean::dec_ref(x_621);
 x_635 = lean::box(0);
}
if (lean::is_scalar(x_635)) {
 x_636 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_636 = x_635;
}
lean::cnstr_set(x_636, 0, x_633);
lean::cnstr_set(x_636, 1, x_634);
return x_636;
}
}
else
{
obj* x_637; obj* x_638; obj* x_639; obj* x_640; 
lean::dec(x_6);
lean::dec(x_1);
x_637 = lean::cnstr_get(x_612, 0);
lean::inc(x_637);
x_638 = lean::cnstr_get(x_612, 1);
lean::inc(x_638);
if (lean::is_exclusive(x_612)) {
 lean::cnstr_release(x_612, 0);
 lean::cnstr_release(x_612, 1);
 x_639 = x_612;
} else {
 lean::dec_ref(x_612);
 x_639 = lean::box(0);
}
if (lean::is_scalar(x_639)) {
 x_640 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_640 = x_639;
}
lean::cnstr_set(x_640, 0, x_637);
lean::cnstr_set(x_640, 1, x_638);
return x_640;
}
}
else
{
obj* x_641; obj* x_642; obj* x_643; obj* x_644; 
lean::dec(x_15);
lean::dec(x_6);
lean::dec(x_1);
x_641 = lean::cnstr_get(x_603, 0);
lean::inc(x_641);
x_642 = lean::cnstr_get(x_603, 1);
lean::inc(x_642);
if (lean::is_exclusive(x_603)) {
 lean::cnstr_release(x_603, 0);
 lean::cnstr_release(x_603, 1);
 x_643 = x_603;
} else {
 lean::dec_ref(x_603);
 x_643 = lean::box(0);
}
if (lean::is_scalar(x_643)) {
 x_644 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_644 = x_643;
}
lean::cnstr_set(x_644, 0, x_641);
lean::cnstr_set(x_644, 1, x_642);
return x_644;
}
}
else
{
obj* x_645; obj* x_646; obj* x_647; obj* x_648; 
lean::dec(x_565);
lean::dec(x_15);
lean::dec(x_6);
lean::dec(x_1);
x_645 = lean::cnstr_get(x_595, 0);
lean::inc(x_645);
x_646 = lean::cnstr_get(x_595, 1);
lean::inc(x_646);
if (lean::is_exclusive(x_595)) {
 lean::cnstr_release(x_595, 0);
 lean::cnstr_release(x_595, 1);
 x_647 = x_595;
} else {
 lean::dec_ref(x_595);
 x_647 = lean::box(0);
}
if (lean::is_scalar(x_647)) {
 x_648 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_648 = x_647;
}
lean::cnstr_set(x_648, 0, x_645);
lean::cnstr_set(x_648, 1, x_646);
return x_648;
}
}
else
{
obj* x_649; obj* x_650; obj* x_651; obj* x_652; 
lean::dec(x_565);
lean::dec(x_15);
lean::dec(x_6);
lean::dec(x_1);
x_649 = lean::cnstr_get(x_587, 0);
lean::inc(x_649);
x_650 = lean::cnstr_get(x_587, 1);
lean::inc(x_650);
if (lean::is_exclusive(x_587)) {
 lean::cnstr_release(x_587, 0);
 lean::cnstr_release(x_587, 1);
 x_651 = x_587;
} else {
 lean::dec_ref(x_587);
 x_651 = lean::box(0);
}
if (lean::is_scalar(x_651)) {
 x_652 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_652 = x_651;
}
lean::cnstr_set(x_652, 0, x_649);
lean::cnstr_set(x_652, 1, x_650);
return x_652;
}
}
else
{
obj* x_653; obj* x_654; obj* x_655; obj* x_656; 
lean::dec(x_574);
lean::dec(x_565);
lean::dec(x_15);
lean::dec(x_6);
lean::dec(x_1);
x_653 = lean::cnstr_get(x_579, 0);
lean::inc(x_653);
x_654 = lean::cnstr_get(x_579, 1);
lean::inc(x_654);
if (lean::is_exclusive(x_579)) {
 lean::cnstr_release(x_579, 0);
 lean::cnstr_release(x_579, 1);
 x_655 = x_579;
} else {
 lean::dec_ref(x_579);
 x_655 = lean::box(0);
}
if (lean::is_scalar(x_655)) {
 x_656 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_656 = x_655;
}
lean::cnstr_set(x_656, 0, x_653);
lean::cnstr_set(x_656, 1, x_654);
return x_656;
}
}
else
{
obj* x_657; obj* x_658; obj* x_659; obj* x_660; 
lean::dec(x_565);
lean::dec(x_15);
lean::dec(x_6);
lean::dec(x_1);
x_657 = lean::cnstr_get(x_570, 0);
lean::inc(x_657);
x_658 = lean::cnstr_get(x_570, 1);
lean::inc(x_658);
if (lean::is_exclusive(x_570)) {
 lean::cnstr_release(x_570, 0);
 lean::cnstr_release(x_570, 1);
 x_659 = x_570;
} else {
 lean::dec_ref(x_570);
 x_659 = lean::box(0);
}
if (lean::is_scalar(x_659)) {
 x_660 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_660 = x_659;
}
lean::cnstr_set(x_660, 0, x_657);
lean::cnstr_set(x_660, 1, x_658);
return x_660;
}
}
else
{
obj* x_661; obj* x_662; obj* x_663; obj* x_664; 
lean::dec(x_15);
lean::dec(x_6);
lean::dec(x_1);
x_661 = lean::cnstr_get(x_561, 0);
lean::inc(x_661);
x_662 = lean::cnstr_get(x_561, 1);
lean::inc(x_662);
if (lean::is_exclusive(x_561)) {
 lean::cnstr_release(x_561, 0);
 lean::cnstr_release(x_561, 1);
 x_663 = x_561;
} else {
 lean::dec_ref(x_561);
 x_663 = lean::box(0);
}
if (lean::is_scalar(x_663)) {
 x_664 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_664 = x_663;
}
lean::cnstr_set(x_664, 0, x_661);
lean::cnstr_set(x_664, 1, x_662);
return x_664;
}
}
}
else
{
uint8 x_665; 
lean::dec(x_15);
lean::dec(x_14);
lean::dec(x_6);
lean::dec(x_1);
x_665 = !lean::is_exclusive(x_21);
if (x_665 == 0)
{
return x_21;
}
else
{
obj* x_666; obj* x_667; obj* x_668; 
x_666 = lean::cnstr_get(x_21, 0);
x_667 = lean::cnstr_get(x_21, 1);
lean::inc(x_667);
lean::inc(x_666);
lean::dec(x_21);
x_668 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_668, 0, x_666);
lean::cnstr_set(x_668, 1, x_667);
return x_668;
}
}
}
else
{
obj* x_669; obj* x_670; obj* x_671; obj* x_672; obj* x_673; obj* x_674; obj* x_675; obj* x_676; obj* x_677; obj* x_678; obj* x_679; obj* x_680; obj* x_681; obj* x_682; obj* x_683; obj* x_684; obj* x_685; obj* x_686; 
x_669 = lean::cnstr_get(x_4, 0);
x_670 = lean::cnstr_get(x_4, 1);
lean::inc(x_670);
lean::inc(x_669);
lean::dec(x_4);
x_671 = lean::box(0);
x_672 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_672, 0, x_671);
lean::cnstr_set(x_672, 1, x_670);
x_673 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_674 = lean::mk_nat_obj(0u);
x_675 = lean_array_get(x_673, x_669, x_674);
x_676 = lean::cnstr_get(x_675, 0);
lean::inc(x_676);
lean::dec(x_675);
x_677 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_676, x_1);
x_678 = lean::cnstr_get(x_677, 0);
lean::inc(x_678);
lean::dec(x_677);
x_679 = lean_array_get_size(x_678);
lean::dec(x_678);
x_680 = lean::cnstr_get(x_1, 3);
lean::inc(x_680);
x_681 = lean::cnstr_get(x_680, 1);
lean::inc(x_681);
x_682 = l_Array_toList___rarg(x_681);
lean::dec(x_681);
x_683 = l_List_toString___at_Lean_Environment_displayStats___spec__1(x_682);
x_684 = l_Lean_Environment_displayStats___closed__1;
x_685 = lean_string_append(x_684, x_683);
lean::dec(x_683);
x_686 = l_IO_println___at_HasRepr_HasEval___spec__1(x_685, x_672);
lean::dec(x_685);
if (lean::obj_tag(x_686) == 0)
{
obj* x_687; obj* x_688; obj* x_689; obj* x_690; obj* x_691; obj* x_692; obj* x_693; 
x_687 = lean::cnstr_get(x_686, 1);
lean::inc(x_687);
if (lean::is_exclusive(x_686)) {
 lean::cnstr_release(x_686, 0);
 lean::cnstr_release(x_686, 1);
 x_688 = x_686;
} else {
 lean::dec_ref(x_686);
 x_688 = lean::box(0);
}
if (lean::is_scalar(x_688)) {
 x_689 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_689 = x_688;
}
lean::cnstr_set(x_689, 0, x_671);
lean::cnstr_set(x_689, 1, x_687);
x_690 = l_Nat_repr(x_679);
x_691 = l_Lean_Environment_displayStats___closed__2;
x_692 = lean_string_append(x_691, x_690);
lean::dec(x_690);
x_693 = l_IO_println___at_HasRepr_HasEval___spec__1(x_692, x_689);
lean::dec(x_692);
if (lean::obj_tag(x_693) == 0)
{
obj* x_694; obj* x_695; obj* x_696; obj* x_697; obj* x_698; obj* x_699; obj* x_700; obj* x_701; obj* x_702; 
x_694 = lean::cnstr_get(x_693, 1);
lean::inc(x_694);
if (lean::is_exclusive(x_693)) {
 lean::cnstr_release(x_693, 0);
 lean::cnstr_release(x_693, 1);
 x_695 = x_693;
} else {
 lean::dec_ref(x_693);
 x_695 = lean::box(0);
}
if (lean::is_scalar(x_695)) {
 x_696 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_696 = x_695;
}
lean::cnstr_set(x_696, 0, x_671);
lean::cnstr_set(x_696, 1, x_694);
x_697 = lean::cnstr_get(x_1, 1);
lean::inc(x_697);
x_698 = l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3(x_697);
x_699 = l_Nat_repr(x_698);
x_700 = l_Lean_Environment_displayStats___closed__3;
x_701 = lean_string_append(x_700, x_699);
lean::dec(x_699);
x_702 = l_IO_println___at_HasRepr_HasEval___spec__1(x_701, x_696);
lean::dec(x_701);
if (lean::obj_tag(x_702) == 0)
{
obj* x_703; obj* x_704; obj* x_705; obj* x_706; obj* x_707; obj* x_708; obj* x_709; obj* x_710; obj* x_711; 
x_703 = lean::cnstr_get(x_702, 1);
lean::inc(x_703);
if (lean::is_exclusive(x_702)) {
 lean::cnstr_release(x_702, 0);
 lean::cnstr_release(x_702, 1);
 x_704 = x_702;
} else {
 lean::dec_ref(x_702);
 x_704 = lean::box(0);
}
if (lean::is_scalar(x_704)) {
 x_705 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_705 = x_704;
}
lean::cnstr_set(x_705, 0, x_671);
lean::cnstr_set(x_705, 1, x_703);
x_706 = l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4(x_697);
x_707 = lean::cnstr_get(x_706, 0);
lean::inc(x_707);
x_708 = l_Nat_repr(x_707);
x_709 = l_Lean_Environment_displayStats___closed__4;
x_710 = lean_string_append(x_709, x_708);
lean::dec(x_708);
x_711 = l_IO_println___at_HasRepr_HasEval___spec__1(x_710, x_705);
lean::dec(x_710);
if (lean::obj_tag(x_711) == 0)
{
obj* x_712; obj* x_713; obj* x_714; obj* x_715; obj* x_716; obj* x_717; obj* x_718; obj* x_719; 
x_712 = lean::cnstr_get(x_711, 1);
lean::inc(x_712);
if (lean::is_exclusive(x_711)) {
 lean::cnstr_release(x_711, 0);
 lean::cnstr_release(x_711, 1);
 x_713 = x_711;
} else {
 lean::dec_ref(x_711);
 x_713 = lean::box(0);
}
if (lean::is_scalar(x_713)) {
 x_714 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_714 = x_713;
}
lean::cnstr_set(x_714, 0, x_671);
lean::cnstr_set(x_714, 1, x_712);
x_715 = lean::cnstr_get(x_706, 1);
lean::inc(x_715);
lean::dec(x_706);
x_716 = l_Nat_repr(x_715);
x_717 = l_Lean_Environment_displayStats___closed__5;
x_718 = lean_string_append(x_717, x_716);
lean::dec(x_716);
x_719 = l_IO_println___at_HasRepr_HasEval___spec__1(x_718, x_714);
lean::dec(x_718);
if (lean::obj_tag(x_719) == 0)
{
obj* x_720; obj* x_721; obj* x_722; obj* x_723; obj* x_724; obj* x_725; obj* x_726; obj* x_727; 
x_720 = lean::cnstr_get(x_719, 1);
lean::inc(x_720);
if (lean::is_exclusive(x_719)) {
 lean::cnstr_release(x_719, 0);
 lean::cnstr_release(x_719, 1);
 x_721 = x_719;
} else {
 lean::dec_ref(x_719);
 x_721 = lean::box(0);
}
if (lean::is_scalar(x_721)) {
 x_722 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_722 = x_721;
}
lean::cnstr_set(x_722, 0, x_671);
lean::cnstr_set(x_722, 1, x_720);
x_723 = l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(x_697);
x_724 = l_Nat_repr(x_723);
x_725 = l_Lean_Environment_displayStats___closed__6;
x_726 = lean_string_append(x_725, x_724);
lean::dec(x_724);
x_727 = l_IO_println___at_HasRepr_HasEval___spec__1(x_726, x_722);
lean::dec(x_726);
if (lean::obj_tag(x_727) == 0)
{
obj* x_728; obj* x_729; obj* x_730; obj* x_731; obj* x_732; obj* x_733; obj* x_734; obj* x_735; 
x_728 = lean::cnstr_get(x_727, 1);
lean::inc(x_728);
if (lean::is_exclusive(x_727)) {
 lean::cnstr_release(x_727, 0);
 lean::cnstr_release(x_727, 1);
 x_729 = x_727;
} else {
 lean::dec_ref(x_727);
 x_729 = lean::box(0);
}
if (lean::is_scalar(x_729)) {
 x_730 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_730 = x_729;
}
lean::cnstr_set(x_730, 0, x_671);
lean::cnstr_set(x_730, 1, x_728);
x_731 = l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(x_697);
lean::dec(x_697);
x_732 = l_Nat_repr(x_731);
x_733 = l_Lean_Environment_displayStats___closed__7;
x_734 = lean_string_append(x_733, x_732);
lean::dec(x_732);
x_735 = l_IO_println___at_HasRepr_HasEval___spec__1(x_734, x_730);
lean::dec(x_734);
if (lean::obj_tag(x_735) == 0)
{
obj* x_736; obj* x_737; obj* x_738; uint32 x_739; obj* x_740; obj* x_741; obj* x_742; obj* x_743; obj* x_744; 
x_736 = lean::cnstr_get(x_735, 1);
lean::inc(x_736);
if (lean::is_exclusive(x_735)) {
 lean::cnstr_release(x_735, 0);
 lean::cnstr_release(x_735, 1);
 x_737 = x_735;
} else {
 lean::dec_ref(x_735);
 x_737 = lean::box(0);
}
if (lean::is_scalar(x_737)) {
 x_738 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_738 = x_737;
}
lean::cnstr_set(x_738, 0, x_671);
lean::cnstr_set(x_738, 1, x_736);
x_739 = lean::cnstr_get_uint32(x_680, sizeof(void*)*2);
lean::dec(x_680);
x_740 = lean_uint32_to_nat(x_739);
x_741 = l_Nat_repr(x_740);
x_742 = l_Lean_Environment_displayStats___closed__8;
x_743 = lean_string_append(x_742, x_741);
lean::dec(x_741);
x_744 = l_IO_println___at_HasRepr_HasEval___spec__1(x_743, x_738);
lean::dec(x_743);
if (lean::obj_tag(x_744) == 0)
{
obj* x_745; obj* x_746; obj* x_747; obj* x_748; obj* x_749; obj* x_750; obj* x_751; obj* x_752; obj* x_753; 
x_745 = lean::cnstr_get(x_744, 1);
lean::inc(x_745);
if (lean::is_exclusive(x_744)) {
 lean::cnstr_release(x_744, 0);
 lean::cnstr_release(x_744, 1);
 x_746 = x_744;
} else {
 lean::dec_ref(x_744);
 x_746 = lean::box(0);
}
if (lean::is_scalar(x_746)) {
 x_747 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_747 = x_746;
}
lean::cnstr_set(x_747, 0, x_671);
lean::cnstr_set(x_747, 1, x_745);
x_748 = lean::cnstr_get(x_1, 2);
lean::inc(x_748);
x_749 = lean_array_get_size(x_748);
lean::dec(x_748);
x_750 = l_Nat_repr(x_749);
x_751 = l_Lean_Environment_displayStats___closed__9;
x_752 = lean_string_append(x_751, x_750);
lean::dec(x_750);
x_753 = l_IO_println___at_HasRepr_HasEval___spec__1(x_752, x_747);
lean::dec(x_752);
if (lean::obj_tag(x_753) == 0)
{
obj* x_754; obj* x_755; obj* x_756; obj* x_757; 
x_754 = lean::cnstr_get(x_753, 1);
lean::inc(x_754);
if (lean::is_exclusive(x_753)) {
 lean::cnstr_release(x_753, 0);
 lean::cnstr_release(x_753, 1);
 x_755 = x_753;
} else {
 lean::dec_ref(x_753);
 x_755 = lean::box(0);
}
if (lean::is_scalar(x_755)) {
 x_756 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_756 = x_755;
}
lean::cnstr_set(x_756, 0, x_671);
lean::cnstr_set(x_756, 1, x_754);
x_757 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10(x_1, x_669, x_674, x_756);
lean::dec(x_669);
lean::dec(x_1);
if (lean::obj_tag(x_757) == 0)
{
obj* x_758; obj* x_759; obj* x_760; 
x_758 = lean::cnstr_get(x_757, 1);
lean::inc(x_758);
if (lean::is_exclusive(x_757)) {
 lean::cnstr_release(x_757, 0);
 lean::cnstr_release(x_757, 1);
 x_759 = x_757;
} else {
 lean::dec_ref(x_757);
 x_759 = lean::box(0);
}
if (lean::is_scalar(x_759)) {
 x_760 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_760 = x_759;
}
lean::cnstr_set(x_760, 0, x_671);
lean::cnstr_set(x_760, 1, x_758);
return x_760;
}
else
{
obj* x_761; obj* x_762; obj* x_763; obj* x_764; 
x_761 = lean::cnstr_get(x_757, 0);
lean::inc(x_761);
x_762 = lean::cnstr_get(x_757, 1);
lean::inc(x_762);
if (lean::is_exclusive(x_757)) {
 lean::cnstr_release(x_757, 0);
 lean::cnstr_release(x_757, 1);
 x_763 = x_757;
} else {
 lean::dec_ref(x_757);
 x_763 = lean::box(0);
}
if (lean::is_scalar(x_763)) {
 x_764 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_764 = x_763;
}
lean::cnstr_set(x_764, 0, x_761);
lean::cnstr_set(x_764, 1, x_762);
return x_764;
}
}
else
{
obj* x_765; obj* x_766; obj* x_767; obj* x_768; 
lean::dec(x_669);
lean::dec(x_1);
x_765 = lean::cnstr_get(x_753, 0);
lean::inc(x_765);
x_766 = lean::cnstr_get(x_753, 1);
lean::inc(x_766);
if (lean::is_exclusive(x_753)) {
 lean::cnstr_release(x_753, 0);
 lean::cnstr_release(x_753, 1);
 x_767 = x_753;
} else {
 lean::dec_ref(x_753);
 x_767 = lean::box(0);
}
if (lean::is_scalar(x_767)) {
 x_768 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_768 = x_767;
}
lean::cnstr_set(x_768, 0, x_765);
lean::cnstr_set(x_768, 1, x_766);
return x_768;
}
}
else
{
obj* x_769; obj* x_770; obj* x_771; obj* x_772; 
lean::dec(x_669);
lean::dec(x_1);
x_769 = lean::cnstr_get(x_744, 0);
lean::inc(x_769);
x_770 = lean::cnstr_get(x_744, 1);
lean::inc(x_770);
if (lean::is_exclusive(x_744)) {
 lean::cnstr_release(x_744, 0);
 lean::cnstr_release(x_744, 1);
 x_771 = x_744;
} else {
 lean::dec_ref(x_744);
 x_771 = lean::box(0);
}
if (lean::is_scalar(x_771)) {
 x_772 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_772 = x_771;
}
lean::cnstr_set(x_772, 0, x_769);
lean::cnstr_set(x_772, 1, x_770);
return x_772;
}
}
else
{
obj* x_773; obj* x_774; obj* x_775; obj* x_776; 
lean::dec(x_680);
lean::dec(x_669);
lean::dec(x_1);
x_773 = lean::cnstr_get(x_735, 0);
lean::inc(x_773);
x_774 = lean::cnstr_get(x_735, 1);
lean::inc(x_774);
if (lean::is_exclusive(x_735)) {
 lean::cnstr_release(x_735, 0);
 lean::cnstr_release(x_735, 1);
 x_775 = x_735;
} else {
 lean::dec_ref(x_735);
 x_775 = lean::box(0);
}
if (lean::is_scalar(x_775)) {
 x_776 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_776 = x_775;
}
lean::cnstr_set(x_776, 0, x_773);
lean::cnstr_set(x_776, 1, x_774);
return x_776;
}
}
else
{
obj* x_777; obj* x_778; obj* x_779; obj* x_780; 
lean::dec(x_697);
lean::dec(x_680);
lean::dec(x_669);
lean::dec(x_1);
x_777 = lean::cnstr_get(x_727, 0);
lean::inc(x_777);
x_778 = lean::cnstr_get(x_727, 1);
lean::inc(x_778);
if (lean::is_exclusive(x_727)) {
 lean::cnstr_release(x_727, 0);
 lean::cnstr_release(x_727, 1);
 x_779 = x_727;
} else {
 lean::dec_ref(x_727);
 x_779 = lean::box(0);
}
if (lean::is_scalar(x_779)) {
 x_780 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_780 = x_779;
}
lean::cnstr_set(x_780, 0, x_777);
lean::cnstr_set(x_780, 1, x_778);
return x_780;
}
}
else
{
obj* x_781; obj* x_782; obj* x_783; obj* x_784; 
lean::dec(x_697);
lean::dec(x_680);
lean::dec(x_669);
lean::dec(x_1);
x_781 = lean::cnstr_get(x_719, 0);
lean::inc(x_781);
x_782 = lean::cnstr_get(x_719, 1);
lean::inc(x_782);
if (lean::is_exclusive(x_719)) {
 lean::cnstr_release(x_719, 0);
 lean::cnstr_release(x_719, 1);
 x_783 = x_719;
} else {
 lean::dec_ref(x_719);
 x_783 = lean::box(0);
}
if (lean::is_scalar(x_783)) {
 x_784 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_784 = x_783;
}
lean::cnstr_set(x_784, 0, x_781);
lean::cnstr_set(x_784, 1, x_782);
return x_784;
}
}
else
{
obj* x_785; obj* x_786; obj* x_787; obj* x_788; 
lean::dec(x_706);
lean::dec(x_697);
lean::dec(x_680);
lean::dec(x_669);
lean::dec(x_1);
x_785 = lean::cnstr_get(x_711, 0);
lean::inc(x_785);
x_786 = lean::cnstr_get(x_711, 1);
lean::inc(x_786);
if (lean::is_exclusive(x_711)) {
 lean::cnstr_release(x_711, 0);
 lean::cnstr_release(x_711, 1);
 x_787 = x_711;
} else {
 lean::dec_ref(x_711);
 x_787 = lean::box(0);
}
if (lean::is_scalar(x_787)) {
 x_788 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_788 = x_787;
}
lean::cnstr_set(x_788, 0, x_785);
lean::cnstr_set(x_788, 1, x_786);
return x_788;
}
}
else
{
obj* x_789; obj* x_790; obj* x_791; obj* x_792; 
lean::dec(x_697);
lean::dec(x_680);
lean::dec(x_669);
lean::dec(x_1);
x_789 = lean::cnstr_get(x_702, 0);
lean::inc(x_789);
x_790 = lean::cnstr_get(x_702, 1);
lean::inc(x_790);
if (lean::is_exclusive(x_702)) {
 lean::cnstr_release(x_702, 0);
 lean::cnstr_release(x_702, 1);
 x_791 = x_702;
} else {
 lean::dec_ref(x_702);
 x_791 = lean::box(0);
}
if (lean::is_scalar(x_791)) {
 x_792 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_792 = x_791;
}
lean::cnstr_set(x_792, 0, x_789);
lean::cnstr_set(x_792, 1, x_790);
return x_792;
}
}
else
{
obj* x_793; obj* x_794; obj* x_795; obj* x_796; 
lean::dec(x_680);
lean::dec(x_669);
lean::dec(x_1);
x_793 = lean::cnstr_get(x_693, 0);
lean::inc(x_793);
x_794 = lean::cnstr_get(x_693, 1);
lean::inc(x_794);
if (lean::is_exclusive(x_693)) {
 lean::cnstr_release(x_693, 0);
 lean::cnstr_release(x_693, 1);
 x_795 = x_693;
} else {
 lean::dec_ref(x_693);
 x_795 = lean::box(0);
}
if (lean::is_scalar(x_795)) {
 x_796 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_796 = x_795;
}
lean::cnstr_set(x_796, 0, x_793);
lean::cnstr_set(x_796, 1, x_794);
return x_796;
}
}
else
{
obj* x_797; obj* x_798; obj* x_799; obj* x_800; 
lean::dec(x_680);
lean::dec(x_679);
lean::dec(x_669);
lean::dec(x_1);
x_797 = lean::cnstr_get(x_686, 0);
lean::inc(x_797);
x_798 = lean::cnstr_get(x_686, 1);
lean::inc(x_798);
if (lean::is_exclusive(x_686)) {
 lean::cnstr_release(x_686, 0);
 lean::cnstr_release(x_686, 1);
 x_799 = x_686;
} else {
 lean::dec_ref(x_686);
 x_799 = lean::box(0);
}
if (lean::is_scalar(x_799)) {
 x_800 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_800 = x_799;
}
lean::cnstr_set(x_800, 0, x_797);
lean::cnstr_set(x_800, 1, x_798);
return x_800;
}
}
}
else
{
uint8 x_801; 
lean::dec(x_1);
x_801 = !lean::is_exclusive(x_4);
if (x_801 == 0)
{
return x_4;
}
else
{
obj* x_802; obj* x_803; obj* x_804; 
x_802 = lean::cnstr_get(x_4, 0);
x_803 = lean::cnstr_get(x_4, 1);
lean::inc(x_803);
lean::inc(x_802);
lean::dec(x_4);
x_804 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_804, 0, x_802);
lean::cnstr_set(x_804, 1, x_803);
return x_804;
}
}
}
}
obj* l_List_toStringAux___main___at_Lean_Environment_displayStats___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
lean::dec(x_1);
x_4 = l_List_toStringAux___main___at_Lean_Environment_displayStats___spec__2(x_3, x_2);
return x_4;
}
}
obj* l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__6___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__6(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__8___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__8(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__9___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__9(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* initialize_init_system_io(obj*);
obj* initialize_init_util(obj*);
obj* initialize_init_data_bytearray_default(obj*);
obj* initialize_init_lean_declaration(obj*);
obj* initialize_init_lean_smap(obj*);
obj* initialize_init_lean_path(obj*);
obj* initialize_init_lean_localcontext(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_environment(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_system_io(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_util(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_data_bytearray_default(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_declaration(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_smap(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_path(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_localcontext(w);
if (lean::io_result_is_error(w)) return w;
l_Lean_EnvExtensionState_inhabited = _init_l_Lean_EnvExtensionState_inhabited();
lean::mark_persistent(l_Lean_EnvExtensionState_inhabited);
l_Lean_ModuleIdx_inhabited = _init_l_Lean_ModuleIdx_inhabited();
lean::mark_persistent(l_Lean_ModuleIdx_inhabited);
l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__1 = _init_l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__1();
lean::mark_persistent(l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__1);
l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__2 = _init_l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__2();
lean::mark_persistent(l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__2);
l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__3 = _init_l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__3();
lean::mark_persistent(l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__3);
l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__4 = _init_l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__4();
lean::mark_persistent(l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__4);
l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2 = _init_l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2();
lean::mark_persistent(l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2);
l_Lean_Environment_Inhabited___closed__1 = _init_l_Lean_Environment_Inhabited___closed__1();
lean::mark_persistent(l_Lean_Environment_Inhabited___closed__1);
l_Lean_Environment_Inhabited___closed__2 = _init_l_Lean_Environment_Inhabited___closed__2();
lean::mark_persistent(l_Lean_Environment_Inhabited___closed__2);
l_Lean_Environment_Inhabited___closed__3 = _init_l_Lean_Environment_Inhabited___closed__3();
lean::mark_persistent(l_Lean_Environment_Inhabited___closed__3);
l_Lean_Environment_Inhabited = _init_l_Lean_Environment_Inhabited();
lean::mark_persistent(l_Lean_Environment_Inhabited);
l_Lean_EnvExtension_setState___closed__1 = _init_l_Lean_EnvExtension_setState___closed__1();
lean::mark_persistent(l_Lean_EnvExtension_setState___closed__1);
w = l___private_init_lean_environment_4__mkEnvExtensionsRef(w);
if (lean::io_result_is_error(w)) return w;
l___private_init_lean_environment_5__envExtensionsRef = lean::io_result_get_value(w);
lean::mark_persistent(l___private_init_lean_environment_5__envExtensionsRef);
l_Lean_EnvExtension_Inhabited___rarg___closed__1 = _init_l_Lean_EnvExtension_Inhabited___rarg___closed__1();
lean::mark_persistent(l_Lean_EnvExtension_Inhabited___rarg___closed__1);
l_Lean_registerEnvExtensionUnsafe___rarg___closed__1 = _init_l_Lean_registerEnvExtensionUnsafe___rarg___closed__1();
lean::mark_persistent(l_Lean_registerEnvExtensionUnsafe___rarg___closed__1);
l_Lean_registerEnvExtensionUnsafe___rarg___closed__2 = _init_l_Lean_registerEnvExtensionUnsafe___rarg___closed__2();
lean::mark_persistent(l_Lean_registerEnvExtensionUnsafe___rarg___closed__2);
l_Lean_mkEmptyEnvironment___closed__1 = _init_l_Lean_mkEmptyEnvironment___closed__1();
lean::mark_persistent(l_Lean_mkEmptyEnvironment___closed__1);
l_Lean_EnvExtensionEntry_inhabited = _init_l_Lean_EnvExtensionEntry_inhabited();
lean::mark_persistent(l_Lean_EnvExtensionEntry_inhabited);
l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1 = _init_l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1();
lean::mark_persistent(l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1);
l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2 = _init_l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2();
lean::mark_persistent(l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2);
l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3 = _init_l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3();
lean::mark_persistent(l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3);
l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4 = _init_l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4();
lean::mark_persistent(l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4);
w = l___private_init_lean_environment_7__mkPersistentEnvExtensionsRef(w);
if (lean::io_result_is_error(w)) return w;
l___private_init_lean_environment_8__persistentEnvExtensionsRef = lean::io_result_get_value(w);
lean::mark_persistent(l___private_init_lean_environment_8__persistentEnvExtensionsRef);
l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1 = _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1();
lean::mark_persistent(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1);
l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2 = _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2();
lean::mark_persistent(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2);
l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3 = _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3();
lean::mark_persistent(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3);
l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4 = _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4();
lean::mark_persistent(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4);
l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__1 = _init_l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__1();
lean::mark_persistent(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__1);
l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__2 = _init_l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__2();
lean::mark_persistent(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__2);
l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1 = _init_l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1();
lean::mark_persistent(l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1);
l_Lean_CPPExtensionState_inhabited = _init_l_Lean_CPPExtensionState_inhabited();
lean::mark_persistent(l_Lean_CPPExtensionState_inhabited);
l_Lean_Modification_inhabited = _init_l_Lean_Modification_inhabited();
lean::mark_persistent(l_Lean_Modification_inhabited);
l_Lean_registerEnvExtensionUnsafe___at_Lean_regModListExtension___spec__1___closed__1 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_regModListExtension___spec__1___closed__1();
lean::mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_regModListExtension___spec__1___closed__1);
l_Lean_regModListExtension___closed__1 = _init_l_Lean_regModListExtension___closed__1();
lean::mark_persistent(l_Lean_regModListExtension___closed__1);
l_Lean_modListExtension___closed__1 = _init_l_Lean_modListExtension___closed__1();
lean::mark_persistent(l_Lean_modListExtension___closed__1);
l_Lean_modListExtension___closed__2 = _init_l_Lean_modListExtension___closed__2();
lean::mark_persistent(l_Lean_modListExtension___closed__2);
w = l_Lean_regModListExtension(w);
if (lean::io_result_is_error(w)) return w;
l_Lean_modListExtension = lean::io_result_get_value(w);
lean::mark_persistent(l_Lean_modListExtension);
l_Lean_ModuleData_inhabited___closed__1 = _init_l_Lean_ModuleData_inhabited___closed__1();
lean::mark_persistent(l_Lean_ModuleData_inhabited___closed__1);
l_Lean_ModuleData_inhabited = _init_l_Lean_ModuleData_inhabited();
lean::mark_persistent(l_Lean_ModuleData_inhabited);
l___private_init_lean_environment_9__getEntriesFor___main___closed__1 = _init_l___private_init_lean_environment_9__getEntriesFor___main___closed__1();
lean::mark_persistent(l___private_init_lean_environment_9__getEntriesFor___main___closed__1);
l_Array_miterateAux___main___at_Lean_importModules___spec__9___closed__1 = _init_l_Array_miterateAux___main___at_Lean_importModules___spec__9___closed__1();
lean::mark_persistent(l_Array_miterateAux___main___at_Lean_importModules___spec__9___closed__1);
l_Lean_importModules___closed__1 = _init_l_Lean_importModules___closed__1();
lean::mark_persistent(l_Lean_importModules___closed__1);
l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7___closed__1 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7___closed__1();
lean::mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7___closed__1);
l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7___closed__2 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7___closed__2();
lean::mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7___closed__2);
l_Lean_regNamespacesExtension___closed__1 = _init_l_Lean_regNamespacesExtension___closed__1();
lean::mark_persistent(l_Lean_regNamespacesExtension___closed__1);
l_Lean_regNamespacesExtension___closed__2 = _init_l_Lean_regNamespacesExtension___closed__2();
lean::mark_persistent(l_Lean_regNamespacesExtension___closed__2);
l_Lean_regNamespacesExtension___closed__3 = _init_l_Lean_regNamespacesExtension___closed__3();
lean::mark_persistent(l_Lean_regNamespacesExtension___closed__3);
l_Lean_regNamespacesExtension___closed__4 = _init_l_Lean_regNamespacesExtension___closed__4();
lean::mark_persistent(l_Lean_regNamespacesExtension___closed__4);
l_Lean_regNamespacesExtension___closed__5 = _init_l_Lean_regNamespacesExtension___closed__5();
lean::mark_persistent(l_Lean_regNamespacesExtension___closed__5);
l_Lean_regNamespacesExtension___closed__6 = _init_l_Lean_regNamespacesExtension___closed__6();
lean::mark_persistent(l_Lean_regNamespacesExtension___closed__6);
l_Lean_namespacesExt___closed__1 = _init_l_Lean_namespacesExt___closed__1();
lean::mark_persistent(l_Lean_namespacesExt___closed__1);
l_Lean_namespacesExt___closed__2 = _init_l_Lean_namespacesExt___closed__2();
lean::mark_persistent(l_Lean_namespacesExt___closed__2);
l_Lean_namespacesExt___closed__3 = _init_l_Lean_namespacesExt___closed__3();
lean::mark_persistent(l_Lean_namespacesExt___closed__3);
l_Lean_namespacesExt___closed__4 = _init_l_Lean_namespacesExt___closed__4();
lean::mark_persistent(l_Lean_namespacesExt___closed__4);
l_Lean_namespacesExt___closed__5 = _init_l_Lean_namespacesExt___closed__5();
lean::mark_persistent(l_Lean_namespacesExt___closed__5);
l_Lean_namespacesExt___closed__6 = _init_l_Lean_namespacesExt___closed__6();
lean::mark_persistent(l_Lean_namespacesExt___closed__6);
w = l_Lean_regNamespacesExtension(w);
if (lean::io_result_is_error(w)) return w;
l_Lean_namespacesExt = lean::io_result_get_value(w);
lean::mark_persistent(l_Lean_namespacesExt);
l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__1 = _init_l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__1();
lean::mark_persistent(l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__1);
l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__2 = _init_l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__2();
lean::mark_persistent(l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__2);
l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__3 = _init_l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__3();
lean::mark_persistent(l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__3);
l_Lean_Environment_displayStats___closed__1 = _init_l_Lean_Environment_displayStats___closed__1();
lean::mark_persistent(l_Lean_Environment_displayStats___closed__1);
l_Lean_Environment_displayStats___closed__2 = _init_l_Lean_Environment_displayStats___closed__2();
lean::mark_persistent(l_Lean_Environment_displayStats___closed__2);
l_Lean_Environment_displayStats___closed__3 = _init_l_Lean_Environment_displayStats___closed__3();
lean::mark_persistent(l_Lean_Environment_displayStats___closed__3);
l_Lean_Environment_displayStats___closed__4 = _init_l_Lean_Environment_displayStats___closed__4();
lean::mark_persistent(l_Lean_Environment_displayStats___closed__4);
l_Lean_Environment_displayStats___closed__5 = _init_l_Lean_Environment_displayStats___closed__5();
lean::mark_persistent(l_Lean_Environment_displayStats___closed__5);
l_Lean_Environment_displayStats___closed__6 = _init_l_Lean_Environment_displayStats___closed__6();
lean::mark_persistent(l_Lean_Environment_displayStats___closed__6);
l_Lean_Environment_displayStats___closed__7 = _init_l_Lean_Environment_displayStats___closed__7();
lean::mark_persistent(l_Lean_Environment_displayStats___closed__7);
l_Lean_Environment_displayStats___closed__8 = _init_l_Lean_Environment_displayStats___closed__8();
lean::mark_persistent(l_Lean_Environment_displayStats___closed__8);
l_Lean_Environment_displayStats___closed__9 = _init_l_Lean_Environment_displayStats___closed__9();
lean::mark_persistent(l_Lean_Environment_displayStats___closed__9);
return w;
}
}

// Lean compiler output
// Module: init.lean.environment
// Imports: init.system.io init.util init.data.bytearray.default init.lean.declaration init.lean.smap init.lean.path init.lean.localcontext
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
lean_object* l_Lean_EnvExtension_modifyState___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_init_lean_environment_9__getEntriesFor___main___closed__1;
lean_object* l_Lean_Environment_getModuleIdxFor___boxed(lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_setStateUnsafe___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashMap___at_Lean_Environment_Inhabited___spec__1(lean_object*);
lean_object* l___private_init_lean_environment_7__mkPersistentEnvExtensionsRef(lean_object*);
lean_object* l_Lean_namespacesExt___closed__1;
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_inhabited(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
lean_object* lean_write_module(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_displayStats___closed__7;
lean_object* l_Lean_Environment_displayStats___closed__6;
lean_object* l_Lean_ModuleData_inhabited___closed__1;
lean_object* l_Lean_performModifications___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_namespacesExt___elambda__4(lean_object*);
uint8_t lean_name_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_importModules___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_set_main_module(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg(lean_object*);
uint8_t l_Array_anyMAux___main___at_Lean_regNamespacesExtension___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
lean_object* l_Lean_namespacesExt___elambda__1___boxed(lean_object*);
lean_object* l_HashMapImp_find___at_Lean_Environment_find___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_modifyStateUnsafe___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_displayStats___closed__4;
extern lean_object* l_Nat_Inhabited;
lean_object* l_Lean_mkStateFromImportedEntries___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_regNamespacesExtension___lambda__3(lean_object*);
lean_object* l_Lean_EnvExtension_Inhabited___rarg(lean_object*);
lean_object* l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_object* l_Lean_importModulesAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_getState(lean_object*);
lean_object* l_Lean_namespacesExt___elambda__2___boxed(lean_object*);
lean_object* l_Lean_isNamespace___boxed(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_importModules___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_addAux(lean_object*, lean_object*);
lean_object* l_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__6___boxed(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_setState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_object* l_Array_mkArray(lean_object*, lean_object*, lean_object*);
uint32_t lean_environment_trust_level(lean_object*);
extern lean_object* l_List_repr___rarg___closed__3;
lean_object* l_Lean_registerSimplePersistentEnvExtension(lean_object*, lean_object*);
lean_object* l_HashMapImp_insert___at_Lean_Environment_addAux___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_add_modification(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_Inhabited___rarg___closed__1;
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_displayStats___closed__5;
lean_object* l_Array_miterateAux___main___at___private_init_lean_environment_11__finalizePersistentExtensions___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_mark_quot_init(lean_object*);
lean_object* l_Lean_namespacesExt___elambda__3(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
lean_object* l_Array_miterateAux___main___at_Lean_importModules___spec__9___closed__1;
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_regNamespacesExtension___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_namespacesExt___elambda__1(lean_object*);
lean_object* l_Lean_EnvExtension_getStateUnsafe___rarg(lean_object*, lean_object*);
lean_object* l_AssocList_replace___main___at_Lean_importModules___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
lean_object* l_Nat_foldAux___main___at_Lean_mkModuleData___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Environment_displayStats___spec__1(lean_object*);
lean_object* l_Lean_mkStateFromImportedEntries(lean_object*, lean_object*);
lean_object* lean_add_decl(lean_object*, lean_object*);
extern lean_object* l_Lean_findOLean___closed__1;
lean_object* l_Lean_EnvExtension_modifyStateUnsafe(lean_object*);
uint8_t l_HashMapImp_contains___at_Lean_Environment_contains___spec__2(lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_import_modules(lean_object*, uint32_t, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__2(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Environment_displayStats___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__2;
lean_object* l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_SMap_contains___at_Lean_Environment_contains___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_mkEmptyEnvironment___closed__1;
lean_object* l_Lean_importModules___closed__1;
lean_object* l___private_init_lean_environment_13__registerNamePrefixes(lean_object*, lean_object*);
lean_object* l_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__6(lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_Environment_addAux___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__1;
lean_object* l_Array_uget(lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l___private_init_lean_environment_3__getTrustLevel___boxed(lean_object*);
lean_object* l_Lean_PersistentEnvExtensionState_inhabited___rarg(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_setState(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Inhabited;
lean_object* l_Array_uset(lean_object*, lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Environment_imports___boxed(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___main___rarg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg___boxed(lean_object*, lean_object*);
lean_object* l_IO_Prim_Ref_set(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at_Lean_Environment_find___spec__3(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_importModules___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__3(lean_object*, lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_Environment_addAux___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x27___at_Lean_Environment_find___spec__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_AssocList_find___main___at_Lean_Environment_getModuleIdxFor___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__3___boxed(lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_displayStats___closed__3;
lean_object* l___private_init_lean_environment_6__mkInitialExtensionStates(lean_object*);
lean_object* l_Lean_Name_quickLt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__3(lean_object*, lean_object*);
lean_object* l_Lean_regNamespacesExtension___lambda__1(lean_object*, lean_object*);
lean_object* l_RBNode_depth___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_setState___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_initializing(lean_object*);
lean_object* l_Lean_Environment_compileDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_importModules___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_setState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkEmpty(lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_Lean_registerSimplePersistentEnvExtension___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__2;
lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__2(lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_importModules___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_setState___closed__1;
lean_object* lean_mk_empty_environment(uint32_t, lean_object*);
extern lean_object* l_Lean_Name_DecidableEq;
lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionEntry_inhabited;
lean_object* l___private_init_lean_environment_10__setImportedEntries(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_regNamespacesExtension___closed__3;
lean_object* l___private_init_lean_environment_9__getEntriesFor___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___rarg(lean_object*, lean_object*);
lean_object* l_Lean_regModListExtension___closed__1;
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_regNamespacesExtension___spec__4(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__3(lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4___boxed(lean_object*);
lean_object* l___private_init_lean_environment_12__isNamespaceName___main___boxed(lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
lean_object* l_Lean_EnvExtensionState_inhabited;
lean_object* l_Lean_regNamespacesExtension___lambda__2(lean_object*);
lean_object* l_Lean_namespacesExt___closed__3;
lean_object* lean_perform_serialized_modifications(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_insert___at_Lean_Environment_addAux___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_find___at_Lean_Environment_getModuleIdxFor___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CPPExtensionState_inhabited;
lean_object* l_Lean_Environment_displayStats___closed__1;
lean_object* l_Lean_Environment_displayStats___closed__2;
size_t lean_name_hash_usize(lean_object*);
lean_object* l_Lean_readModuleData___boxed(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
lean_object* l___private_init_lean_environment_12__isNamespaceName___boxed(lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_importModules___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_registerPersistentEnvExtensionUnsafe___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_getStateUnsafe___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe(lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Environment_displayStats___spec__2(uint8_t, lean_object*);
lean_object* l_HashMapImp_insert___at_Lean_importModules___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_switch___at_Lean_importModules___spec__11(lean_object*);
lean_object* l_Array_miterateAux___main___at___private_init_lean_environment_10__setImportedEntries___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_importModules___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_beqOfEq___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_init_lean_environment_4__mkEnvExtensionsRef(lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_regModListExtension___spec__1___closed__1;
uint8_t lean_environment_quot_init(lean_object*);
lean_object* l_Lean_namespacesExt___elambda__3___boxed(lean_object*, lean_object*);
uint8_t l_Array_anyMAux___main___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_display_stats(lean_object*, lean_object*);
uint8_t l_Lean_Environment_isConstructor(lean_object*, lean_object*);
lean_object* l_Lean_regNamespacesExtension___closed__6;
lean_object* l_Lean_registerPersistentEnvExtension___rarg(lean_object*);
lean_object* l_Lean_Environment_Inhabited;
lean_object* l_Lean_Environment_Inhabited___closed__2;
lean_object* l_Lean_regNamespacesExtension___lambda__2___boxed(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_importModules___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtensionState_inhabited(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_importModules___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_namespacesExt;
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l_HashMapImp_moveEntries___main___at_Lean_importModules___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
uint8_t l_RBNode_isRed___rarg(lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* lean_save_module_data(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_getState___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState(lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x27___at_Lean_Environment_find___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
lean_object* l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_serialize_modifications(lean_object*, lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Array_miterateAux___main___at___private_init_lean_environment_11__finalizePersistentExtensions___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Environment_addAux___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3___boxed(lean_object*);
lean_object* l_Lean_Environment_Inhabited___closed__3;
lean_object* l_Lean_SimplePersistentEnvExtension_getEntries(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_namespacesExt___closed__4;
lean_object* l_Array_fget(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_importModules___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_regModListExtension___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_addAndCompile(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_regNamespacesExtension___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_Lean_regNamespacesExtension___spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_namespacesExt___closed__2;
lean_object* l_Lean_regNamespacesExtension___closed__2;
lean_object* l_Lean_namespacesExt___elambda__4___boxed(lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_RBMap_maxDepth___rarg___closed__1;
lean_object* l_Array_ummapAux___main___at___private_init_lean_environment_6__mkInitialExtensionStates___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getNamespaceSet___boxed(lean_object*);
lean_object* l_Lean_findLeanFile(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__3;
lean_object* l_Array_miterateAux___main___at___private_init_lean_environment_10__setImportedEntries___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ModuleIdx_inhabited;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(lean_object*);
lean_object* l_Lean_EnvExtension_setStateUnsafe___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_displayStats___closed__9;
lean_object* l_ExceptT_Monad___rarg___lambda__8___boxed(lean_object*, lean_object*);
lean_object* l_Lean_saveModuleData___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_regNamespacesExtension___closed__4;
lean_object* l_Array_push(lean_object*, lean_object*, lean_object*);
lean_object* lean_set_extension(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_regModListExtension(lean_object*);
lean_object* l_RBNode_find___main___at_Lean_Environment_find___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_SMap_insert___at_Lean_Environment_addAux___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4(lean_object*);
lean_object* l_Lean_namespacesExt___elambda__2(lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1;
lean_object* l_Lean_registerEnvExtension(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_importModulesAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_regNamespacesExtension___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_getState___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtension(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_registerCPPExtension___spec__1(lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at_Lean_Environment_find___spec__4(lean_object*, lean_object*);
lean_object* l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe(lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at_Lean_Environment_getModuleIdxFor___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_mkModuleData(lean_object*, lean_object*);
lean_object* l_IO_Prim_mkRef(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState(lean_object*, lean_object*);
lean_object* l___private_init_lean_environment_11__finalizePersistentExtensions(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_setState(lean_object*, lean_object*);
lean_object* l___private_init_lean_environment_13__registerNamePrefixes___main(lean_object*, lean_object*);
lean_object* l_Lean_SMap_contains___at_Lean_Environment_contains___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_modifyState(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_regNamespacesExtension___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_compile_decl(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at_Lean_mkModuleData___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isNamespace(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_find___at_Lean_Environment_getModuleIdxFor___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_regNamespacesExtension___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_namespacesExt___closed__5;
lean_object* l_Array_miterateAux___main___at_Lean_regNamespacesExtension___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_modListExtension___closed__1;
lean_object* l_Array_miterateAux___main___at___private_init_lean_environment_10__setImportedEntries___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_registerPersistentEnvExtensionUnsafe___spec__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_mfoldl___main___at_Lean_importModules___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_importModules___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_addDecl___boxed(lean_object*, lean_object*);
extern lean_object* l_NonScalar_Inhabited;
lean_object* l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__3;
lean_object* l_Lean_Environment_contains___boxed(lean_object*, lean_object*);
lean_object* lean_read_module_data(lean_object*, lean_object*);
lean_object* l_EState_bind___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_println___at_HasRepr_HasEval___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___boxed(lean_object*);
lean_object* l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5___boxed(lean_object*);
lean_object* l_Lean_namespacesExt___closed__6;
lean_object* l_RBNode_fold___main___at_Lean_mkModuleData___spec__2(lean_object*, lean_object*);
uint8_t l_Array_anyMAux___main___at_Lean_registerSimplePersistentEnvExtension___spec__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4(lean_object*);
lean_object* l_Lean_Environment_Inhabited___closed__1;
lean_object* l_Lean_Environment_addAndCompile___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__4;
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_replace___main___at_Lean_Environment_addAux___spec__9(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_Ref_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerNamespace(lean_object*, lean_object*);
lean_object* l___private_init_lean_environment_2__isQuotInit___boxed(lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* lean_register_extension(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_Inhabited___rarg(lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_getNamespaceSet(lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7___closed__1;
lean_object* l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2;
extern lean_object* l_HashMap_Inhabited___closed__1;
lean_object* l_Lean_modListExtension;
lean_object* l_Lean_Environment_isConstructor___boxed(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_importModules___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_init_lean_environment_9__getEntriesFor___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__2___boxed(lean_object*);
lean_object* lean_environment_add(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_setStateUnsafe(lean_object*);
lean_object* l_Array_size(lean_object*, lean_object*);
lean_object* l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__1;
lean_object* l_Lean_EnvExtension_Inhabited(lean_object*);
lean_object* l_EState_pure___rarg(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_setState___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Array_fset(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_get(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__2;
lean_object* l_Lean_EnvExtension_getStateUnsafe(lean_object*);
lean_object* l_RBNode_setBlack___rarg(lean_object*);
lean_object* l_Lean_Environment_imports(lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7(lean_object*, lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_importModules___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__1;
lean_object* l_Lean_SimplePersistentEnvExtension_Inhabited(lean_object*, lean_object*);
lean_object* l_Lean_modListExtension___closed__2;
lean_object* l_AssocList_find___main___at_Lean_Environment_find___spec__3___boxed(lean_object*, lean_object*);
lean_object* lean_get_extension(lean_object*, lean_object*);
lean_object* l_Lean_mkEmptyEnvironment___boxed(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtension___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
extern lean_object* l_Lean_Name_toString___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_Lean_registerSimplePersistentEnvExtension___spec__2(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Lean_regNamespacesExtension(lean_object*);
lean_object* l_AssocList_mfoldl___main___at_Lean_Environment_addAux___spec__8(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_modifyState(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__1(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Lean_serializeModifications___boxed(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_setState(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Format_isNil(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry(lean_object*, lean_object*);
lean_object* l_Array_set(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_regNamespacesExtension___closed__1;
lean_object* l_mkHashMap___at_Lean_Environment_Inhabited___spec__3(lean_object*);
lean_object* l_HashMapImp_find___at_Lean_Environment_find___spec__2(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_namespacesExt___elambda__4___rarg(lean_object*);
lean_object* l___private_init_lean_environment_9__getEntriesFor___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___rarg(lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_init_lean_environment_8__persistentEnvExtensionsRef;
lean_object* l_Lean_Modification_inhabited;
uint8_t l___private_init_lean_environment_12__isNamespaceName___main(lean_object*);
lean_object* l_Lean_Environment_displayStats___closed__8;
lean_object* l_Array_miterateAux___main___at___private_init_lean_environment_10__setImportedEntries___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3(lean_object*);
lean_object* l_Lean_ModuleData_inhabited;
uint8_t l___private_init_lean_environment_12__isNamespaceName(lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_Environment_addAux___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_modifyState(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_Inhabited___rarg___lambda__1(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l___private_init_lean_environment_9__getEntriesFor(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkStateFromImportedEntries___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
lean_object* l_Lean_regNamespacesExtension___closed__5;
lean_object* l___private_init_lean_environment_10__setImportedEntries___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_Ref_reset(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_importModules___spec__3(lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__1;
lean_object* l___private_init_lean_environment_5__envExtensionsRef;
lean_object* l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_importModules___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_importModules___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7___closed__2;
lean_object* l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7___boxed(lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_modListExtension___elambda__1(lean_object*);
lean_object* l_HashMapImp_contains___at_Lean_Environment_contains___spec__2___boxed(lean_object*, lean_object*);
lean_object* _init_l_Lean_EnvExtensionState_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_NonScalar_Inhabited;
return x_1;
}
}
lean_object* _init_l_Lean_ModuleIdx_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_Inhabited;
return x_1;
}
}
lean_object* l_mkHashMap___at_Lean_Environment_Inhabited___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_mkHashMap___at_Lean_Environment_Inhabited___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Name_DecidableEq;
x_2 = lean_alloc_closure((void*)(l_beqOfEq___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickLt___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 1;
x_3 = l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__2;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__4;
return x_1;
}
}
lean_object* _init_l_Lean_Environment_Inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Environment_Inhabited___closed__2() {
_start:
{
uint32_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 0;
x_3 = lean_box(0);
x_4 = l_Array_empty___closed__1;
x_5 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set_uint32(x_5, sizeof(void*)*2, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 4, x_2);
return x_5;
}
}
lean_object* _init_l_Lean_Environment_Inhabited___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Environment_Inhabited___closed__1;
x_2 = l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2;
x_3 = l_Array_empty___closed__1;
x_4 = l_Lean_Environment_Inhabited___closed__2;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Environment_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Environment_Inhabited___closed__3;
return x_1;
}
}
lean_object* l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; lean_object* x_5; 
x_4 = 0;
x_5 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*4, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = l_Lean_Name_quickLt(x_2, x_9);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Name_quickLt(x_9, x_2);
if (x_13 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_14; 
x_14 = l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(x_11, x_2, x_3);
lean_ctor_set(x_1, 3, x_14);
return x_1;
}
}
else
{
lean_object* x_15; 
x_15 = l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(x_8, x_2, x_3);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
x_20 = l_Lean_Name_quickLt(x_2, x_17);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Name_quickLt(x_17, x_2);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_17);
x_22 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_2);
lean_ctor_set(x_22, 2, x_3);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*4, x_6);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(x_19, x_2, x_3);
x_24 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_17);
lean_ctor_set(x_24, 2, x_18);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*4, x_6);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(x_16, x_2, x_3);
x_26 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_17);
lean_ctor_set(x_26, 2, x_18);
lean_ctor_set(x_26, 3, x_19);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_6);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_1);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_ctor_get(x_1, 2);
x_31 = lean_ctor_get(x_1, 3);
x_32 = l_Lean_Name_quickLt(x_2, x_29);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_Name_quickLt(x_29, x_2);
if (x_33 == 0)
{
lean_dec(x_30);
lean_dec(x_29);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
uint8_t x_34; 
x_34 = l_RBNode_isRed___rarg(x_31);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(x_31, x_2, x_3);
lean_ctor_set(x_1, 3, x_35);
return x_1;
}
else
{
lean_object* x_36; 
x_36 = l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(x_31, x_2, x_3);
if (lean_obj_tag(x_36) == 0)
{
lean_free_object(x_1);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 3);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_36, 3);
lean_dec(x_40);
x_41 = lean_ctor_get(x_36, 0);
lean_dec(x_41);
x_42 = 0;
lean_ctor_set(x_36, 0, x_38);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_42);
x_43 = 1;
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_43);
return x_1;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_36, 1);
x_45 = lean_ctor_get(x_36, 2);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = 0;
x_47 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_44);
lean_ctor_set(x_47, 2, x_45);
lean_ctor_set(x_47, 3, x_38);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_46);
x_48 = 1;
lean_ctor_set(x_1, 3, x_47);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_48);
return x_1;
}
}
else
{
uint8_t x_49; 
x_49 = lean_ctor_get_uint8(x_38, sizeof(void*)*4);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_36);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_36, 1);
x_52 = lean_ctor_get(x_36, 2);
x_53 = lean_ctor_get(x_36, 3);
lean_dec(x_53);
x_54 = lean_ctor_get(x_36, 0);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_38);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_38, 0);
x_57 = lean_ctor_get(x_38, 1);
x_58 = lean_ctor_get(x_38, 2);
x_59 = lean_ctor_get(x_38, 3);
x_60 = 1;
lean_ctor_set(x_38, 3, x_37);
lean_ctor_set(x_38, 2, x_30);
lean_ctor_set(x_38, 1, x_29);
lean_ctor_set(x_38, 0, x_28);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_60);
lean_ctor_set(x_36, 3, x_59);
lean_ctor_set(x_36, 2, x_58);
lean_ctor_set(x_36, 1, x_57);
lean_ctor_set(x_36, 0, x_56);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_60);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set(x_1, 2, x_52);
lean_ctor_set(x_1, 1, x_51);
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_38, 0);
x_62 = lean_ctor_get(x_38, 1);
x_63 = lean_ctor_get(x_38, 2);
x_64 = lean_ctor_get(x_38, 3);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_38);
x_65 = 1;
x_66 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_66, 0, x_28);
lean_ctor_set(x_66, 1, x_29);
lean_ctor_set(x_66, 2, x_30);
lean_ctor_set(x_66, 3, x_37);
lean_ctor_set_uint8(x_66, sizeof(void*)*4, x_65);
lean_ctor_set(x_36, 3, x_64);
lean_ctor_set(x_36, 2, x_63);
lean_ctor_set(x_36, 1, x_62);
lean_ctor_set(x_36, 0, x_61);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_65);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set(x_1, 2, x_52);
lean_ctor_set(x_1, 1, x_51);
lean_ctor_set(x_1, 0, x_66);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; 
x_67 = lean_ctor_get(x_36, 1);
x_68 = lean_ctor_get(x_36, 2);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_36);
x_69 = lean_ctor_get(x_38, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_38, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_38, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_38, 3);
lean_inc(x_72);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 x_73 = x_38;
} else {
 lean_dec_ref(x_38);
 x_73 = lean_box(0);
}
x_74 = 1;
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(1, 4, 1);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_28);
lean_ctor_set(x_75, 1, x_29);
lean_ctor_set(x_75, 2, x_30);
lean_ctor_set(x_75, 3, x_37);
lean_ctor_set_uint8(x_75, sizeof(void*)*4, x_74);
x_76 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_76, 0, x_69);
lean_ctor_set(x_76, 1, x_70);
lean_ctor_set(x_76, 2, x_71);
lean_ctor_set(x_76, 3, x_72);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_74);
lean_ctor_set(x_1, 3, x_76);
lean_ctor_set(x_1, 2, x_68);
lean_ctor_set(x_1, 1, x_67);
lean_ctor_set(x_1, 0, x_75);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_36);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_36, 3);
lean_dec(x_78);
x_79 = lean_ctor_get(x_36, 0);
lean_dec(x_79);
x_80 = 0;
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_80);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_36, 1);
x_82 = lean_ctor_get(x_36, 2);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_36);
x_83 = 0;
x_84 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_84, 0, x_37);
lean_ctor_set(x_84, 1, x_81);
lean_ctor_set(x_84, 2, x_82);
lean_ctor_set(x_84, 3, x_38);
lean_ctor_set_uint8(x_84, sizeof(void*)*4, x_83);
lean_ctor_set(x_1, 3, x_84);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
}
}
else
{
uint8_t x_85; 
x_85 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
if (x_85 == 0)
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_36);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_36, 0);
lean_dec(x_87);
x_88 = !lean_is_exclusive(x_37);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_89 = lean_ctor_get(x_37, 0);
x_90 = lean_ctor_get(x_37, 1);
x_91 = lean_ctor_get(x_37, 2);
x_92 = lean_ctor_get(x_37, 3);
x_93 = 1;
lean_ctor_set(x_37, 3, x_89);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 1, x_29);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_93);
lean_ctor_set(x_36, 0, x_92);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_93);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set(x_1, 2, x_91);
lean_ctor_set(x_1, 1, x_90);
lean_ctor_set(x_1, 0, x_37);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_37, 0);
x_95 = lean_ctor_get(x_37, 1);
x_96 = lean_ctor_get(x_37, 2);
x_97 = lean_ctor_get(x_37, 3);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_37);
x_98 = 1;
x_99 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_99, 0, x_28);
lean_ctor_set(x_99, 1, x_29);
lean_ctor_set(x_99, 2, x_30);
lean_ctor_set(x_99, 3, x_94);
lean_ctor_set_uint8(x_99, sizeof(void*)*4, x_98);
lean_ctor_set(x_36, 0, x_97);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_98);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set(x_1, 2, x_96);
lean_ctor_set(x_1, 1, x_95);
lean_ctor_set(x_1, 0, x_99);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; 
x_100 = lean_ctor_get(x_36, 1);
x_101 = lean_ctor_get(x_36, 2);
x_102 = lean_ctor_get(x_36, 3);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_36);
x_103 = lean_ctor_get(x_37, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_37, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_37, 2);
lean_inc(x_105);
x_106 = lean_ctor_get(x_37, 3);
lean_inc(x_106);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_107 = x_37;
} else {
 lean_dec_ref(x_37);
 x_107 = lean_box(0);
}
x_108 = 1;
if (lean_is_scalar(x_107)) {
 x_109 = lean_alloc_ctor(1, 4, 1);
} else {
 x_109 = x_107;
}
lean_ctor_set(x_109, 0, x_28);
lean_ctor_set(x_109, 1, x_29);
lean_ctor_set(x_109, 2, x_30);
lean_ctor_set(x_109, 3, x_103);
lean_ctor_set_uint8(x_109, sizeof(void*)*4, x_108);
x_110 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_110, 0, x_106);
lean_ctor_set(x_110, 1, x_100);
lean_ctor_set(x_110, 2, x_101);
lean_ctor_set(x_110, 3, x_102);
lean_ctor_set_uint8(x_110, sizeof(void*)*4, x_108);
lean_ctor_set(x_1, 3, x_110);
lean_ctor_set(x_1, 2, x_105);
lean_ctor_set(x_1, 1, x_104);
lean_ctor_set(x_1, 0, x_109);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_36, 3);
lean_inc(x_111);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_36);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_113 = lean_ctor_get(x_36, 3);
lean_dec(x_113);
x_114 = lean_ctor_get(x_36, 0);
lean_dec(x_114);
x_115 = 0;
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_115);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_36, 1);
x_117 = lean_ctor_get(x_36, 2);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_36);
x_118 = 0;
x_119 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_119, 0, x_37);
lean_ctor_set(x_119, 1, x_116);
lean_ctor_set(x_119, 2, x_117);
lean_ctor_set(x_119, 3, x_111);
lean_ctor_set_uint8(x_119, sizeof(void*)*4, x_118);
lean_ctor_set(x_1, 3, x_119);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
uint8_t x_120; 
x_120 = lean_ctor_get_uint8(x_111, sizeof(void*)*4);
if (x_120 == 0)
{
uint8_t x_121; 
lean_free_object(x_1);
x_121 = !lean_is_exclusive(x_36);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_122 = lean_ctor_get(x_36, 3);
lean_dec(x_122);
x_123 = lean_ctor_get(x_36, 0);
lean_dec(x_123);
x_124 = !lean_is_exclusive(x_111);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_125 = lean_ctor_get(x_111, 0);
x_126 = lean_ctor_get(x_111, 1);
x_127 = lean_ctor_get(x_111, 2);
x_128 = lean_ctor_get(x_111, 3);
lean_inc(x_37);
lean_ctor_set(x_111, 3, x_37);
lean_ctor_set(x_111, 2, x_30);
lean_ctor_set(x_111, 1, x_29);
lean_ctor_set(x_111, 0, x_28);
x_129 = !lean_is_exclusive(x_37);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_37, 3);
lean_dec(x_130);
x_131 = lean_ctor_get(x_37, 2);
lean_dec(x_131);
x_132 = lean_ctor_get(x_37, 1);
lean_dec(x_132);
x_133 = lean_ctor_get(x_37, 0);
lean_dec(x_133);
lean_ctor_set_uint8(x_111, sizeof(void*)*4, x_85);
lean_ctor_set(x_37, 3, x_128);
lean_ctor_set(x_37, 2, x_127);
lean_ctor_set(x_37, 1, x_126);
lean_ctor_set(x_37, 0, x_125);
lean_ctor_set(x_36, 3, x_37);
lean_ctor_set(x_36, 0, x_111);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_120);
return x_36;
}
else
{
lean_object* x_134; 
lean_dec(x_37);
lean_ctor_set_uint8(x_111, sizeof(void*)*4, x_85);
x_134 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_134, 0, x_125);
lean_ctor_set(x_134, 1, x_126);
lean_ctor_set(x_134, 2, x_127);
lean_ctor_set(x_134, 3, x_128);
lean_ctor_set_uint8(x_134, sizeof(void*)*4, x_85);
lean_ctor_set(x_36, 3, x_134);
lean_ctor_set(x_36, 0, x_111);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_135 = lean_ctor_get(x_111, 0);
x_136 = lean_ctor_get(x_111, 1);
x_137 = lean_ctor_get(x_111, 2);
x_138 = lean_ctor_get(x_111, 3);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_111);
lean_inc(x_37);
x_139 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_139, 0, x_28);
lean_ctor_set(x_139, 1, x_29);
lean_ctor_set(x_139, 2, x_30);
lean_ctor_set(x_139, 3, x_37);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_140 = x_37;
} else {
 lean_dec_ref(x_37);
 x_140 = lean_box(0);
}
lean_ctor_set_uint8(x_139, sizeof(void*)*4, x_85);
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 4, 1);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_135);
lean_ctor_set(x_141, 1, x_136);
lean_ctor_set(x_141, 2, x_137);
lean_ctor_set(x_141, 3, x_138);
lean_ctor_set_uint8(x_141, sizeof(void*)*4, x_85);
lean_ctor_set(x_36, 3, x_141);
lean_ctor_set(x_36, 0, x_139);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_142 = lean_ctor_get(x_36, 1);
x_143 = lean_ctor_get(x_36, 2);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_36);
x_144 = lean_ctor_get(x_111, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_111, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_111, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_111, 3);
lean_inc(x_147);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 lean_ctor_release(x_111, 2);
 lean_ctor_release(x_111, 3);
 x_148 = x_111;
} else {
 lean_dec_ref(x_111);
 x_148 = lean_box(0);
}
lean_inc(x_37);
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 4, 1);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_28);
lean_ctor_set(x_149, 1, x_29);
lean_ctor_set(x_149, 2, x_30);
lean_ctor_set(x_149, 3, x_37);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_150 = x_37;
} else {
 lean_dec_ref(x_37);
 x_150 = lean_box(0);
}
lean_ctor_set_uint8(x_149, sizeof(void*)*4, x_85);
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 4, 1);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_144);
lean_ctor_set(x_151, 1, x_145);
lean_ctor_set(x_151, 2, x_146);
lean_ctor_set(x_151, 3, x_147);
lean_ctor_set_uint8(x_151, sizeof(void*)*4, x_85);
x_152 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_142);
lean_ctor_set(x_152, 2, x_143);
lean_ctor_set(x_152, 3, x_151);
lean_ctor_set_uint8(x_152, sizeof(void*)*4, x_120);
return x_152;
}
}
else
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_36);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_154 = lean_ctor_get(x_36, 3);
lean_dec(x_154);
x_155 = lean_ctor_get(x_36, 0);
lean_dec(x_155);
x_156 = !lean_is_exclusive(x_37);
if (x_156 == 0)
{
uint8_t x_157; 
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_120);
x_157 = 0;
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_157);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_120);
return x_1;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_158 = lean_ctor_get(x_37, 0);
x_159 = lean_ctor_get(x_37, 1);
x_160 = lean_ctor_get(x_37, 2);
x_161 = lean_ctor_get(x_37, 3);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_37);
x_162 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_162, 0, x_158);
lean_ctor_set(x_162, 1, x_159);
lean_ctor_set(x_162, 2, x_160);
lean_ctor_set(x_162, 3, x_161);
lean_ctor_set_uint8(x_162, sizeof(void*)*4, x_120);
x_163 = 0;
lean_ctor_set(x_36, 0, x_162);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_163);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_120);
return x_1;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; 
x_164 = lean_ctor_get(x_36, 1);
x_165 = lean_ctor_get(x_36, 2);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_36);
x_166 = lean_ctor_get(x_37, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_37, 1);
lean_inc(x_167);
x_168 = lean_ctor_get(x_37, 2);
lean_inc(x_168);
x_169 = lean_ctor_get(x_37, 3);
lean_inc(x_169);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_170 = x_37;
} else {
 lean_dec_ref(x_37);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 4, 1);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_166);
lean_ctor_set(x_171, 1, x_167);
lean_ctor_set(x_171, 2, x_168);
lean_ctor_set(x_171, 3, x_169);
lean_ctor_set_uint8(x_171, sizeof(void*)*4, x_120);
x_172 = 0;
x_173 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_164);
lean_ctor_set(x_173, 2, x_165);
lean_ctor_set(x_173, 3, x_111);
lean_ctor_set_uint8(x_173, sizeof(void*)*4, x_172);
lean_ctor_set(x_1, 3, x_173);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_120);
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
uint8_t x_174; 
x_174 = l_RBNode_isRed___rarg(x_28);
if (x_174 == 0)
{
lean_object* x_175; 
x_175 = l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(x_28, x_2, x_3);
lean_ctor_set(x_1, 0, x_175);
return x_1;
}
else
{
lean_object* x_176; 
x_176 = l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(x_28, x_2, x_3);
if (lean_obj_tag(x_176) == 0)
{
lean_free_object(x_1);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
return x_176;
}
else
{
lean_object* x_177; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; 
x_178 = lean_ctor_get(x_176, 3);
lean_inc(x_178);
if (lean_obj_tag(x_178) == 0)
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_176);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; uint8_t x_183; 
x_180 = lean_ctor_get(x_176, 3);
lean_dec(x_180);
x_181 = lean_ctor_get(x_176, 0);
lean_dec(x_181);
x_182 = 0;
lean_ctor_set(x_176, 0, x_178);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_182);
x_183 = 1;
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_183);
return x_1;
}
else
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; uint8_t x_188; 
x_184 = lean_ctor_get(x_176, 1);
x_185 = lean_ctor_get(x_176, 2);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_176);
x_186 = 0;
x_187 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_187, 0, x_178);
lean_ctor_set(x_187, 1, x_184);
lean_ctor_set(x_187, 2, x_185);
lean_ctor_set(x_187, 3, x_178);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_186);
x_188 = 1;
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
else
{
uint8_t x_189; 
x_189 = lean_ctor_get_uint8(x_178, sizeof(void*)*4);
if (x_189 == 0)
{
uint8_t x_190; 
x_190 = !lean_is_exclusive(x_176);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_191 = lean_ctor_get(x_176, 1);
x_192 = lean_ctor_get(x_176, 2);
x_193 = lean_ctor_get(x_176, 3);
lean_dec(x_193);
x_194 = lean_ctor_get(x_176, 0);
lean_dec(x_194);
x_195 = !lean_is_exclusive(x_178);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_196 = lean_ctor_get(x_178, 0);
x_197 = lean_ctor_get(x_178, 1);
x_198 = lean_ctor_get(x_178, 2);
x_199 = lean_ctor_get(x_178, 3);
x_200 = 1;
lean_ctor_set(x_178, 3, x_196);
lean_ctor_set(x_178, 2, x_192);
lean_ctor_set(x_178, 1, x_191);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set_uint8(x_178, sizeof(void*)*4, x_200);
lean_ctor_set(x_176, 3, x_31);
lean_ctor_set(x_176, 2, x_30);
lean_ctor_set(x_176, 1, x_29);
lean_ctor_set(x_176, 0, x_199);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_200);
lean_ctor_set(x_1, 3, x_176);
lean_ctor_set(x_1, 2, x_198);
lean_ctor_set(x_1, 1, x_197);
lean_ctor_set(x_1, 0, x_178);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; 
x_201 = lean_ctor_get(x_178, 0);
x_202 = lean_ctor_get(x_178, 1);
x_203 = lean_ctor_get(x_178, 2);
x_204 = lean_ctor_get(x_178, 3);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_178);
x_205 = 1;
x_206 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_206, 0, x_177);
lean_ctor_set(x_206, 1, x_191);
lean_ctor_set(x_206, 2, x_192);
lean_ctor_set(x_206, 3, x_201);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_205);
lean_ctor_set(x_176, 3, x_31);
lean_ctor_set(x_176, 2, x_30);
lean_ctor_set(x_176, 1, x_29);
lean_ctor_set(x_176, 0, x_204);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_205);
lean_ctor_set(x_1, 3, x_176);
lean_ctor_set(x_1, 2, x_203);
lean_ctor_set(x_1, 1, x_202);
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; 
x_207 = lean_ctor_get(x_176, 1);
x_208 = lean_ctor_get(x_176, 2);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_176);
x_209 = lean_ctor_get(x_178, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_178, 1);
lean_inc(x_210);
x_211 = lean_ctor_get(x_178, 2);
lean_inc(x_211);
x_212 = lean_ctor_get(x_178, 3);
lean_inc(x_212);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 lean_ctor_release(x_178, 2);
 lean_ctor_release(x_178, 3);
 x_213 = x_178;
} else {
 lean_dec_ref(x_178);
 x_213 = lean_box(0);
}
x_214 = 1;
if (lean_is_scalar(x_213)) {
 x_215 = lean_alloc_ctor(1, 4, 1);
} else {
 x_215 = x_213;
}
lean_ctor_set(x_215, 0, x_177);
lean_ctor_set(x_215, 1, x_207);
lean_ctor_set(x_215, 2, x_208);
lean_ctor_set(x_215, 3, x_209);
lean_ctor_set_uint8(x_215, sizeof(void*)*4, x_214);
x_216 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_216, 0, x_212);
lean_ctor_set(x_216, 1, x_29);
lean_ctor_set(x_216, 2, x_30);
lean_ctor_set(x_216, 3, x_31);
lean_ctor_set_uint8(x_216, sizeof(void*)*4, x_214);
lean_ctor_set(x_1, 3, x_216);
lean_ctor_set(x_1, 2, x_211);
lean_ctor_set(x_1, 1, x_210);
lean_ctor_set(x_1, 0, x_215);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
uint8_t x_217; 
x_217 = !lean_is_exclusive(x_176);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_218 = lean_ctor_get(x_176, 3);
lean_dec(x_218);
x_219 = lean_ctor_get(x_176, 0);
lean_dec(x_219);
x_220 = 0;
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_220);
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; 
x_221 = lean_ctor_get(x_176, 1);
x_222 = lean_ctor_get(x_176, 2);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_176);
x_223 = 0;
x_224 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_224, 0, x_177);
lean_ctor_set(x_224, 1, x_221);
lean_ctor_set(x_224, 2, x_222);
lean_ctor_set(x_224, 3, x_178);
lean_ctor_set_uint8(x_224, sizeof(void*)*4, x_223);
lean_ctor_set(x_1, 0, x_224);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
}
}
else
{
uint8_t x_225; 
x_225 = lean_ctor_get_uint8(x_177, sizeof(void*)*4);
if (x_225 == 0)
{
uint8_t x_226; 
x_226 = !lean_is_exclusive(x_176);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_227 = lean_ctor_get(x_176, 1);
x_228 = lean_ctor_get(x_176, 2);
x_229 = lean_ctor_get(x_176, 3);
x_230 = lean_ctor_get(x_176, 0);
lean_dec(x_230);
x_231 = !lean_is_exclusive(x_177);
if (x_231 == 0)
{
uint8_t x_232; 
x_232 = 1;
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_232);
lean_ctor_set(x_176, 3, x_31);
lean_ctor_set(x_176, 2, x_30);
lean_ctor_set(x_176, 1, x_29);
lean_ctor_set(x_176, 0, x_229);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_232);
lean_ctor_set(x_1, 3, x_176);
lean_ctor_set(x_1, 2, x_228);
lean_ctor_set(x_1, 1, x_227);
lean_ctor_set(x_1, 0, x_177);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; lean_object* x_238; 
x_233 = lean_ctor_get(x_177, 0);
x_234 = lean_ctor_get(x_177, 1);
x_235 = lean_ctor_get(x_177, 2);
x_236 = lean_ctor_get(x_177, 3);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_177);
x_237 = 1;
x_238 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_238, 0, x_233);
lean_ctor_set(x_238, 1, x_234);
lean_ctor_set(x_238, 2, x_235);
lean_ctor_set(x_238, 3, x_236);
lean_ctor_set_uint8(x_238, sizeof(void*)*4, x_237);
lean_ctor_set(x_176, 3, x_31);
lean_ctor_set(x_176, 2, x_30);
lean_ctor_set(x_176, 1, x_29);
lean_ctor_set(x_176, 0, x_229);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_237);
lean_ctor_set(x_1, 3, x_176);
lean_ctor_set(x_1, 2, x_228);
lean_ctor_set(x_1, 1, x_227);
lean_ctor_set(x_1, 0, x_238);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; 
x_239 = lean_ctor_get(x_176, 1);
x_240 = lean_ctor_get(x_176, 2);
x_241 = lean_ctor_get(x_176, 3);
lean_inc(x_241);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_176);
x_242 = lean_ctor_get(x_177, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_177, 1);
lean_inc(x_243);
x_244 = lean_ctor_get(x_177, 2);
lean_inc(x_244);
x_245 = lean_ctor_get(x_177, 3);
lean_inc(x_245);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 x_246 = x_177;
} else {
 lean_dec_ref(x_177);
 x_246 = lean_box(0);
}
x_247 = 1;
if (lean_is_scalar(x_246)) {
 x_248 = lean_alloc_ctor(1, 4, 1);
} else {
 x_248 = x_246;
}
lean_ctor_set(x_248, 0, x_242);
lean_ctor_set(x_248, 1, x_243);
lean_ctor_set(x_248, 2, x_244);
lean_ctor_set(x_248, 3, x_245);
lean_ctor_set_uint8(x_248, sizeof(void*)*4, x_247);
x_249 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_249, 0, x_241);
lean_ctor_set(x_249, 1, x_29);
lean_ctor_set(x_249, 2, x_30);
lean_ctor_set(x_249, 3, x_31);
lean_ctor_set_uint8(x_249, sizeof(void*)*4, x_247);
lean_ctor_set(x_1, 3, x_249);
lean_ctor_set(x_1, 2, x_240);
lean_ctor_set(x_1, 1, x_239);
lean_ctor_set(x_1, 0, x_248);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
lean_object* x_250; 
x_250 = lean_ctor_get(x_176, 3);
lean_inc(x_250);
if (lean_obj_tag(x_250) == 0)
{
uint8_t x_251; 
x_251 = !lean_is_exclusive(x_176);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_252 = lean_ctor_get(x_176, 3);
lean_dec(x_252);
x_253 = lean_ctor_get(x_176, 0);
lean_dec(x_253);
x_254 = 0;
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_254);
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; 
x_255 = lean_ctor_get(x_176, 1);
x_256 = lean_ctor_get(x_176, 2);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_176);
x_257 = 0;
x_258 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_258, 0, x_177);
lean_ctor_set(x_258, 1, x_255);
lean_ctor_set(x_258, 2, x_256);
lean_ctor_set(x_258, 3, x_250);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_257);
lean_ctor_set(x_1, 0, x_258);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
uint8_t x_259; 
x_259 = lean_ctor_get_uint8(x_250, sizeof(void*)*4);
if (x_259 == 0)
{
uint8_t x_260; 
lean_free_object(x_1);
x_260 = !lean_is_exclusive(x_176);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_261 = lean_ctor_get(x_176, 1);
x_262 = lean_ctor_get(x_176, 2);
x_263 = lean_ctor_get(x_176, 3);
lean_dec(x_263);
x_264 = lean_ctor_get(x_176, 0);
lean_dec(x_264);
x_265 = !lean_is_exclusive(x_250);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_266 = lean_ctor_get(x_250, 0);
x_267 = lean_ctor_get(x_250, 1);
x_268 = lean_ctor_get(x_250, 2);
x_269 = lean_ctor_get(x_250, 3);
lean_inc(x_177);
lean_ctor_set(x_250, 3, x_266);
lean_ctor_set(x_250, 2, x_262);
lean_ctor_set(x_250, 1, x_261);
lean_ctor_set(x_250, 0, x_177);
x_270 = !lean_is_exclusive(x_177);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_271 = lean_ctor_get(x_177, 3);
lean_dec(x_271);
x_272 = lean_ctor_get(x_177, 2);
lean_dec(x_272);
x_273 = lean_ctor_get(x_177, 1);
lean_dec(x_273);
x_274 = lean_ctor_get(x_177, 0);
lean_dec(x_274);
lean_ctor_set_uint8(x_250, sizeof(void*)*4, x_225);
lean_ctor_set(x_177, 3, x_31);
lean_ctor_set(x_177, 2, x_30);
lean_ctor_set(x_177, 1, x_29);
lean_ctor_set(x_177, 0, x_269);
lean_ctor_set(x_176, 3, x_177);
lean_ctor_set(x_176, 2, x_268);
lean_ctor_set(x_176, 1, x_267);
lean_ctor_set(x_176, 0, x_250);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_259);
return x_176;
}
else
{
lean_object* x_275; 
lean_dec(x_177);
lean_ctor_set_uint8(x_250, sizeof(void*)*4, x_225);
x_275 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_275, 0, x_269);
lean_ctor_set(x_275, 1, x_29);
lean_ctor_set(x_275, 2, x_30);
lean_ctor_set(x_275, 3, x_31);
lean_ctor_set_uint8(x_275, sizeof(void*)*4, x_225);
lean_ctor_set(x_176, 3, x_275);
lean_ctor_set(x_176, 2, x_268);
lean_ctor_set(x_176, 1, x_267);
lean_ctor_set(x_176, 0, x_250);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_276 = lean_ctor_get(x_250, 0);
x_277 = lean_ctor_get(x_250, 1);
x_278 = lean_ctor_get(x_250, 2);
x_279 = lean_ctor_get(x_250, 3);
lean_inc(x_279);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_250);
lean_inc(x_177);
x_280 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_280, 0, x_177);
lean_ctor_set(x_280, 1, x_261);
lean_ctor_set(x_280, 2, x_262);
lean_ctor_set(x_280, 3, x_276);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 x_281 = x_177;
} else {
 lean_dec_ref(x_177);
 x_281 = lean_box(0);
}
lean_ctor_set_uint8(x_280, sizeof(void*)*4, x_225);
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 4, 1);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_29);
lean_ctor_set(x_282, 2, x_30);
lean_ctor_set(x_282, 3, x_31);
lean_ctor_set_uint8(x_282, sizeof(void*)*4, x_225);
lean_ctor_set(x_176, 3, x_282);
lean_ctor_set(x_176, 2, x_278);
lean_ctor_set(x_176, 1, x_277);
lean_ctor_set(x_176, 0, x_280);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_283 = lean_ctor_get(x_176, 1);
x_284 = lean_ctor_get(x_176, 2);
lean_inc(x_284);
lean_inc(x_283);
lean_dec(x_176);
x_285 = lean_ctor_get(x_250, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_250, 1);
lean_inc(x_286);
x_287 = lean_ctor_get(x_250, 2);
lean_inc(x_287);
x_288 = lean_ctor_get(x_250, 3);
lean_inc(x_288);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 lean_ctor_release(x_250, 2);
 lean_ctor_release(x_250, 3);
 x_289 = x_250;
} else {
 lean_dec_ref(x_250);
 x_289 = lean_box(0);
}
lean_inc(x_177);
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(1, 4, 1);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_177);
lean_ctor_set(x_290, 1, x_283);
lean_ctor_set(x_290, 2, x_284);
lean_ctor_set(x_290, 3, x_285);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 x_291 = x_177;
} else {
 lean_dec_ref(x_177);
 x_291 = lean_box(0);
}
lean_ctor_set_uint8(x_290, sizeof(void*)*4, x_225);
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(1, 4, 1);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_288);
lean_ctor_set(x_292, 1, x_29);
lean_ctor_set(x_292, 2, x_30);
lean_ctor_set(x_292, 3, x_31);
lean_ctor_set_uint8(x_292, sizeof(void*)*4, x_225);
x_293 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_286);
lean_ctor_set(x_293, 2, x_287);
lean_ctor_set(x_293, 3, x_292);
lean_ctor_set_uint8(x_293, sizeof(void*)*4, x_259);
return x_293;
}
}
else
{
uint8_t x_294; 
x_294 = !lean_is_exclusive(x_176);
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; uint8_t x_297; 
x_295 = lean_ctor_get(x_176, 3);
lean_dec(x_295);
x_296 = lean_ctor_get(x_176, 0);
lean_dec(x_296);
x_297 = !lean_is_exclusive(x_177);
if (x_297 == 0)
{
uint8_t x_298; 
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_259);
x_298 = 0;
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_298);
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
return x_1;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; 
x_299 = lean_ctor_get(x_177, 0);
x_300 = lean_ctor_get(x_177, 1);
x_301 = lean_ctor_get(x_177, 2);
x_302 = lean_ctor_get(x_177, 3);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_177);
x_303 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_303, 0, x_299);
lean_ctor_set(x_303, 1, x_300);
lean_ctor_set(x_303, 2, x_301);
lean_ctor_set(x_303, 3, x_302);
lean_ctor_set_uint8(x_303, sizeof(void*)*4, x_259);
x_304 = 0;
lean_ctor_set(x_176, 0, x_303);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_304);
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; 
x_305 = lean_ctor_get(x_176, 1);
x_306 = lean_ctor_get(x_176, 2);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_176);
x_307 = lean_ctor_get(x_177, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_177, 1);
lean_inc(x_308);
x_309 = lean_ctor_get(x_177, 2);
lean_inc(x_309);
x_310 = lean_ctor_get(x_177, 3);
lean_inc(x_310);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 x_311 = x_177;
} else {
 lean_dec_ref(x_177);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(1, 4, 1);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_307);
lean_ctor_set(x_312, 1, x_308);
lean_ctor_set(x_312, 2, x_309);
lean_ctor_set(x_312, 3, x_310);
lean_ctor_set_uint8(x_312, sizeof(void*)*4, x_259);
x_313 = 0;
x_314 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_305);
lean_ctor_set(x_314, 2, x_306);
lean_ctor_set(x_314, 3, x_250);
lean_ctor_set_uint8(x_314, sizeof(void*)*4, x_313);
lean_ctor_set(x_1, 0, x_314);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
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
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_315 = lean_ctor_get(x_1, 0);
x_316 = lean_ctor_get(x_1, 1);
x_317 = lean_ctor_get(x_1, 2);
x_318 = lean_ctor_get(x_1, 3);
lean_inc(x_318);
lean_inc(x_317);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_1);
x_319 = l_Lean_Name_quickLt(x_2, x_316);
if (x_319 == 0)
{
uint8_t x_320; 
x_320 = l_Lean_Name_quickLt(x_316, x_2);
if (x_320 == 0)
{
lean_object* x_321; 
lean_dec(x_317);
lean_dec(x_316);
x_321 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_321, 0, x_315);
lean_ctor_set(x_321, 1, x_2);
lean_ctor_set(x_321, 2, x_3);
lean_ctor_set(x_321, 3, x_318);
lean_ctor_set_uint8(x_321, sizeof(void*)*4, x_6);
return x_321;
}
else
{
uint8_t x_322; 
x_322 = l_RBNode_isRed___rarg(x_318);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; 
x_323 = l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(x_318, x_2, x_3);
x_324 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_324, 0, x_315);
lean_ctor_set(x_324, 1, x_316);
lean_ctor_set(x_324, 2, x_317);
lean_ctor_set(x_324, 3, x_323);
lean_ctor_set_uint8(x_324, sizeof(void*)*4, x_6);
return x_324;
}
else
{
lean_object* x_325; 
x_325 = l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(x_318, x_2, x_3);
if (lean_obj_tag(x_325) == 0)
{
lean_dec(x_317);
lean_dec(x_316);
lean_dec(x_315);
return x_325;
}
else
{
lean_object* x_326; 
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; 
x_327 = lean_ctor_get(x_325, 3);
lean_inc(x_327);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; lean_object* x_332; uint8_t x_333; lean_object* x_334; 
x_328 = lean_ctor_get(x_325, 1);
lean_inc(x_328);
x_329 = lean_ctor_get(x_325, 2);
lean_inc(x_329);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_330 = x_325;
} else {
 lean_dec_ref(x_325);
 x_330 = lean_box(0);
}
x_331 = 0;
if (lean_is_scalar(x_330)) {
 x_332 = lean_alloc_ctor(1, 4, 1);
} else {
 x_332 = x_330;
}
lean_ctor_set(x_332, 0, x_327);
lean_ctor_set(x_332, 1, x_328);
lean_ctor_set(x_332, 2, x_329);
lean_ctor_set(x_332, 3, x_327);
lean_ctor_set_uint8(x_332, sizeof(void*)*4, x_331);
x_333 = 1;
x_334 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_334, 0, x_315);
lean_ctor_set(x_334, 1, x_316);
lean_ctor_set(x_334, 2, x_317);
lean_ctor_set(x_334, 3, x_332);
lean_ctor_set_uint8(x_334, sizeof(void*)*4, x_333);
return x_334;
}
else
{
uint8_t x_335; 
x_335 = lean_ctor_get_uint8(x_327, sizeof(void*)*4);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_336 = lean_ctor_get(x_325, 1);
lean_inc(x_336);
x_337 = lean_ctor_get(x_325, 2);
lean_inc(x_337);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_338 = x_325;
} else {
 lean_dec_ref(x_325);
 x_338 = lean_box(0);
}
x_339 = lean_ctor_get(x_327, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_327, 1);
lean_inc(x_340);
x_341 = lean_ctor_get(x_327, 2);
lean_inc(x_341);
x_342 = lean_ctor_get(x_327, 3);
lean_inc(x_342);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 lean_ctor_release(x_327, 2);
 lean_ctor_release(x_327, 3);
 x_343 = x_327;
} else {
 lean_dec_ref(x_327);
 x_343 = lean_box(0);
}
x_344 = 1;
if (lean_is_scalar(x_343)) {
 x_345 = lean_alloc_ctor(1, 4, 1);
} else {
 x_345 = x_343;
}
lean_ctor_set(x_345, 0, x_315);
lean_ctor_set(x_345, 1, x_316);
lean_ctor_set(x_345, 2, x_317);
lean_ctor_set(x_345, 3, x_326);
lean_ctor_set_uint8(x_345, sizeof(void*)*4, x_344);
if (lean_is_scalar(x_338)) {
 x_346 = lean_alloc_ctor(1, 4, 1);
} else {
 x_346 = x_338;
}
lean_ctor_set(x_346, 0, x_339);
lean_ctor_set(x_346, 1, x_340);
lean_ctor_set(x_346, 2, x_341);
lean_ctor_set(x_346, 3, x_342);
lean_ctor_set_uint8(x_346, sizeof(void*)*4, x_344);
x_347 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_347, 1, x_336);
lean_ctor_set(x_347, 2, x_337);
lean_ctor_set(x_347, 3, x_346);
lean_ctor_set_uint8(x_347, sizeof(void*)*4, x_335);
return x_347;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; lean_object* x_352; lean_object* x_353; 
x_348 = lean_ctor_get(x_325, 1);
lean_inc(x_348);
x_349 = lean_ctor_get(x_325, 2);
lean_inc(x_349);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_350 = x_325;
} else {
 lean_dec_ref(x_325);
 x_350 = lean_box(0);
}
x_351 = 0;
if (lean_is_scalar(x_350)) {
 x_352 = lean_alloc_ctor(1, 4, 1);
} else {
 x_352 = x_350;
}
lean_ctor_set(x_352, 0, x_326);
lean_ctor_set(x_352, 1, x_348);
lean_ctor_set(x_352, 2, x_349);
lean_ctor_set(x_352, 3, x_327);
lean_ctor_set_uint8(x_352, sizeof(void*)*4, x_351);
x_353 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_353, 0, x_315);
lean_ctor_set(x_353, 1, x_316);
lean_ctor_set(x_353, 2, x_317);
lean_ctor_set(x_353, 3, x_352);
lean_ctor_set_uint8(x_353, sizeof(void*)*4, x_335);
return x_353;
}
}
}
else
{
uint8_t x_354; 
x_354 = lean_ctor_get_uint8(x_326, sizeof(void*)*4);
if (x_354 == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_355 = lean_ctor_get(x_325, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_325, 2);
lean_inc(x_356);
x_357 = lean_ctor_get(x_325, 3);
lean_inc(x_357);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_358 = x_325;
} else {
 lean_dec_ref(x_325);
 x_358 = lean_box(0);
}
x_359 = lean_ctor_get(x_326, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_326, 1);
lean_inc(x_360);
x_361 = lean_ctor_get(x_326, 2);
lean_inc(x_361);
x_362 = lean_ctor_get(x_326, 3);
lean_inc(x_362);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 x_363 = x_326;
} else {
 lean_dec_ref(x_326);
 x_363 = lean_box(0);
}
x_364 = 1;
if (lean_is_scalar(x_363)) {
 x_365 = lean_alloc_ctor(1, 4, 1);
} else {
 x_365 = x_363;
}
lean_ctor_set(x_365, 0, x_315);
lean_ctor_set(x_365, 1, x_316);
lean_ctor_set(x_365, 2, x_317);
lean_ctor_set(x_365, 3, x_359);
lean_ctor_set_uint8(x_365, sizeof(void*)*4, x_364);
if (lean_is_scalar(x_358)) {
 x_366 = lean_alloc_ctor(1, 4, 1);
} else {
 x_366 = x_358;
}
lean_ctor_set(x_366, 0, x_362);
lean_ctor_set(x_366, 1, x_355);
lean_ctor_set(x_366, 2, x_356);
lean_ctor_set(x_366, 3, x_357);
lean_ctor_set_uint8(x_366, sizeof(void*)*4, x_364);
x_367 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_367, 0, x_365);
lean_ctor_set(x_367, 1, x_360);
lean_ctor_set(x_367, 2, x_361);
lean_ctor_set(x_367, 3, x_366);
lean_ctor_set_uint8(x_367, sizeof(void*)*4, x_354);
return x_367;
}
else
{
lean_object* x_368; 
x_368 = lean_ctor_get(x_325, 3);
lean_inc(x_368);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; lean_object* x_373; lean_object* x_374; 
x_369 = lean_ctor_get(x_325, 1);
lean_inc(x_369);
x_370 = lean_ctor_get(x_325, 2);
lean_inc(x_370);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_371 = x_325;
} else {
 lean_dec_ref(x_325);
 x_371 = lean_box(0);
}
x_372 = 0;
if (lean_is_scalar(x_371)) {
 x_373 = lean_alloc_ctor(1, 4, 1);
} else {
 x_373 = x_371;
}
lean_ctor_set(x_373, 0, x_326);
lean_ctor_set(x_373, 1, x_369);
lean_ctor_set(x_373, 2, x_370);
lean_ctor_set(x_373, 3, x_368);
lean_ctor_set_uint8(x_373, sizeof(void*)*4, x_372);
x_374 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_374, 0, x_315);
lean_ctor_set(x_374, 1, x_316);
lean_ctor_set(x_374, 2, x_317);
lean_ctor_set(x_374, 3, x_373);
lean_ctor_set_uint8(x_374, sizeof(void*)*4, x_354);
return x_374;
}
else
{
uint8_t x_375; 
x_375 = lean_ctor_get_uint8(x_368, sizeof(void*)*4);
if (x_375 == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_376 = lean_ctor_get(x_325, 1);
lean_inc(x_376);
x_377 = lean_ctor_get(x_325, 2);
lean_inc(x_377);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_378 = x_325;
} else {
 lean_dec_ref(x_325);
 x_378 = lean_box(0);
}
x_379 = lean_ctor_get(x_368, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_368, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_368, 2);
lean_inc(x_381);
x_382 = lean_ctor_get(x_368, 3);
lean_inc(x_382);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 lean_ctor_release(x_368, 2);
 lean_ctor_release(x_368, 3);
 x_383 = x_368;
} else {
 lean_dec_ref(x_368);
 x_383 = lean_box(0);
}
lean_inc(x_326);
if (lean_is_scalar(x_383)) {
 x_384 = lean_alloc_ctor(1, 4, 1);
} else {
 x_384 = x_383;
}
lean_ctor_set(x_384, 0, x_315);
lean_ctor_set(x_384, 1, x_316);
lean_ctor_set(x_384, 2, x_317);
lean_ctor_set(x_384, 3, x_326);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 x_385 = x_326;
} else {
 lean_dec_ref(x_326);
 x_385 = lean_box(0);
}
lean_ctor_set_uint8(x_384, sizeof(void*)*4, x_354);
if (lean_is_scalar(x_385)) {
 x_386 = lean_alloc_ctor(1, 4, 1);
} else {
 x_386 = x_385;
}
lean_ctor_set(x_386, 0, x_379);
lean_ctor_set(x_386, 1, x_380);
lean_ctor_set(x_386, 2, x_381);
lean_ctor_set(x_386, 3, x_382);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_354);
if (lean_is_scalar(x_378)) {
 x_387 = lean_alloc_ctor(1, 4, 1);
} else {
 x_387 = x_378;
}
lean_ctor_set(x_387, 0, x_384);
lean_ctor_set(x_387, 1, x_376);
lean_ctor_set(x_387, 2, x_377);
lean_ctor_set(x_387, 3, x_386);
lean_ctor_set_uint8(x_387, sizeof(void*)*4, x_375);
return x_387;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; lean_object* x_398; lean_object* x_399; 
x_388 = lean_ctor_get(x_325, 1);
lean_inc(x_388);
x_389 = lean_ctor_get(x_325, 2);
lean_inc(x_389);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_390 = x_325;
} else {
 lean_dec_ref(x_325);
 x_390 = lean_box(0);
}
x_391 = lean_ctor_get(x_326, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_326, 1);
lean_inc(x_392);
x_393 = lean_ctor_get(x_326, 2);
lean_inc(x_393);
x_394 = lean_ctor_get(x_326, 3);
lean_inc(x_394);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 x_395 = x_326;
} else {
 lean_dec_ref(x_326);
 x_395 = lean_box(0);
}
if (lean_is_scalar(x_395)) {
 x_396 = lean_alloc_ctor(1, 4, 1);
} else {
 x_396 = x_395;
}
lean_ctor_set(x_396, 0, x_391);
lean_ctor_set(x_396, 1, x_392);
lean_ctor_set(x_396, 2, x_393);
lean_ctor_set(x_396, 3, x_394);
lean_ctor_set_uint8(x_396, sizeof(void*)*4, x_375);
x_397 = 0;
if (lean_is_scalar(x_390)) {
 x_398 = lean_alloc_ctor(1, 4, 1);
} else {
 x_398 = x_390;
}
lean_ctor_set(x_398, 0, x_396);
lean_ctor_set(x_398, 1, x_388);
lean_ctor_set(x_398, 2, x_389);
lean_ctor_set(x_398, 3, x_368);
lean_ctor_set_uint8(x_398, sizeof(void*)*4, x_397);
x_399 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_399, 0, x_315);
lean_ctor_set(x_399, 1, x_316);
lean_ctor_set(x_399, 2, x_317);
lean_ctor_set(x_399, 3, x_398);
lean_ctor_set_uint8(x_399, sizeof(void*)*4, x_375);
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
uint8_t x_400; 
x_400 = l_RBNode_isRed___rarg(x_315);
if (x_400 == 0)
{
lean_object* x_401; lean_object* x_402; 
x_401 = l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(x_315, x_2, x_3);
x_402 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_316);
lean_ctor_set(x_402, 2, x_317);
lean_ctor_set(x_402, 3, x_318);
lean_ctor_set_uint8(x_402, sizeof(void*)*4, x_6);
return x_402;
}
else
{
lean_object* x_403; 
x_403 = l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(x_315, x_2, x_3);
if (lean_obj_tag(x_403) == 0)
{
lean_dec(x_318);
lean_dec(x_317);
lean_dec(x_316);
return x_403;
}
else
{
lean_object* x_404; 
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; 
x_405 = lean_ctor_get(x_403, 3);
lean_inc(x_405);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; uint8_t x_409; lean_object* x_410; uint8_t x_411; lean_object* x_412; 
x_406 = lean_ctor_get(x_403, 1);
lean_inc(x_406);
x_407 = lean_ctor_get(x_403, 2);
lean_inc(x_407);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_408 = x_403;
} else {
 lean_dec_ref(x_403);
 x_408 = lean_box(0);
}
x_409 = 0;
if (lean_is_scalar(x_408)) {
 x_410 = lean_alloc_ctor(1, 4, 1);
} else {
 x_410 = x_408;
}
lean_ctor_set(x_410, 0, x_405);
lean_ctor_set(x_410, 1, x_406);
lean_ctor_set(x_410, 2, x_407);
lean_ctor_set(x_410, 3, x_405);
lean_ctor_set_uint8(x_410, sizeof(void*)*4, x_409);
x_411 = 1;
x_412 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_412, 0, x_410);
lean_ctor_set(x_412, 1, x_316);
lean_ctor_set(x_412, 2, x_317);
lean_ctor_set(x_412, 3, x_318);
lean_ctor_set_uint8(x_412, sizeof(void*)*4, x_411);
return x_412;
}
else
{
uint8_t x_413; 
x_413 = lean_ctor_get_uint8(x_405, sizeof(void*)*4);
if (x_413 == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_414 = lean_ctor_get(x_403, 1);
lean_inc(x_414);
x_415 = lean_ctor_get(x_403, 2);
lean_inc(x_415);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_416 = x_403;
} else {
 lean_dec_ref(x_403);
 x_416 = lean_box(0);
}
x_417 = lean_ctor_get(x_405, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_405, 1);
lean_inc(x_418);
x_419 = lean_ctor_get(x_405, 2);
lean_inc(x_419);
x_420 = lean_ctor_get(x_405, 3);
lean_inc(x_420);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 lean_ctor_release(x_405, 2);
 lean_ctor_release(x_405, 3);
 x_421 = x_405;
} else {
 lean_dec_ref(x_405);
 x_421 = lean_box(0);
}
x_422 = 1;
if (lean_is_scalar(x_421)) {
 x_423 = lean_alloc_ctor(1, 4, 1);
} else {
 x_423 = x_421;
}
lean_ctor_set(x_423, 0, x_404);
lean_ctor_set(x_423, 1, x_414);
lean_ctor_set(x_423, 2, x_415);
lean_ctor_set(x_423, 3, x_417);
lean_ctor_set_uint8(x_423, sizeof(void*)*4, x_422);
if (lean_is_scalar(x_416)) {
 x_424 = lean_alloc_ctor(1, 4, 1);
} else {
 x_424 = x_416;
}
lean_ctor_set(x_424, 0, x_420);
lean_ctor_set(x_424, 1, x_316);
lean_ctor_set(x_424, 2, x_317);
lean_ctor_set(x_424, 3, x_318);
lean_ctor_set_uint8(x_424, sizeof(void*)*4, x_422);
x_425 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_418);
lean_ctor_set(x_425, 2, x_419);
lean_ctor_set(x_425, 3, x_424);
lean_ctor_set_uint8(x_425, sizeof(void*)*4, x_413);
return x_425;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_429; lean_object* x_430; lean_object* x_431; 
x_426 = lean_ctor_get(x_403, 1);
lean_inc(x_426);
x_427 = lean_ctor_get(x_403, 2);
lean_inc(x_427);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_428 = x_403;
} else {
 lean_dec_ref(x_403);
 x_428 = lean_box(0);
}
x_429 = 0;
if (lean_is_scalar(x_428)) {
 x_430 = lean_alloc_ctor(1, 4, 1);
} else {
 x_430 = x_428;
}
lean_ctor_set(x_430, 0, x_404);
lean_ctor_set(x_430, 1, x_426);
lean_ctor_set(x_430, 2, x_427);
lean_ctor_set(x_430, 3, x_405);
lean_ctor_set_uint8(x_430, sizeof(void*)*4, x_429);
x_431 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_316);
lean_ctor_set(x_431, 2, x_317);
lean_ctor_set(x_431, 3, x_318);
lean_ctor_set_uint8(x_431, sizeof(void*)*4, x_413);
return x_431;
}
}
}
else
{
uint8_t x_432; 
x_432 = lean_ctor_get_uint8(x_404, sizeof(void*)*4);
if (x_432 == 0)
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_433 = lean_ctor_get(x_403, 1);
lean_inc(x_433);
x_434 = lean_ctor_get(x_403, 2);
lean_inc(x_434);
x_435 = lean_ctor_get(x_403, 3);
lean_inc(x_435);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_436 = x_403;
} else {
 lean_dec_ref(x_403);
 x_436 = lean_box(0);
}
x_437 = lean_ctor_get(x_404, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_404, 1);
lean_inc(x_438);
x_439 = lean_ctor_get(x_404, 2);
lean_inc(x_439);
x_440 = lean_ctor_get(x_404, 3);
lean_inc(x_440);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 lean_ctor_release(x_404, 2);
 lean_ctor_release(x_404, 3);
 x_441 = x_404;
} else {
 lean_dec_ref(x_404);
 x_441 = lean_box(0);
}
x_442 = 1;
if (lean_is_scalar(x_441)) {
 x_443 = lean_alloc_ctor(1, 4, 1);
} else {
 x_443 = x_441;
}
lean_ctor_set(x_443, 0, x_437);
lean_ctor_set(x_443, 1, x_438);
lean_ctor_set(x_443, 2, x_439);
lean_ctor_set(x_443, 3, x_440);
lean_ctor_set_uint8(x_443, sizeof(void*)*4, x_442);
if (lean_is_scalar(x_436)) {
 x_444 = lean_alloc_ctor(1, 4, 1);
} else {
 x_444 = x_436;
}
lean_ctor_set(x_444, 0, x_435);
lean_ctor_set(x_444, 1, x_316);
lean_ctor_set(x_444, 2, x_317);
lean_ctor_set(x_444, 3, x_318);
lean_ctor_set_uint8(x_444, sizeof(void*)*4, x_442);
x_445 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_445, 0, x_443);
lean_ctor_set(x_445, 1, x_433);
lean_ctor_set(x_445, 2, x_434);
lean_ctor_set(x_445, 3, x_444);
lean_ctor_set_uint8(x_445, sizeof(void*)*4, x_432);
return x_445;
}
else
{
lean_object* x_446; 
x_446 = lean_ctor_get(x_403, 3);
lean_inc(x_446);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; uint8_t x_450; lean_object* x_451; lean_object* x_452; 
x_447 = lean_ctor_get(x_403, 1);
lean_inc(x_447);
x_448 = lean_ctor_get(x_403, 2);
lean_inc(x_448);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_449 = x_403;
} else {
 lean_dec_ref(x_403);
 x_449 = lean_box(0);
}
x_450 = 0;
if (lean_is_scalar(x_449)) {
 x_451 = lean_alloc_ctor(1, 4, 1);
} else {
 x_451 = x_449;
}
lean_ctor_set(x_451, 0, x_404);
lean_ctor_set(x_451, 1, x_447);
lean_ctor_set(x_451, 2, x_448);
lean_ctor_set(x_451, 3, x_446);
lean_ctor_set_uint8(x_451, sizeof(void*)*4, x_450);
x_452 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_452, 0, x_451);
lean_ctor_set(x_452, 1, x_316);
lean_ctor_set(x_452, 2, x_317);
lean_ctor_set(x_452, 3, x_318);
lean_ctor_set_uint8(x_452, sizeof(void*)*4, x_432);
return x_452;
}
else
{
uint8_t x_453; 
x_453 = lean_ctor_get_uint8(x_446, sizeof(void*)*4);
if (x_453 == 0)
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_454 = lean_ctor_get(x_403, 1);
lean_inc(x_454);
x_455 = lean_ctor_get(x_403, 2);
lean_inc(x_455);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_456 = x_403;
} else {
 lean_dec_ref(x_403);
 x_456 = lean_box(0);
}
x_457 = lean_ctor_get(x_446, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_446, 1);
lean_inc(x_458);
x_459 = lean_ctor_get(x_446, 2);
lean_inc(x_459);
x_460 = lean_ctor_get(x_446, 3);
lean_inc(x_460);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 lean_ctor_release(x_446, 1);
 lean_ctor_release(x_446, 2);
 lean_ctor_release(x_446, 3);
 x_461 = x_446;
} else {
 lean_dec_ref(x_446);
 x_461 = lean_box(0);
}
lean_inc(x_404);
if (lean_is_scalar(x_461)) {
 x_462 = lean_alloc_ctor(1, 4, 1);
} else {
 x_462 = x_461;
}
lean_ctor_set(x_462, 0, x_404);
lean_ctor_set(x_462, 1, x_454);
lean_ctor_set(x_462, 2, x_455);
lean_ctor_set(x_462, 3, x_457);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 lean_ctor_release(x_404, 2);
 lean_ctor_release(x_404, 3);
 x_463 = x_404;
} else {
 lean_dec_ref(x_404);
 x_463 = lean_box(0);
}
lean_ctor_set_uint8(x_462, sizeof(void*)*4, x_432);
if (lean_is_scalar(x_463)) {
 x_464 = lean_alloc_ctor(1, 4, 1);
} else {
 x_464 = x_463;
}
lean_ctor_set(x_464, 0, x_460);
lean_ctor_set(x_464, 1, x_316);
lean_ctor_set(x_464, 2, x_317);
lean_ctor_set(x_464, 3, x_318);
lean_ctor_set_uint8(x_464, sizeof(void*)*4, x_432);
if (lean_is_scalar(x_456)) {
 x_465 = lean_alloc_ctor(1, 4, 1);
} else {
 x_465 = x_456;
}
lean_ctor_set(x_465, 0, x_462);
lean_ctor_set(x_465, 1, x_458);
lean_ctor_set(x_465, 2, x_459);
lean_ctor_set(x_465, 3, x_464);
lean_ctor_set_uint8(x_465, sizeof(void*)*4, x_453);
return x_465;
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; uint8_t x_475; lean_object* x_476; lean_object* x_477; 
x_466 = lean_ctor_get(x_403, 1);
lean_inc(x_466);
x_467 = lean_ctor_get(x_403, 2);
lean_inc(x_467);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_468 = x_403;
} else {
 lean_dec_ref(x_403);
 x_468 = lean_box(0);
}
x_469 = lean_ctor_get(x_404, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_404, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_404, 2);
lean_inc(x_471);
x_472 = lean_ctor_get(x_404, 3);
lean_inc(x_472);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 lean_ctor_release(x_404, 2);
 lean_ctor_release(x_404, 3);
 x_473 = x_404;
} else {
 lean_dec_ref(x_404);
 x_473 = lean_box(0);
}
if (lean_is_scalar(x_473)) {
 x_474 = lean_alloc_ctor(1, 4, 1);
} else {
 x_474 = x_473;
}
lean_ctor_set(x_474, 0, x_469);
lean_ctor_set(x_474, 1, x_470);
lean_ctor_set(x_474, 2, x_471);
lean_ctor_set(x_474, 3, x_472);
lean_ctor_set_uint8(x_474, sizeof(void*)*4, x_453);
x_475 = 0;
if (lean_is_scalar(x_468)) {
 x_476 = lean_alloc_ctor(1, 4, 1);
} else {
 x_476 = x_468;
}
lean_ctor_set(x_476, 0, x_474);
lean_ctor_set(x_476, 1, x_466);
lean_ctor_set(x_476, 2, x_467);
lean_ctor_set(x_476, 3, x_446);
lean_ctor_set_uint8(x_476, sizeof(void*)*4, x_475);
x_477 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_477, 1, x_316);
lean_ctor_set(x_477, 2, x_317);
lean_ctor_set(x_477, 3, x_318);
lean_ctor_set_uint8(x_477, sizeof(void*)*4, x_453);
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
lean_object* l_RBNode_insert___at_Lean_Environment_addAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_RBNode_ins___main___at_Lean_Environment_addAux___spec__3(x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
uint8_t l_AssocList_contains___main___at_Lean_Environment_addAux___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_name_dec_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
lean_object* l_AssocList_mfoldl___main___at_Lean_Environment_addAux___spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; size_t x_10; lean_object* x_11; size_t x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_name_hash_usize(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_box_usize(x_8);
x_10 = lean_unbox_usize(x_9);
x_11 = lean_array_uget(x_1, x_10);
lean_ctor_set(x_2, 2, x_11);
x_12 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_13 = lean_array_uset(x_1, x_12, x_2);
x_1 = x_13;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; size_t x_22; lean_object* x_23; lean_object* x_24; size_t x_25; lean_object* x_26; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_ctor_get(x_2, 2);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_2);
x_18 = lean_array_get_size(x_1);
x_19 = lean_name_hash_usize(x_15);
x_20 = lean_usize_modn(x_19, x_18);
lean_dec(x_18);
x_21 = lean_box_usize(x_20);
x_22 = lean_unbox_usize(x_21);
x_23 = lean_array_uget(x_1, x_22);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_unbox_usize(x_21);
lean_dec(x_21);
x_26 = lean_array_uset(x_1, x_25, x_24);
x_1 = x_26;
x_2 = x_17;
goto _start;
}
}
}
}
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Environment_addAux___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_AssocList_mfoldl___main___at_Lean_Environment_addAux___spec__8(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
lean_object* l_HashMapImp_expand___at_Lean_Environment_addAux___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_HashMapImp_moveEntries___main___at_Lean_Environment_addAux___spec__7(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_Environment_addAux___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_name_dec_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_AssocList_replace___main___at_Lean_Environment_addAux___spec__9(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_name_dec_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_AssocList_replace___main___at_Lean_Environment_addAux___spec__9(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
lean_object* l_HashMapImp_insert___at_Lean_Environment_addAux___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; size_t x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_name_hash_usize(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_box_usize(x_9);
x_11 = lean_unbox_usize(x_10);
x_12 = lean_array_uget(x_6, x_11);
x_13 = l_AssocList_contains___main___at_Lean_Environment_addAux___spec__5(x_2, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_5, x_14);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_3);
lean_ctor_set(x_16, 2, x_12);
x_17 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_18 = lean_array_uset(x_6, x_17, x_16);
x_19 = lean_nat_dec_le(x_15, x_7);
lean_dec(x_7);
if (x_19 == 0)
{
lean_object* x_20; 
lean_free_object(x_1);
x_20 = l_HashMapImp_expand___at_Lean_Environment_addAux___spec__6(x_15, x_18);
return x_20;
}
else
{
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
}
else
{
lean_object* x_21; size_t x_22; lean_object* x_23; 
lean_dec(x_7);
x_21 = l_AssocList_replace___main___at_Lean_Environment_addAux___spec__9(x_2, x_3, x_12);
x_22 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_23 = lean_array_uset(x_6, x_22, x_21);
lean_ctor_set(x_1, 1, x_23);
return x_1;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; size_t x_30; lean_object* x_31; uint8_t x_32; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_1);
x_26 = lean_array_get_size(x_25);
x_27 = lean_name_hash_usize(x_2);
x_28 = lean_usize_modn(x_27, x_26);
x_29 = lean_box_usize(x_28);
x_30 = lean_unbox_usize(x_29);
x_31 = lean_array_uget(x_25, x_30);
x_32 = l_AssocList_contains___main___at_Lean_Environment_addAux___spec__5(x_2, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_24, x_33);
lean_dec(x_24);
x_35 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set(x_35, 1, x_3);
lean_ctor_set(x_35, 2, x_31);
x_36 = lean_unbox_usize(x_29);
lean_dec(x_29);
x_37 = lean_array_uset(x_25, x_36, x_35);
x_38 = lean_nat_dec_le(x_34, x_26);
lean_dec(x_26);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = l_HashMapImp_expand___at_Lean_Environment_addAux___spec__6(x_34, x_37);
return x_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
lean_object* x_41; size_t x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_26);
x_41 = l_AssocList_replace___main___at_Lean_Environment_addAux___spec__9(x_2, x_3, x_31);
x_42 = lean_unbox_usize(x_29);
lean_dec(x_29);
x_43 = lean_array_uset(x_25, x_42, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_24);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
lean_object* l_Lean_SMap_insert___at_Lean_Environment_addAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_RBNode_insert___at_Lean_Environment_addAux___spec__2(x_6, x_2, x_3);
lean_ctor_set(x_1, 1, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_RBNode_insert___at_Lean_Environment_addAux___spec__2(x_9, x_2, x_3);
x_11 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_4);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = l_HashMapImp_insert___at_Lean_Environment_addAux___spec__4(x_13, x_2, x_3);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_17 = l_HashMapImp_insert___at_Lean_Environment_addAux___spec__4(x_15, x_2, x_3);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_4);
return x_18;
}
}
}
}
lean_object* l_Lean_Environment_addAux(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_ConstantInfo_name(x_2);
x_6 = l_Lean_SMap_insert___at_Lean_Environment_addAux___spec__1(x_4, x_5, x_2);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_11 = l_Lean_ConstantInfo_name(x_2);
x_12 = l_Lean_SMap_insert___at_Lean_Environment_addAux___spec__1(x_8, x_11, x_2);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_9);
lean_ctor_set(x_13, 3, x_10);
return x_13;
}
}
}
lean_object* l_AssocList_contains___main___at_Lean_Environment_addAux___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_Environment_addAux___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_AssocList_find___main___at_Lean_Environment_find___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_dec_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
lean_object* l_HashMapImp_find___at_Lean_Environment_find___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_name_hash_usize(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_box_usize(x_6);
x_8 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_9 = lean_array_uget(x_3, x_8);
x_10 = l_AssocList_find___main___at_Lean_Environment_find___spec__3(x_2, x_9);
lean_dec(x_9);
return x_10;
}
}
lean_object* l_RBNode_find___main___at_Lean_Environment_find___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
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
lean_object* l_Lean_SMap_find_x27___at_Lean_Environment_find___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_HashMapImp_find___at_Lean_Environment_find___spec__2(x_4, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
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
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = l_HashMapImp_find___at_Lean_Environment_find___spec__2(x_8, x_2);
return x_9;
}
}
}
lean_object* lean_environment_find(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_SMap_find_x27___at_Lean_Environment_find___spec__1(x_3, x_2);
lean_dec(x_2);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_AssocList_find___main___at_Lean_Environment_find___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find___main___at_Lean_Environment_find___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find___at_Lean_Environment_find___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find___at_Lean_Environment_find___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_RBNode_find___main___at_Lean_Environment_find___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_find___main___at_Lean_Environment_find___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SMap_find_x27___at_Lean_Environment_find___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find_x27___at_Lean_Environment_find___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
uint8_t l_HashMapImp_contains___at_Lean_Environment_contains___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_name_hash_usize(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_box_usize(x_6);
x_8 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_9 = lean_array_uget(x_3, x_8);
x_10 = l_AssocList_contains___main___at_Lean_Environment_addAux___spec__5(x_2, x_9);
lean_dec(x_9);
return x_10;
}
}
uint8_t l_Lean_SMap_contains___at_Lean_Environment_contains___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_HashMapImp_contains___at_Lean_Environment_contains___spec__2(x_4, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_RBNode_find___main___at_Lean_Environment_find___spec__4(x_5, x_2);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 1;
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = l_HashMapImp_contains___at_Lean_Environment_contains___spec__2(x_11, x_2);
return x_12;
}
}
}
uint8_t l_Lean_Environment_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_SMap_contains___at_Lean_Environment_contains___spec__1(x_3, x_2);
return x_4;
}
}
lean_object* l_HashMapImp_contains___at_Lean_Environment_contains___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_HashMapImp_contains___at_Lean_Environment_contains___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_SMap_contains___at_Lean_Environment_contains___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_SMap_contains___at_Lean_Environment_contains___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Environment_contains___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Environment_contains(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Environment_imports(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
return x_3;
}
}
lean_object* l_Lean_Environment_imports___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Environment_imports(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* lean_environment_set_main_module(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 0);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_2);
return x_1;
}
else
{
uint32_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get_uint32(x_4, sizeof(void*)*2);
x_8 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 4);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set_uint32(x_10, sizeof(void*)*2, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*2 + 4, x_8);
lean_ctor_set(x_1, 3, x_10);
return x_1;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint32_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_15 = lean_ctor_get_uint32(x_11, sizeof(void*)*2);
x_16 = lean_ctor_get_uint8(x_11, sizeof(void*)*2 + 4);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_18 = x_11;
} else {
 lean_dec_ref(x_11);
 x_18 = lean_box(0);
}
if (lean_is_scalar(x_18)) {
 x_19 = lean_alloc_ctor(0, 2, 5);
} else {
 x_19 = x_18;
}
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set_uint32(x_19, sizeof(void*)*2, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 4, x_16);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_13);
lean_ctor_set(x_20, 2, x_14);
lean_ctor_set(x_20, 3, x_19);
return x_20;
}
}
}
lean_object* lean_environment_main_module(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
return x_3;
}
}
lean_object* lean_environment_mark_quot_init(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 1;
lean_ctor_set_uint8(x_3, sizeof(void*)*2 + 4, x_5);
return x_1;
}
else
{
uint32_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_ctor_get_uint32(x_3, sizeof(void*)*2);
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = 1;
x_10 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set_uint32(x_10, sizeof(void*)*2, x_6);
lean_ctor_set_uint8(x_10, sizeof(void*)*2 + 4, x_9);
lean_ctor_set(x_1, 3, x_10);
return x_1;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint32_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_15 = lean_ctor_get_uint32(x_11, sizeof(void*)*2);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_18 = x_11;
} else {
 lean_dec_ref(x_11);
 x_18 = lean_box(0);
}
x_19 = 1;
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 2, 5);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set_uint32(x_20, sizeof(void*)*2, x_15);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 4, x_19);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_13);
lean_ctor_set(x_21, 2, x_14);
lean_ctor_set(x_21, 3, x_20);
return x_21;
}
}
}
uint8_t lean_environment_quot_init(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 4);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_init_lean_environment_2__isQuotInit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_environment_quot_init(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint32_t lean_environment_trust_level(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get_uint32(x_2, sizeof(void*)*2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_init_lean_environment_3__getTrustLevel___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_environment_trust_level(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
lean_object* l_AssocList_find___main___at_Lean_Environment_getModuleIdxFor___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_dec_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
lean_object* l_HashMapImp_find___at_Lean_Environment_getModuleIdxFor___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_name_hash_usize(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_box_usize(x_6);
x_8 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_9 = lean_array_uget(x_3, x_8);
x_10 = l_AssocList_find___main___at_Lean_Environment_getModuleIdxFor___spec__2(x_2, x_9);
lean_dec(x_9);
return x_10;
}
}
lean_object* l_Lean_Environment_getModuleIdxFor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_HashMapImp_find___at_Lean_Environment_getModuleIdxFor___spec__1(x_3, x_2);
return x_4;
}
}
lean_object* l_AssocList_find___main___at_Lean_Environment_getModuleIdxFor___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find___main___at_Lean_Environment_getModuleIdxFor___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find___at_Lean_Environment_getModuleIdxFor___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find___at_Lean_Environment_getModuleIdxFor___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Environment_getModuleIdxFor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Environment_getModuleIdxFor(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
uint8_t l_Lean_Environment_isConstructor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_environment_find(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 6)
{
uint8_t x_6; 
lean_dec(x_5);
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
}
}
}
lean_object* l_Lean_Environment_isConstructor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Environment_isConstructor(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Environment_addDecl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_add_decl(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Environment_compileDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_compile_decl(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Environment_addAndCompile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_add_decl(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_compile_decl(x_8, x_2, x_3);
return x_9;
}
}
}
lean_object* l_Lean_Environment_addAndCompile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_addAndCompile(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_EnvExtension_setStateUnsafe___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_1, 0);
x_7 = l_Lean_EnvExtensionState_inhabited;
x_8 = x_3;
x_9 = lean_array_set(x_5, x_6, x_8);
lean_ctor_set(x_2, 2, x_9);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
x_15 = l_Lean_EnvExtensionState_inhabited;
x_16 = x_3;
x_17 = lean_array_set(x_12, x_14, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_13);
return x_18;
}
}
}
lean_object* l_Lean_EnvExtension_setStateUnsafe(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_EnvExtension_setStateUnsafe___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_EnvExtension_setStateUnsafe___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnvExtension_setStateUnsafe___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Lean_EnvExtension_setState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_HashMap_Inhabited___closed__1;
x_2 = l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2;
x_3 = l_Array_empty___closed__1;
x_4 = l_Lean_Environment_Inhabited___closed__2;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* l_Lean_EnvExtension_setState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_EnvExtension_setState___closed__1;
return x_5;
}
}
lean_object* l_Lean_EnvExtension_setState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_EnvExtension_setState(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_EnvExtension_getStateUnsafe___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = l_Lean_EnvExtensionState_inhabited;
x_6 = lean_array_get(x_5, x_3, x_4);
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
x_8 = x_6;
return x_8;
}
}
lean_object* l_Lean_EnvExtension_getStateUnsafe(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_EnvExtension_getStateUnsafe___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_EnvExtension_getStateUnsafe___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_EnvExtension_getState___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
return x_3;
}
}
lean_object* l_Lean_EnvExtension_getState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_EnvExtension_getState___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_EnvExtension_getState___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EnvExtension_getState___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_EnvExtension_modifyStateUnsafe___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_array_fget(x_5, x_6);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_fset(x_5, x_6, x_10);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_dec(x_1);
x_13 = x_9;
x_14 = lean_apply_1(x_3, x_13);
x_15 = l_Lean_EnvExtensionState_inhabited;
x_16 = x_14;
x_17 = lean_array_fset(x_11, x_6, x_16);
lean_dec(x_6);
lean_ctor_set(x_2, 2, x_17);
return x_2;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
x_20 = lean_ctor_get(x_2, 2);
x_21 = lean_ctor_get(x_2, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_2);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_array_get_size(x_20);
x_24 = lean_nat_dec_lt(x_22, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 3, x_21);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_array_fget(x_20, x_22);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_array_fset(x_20, x_22, x_27);
x_29 = lean_ctor_get(x_1, 2);
lean_inc(x_29);
lean_dec(x_1);
x_30 = x_26;
x_31 = lean_apply_1(x_3, x_30);
x_32 = l_Lean_EnvExtensionState_inhabited;
x_33 = x_31;
x_34 = lean_array_fset(x_28, x_22, x_33);
lean_dec(x_22);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_18);
lean_ctor_set(x_35, 1, x_19);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set(x_35, 3, x_21);
return x_35;
}
}
}
}
lean_object* l_Lean_EnvExtension_modifyStateUnsafe(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_EnvExtension_modifyStateUnsafe___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_EnvExtension_modifyState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_EnvExtension_setState___closed__1;
return x_5;
}
}
lean_object* l_Lean_EnvExtension_modifyState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_EnvExtension_modifyState(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l___private_init_lean_environment_4__mkEnvExtensionsRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Array_empty___closed__1;
x_3 = lean_io_mk_ref(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_EnvExtension_Inhabited___rarg___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_dec(x_3);
x_4 = l_String_splitAux___main___closed__1;
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_String_splitAux___main___closed__1;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
lean_object* _init_l_Lean_EnvExtension_Inhabited___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtension_Inhabited___rarg___lambda__1), 1, 0);
return x_1;
}
}
lean_object* l_Lean_EnvExtension_Inhabited___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
lean_object* l_Lean_EnvExtension_Inhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_EnvExtension_Inhabited___rarg), 1, 0);
return x_2;
}
}
lean_object* _init_l_Lean_registerEnvExtensionUnsafe___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to register environment, extensions can only be registered during initialization");
return x_1;
}
}
lean_object* _init_l_Lean_registerEnvExtensionUnsafe___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_3 = l_Lean_EnvExtensionState_inhabited;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_registerEnvExtensionUnsafe___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_initializing(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_4, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_4, 0, x_15);
x_16 = l___private_init_lean_environment_5__envExtensionsRef;
x_17 = lean_io_ref_get(x_16, x_4);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_17, 0, x_15);
x_20 = lean_array_get_size(x_19);
lean_dec(x_19);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_2);
lean_ctor_set(x_21, 2, x_1);
x_22 = lean_io_ref_get(x_16, x_17);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_ctor_set(x_22, 0, x_15);
x_25 = lean_io_ref_reset(x_16, x_22);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_15);
x_28 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_21);
x_29 = x_21;
x_30 = lean_array_push(x_24, x_29);
x_31 = lean_io_ref_set(x_16, x_30, x_25);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_21);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_21);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
lean_dec(x_25);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_15);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_21);
x_43 = x_21;
x_44 = lean_array_push(x_24, x_43);
x_45 = lean_io_ref_set(x_16, x_44, x_41);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_21);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_21);
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_51 = x_45;
} else {
 lean_dec_ref(x_45);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_24);
lean_dec(x_21);
x_53 = !lean_is_exclusive(x_25);
if (x_53 == 0)
{
return x_25;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_25, 0);
x_55 = lean_ctor_get(x_25, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_25);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_22, 0);
x_58 = lean_ctor_get(x_22, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_22);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_15);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_io_ref_reset(x_16, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_15);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_21);
x_65 = x_21;
x_66 = lean_array_push(x_57, x_65);
x_67 = lean_io_ref_set(x_16, x_66, x_63);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_21);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_21);
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_73 = x_67;
} else {
 lean_dec_ref(x_67);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_57);
lean_dec(x_21);
x_75 = lean_ctor_get(x_60, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_60, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_77 = x_60;
} else {
 lean_dec_ref(x_60);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_21);
x_79 = !lean_is_exclusive(x_22);
if (x_79 == 0)
{
return x_22;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_22, 0);
x_81 = lean_ctor_get(x_22, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_22);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_17, 0);
x_84 = lean_ctor_get(x_17, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_17);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_15);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_array_get_size(x_83);
lean_dec(x_83);
x_87 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_2);
lean_ctor_set(x_87, 2, x_1);
x_88 = lean_io_ref_get(x_16, x_85);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_91 = x_88;
} else {
 lean_dec_ref(x_88);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_15);
lean_ctor_set(x_92, 1, x_90);
x_93 = lean_io_ref_reset(x_16, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_95 = x_93;
} else {
 lean_dec_ref(x_93);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_15);
lean_ctor_set(x_96, 1, x_94);
x_97 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_87);
x_98 = x_87;
x_99 = lean_array_push(x_89, x_98);
x_100 = lean_io_ref_set(x_16, x_99, x_96);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_87);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_87);
x_104 = lean_ctor_get(x_100, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_100, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_106 = x_100;
} else {
 lean_dec_ref(x_100);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_89);
lean_dec(x_87);
x_108 = lean_ctor_get(x_93, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_93, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_110 = x_93;
} else {
 lean_dec_ref(x_93);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_87);
x_112 = lean_ctor_get(x_88, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_88, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_114 = x_88;
} else {
 lean_dec_ref(x_88);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_2);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_17);
if (x_116 == 0)
{
return x_17;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_17, 0);
x_118 = lean_ctor_get(x_17, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_17);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_120 = lean_ctor_get(x_4, 1);
lean_inc(x_120);
lean_dec(x_4);
x_121 = lean_box(0);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_120);
x_123 = l___private_init_lean_environment_5__envExtensionsRef;
x_124 = lean_io_ref_get(x_123, x_122);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_127 = x_124;
} else {
 lean_dec_ref(x_124);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_121);
lean_ctor_set(x_128, 1, x_126);
x_129 = lean_array_get_size(x_125);
lean_dec(x_125);
x_130 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_2);
lean_ctor_set(x_130, 2, x_1);
x_131 = lean_io_ref_get(x_123, x_128);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_134 = x_131;
} else {
 lean_dec_ref(x_131);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_121);
lean_ctor_set(x_135, 1, x_133);
x_136 = lean_io_ref_reset(x_123, x_135);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_138 = x_136;
} else {
 lean_dec_ref(x_136);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_121);
lean_ctor_set(x_139, 1, x_137);
x_140 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_130);
x_141 = x_130;
x_142 = lean_array_push(x_132, x_141);
x_143 = lean_io_ref_set(x_123, x_142, x_139);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_145 = x_143;
} else {
 lean_dec_ref(x_143);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_130);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_130);
x_147 = lean_ctor_get(x_143, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_143, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_149 = x_143;
} else {
 lean_dec_ref(x_143);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_132);
lean_dec(x_130);
x_151 = lean_ctor_get(x_136, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_136, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_153 = x_136;
} else {
 lean_dec_ref(x_136);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_130);
x_155 = lean_ctor_get(x_131, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_131, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_157 = x_131;
} else {
 lean_dec_ref(x_131);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_2);
lean_dec(x_1);
x_159 = lean_ctor_get(x_124, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_124, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_161 = x_124;
} else {
 lean_dec_ref(x_124);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
}
}
else
{
uint8_t x_163; 
lean_dec(x_2);
lean_dec(x_1);
x_163 = !lean_is_exclusive(x_4);
if (x_163 == 0)
{
return x_4;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_4, 0);
x_165 = lean_ctor_get(x_4, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_4);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
}
lean_object* l_Lean_registerEnvExtensionUnsafe(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_registerEnvExtensionUnsafe___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_registerEnvExtension___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_dec(x_3);
x_4 = l_String_splitAux___main___closed__1;
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_String_splitAux___main___closed__1;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
lean_object* l_Lean_registerEnvExtension(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_registerEnvExtension___rarg), 1, 0);
return x_4;
}
}
lean_object* l_Lean_registerEnvExtension___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_registerEnvExtension(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_ummapAux___main___at___private_init_lean_environment_6__mkInitialExtensionStates___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = l_Array_empty___closed__1;
x_9 = x_2;
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
x_11 = l_Array_empty___closed__1;
x_12 = x_2;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_array_fget(x_2, x_1);
x_15 = lean_box(0);
lean_inc(x_14);
x_16 = x_15;
x_17 = lean_array_fset(x_2, x_1, x_16);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
x_19 = lean_apply_1(x_18, x_3);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_19, 0);
lean_ctor_set(x_19, 0, x_15);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_1, x_22);
x_24 = x_21;
x_25 = lean_array_fset(x_17, x_1, x_24);
lean_dec(x_1);
x_1 = x_23;
x_2 = x_25;
x_3 = x_19;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_1, x_30);
x_32 = x_27;
x_33 = lean_array_fset(x_17, x_1, x_32);
lean_dec(x_1);
x_1 = x_31;
x_2 = x_33;
x_3 = x_29;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_19);
if (x_35 == 0)
{
return x_19;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_19, 0);
x_37 = lean_ctor_get(x_19, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_19);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
lean_object* l___private_init_lean_environment_6__mkInitialExtensionStates(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_init_lean_environment_5__envExtensionsRef;
x_3 = lean_io_ref_get(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_6);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_ummapAux___main___at___private_init_lean_environment_6__mkInitialExtensionStates___spec__1(x_7, x_5, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_ummapAux___main___at___private_init_lean_environment_6__mkInitialExtensionStates___spec__1(x_13, x_9, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
return x_3;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_3);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* _init_l_Lean_mkEmptyEnvironment___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("environment objects cannot be created during initialization");
return x_1;
}
}
lean_object* lean_mk_empty_environment(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_initializing(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = lean_box(0);
lean_ctor_set(x_3, 0, x_8);
x_9 = l___private_init_lean_environment_6__mkInitialExtensionStates(x_3);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = 0;
x_13 = lean_box(0);
x_14 = l_Array_empty___closed__1;
x_15 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_uint32(x_15, sizeof(void*)*2, x_1);
lean_ctor_set_uint8(x_15, sizeof(void*)*2 + 4, x_12);
x_16 = l_HashMap_Inhabited___closed__1;
x_17 = l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2;
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_11);
lean_ctor_set(x_18, 3, x_15);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_9);
x_21 = 0;
x_22 = lean_box(0);
x_23 = l_Array_empty___closed__1;
x_24 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set_uint32(x_24, sizeof(void*)*2, x_1);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 4, x_21);
x_25 = l_HashMap_Inhabited___closed__1;
x_26 = l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2;
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_19);
lean_ctor_set(x_27, 3, x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_20);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_9);
if (x_29 == 0)
{
return x_9;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_9, 0);
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_9);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_3, 1);
lean_inc(x_33);
lean_dec(x_3);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l___private_init_lean_environment_6__mkInitialExtensionStates(x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = 0;
x_41 = lean_box(0);
x_42 = l_Array_empty___closed__1;
x_43 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set_uint32(x_43, sizeof(void*)*2, x_1);
lean_ctor_set_uint8(x_43, sizeof(void*)*2 + 4, x_40);
x_44 = l_HashMap_Inhabited___closed__1;
x_45 = l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2;
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_37);
lean_ctor_set(x_46, 3, x_43);
if (lean_is_scalar(x_39)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_39;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_38);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_36, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_36, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_50 = x_36;
} else {
 lean_dec_ref(x_36);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_3);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_3, 0);
lean_dec(x_53);
x_54 = l_Lean_mkEmptyEnvironment___closed__1;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_54);
return x_3;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_3, 1);
lean_inc(x_55);
lean_dec(x_3);
x_56 = l_Lean_mkEmptyEnvironment___closed__1;
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_3);
if (x_58 == 0)
{
return x_3;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_3, 0);
x_60 = lean_ctor_get(x_3, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_3);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
lean_object* l_Lean_mkEmptyEnvironment___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_empty_environment(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_EnvExtensionEntry_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_NonScalar_Inhabited;
return x_1;
}
}
lean_object* l_Lean_PersistentEnvExtensionState_inhabited___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PersistentEnvExtensionState_inhabited(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PersistentEnvExtensionState_inhabited___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_dec(x_4);
x_5 = l_String_splitAux___main___closed__1;
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_String_splitAux___main___closed__1;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
}
lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_empty___closed__1;
return x_2;
}
}
lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* _init_l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__1___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ExceptT_Monad___rarg___lambda__8___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__2___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__3___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_3);
x_7 = lean_box(0);
x_8 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
x_9 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
x_10 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
x_11 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
x_12 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_8);
lean_ctor_set(x_12, 3, x_9);
lean_ctor_set(x_12, 4, x_10);
lean_ctor_set(x_12, 5, x_11);
return x_12;
}
}
lean_object* l_Lean_PersistentEnvExtension_inhabited(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PersistentEnvExtension_inhabited___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__3(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_4, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Array_empty___closed__1;
x_8 = lean_array_get(x_7, x_6, x_3);
lean_dec(x_6);
return x_8;
}
}
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PersistentEnvExtension_getModuleEntries___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentEnvExtension_getModuleEntries___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_array_fget(x_6, x_7);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_fset(x_6, x_7, x_11);
x_13 = lean_ctor_get(x_4, 2);
lean_inc(x_13);
lean_dec(x_4);
x_14 = x_10;
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_apply_2(x_15, x_17, x_3);
lean_ctor_set(x_14, 1, x_18);
x_19 = l_Lean_EnvExtensionState_inhabited;
x_20 = x_14;
x_21 = lean_array_fset(x_12, x_7, x_20);
lean_dec(x_7);
lean_ctor_set(x_2, 2, x_21);
return x_2;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_apply_2(x_15, x_23, x_3);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_EnvExtensionState_inhabited;
x_27 = x_25;
x_28 = lean_array_fset(x_12, x_7, x_27);
lean_dec(x_7);
lean_ctor_set(x_2, 2, x_28);
return x_2;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_ctor_get(x_2, 1);
x_31 = lean_ctor_get(x_2, 2);
x_32 = lean_ctor_get(x_2, 3);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_2);
x_33 = lean_ctor_get(x_4, 0);
lean_inc(x_33);
x_34 = lean_array_get_size(x_31);
x_35 = lean_nat_dec_lt(x_33, x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_33);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_30);
lean_ctor_set(x_36, 2, x_31);
lean_ctor_set(x_36, 3, x_32);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_37 = lean_array_fget(x_31, x_33);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_array_fset(x_31, x_33, x_38);
x_40 = lean_ctor_get(x_4, 2);
lean_inc(x_40);
lean_dec(x_4);
x_41 = x_37;
x_42 = lean_ctor_get(x_1, 3);
lean_inc(x_42);
lean_dec(x_1);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_45 = x_41;
} else {
 lean_dec_ref(x_41);
 x_45 = lean_box(0);
}
x_46 = lean_apply_2(x_42, x_44, x_3);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_EnvExtensionState_inhabited;
x_49 = x_47;
x_50 = lean_array_fset(x_39, x_33, x_49);
lean_dec(x_33);
x_51 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_51, 0, x_29);
lean_ctor_set(x_51, 1, x_30);
lean_ctor_set(x_51, 2, x_50);
lean_ctor_set(x_51, 3, x_32);
return x_51;
}
}
}
}
lean_object* l_Lean_PersistentEnvExtension_addEntry(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PersistentEnvExtension_addEntry___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_3, x_2);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Lean_PersistentEnvExtension_getState(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PersistentEnvExtension_getState___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_Lean_PersistentEnvExtension_getState___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentEnvExtension_getState___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_PersistentEnvExtension_setState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_array_fget(x_6, x_7);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_fset(x_6, x_7, x_11);
x_13 = lean_ctor_get(x_4, 2);
lean_inc(x_13);
lean_dec(x_4);
x_14 = x_10;
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 1);
lean_dec(x_16);
lean_ctor_set(x_14, 1, x_3);
x_17 = l_Lean_EnvExtensionState_inhabited;
x_18 = x_14;
x_19 = lean_array_fset(x_12, x_7, x_18);
lean_dec(x_7);
lean_ctor_set(x_2, 2, x_19);
return x_2;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
x_22 = l_Lean_EnvExtensionState_inhabited;
x_23 = x_21;
x_24 = lean_array_fset(x_12, x_7, x_23);
lean_dec(x_7);
lean_ctor_set(x_2, 2, x_24);
return x_2;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
x_28 = lean_ctor_get(x_2, 3);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
x_29 = lean_ctor_get(x_4, 0);
lean_inc(x_29);
x_30 = lean_array_get_size(x_27);
x_31 = lean_nat_dec_lt(x_29, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_29);
lean_dec(x_4);
lean_dec(x_3);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 3, x_28);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_33 = lean_array_fget(x_27, x_29);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_array_fset(x_27, x_29, x_34);
x_36 = lean_ctor_get(x_4, 2);
lean_inc(x_36);
lean_dec(x_4);
x_37 = x_33;
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_3);
x_41 = l_Lean_EnvExtensionState_inhabited;
x_42 = x_40;
x_43 = lean_array_fset(x_35, x_29, x_42);
lean_dec(x_29);
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_25);
lean_ctor_set(x_44, 1, x_26);
lean_ctor_set(x_44, 2, x_43);
lean_ctor_set(x_44, 3, x_28);
return x_44;
}
}
}
}
lean_object* l_Lean_PersistentEnvExtension_setState(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PersistentEnvExtension_setState___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_PersistentEnvExtension_modifyState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_array_fget(x_6, x_7);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_fset(x_6, x_7, x_11);
x_13 = lean_ctor_get(x_4, 2);
lean_inc(x_13);
lean_dec(x_4);
x_14 = x_10;
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_apply_1(x_3, x_16);
lean_ctor_set(x_14, 1, x_17);
x_18 = l_Lean_EnvExtensionState_inhabited;
x_19 = x_14;
x_20 = lean_array_fset(x_12, x_7, x_19);
lean_dec(x_7);
lean_ctor_set(x_2, 2, x_20);
return x_2;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_apply_1(x_3, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_EnvExtensionState_inhabited;
x_26 = x_24;
x_27 = lean_array_fset(x_12, x_7, x_26);
lean_dec(x_7);
lean_ctor_set(x_2, 2, x_27);
return x_2;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_2, 0);
x_29 = lean_ctor_get(x_2, 1);
x_30 = lean_ctor_get(x_2, 2);
x_31 = lean_ctor_get(x_2, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_2);
x_32 = lean_ctor_get(x_4, 0);
lean_inc(x_32);
x_33 = lean_array_get_size(x_30);
x_34 = lean_nat_dec_lt(x_32, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_3);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_29);
lean_ctor_set(x_35, 2, x_30);
lean_ctor_set(x_35, 3, x_31);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_36 = lean_array_fget(x_30, x_32);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_array_fset(x_30, x_32, x_37);
x_39 = lean_ctor_get(x_4, 2);
lean_inc(x_39);
lean_dec(x_4);
x_40 = x_36;
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
x_44 = lean_apply_1(x_3, x_42);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_EnvExtensionState_inhabited;
x_47 = x_45;
x_48 = lean_array_fset(x_38, x_32, x_47);
lean_dec(x_32);
x_49 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_49, 0, x_28);
lean_ctor_set(x_49, 1, x_29);
lean_ctor_set(x_49, 2, x_48);
lean_ctor_set(x_49, 3, x_31);
return x_49;
}
}
}
}
lean_object* l_Lean_PersistentEnvExtension_modifyState(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PersistentEnvExtension_modifyState___rarg), 3, 0);
return x_3;
}
}
lean_object* l___private_init_lean_environment_7__mkPersistentEnvExtensionsRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Array_empty___closed__1;
x_3 = lean_io_mk_ref(x_2, x_1);
return x_3;
}
}
uint8_t l_Array_anyMAux___main___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_name_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_3 = x_12;
goto _start;
}
else
{
lean_dec(x_3);
return x_10;
}
}
}
}
lean_object* l_Array_anyMAux___main___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_anyMAux___main___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_registerPersistentEnvExtensionUnsafe___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_initializing(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_4, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_4, 0, x_15);
x_16 = l___private_init_lean_environment_5__envExtensionsRef;
x_17 = lean_io_ref_get(x_16, x_4);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_17, 0, x_15);
x_20 = lean_array_get_size(x_19);
lean_dec(x_19);
x_21 = l_Array_empty___closed__1;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_1);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_2);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_io_ref_get(x_16, x_17);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_ctor_set(x_24, 0, x_15);
x_27 = lean_io_ref_reset(x_16, x_24);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_15);
x_30 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_23);
x_31 = x_23;
x_32 = lean_array_push(x_26, x_31);
x_33 = lean_io_ref_set(x_16, x_32, x_27);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_23);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_23);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_27, 1);
lean_inc(x_42);
lean_dec(x_27);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_15);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_23);
x_45 = x_23;
x_46 = lean_array_push(x_26, x_45);
x_47 = lean_io_ref_set(x_16, x_46, x_43);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_23);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_23);
x_51 = lean_ctor_get(x_47, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_47, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_53 = x_47;
} else {
 lean_dec_ref(x_47);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_26);
lean_dec(x_23);
x_55 = !lean_is_exclusive(x_27);
if (x_55 == 0)
{
return x_27;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_27, 0);
x_57 = lean_ctor_get(x_27, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_27);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_24, 0);
x_60 = lean_ctor_get(x_24, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_24);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_15);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_io_ref_reset(x_16, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_15);
lean_ctor_set(x_65, 1, x_63);
x_66 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_23);
x_67 = x_23;
x_68 = lean_array_push(x_59, x_67);
x_69 = lean_io_ref_set(x_16, x_68, x_65);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_23);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_23);
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_75 = x_69;
} else {
 lean_dec_ref(x_69);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_59);
lean_dec(x_23);
x_77 = lean_ctor_get(x_62, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_62, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_79 = x_62;
} else {
 lean_dec_ref(x_62);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_23);
x_81 = !lean_is_exclusive(x_24);
if (x_81 == 0)
{
return x_24;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_24, 0);
x_83 = lean_ctor_get(x_24, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_24);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_85 = lean_ctor_get(x_17, 0);
x_86 = lean_ctor_get(x_17, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_17);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_15);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_array_get_size(x_85);
lean_dec(x_85);
x_89 = l_Array_empty___closed__1;
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_1);
x_91 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_2);
lean_ctor_set(x_91, 2, x_90);
x_92 = lean_io_ref_get(x_16, x_87);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_95 = x_92;
} else {
 lean_dec_ref(x_92);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_15);
lean_ctor_set(x_96, 1, x_94);
x_97 = lean_io_ref_reset(x_16, x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_15);
lean_ctor_set(x_100, 1, x_98);
x_101 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_91);
x_102 = x_91;
x_103 = lean_array_push(x_93, x_102);
x_104 = lean_io_ref_set(x_16, x_103, x_100);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_106 = x_104;
} else {
 lean_dec_ref(x_104);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_91);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_91);
x_108 = lean_ctor_get(x_104, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_104, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_110 = x_104;
} else {
 lean_dec_ref(x_104);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_93);
lean_dec(x_91);
x_112 = lean_ctor_get(x_97, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_97, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_114 = x_97;
} else {
 lean_dec_ref(x_97);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_91);
x_116 = lean_ctor_get(x_92, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_92, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_118 = x_92;
} else {
 lean_dec_ref(x_92);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_2);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_17);
if (x_120 == 0)
{
return x_17;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_17, 0);
x_122 = lean_ctor_get(x_17, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_17);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_124 = lean_ctor_get(x_4, 1);
lean_inc(x_124);
lean_dec(x_4);
x_125 = lean_box(0);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
x_127 = l___private_init_lean_environment_5__envExtensionsRef;
x_128 = lean_io_ref_get(x_127, x_126);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_131 = x_128;
} else {
 lean_dec_ref(x_128);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_125);
lean_ctor_set(x_132, 1, x_130);
x_133 = lean_array_get_size(x_129);
lean_dec(x_129);
x_134 = l_Array_empty___closed__1;
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_1);
x_136 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_2);
lean_ctor_set(x_136, 2, x_135);
x_137 = lean_io_ref_get(x_127, x_132);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_140 = x_137;
} else {
 lean_dec_ref(x_137);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_125);
lean_ctor_set(x_141, 1, x_139);
x_142 = lean_io_ref_reset(x_127, x_141);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_144 = x_142;
} else {
 lean_dec_ref(x_142);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_125);
lean_ctor_set(x_145, 1, x_143);
x_146 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_136);
x_147 = x_136;
x_148 = lean_array_push(x_138, x_147);
x_149 = lean_io_ref_set(x_127, x_148, x_145);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_151 = x_149;
} else {
 lean_dec_ref(x_149);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_136);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_136);
x_153 = lean_ctor_get(x_149, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_149, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_155 = x_149;
} else {
 lean_dec_ref(x_149);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_138);
lean_dec(x_136);
x_157 = lean_ctor_get(x_142, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_142, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_159 = x_142;
} else {
 lean_dec_ref(x_142);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_136);
x_161 = lean_ctor_get(x_137, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_137, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_163 = x_137;
} else {
 lean_dec_ref(x_137);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_2);
lean_dec(x_1);
x_165 = lean_ctor_get(x_128, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_128, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_167 = x_128;
} else {
 lean_dec_ref(x_128);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
}
}
}
else
{
uint8_t x_169; 
lean_dec(x_2);
lean_dec(x_1);
x_169 = !lean_is_exclusive(x_4);
if (x_169 == 0)
{
return x_4;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_4, 0);
x_171 = lean_ctor_get(x_4, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_4);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
}
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_registerPersistentEnvExtensionUnsafe___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_registerEnvExtensionUnsafe___at_Lean_registerPersistentEnvExtensionUnsafe___spec__2___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
lean_object* _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_empty___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__1), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_EnvExtensionState_inhabited;
x_2 = l_Lean_PersistentEnvExtension_inhabited___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid environment extension, '");
return x_1;
}
}
lean_object* _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has already been used");
return x_1;
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_init_lean_environment_8__persistentEnvExtensionsRef;
x_5 = lean_io_ref_get(x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_anyMAux___main___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg(x_2, x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_box(0);
lean_ctor_set(x_5, 0, x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = l_Array_empty___closed__1;
lean_inc(x_11);
x_13 = lean_apply_1(x_11, x_12);
x_14 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_15 = lean_alloc_closure((void*)(l_EState_bind___rarg), 3, 2);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_registerEnvExtensionUnsafe___at_Lean_registerPersistentEnvExtensionUnsafe___spec__2___rarg(x_1, x_15, x_5);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_16, 0, x_10);
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 4);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_11);
lean_ctor_set(x_23, 3, x_20);
lean_ctor_set(x_23, 4, x_21);
lean_ctor_set(x_23, 5, x_22);
x_24 = lean_io_ref_get(x_4, x_16);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_ctor_set(x_24, 0, x_10);
x_27 = lean_io_ref_reset(x_4, x_24);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_10);
x_30 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_23);
x_31 = x_23;
x_32 = lean_array_push(x_26, x_31);
x_33 = lean_io_ref_set(x_4, x_32, x_27);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_23);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_23);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_27, 1);
lean_inc(x_42);
lean_dec(x_27);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_10);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_23);
x_45 = x_23;
x_46 = lean_array_push(x_26, x_45);
x_47 = lean_io_ref_set(x_4, x_46, x_43);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_23);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_23);
x_51 = lean_ctor_get(x_47, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_47, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_53 = x_47;
} else {
 lean_dec_ref(x_47);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_26);
lean_dec(x_23);
x_55 = !lean_is_exclusive(x_27);
if (x_55 == 0)
{
return x_27;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_27, 0);
x_57 = lean_ctor_get(x_27, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_27);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_24, 0);
x_60 = lean_ctor_get(x_24, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_24);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_10);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_io_ref_reset(x_4, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_10);
lean_ctor_set(x_65, 1, x_63);
x_66 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_23);
x_67 = x_23;
x_68 = lean_array_push(x_59, x_67);
x_69 = lean_io_ref_set(x_4, x_68, x_65);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_23);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_23);
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_75 = x_69;
} else {
 lean_dec_ref(x_69);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_59);
lean_dec(x_23);
x_77 = lean_ctor_get(x_62, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_62, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_79 = x_62;
} else {
 lean_dec_ref(x_62);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_23);
x_81 = !lean_is_exclusive(x_24);
if (x_81 == 0)
{
return x_24;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_24, 0);
x_83 = lean_ctor_get(x_24, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_24);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_85 = lean_ctor_get(x_16, 0);
x_86 = lean_ctor_get(x_16, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_16);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_10);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_ctor_get(x_2, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_2, 2);
lean_inc(x_89);
x_90 = lean_ctor_get(x_2, 3);
lean_inc(x_90);
x_91 = lean_ctor_get(x_2, 4);
lean_inc(x_91);
lean_dec(x_2);
x_92 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_92, 0, x_85);
lean_ctor_set(x_92, 1, x_88);
lean_ctor_set(x_92, 2, x_11);
lean_ctor_set(x_92, 3, x_89);
lean_ctor_set(x_92, 4, x_90);
lean_ctor_set(x_92, 5, x_91);
x_93 = lean_io_ref_get(x_4, x_87);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_96 = x_93;
} else {
 lean_dec_ref(x_93);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_10);
lean_ctor_set(x_97, 1, x_95);
x_98 = lean_io_ref_reset(x_4, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_10);
lean_ctor_set(x_101, 1, x_99);
x_102 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_92);
x_103 = x_92;
x_104 = lean_array_push(x_94, x_103);
x_105 = lean_io_ref_set(x_4, x_104, x_101);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_107 = x_105;
} else {
 lean_dec_ref(x_105);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_92);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_92);
x_109 = lean_ctor_get(x_105, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_105, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_111 = x_105;
} else {
 lean_dec_ref(x_105);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_94);
lean_dec(x_92);
x_113 = lean_ctor_get(x_98, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_98, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_115 = x_98;
} else {
 lean_dec_ref(x_98);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_92);
x_117 = lean_ctor_get(x_93, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_93, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_119 = x_93;
} else {
 lean_dec_ref(x_93);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_11);
lean_dec(x_2);
x_121 = !lean_is_exclusive(x_16);
if (x_121 == 0)
{
return x_16;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_16, 0);
x_123 = lean_ctor_get(x_16, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_16);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_1);
x_125 = lean_ctor_get(x_2, 0);
lean_inc(x_125);
lean_dec(x_2);
x_126 = l_Lean_Name_toString___closed__1;
x_127 = l_Lean_Name_toStringWithSep___main(x_126, x_125);
x_128 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_129 = lean_string_append(x_128, x_127);
lean_dec(x_127);
x_130 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_131 = lean_string_append(x_129, x_130);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_131);
return x_5;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_132 = lean_ctor_get(x_5, 0);
x_133 = lean_ctor_get(x_5, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_5);
x_134 = lean_unsigned_to_nat(0u);
x_135 = l_Array_anyMAux___main___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg(x_2, x_132, x_134);
lean_dec(x_132);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_133);
x_138 = lean_ctor_get(x_2, 1);
lean_inc(x_138);
x_139 = l_Array_empty___closed__1;
lean_inc(x_138);
x_140 = lean_apply_1(x_138, x_139);
x_141 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_142 = lean_alloc_closure((void*)(l_EState_bind___rarg), 3, 2);
lean_closure_set(x_142, 0, x_140);
lean_closure_set(x_142, 1, x_141);
x_143 = l_Lean_registerEnvExtensionUnsafe___at_Lean_registerPersistentEnvExtensionUnsafe___spec__2___rarg(x_1, x_142, x_137);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_146 = x_143;
} else {
 lean_dec_ref(x_143);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_136);
lean_ctor_set(x_147, 1, x_145);
x_148 = lean_ctor_get(x_2, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_2, 2);
lean_inc(x_149);
x_150 = lean_ctor_get(x_2, 3);
lean_inc(x_150);
x_151 = lean_ctor_get(x_2, 4);
lean_inc(x_151);
lean_dec(x_2);
x_152 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_152, 0, x_144);
lean_ctor_set(x_152, 1, x_148);
lean_ctor_set(x_152, 2, x_138);
lean_ctor_set(x_152, 3, x_149);
lean_ctor_set(x_152, 4, x_150);
lean_ctor_set(x_152, 5, x_151);
x_153 = lean_io_ref_get(x_4, x_147);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_156 = x_153;
} else {
 lean_dec_ref(x_153);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_136);
lean_ctor_set(x_157, 1, x_155);
x_158 = lean_io_ref_reset(x_4, x_157);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_160 = x_158;
} else {
 lean_dec_ref(x_158);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_136);
lean_ctor_set(x_161, 1, x_159);
x_162 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_152);
x_163 = x_152;
x_164 = lean_array_push(x_154, x_163);
x_165 = lean_io_ref_set(x_4, x_164, x_161);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_167 = x_165;
} else {
 lean_dec_ref(x_165);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_152);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_152);
x_169 = lean_ctor_get(x_165, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_165, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_171 = x_165;
} else {
 lean_dec_ref(x_165);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_154);
lean_dec(x_152);
x_173 = lean_ctor_get(x_158, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_158, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_175 = x_158;
} else {
 lean_dec_ref(x_158);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
return x_176;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_152);
x_177 = lean_ctor_get(x_153, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_153, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_179 = x_153;
} else {
 lean_dec_ref(x_153);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_138);
lean_dec(x_2);
x_181 = lean_ctor_get(x_143, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_143, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_183 = x_143;
} else {
 lean_dec_ref(x_143);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_1);
x_185 = lean_ctor_get(x_2, 0);
lean_inc(x_185);
lean_dec(x_2);
x_186 = l_Lean_Name_toString___closed__1;
x_187 = l_Lean_Name_toStringWithSep___main(x_186, x_185);
x_188 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_189 = lean_string_append(x_188, x_187);
lean_dec(x_187);
x_190 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_191 = lean_string_append(x_189, x_190);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_133);
return x_192;
}
}
}
else
{
uint8_t x_193; 
lean_dec(x_2);
lean_dec(x_1);
x_193 = !lean_is_exclusive(x_5);
if (x_193 == 0)
{
return x_5;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_5, 0);
x_195 = lean_ctor_get(x_5, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_5);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_registerPersistentEnvExtensionUnsafe___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Array_anyMAux___main___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_anyMAux___main___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Lean_registerPersistentEnvExtension___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_dec(x_3);
x_4 = l_String_splitAux___main___closed__1;
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_String_splitAux___main___closed__1;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
lean_object* l_Lean_registerPersistentEnvExtension(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_registerPersistentEnvExtension___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_registerPersistentEnvExtension___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_registerPersistentEnvExtension(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_9 = lean_apply_2(x_1, x_5, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
lean_object* l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_10 = l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__1___rarg(x_1, x_8, x_8, x_9, x_5);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_4 = x_12;
x_5 = x_10;
goto _start;
}
}
}
lean_object* l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__2___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_Lean_mkStateFromImportedEntries___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__2___rarg(x_1, x_3, x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_Lean_mkStateFromImportedEntries(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_mkStateFromImportedEntries___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_mkStateFromImportedEntries___spec__2___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_mkStateFromImportedEntries___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkStateFromImportedEntries___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
uint8_t l_Array_anyMAux___main___at_Lean_registerSimplePersistentEnvExtension___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_name_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_3 = x_12;
goto _start;
}
else
{
lean_dec(x_3);
return x_10;
}
}
}
}
lean_object* l_Array_anyMAux___main___at_Lean_registerSimplePersistentEnvExtension___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_anyMAux___main___at_Lean_registerSimplePersistentEnvExtension___spec__2___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_initializing(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_4, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_4, 0, x_15);
x_16 = l___private_init_lean_environment_5__envExtensionsRef;
x_17 = lean_io_ref_get(x_16, x_4);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_17, 0, x_15);
x_20 = lean_array_get_size(x_19);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_1);
x_23 = l_Array_empty___closed__1;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_2);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_io_ref_get(x_16, x_17);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_ctor_set(x_26, 0, x_15);
x_29 = lean_io_ref_reset(x_16, x_26);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_15);
x_32 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_25);
x_33 = x_25;
x_34 = lean_array_push(x_28, x_33);
x_35 = lean_io_ref_set(x_16, x_34, x_29);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_25);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_25);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_25);
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
return x_35;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_35);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_29, 1);
lean_inc(x_44);
lean_dec(x_29);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_15);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_25);
x_47 = x_25;
x_48 = lean_array_push(x_28, x_47);
x_49 = lean_io_ref_set(x_16, x_48, x_45);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_25);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_25);
x_53 = lean_ctor_get(x_49, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_55 = x_49;
} else {
 lean_dec_ref(x_49);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_28);
lean_dec(x_25);
x_57 = !lean_is_exclusive(x_29);
if (x_57 == 0)
{
return x_29;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_29, 0);
x_59 = lean_ctor_get(x_29, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_29);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_26, 0);
x_62 = lean_ctor_get(x_26, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_26);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_15);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_io_ref_reset(x_16, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_15);
lean_ctor_set(x_67, 1, x_65);
x_68 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_25);
x_69 = x_25;
x_70 = lean_array_push(x_61, x_69);
x_71 = lean_io_ref_set(x_16, x_70, x_67);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_25);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_25);
x_75 = lean_ctor_get(x_71, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_71, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_77 = x_71;
} else {
 lean_dec_ref(x_71);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_61);
lean_dec(x_25);
x_79 = lean_ctor_get(x_64, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_64, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_81 = x_64;
} else {
 lean_dec_ref(x_64);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_25);
x_83 = !lean_is_exclusive(x_26);
if (x_83 == 0)
{
return x_26;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_26, 0);
x_85 = lean_ctor_get(x_26, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_26);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_87 = lean_ctor_get(x_17, 0);
x_88 = lean_ctor_get(x_17, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_17);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_15);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_array_get_size(x_87);
lean_dec(x_87);
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_1);
x_93 = l_Array_empty___closed__1;
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
x_95 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_95, 0, x_90);
lean_ctor_set(x_95, 1, x_2);
lean_ctor_set(x_95, 2, x_94);
x_96 = lean_io_ref_get(x_16, x_89);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_99 = x_96;
} else {
 lean_dec_ref(x_96);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_15);
lean_ctor_set(x_100, 1, x_98);
x_101 = lean_io_ref_reset(x_16, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_103 = x_101;
} else {
 lean_dec_ref(x_101);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_15);
lean_ctor_set(x_104, 1, x_102);
x_105 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_95);
x_106 = x_95;
x_107 = lean_array_push(x_97, x_106);
x_108 = lean_io_ref_set(x_16, x_107, x_104);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_110 = x_108;
} else {
 lean_dec_ref(x_108);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_95);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_95);
x_112 = lean_ctor_get(x_108, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_108, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_114 = x_108;
} else {
 lean_dec_ref(x_108);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_97);
lean_dec(x_95);
x_116 = lean_ctor_get(x_101, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_101, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_118 = x_101;
} else {
 lean_dec_ref(x_101);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_95);
x_120 = lean_ctor_get(x_96, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_96, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_122 = x_96;
} else {
 lean_dec_ref(x_96);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_2);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_17);
if (x_124 == 0)
{
return x_17;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_17, 0);
x_126 = lean_ctor_get(x_17, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_17);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_128 = lean_ctor_get(x_4, 1);
lean_inc(x_128);
lean_dec(x_4);
x_129 = lean_box(0);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_128);
x_131 = l___private_init_lean_environment_5__envExtensionsRef;
x_132 = lean_io_ref_get(x_131, x_130);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_135 = x_132;
} else {
 lean_dec_ref(x_132);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_129);
lean_ctor_set(x_136, 1, x_134);
x_137 = lean_array_get_size(x_133);
lean_dec(x_133);
x_138 = lean_box(0);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_1);
x_140 = l_Array_empty___closed__1;
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
x_142 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_142, 0, x_137);
lean_ctor_set(x_142, 1, x_2);
lean_ctor_set(x_142, 2, x_141);
x_143 = lean_io_ref_get(x_131, x_136);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_146 = x_143;
} else {
 lean_dec_ref(x_143);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_129);
lean_ctor_set(x_147, 1, x_145);
x_148 = lean_io_ref_reset(x_131, x_147);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_150 = x_148;
} else {
 lean_dec_ref(x_148);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_129);
lean_ctor_set(x_151, 1, x_149);
x_152 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_142);
x_153 = x_142;
x_154 = lean_array_push(x_144, x_153);
x_155 = lean_io_ref_set(x_131, x_154, x_151);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_157 = x_155;
} else {
 lean_dec_ref(x_155);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_142);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_142);
x_159 = lean_ctor_get(x_155, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_155, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_161 = x_155;
} else {
 lean_dec_ref(x_155);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_144);
lean_dec(x_142);
x_163 = lean_ctor_get(x_148, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_148, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_165 = x_148;
} else {
 lean_dec_ref(x_148);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_142);
x_167 = lean_ctor_get(x_143, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_143, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_169 = x_143;
} else {
 lean_dec_ref(x_143);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_2);
lean_dec(x_1);
x_171 = lean_ctor_get(x_132, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_132, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_173 = x_132;
} else {
 lean_dec_ref(x_132);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_2);
lean_dec(x_1);
x_175 = !lean_is_exclusive(x_4);
if (x_175 == 0)
{
return x_4;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_4, 0);
x_177 = lean_ctor_get(x_4, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_4);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
}
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_registerEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__3___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_init_lean_environment_8__persistentEnvExtensionsRef;
x_5 = lean_io_ref_get(x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_anyMAux___main___at_Lean_registerSimplePersistentEnvExtension___spec__2___rarg(x_2, x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_box(0);
lean_ctor_set(x_5, 0, x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = l_Array_empty___closed__1;
lean_inc(x_11);
x_13 = lean_apply_1(x_11, x_12);
x_14 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_15 = lean_alloc_closure((void*)(l_EState_bind___rarg), 3, 2);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_registerEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__3___rarg(x_1, x_15, x_5);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_16, 0, x_10);
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 4);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_11);
lean_ctor_set(x_23, 3, x_20);
lean_ctor_set(x_23, 4, x_21);
lean_ctor_set(x_23, 5, x_22);
x_24 = lean_io_ref_get(x_4, x_16);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_ctor_set(x_24, 0, x_10);
x_27 = lean_io_ref_reset(x_4, x_24);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_10);
x_30 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_23);
x_31 = x_23;
x_32 = lean_array_push(x_26, x_31);
x_33 = lean_io_ref_set(x_4, x_32, x_27);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_23);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_23);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_27, 1);
lean_inc(x_42);
lean_dec(x_27);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_10);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_23);
x_45 = x_23;
x_46 = lean_array_push(x_26, x_45);
x_47 = lean_io_ref_set(x_4, x_46, x_43);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_23);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_23);
x_51 = lean_ctor_get(x_47, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_47, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_53 = x_47;
} else {
 lean_dec_ref(x_47);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_26);
lean_dec(x_23);
x_55 = !lean_is_exclusive(x_27);
if (x_55 == 0)
{
return x_27;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_27, 0);
x_57 = lean_ctor_get(x_27, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_27);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_24, 0);
x_60 = lean_ctor_get(x_24, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_24);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_10);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_io_ref_reset(x_4, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_10);
lean_ctor_set(x_65, 1, x_63);
x_66 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_23);
x_67 = x_23;
x_68 = lean_array_push(x_59, x_67);
x_69 = lean_io_ref_set(x_4, x_68, x_65);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_23);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_23);
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_75 = x_69;
} else {
 lean_dec_ref(x_69);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_59);
lean_dec(x_23);
x_77 = lean_ctor_get(x_62, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_62, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_79 = x_62;
} else {
 lean_dec_ref(x_62);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_23);
x_81 = !lean_is_exclusive(x_24);
if (x_81 == 0)
{
return x_24;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_24, 0);
x_83 = lean_ctor_get(x_24, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_24);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_85 = lean_ctor_get(x_16, 0);
x_86 = lean_ctor_get(x_16, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_16);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_10);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_ctor_get(x_2, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_2, 2);
lean_inc(x_89);
x_90 = lean_ctor_get(x_2, 3);
lean_inc(x_90);
x_91 = lean_ctor_get(x_2, 4);
lean_inc(x_91);
lean_dec(x_2);
x_92 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_92, 0, x_85);
lean_ctor_set(x_92, 1, x_88);
lean_ctor_set(x_92, 2, x_11);
lean_ctor_set(x_92, 3, x_89);
lean_ctor_set(x_92, 4, x_90);
lean_ctor_set(x_92, 5, x_91);
x_93 = lean_io_ref_get(x_4, x_87);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_96 = x_93;
} else {
 lean_dec_ref(x_93);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_10);
lean_ctor_set(x_97, 1, x_95);
x_98 = lean_io_ref_reset(x_4, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_10);
lean_ctor_set(x_101, 1, x_99);
x_102 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_92);
x_103 = x_92;
x_104 = lean_array_push(x_94, x_103);
x_105 = lean_io_ref_set(x_4, x_104, x_101);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_107 = x_105;
} else {
 lean_dec_ref(x_105);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_92);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_92);
x_109 = lean_ctor_get(x_105, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_105, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_111 = x_105;
} else {
 lean_dec_ref(x_105);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_94);
lean_dec(x_92);
x_113 = lean_ctor_get(x_98, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_98, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_115 = x_98;
} else {
 lean_dec_ref(x_98);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_92);
x_117 = lean_ctor_get(x_93, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_93, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_119 = x_93;
} else {
 lean_dec_ref(x_93);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_11);
lean_dec(x_2);
x_121 = !lean_is_exclusive(x_16);
if (x_121 == 0)
{
return x_16;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_16, 0);
x_123 = lean_ctor_get(x_16, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_16);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_1);
x_125 = lean_ctor_get(x_2, 0);
lean_inc(x_125);
lean_dec(x_2);
x_126 = l_Lean_Name_toString___closed__1;
x_127 = l_Lean_Name_toStringWithSep___main(x_126, x_125);
x_128 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_129 = lean_string_append(x_128, x_127);
lean_dec(x_127);
x_130 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_131 = lean_string_append(x_129, x_130);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_131);
return x_5;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_132 = lean_ctor_get(x_5, 0);
x_133 = lean_ctor_get(x_5, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_5);
x_134 = lean_unsigned_to_nat(0u);
x_135 = l_Array_anyMAux___main___at_Lean_registerSimplePersistentEnvExtension___spec__2___rarg(x_2, x_132, x_134);
lean_dec(x_132);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_133);
x_138 = lean_ctor_get(x_2, 1);
lean_inc(x_138);
x_139 = l_Array_empty___closed__1;
lean_inc(x_138);
x_140 = lean_apply_1(x_138, x_139);
x_141 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_142 = lean_alloc_closure((void*)(l_EState_bind___rarg), 3, 2);
lean_closure_set(x_142, 0, x_140);
lean_closure_set(x_142, 1, x_141);
x_143 = l_Lean_registerEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__3___rarg(x_1, x_142, x_137);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_146 = x_143;
} else {
 lean_dec_ref(x_143);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_136);
lean_ctor_set(x_147, 1, x_145);
x_148 = lean_ctor_get(x_2, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_2, 2);
lean_inc(x_149);
x_150 = lean_ctor_get(x_2, 3);
lean_inc(x_150);
x_151 = lean_ctor_get(x_2, 4);
lean_inc(x_151);
lean_dec(x_2);
x_152 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_152, 0, x_144);
lean_ctor_set(x_152, 1, x_148);
lean_ctor_set(x_152, 2, x_138);
lean_ctor_set(x_152, 3, x_149);
lean_ctor_set(x_152, 4, x_150);
lean_ctor_set(x_152, 5, x_151);
x_153 = lean_io_ref_get(x_4, x_147);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_156 = x_153;
} else {
 lean_dec_ref(x_153);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_136);
lean_ctor_set(x_157, 1, x_155);
x_158 = lean_io_ref_reset(x_4, x_157);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_160 = x_158;
} else {
 lean_dec_ref(x_158);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_136);
lean_ctor_set(x_161, 1, x_159);
x_162 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_152);
x_163 = x_152;
x_164 = lean_array_push(x_154, x_163);
x_165 = lean_io_ref_set(x_4, x_164, x_161);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_167 = x_165;
} else {
 lean_dec_ref(x_165);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_152);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_152);
x_169 = lean_ctor_get(x_165, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_165, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_171 = x_165;
} else {
 lean_dec_ref(x_165);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_154);
lean_dec(x_152);
x_173 = lean_ctor_get(x_158, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_158, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_175 = x_158;
} else {
 lean_dec_ref(x_158);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
return x_176;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_152);
x_177 = lean_ctor_get(x_153, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_153, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_179 = x_153;
} else {
 lean_dec_ref(x_153);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_138);
lean_dec(x_2);
x_181 = lean_ctor_get(x_143, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_143, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_183 = x_143;
} else {
 lean_dec_ref(x_143);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_1);
x_185 = lean_ctor_get(x_2, 0);
lean_inc(x_185);
lean_dec(x_2);
x_186 = l_Lean_Name_toString___closed__1;
x_187 = l_Lean_Name_toStringWithSep___main(x_186, x_185);
x_188 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_189 = lean_string_append(x_188, x_187);
lean_dec(x_187);
x_190 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_191 = lean_string_append(x_189, x_190);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_133);
return x_192;
}
}
}
else
{
uint8_t x_193; 
lean_dec(x_2);
lean_dec(x_1);
x_193 = !lean_is_exclusive(x_5);
if (x_193 == 0)
{
return x_5;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_5, 0);
x_195 = lean_ctor_get(x_5, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_5);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = lean_box(0);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_7, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_1(x_12, x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
}
}
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_8, x_6, x_3);
lean_ctor_set(x_2, 1, x_9);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_3);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_apply_2(x_13, x_11, x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_List_reverse___rarg(x_4);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
}
lean_object* _init_l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("number of local entries: ");
return x_1;
}
}
lean_object* _init_l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_lengthAux___main___rarg(x_2, x_3);
x_5 = l_Nat_repr(x_4);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = 0;
x_8 = l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__2;
x_9 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*2, x_7);
return x_9;
}
}
lean_object* _init_l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_inc(x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1), 3, 1);
lean_closure_set(x_5, 0, x_2);
lean_inc(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__2), 3, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__3), 2, 1);
lean_closure_set(x_7, 0, x_2);
x_8 = l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1;
x_9 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set(x_9, 4, x_8);
x_10 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__1___rarg(x_1, x_9, x_3);
return x_10;
}
}
lean_object* l_Lean_registerSimplePersistentEnvExtension(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Array_anyMAux___main___at_Lean_registerSimplePersistentEnvExtension___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_anyMAux___main___at_Lean_registerSimplePersistentEnvExtension___spec__2___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_SimplePersistentEnvExtension_Inhabited___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
x_4 = l_Lean_PersistentEnvExtension_inhabited___rarg(x_3);
return x_4;
}
}
lean_object* l_Lean_SimplePersistentEnvExtension_Inhabited(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_Inhabited___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentEnvExtension_getState___rarg(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_SimplePersistentEnvExtension_getEntries(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_getEntries___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SimplePersistentEnvExtension_getEntries___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_SimplePersistentEnvExtension_getState___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentEnvExtension_getState___rarg(x_1, x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_SimplePersistentEnvExtension_getState(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_getState___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_Lean_SimplePersistentEnvExtension_getState___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_SimplePersistentEnvExtension_setState___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 1);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_1);
return x_6;
}
}
}
lean_object* l_Lean_SimplePersistentEnvExtension_setState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_setState___rarg___lambda__1), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = l_Lean_PersistentEnvExtension_modifyState___rarg(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l_Lean_SimplePersistentEnvExtension_setState(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_setState___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_modifyState___rarg___lambda__1), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = l_Lean_PersistentEnvExtension_modifyState___rarg(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l_Lean_SimplePersistentEnvExtension_modifyState(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_modifyState___rarg), 3, 0);
return x_3;
}
}
lean_object* _init_l_Lean_CPPExtensionState_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_NonScalar_Inhabited;
return x_1;
}
}
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_registerCPPExtension___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_initializing(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = lean_mk_string("failed to register environment, extensions can only be registered during initialization");
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_mk_string("failed to register environment, extensions can only be registered during initialization");
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_3, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_3, 0, x_14);
x_15 = l___private_init_lean_environment_5__envExtensionsRef;
x_16 = lean_io_ref_get(x_15, x_3);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_16, 0, x_14);
x_19 = lean_array_get_size(x_18);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_1);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_io_ref_get(x_15, x_16);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_ctor_set(x_22, 0, x_14);
x_25 = lean_io_ref_reset(x_15, x_22);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_14);
x_28 = lean_alloc_closure((void*)(l_Lean_EnvExtension_Inhabited___rarg___lambda__1), 1, 0);
x_29 = l_Lean_EnvExtensionState_inhabited;
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_29);
lean_inc(x_21);
x_31 = x_21;
x_32 = lean_array_push(x_24, x_31);
x_33 = lean_io_ref_set(x_15, x_32, x_25);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_21);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_21);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_21);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_25, 1);
lean_inc(x_42);
lean_dec(x_25);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_14);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_closure((void*)(l_Lean_EnvExtension_Inhabited___rarg___lambda__1), 1, 0);
x_45 = l_Lean_EnvExtensionState_inhabited;
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_20);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_45);
lean_inc(x_21);
x_47 = x_21;
x_48 = lean_array_push(x_24, x_47);
x_49 = lean_io_ref_set(x_15, x_48, x_43);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_21);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_21);
x_53 = lean_ctor_get(x_49, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_55 = x_49;
} else {
 lean_dec_ref(x_49);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_24);
lean_dec(x_21);
x_57 = !lean_is_exclusive(x_25);
if (x_57 == 0)
{
return x_25;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_25, 0);
x_59 = lean_ctor_get(x_25, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_25);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_22, 0);
x_62 = lean_ctor_get(x_22, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_22);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_14);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_io_ref_reset(x_15, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_14);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_alloc_closure((void*)(l_Lean_EnvExtension_Inhabited___rarg___lambda__1), 1, 0);
x_69 = l_Lean_EnvExtensionState_inhabited;
x_70 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_70, 0, x_20);
lean_ctor_set(x_70, 1, x_68);
lean_ctor_set(x_70, 2, x_69);
lean_inc(x_21);
x_71 = x_21;
x_72 = lean_array_push(x_61, x_71);
x_73 = lean_io_ref_set(x_15, x_72, x_67);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_75 = x_73;
} else {
 lean_dec_ref(x_73);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_21);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_21);
x_77 = lean_ctor_get(x_73, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_79 = x_73;
} else {
 lean_dec_ref(x_73);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_61);
lean_dec(x_21);
x_81 = lean_ctor_get(x_64, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_64, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_83 = x_64;
} else {
 lean_dec_ref(x_64);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_21);
x_85 = !lean_is_exclusive(x_22);
if (x_85 == 0)
{
return x_22;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_22, 0);
x_87 = lean_ctor_get(x_22, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_22);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_89 = lean_ctor_get(x_16, 0);
x_90 = lean_ctor_get(x_16, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_16);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_14);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_array_get_size(x_89);
lean_dec(x_89);
x_93 = lean_unsigned_to_nat(0u);
x_94 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_1);
lean_ctor_set(x_94, 2, x_93);
x_95 = lean_io_ref_get(x_15, x_91);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_14);
lean_ctor_set(x_99, 1, x_97);
x_100 = lean_io_ref_reset(x_15, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_14);
lean_ctor_set(x_103, 1, x_101);
x_104 = lean_alloc_closure((void*)(l_Lean_EnvExtension_Inhabited___rarg___lambda__1), 1, 0);
x_105 = l_Lean_EnvExtensionState_inhabited;
x_106 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_106, 0, x_93);
lean_ctor_set(x_106, 1, x_104);
lean_ctor_set(x_106, 2, x_105);
lean_inc(x_94);
x_107 = x_94;
x_108 = lean_array_push(x_96, x_107);
x_109 = lean_io_ref_set(x_15, x_108, x_103);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_94);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_94);
x_113 = lean_ctor_get(x_109, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_109, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_115 = x_109;
} else {
 lean_dec_ref(x_109);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_96);
lean_dec(x_94);
x_117 = lean_ctor_get(x_100, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_100, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_119 = x_100;
} else {
 lean_dec_ref(x_100);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_94);
x_121 = lean_ctor_get(x_95, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_95, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_123 = x_95;
} else {
 lean_dec_ref(x_95);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_16);
if (x_125 == 0)
{
return x_16;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_16, 0);
x_127 = lean_ctor_get(x_16, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_16);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_129 = lean_ctor_get(x_3, 1);
lean_inc(x_129);
lean_dec(x_3);
x_130 = lean_box(0);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
x_132 = l___private_init_lean_environment_5__envExtensionsRef;
x_133 = lean_io_ref_get(x_132, x_131);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_136 = x_133;
} else {
 lean_dec_ref(x_133);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_130);
lean_ctor_set(x_137, 1, x_135);
x_138 = lean_array_get_size(x_134);
lean_dec(x_134);
x_139 = lean_unsigned_to_nat(0u);
x_140 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_1);
lean_ctor_set(x_140, 2, x_139);
x_141 = lean_io_ref_get(x_132, x_137);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_144 = x_141;
} else {
 lean_dec_ref(x_141);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_130);
lean_ctor_set(x_145, 1, x_143);
x_146 = lean_io_ref_reset(x_132, x_145);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_148 = x_146;
} else {
 lean_dec_ref(x_146);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_130);
lean_ctor_set(x_149, 1, x_147);
x_150 = lean_alloc_closure((void*)(l_Lean_EnvExtension_Inhabited___rarg___lambda__1), 1, 0);
x_151 = l_Lean_EnvExtensionState_inhabited;
x_152 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_152, 0, x_139);
lean_ctor_set(x_152, 1, x_150);
lean_ctor_set(x_152, 2, x_151);
lean_inc(x_140);
x_153 = x_140;
x_154 = lean_array_push(x_142, x_153);
x_155 = lean_io_ref_set(x_132, x_154, x_149);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_157 = x_155;
} else {
 lean_dec_ref(x_155);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_140);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_140);
x_159 = lean_ctor_get(x_155, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_155, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_161 = x_155;
} else {
 lean_dec_ref(x_155);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_142);
lean_dec(x_140);
x_163 = lean_ctor_get(x_146, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_146, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_165 = x_146;
} else {
 lean_dec_ref(x_146);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_140);
x_167 = lean_ctor_get(x_141, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_141, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_169 = x_141;
} else {
 lean_dec_ref(x_141);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_1);
x_171 = lean_ctor_get(x_133, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_133, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_173 = x_133;
} else {
 lean_dec_ref(x_133);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_1);
x_175 = !lean_is_exclusive(x_3);
if (x_175 == 0)
{
return x_3;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_3, 0);
x_177 = lean_ctor_get(x_3, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_3);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
}
lean_object* lean_register_extension(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_alloc_closure((void*)(l_EState_pure___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
x_5 = l_Lean_registerEnvExtensionUnsafe___at_Lean_registerCPPExtension___spec__1(x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_box(0);
return x_9;
}
}
}
lean_object* lean_set_extension(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_4);
x_6 = l___private_init_lean_environment_5__envExtensionsRef;
x_7 = lean_io_ref_get(x_6, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_alloc_closure((void*)(l_Lean_EnvExtension_Inhabited___rarg___lambda__1), 1, 0);
x_11 = l_Lean_EnvExtensionState_inhabited;
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_array_get(x_12, x_8, x_2);
lean_dec(x_2);
lean_dec(x_8);
x_14 = l_Lean_EnvExtension_setStateUnsafe___rarg(x_13, x_1, x_3);
lean_dec(x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_box(0);
return x_16;
}
}
}
lean_object* lean_get_extension(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
x_5 = l___private_init_lean_environment_5__envExtensionsRef;
x_6 = lean_io_ref_get(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_closure((void*)(l_Lean_EnvExtension_Inhabited___rarg___lambda__1), 1, 0);
x_10 = l_Lean_EnvExtensionState_inhabited;
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
x_12 = lean_array_get(x_11, x_7, x_2);
lean_dec(x_2);
lean_dec(x_7);
x_13 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_12, x_1);
lean_dec(x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(0);
return x_15;
}
}
}
lean_object* _init_l_Lean_Modification_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_NonScalar_Inhabited;
return x_1;
}
}
lean_object* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_regModListExtension___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_regModListExtension___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_initializing(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_3, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_3, 0, x_14);
x_15 = l___private_init_lean_environment_5__envExtensionsRef;
x_16 = lean_io_ref_get(x_15, x_3);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_16, 0, x_14);
x_19 = lean_array_get_size(x_18);
lean_dec(x_18);
x_20 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regModListExtension___spec__1___closed__1;
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_1);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_io_ref_get(x_15, x_16);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_ctor_set(x_22, 0, x_14);
x_25 = lean_io_ref_reset(x_15, x_22);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_14);
x_28 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_21);
x_29 = x_21;
x_30 = lean_array_push(x_24, x_29);
x_31 = lean_io_ref_set(x_15, x_30, x_25);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_21);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_21);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
lean_dec(x_25);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_14);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_21);
x_43 = x_21;
x_44 = lean_array_push(x_24, x_43);
x_45 = lean_io_ref_set(x_15, x_44, x_41);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_21);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_21);
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_51 = x_45;
} else {
 lean_dec_ref(x_45);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_24);
lean_dec(x_21);
x_53 = !lean_is_exclusive(x_25);
if (x_53 == 0)
{
return x_25;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_25, 0);
x_55 = lean_ctor_get(x_25, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_25);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_22, 0);
x_58 = lean_ctor_get(x_22, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_22);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_14);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_io_ref_reset(x_15, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_14);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_21);
x_65 = x_21;
x_66 = lean_array_push(x_57, x_65);
x_67 = lean_io_ref_set(x_15, x_66, x_63);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_21);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_21);
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_73 = x_67;
} else {
 lean_dec_ref(x_67);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_57);
lean_dec(x_21);
x_75 = lean_ctor_get(x_60, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_60, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_77 = x_60;
} else {
 lean_dec_ref(x_60);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_21);
x_79 = !lean_is_exclusive(x_22);
if (x_79 == 0)
{
return x_22;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_22, 0);
x_81 = lean_ctor_get(x_22, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_22);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_83 = lean_ctor_get(x_16, 0);
x_84 = lean_ctor_get(x_16, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_16);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_14);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_array_get_size(x_83);
lean_dec(x_83);
x_87 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regModListExtension___spec__1___closed__1;
x_88 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_1);
lean_ctor_set(x_88, 2, x_87);
x_89 = lean_io_ref_get(x_15, x_85);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_92 = x_89;
} else {
 lean_dec_ref(x_89);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_14);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_io_ref_reset(x_15, x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_96 = x_94;
} else {
 lean_dec_ref(x_94);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_14);
lean_ctor_set(x_97, 1, x_95);
x_98 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_88);
x_99 = x_88;
x_100 = lean_array_push(x_90, x_99);
x_101 = lean_io_ref_set(x_15, x_100, x_97);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_103 = x_101;
} else {
 lean_dec_ref(x_101);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_88);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_88);
x_105 = lean_ctor_get(x_101, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_101, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_107 = x_101;
} else {
 lean_dec_ref(x_101);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_90);
lean_dec(x_88);
x_109 = lean_ctor_get(x_94, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_94, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_111 = x_94;
} else {
 lean_dec_ref(x_94);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_88);
x_113 = lean_ctor_get(x_89, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_89, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_115 = x_89;
} else {
 lean_dec_ref(x_89);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_16);
if (x_117 == 0)
{
return x_16;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_16, 0);
x_119 = lean_ctor_get(x_16, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_16);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = lean_ctor_get(x_3, 1);
lean_inc(x_121);
lean_dec(x_3);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
x_124 = l___private_init_lean_environment_5__envExtensionsRef;
x_125 = lean_io_ref_get(x_124, x_123);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_128 = x_125;
} else {
 lean_dec_ref(x_125);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_122);
lean_ctor_set(x_129, 1, x_127);
x_130 = lean_array_get_size(x_126);
lean_dec(x_126);
x_131 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regModListExtension___spec__1___closed__1;
x_132 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_1);
lean_ctor_set(x_132, 2, x_131);
x_133 = lean_io_ref_get(x_124, x_129);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_136 = x_133;
} else {
 lean_dec_ref(x_133);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_122);
lean_ctor_set(x_137, 1, x_135);
x_138 = lean_io_ref_reset(x_124, x_137);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_140 = x_138;
} else {
 lean_dec_ref(x_138);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_122);
lean_ctor_set(x_141, 1, x_139);
x_142 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_132);
x_143 = x_132;
x_144 = lean_array_push(x_134, x_143);
x_145 = lean_io_ref_set(x_124, x_144, x_141);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_147 = x_145;
} else {
 lean_dec_ref(x_145);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_132);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_132);
x_149 = lean_ctor_get(x_145, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_145, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_151 = x_145;
} else {
 lean_dec_ref(x_145);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_134);
lean_dec(x_132);
x_153 = lean_ctor_get(x_138, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_138, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_155 = x_138;
} else {
 lean_dec_ref(x_138);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_132);
x_157 = lean_ctor_get(x_133, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_133, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_159 = x_133;
} else {
 lean_dec_ref(x_133);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_1);
x_161 = lean_ctor_get(x_125, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_125, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_163 = x_125;
} else {
 lean_dec_ref(x_125);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_1);
x_165 = !lean_is_exclusive(x_3);
if (x_165 == 0)
{
return x_3;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_3, 0);
x_167 = lean_ctor_get(x_3, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_3);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
}
lean_object* _init_l_Lean_regModListExtension___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_EState_pure___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_regModListExtension(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_regModListExtension___closed__1;
x_3 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regModListExtension___spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_modListExtension___elambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_dec(x_3);
x_4 = l_String_splitAux___main___closed__1;
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_String_splitAux___main___closed__1;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
lean_object* _init_l_Lean_modListExtension___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_modListExtension___elambda__1), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_modListExtension___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_modListExtension___closed__1;
x_3 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regModListExtension___spec__1___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* lean_environment_add_modification(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = l_Lean_modListExtension;
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_6);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_array_fget(x_4, x_6);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_fset(x_4, x_6, x_10);
x_12 = lean_ctor_get(x_5, 2);
lean_inc(x_12);
x_13 = x_9;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_EnvExtensionState_inhabited;
x_16 = x_14;
x_17 = lean_array_fset(x_11, x_6, x_16);
lean_dec(x_6);
lean_ctor_set(x_1, 2, x_17);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_1, 2);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_22 = l_Lean_modListExtension;
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_array_get_size(x_20);
x_25 = lean_nat_dec_lt(x_23, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_23);
lean_dec(x_2);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_19);
lean_ctor_set(x_26, 2, x_20);
lean_ctor_set(x_26, 3, x_21);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_array_fget(x_20, x_23);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_array_fset(x_20, x_23, x_28);
x_30 = lean_ctor_get(x_22, 2);
lean_inc(x_30);
x_31 = x_27;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_EnvExtensionState_inhabited;
x_34 = x_32;
x_35 = lean_array_fset(x_29, x_23, x_34);
lean_dec(x_23);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_18);
lean_ctor_set(x_36, 1, x_19);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set(x_36, 3, x_21);
return x_36;
}
}
}
}
lean_object* l_Lean_serializeModifications___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_serialize_modifications(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_performModifications___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_perform_serialized_modifications(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_ModuleData_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_ByteArray_empty;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_ModuleData_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_ModuleData_inhabited___closed__1;
return x_1;
}
}
lean_object* l_Lean_saveModuleData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_save_module_data(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_readModuleData___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_read_module_data(x_1, x_2);
return x_3;
}
}
lean_object* l_Nat_foldAux___main___at_Lean_mkModuleData___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
x_10 = lean_nat_sub(x_3, x_4);
lean_dec(x_4);
x_11 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_12 = lean_array_get(x_11, x_2, x_10);
lean_dec(x_10);
lean_inc(x_12);
x_13 = l_Lean_PersistentEnvExtension_getState___rarg(x_12, x_1);
x_14 = lean_ctor_get(x_12, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_apply_1(x_14, x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_array_push(x_5, x_17);
x_4 = x_9;
x_5 = x_18;
goto _start;
}
else
{
lean_dec(x_4);
return x_5;
}
}
}
lean_object* l_RBNode_fold___main___at_Lean_mkModuleData___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_RBNode_fold___main___at_Lean_mkModuleData___spec__2(x_1, x_3);
x_7 = lean_array_push(x_6, x_4);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
lean_object* l_Lean_mkModuleData(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_init_lean_environment_8__persistentEnvExtensionsRef;
x_4 = lean_io_ref_get(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_box(0);
lean_ctor_set(x_4, 0, x_7);
x_8 = lean_array_get_size(x_6);
x_9 = l_Array_empty___closed__1;
lean_inc(x_8);
x_10 = l_Nat_foldAux___main___at_Lean_mkModuleData___spec__1(x_1, x_6, x_8, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
x_11 = l_Lean_modListExtension;
x_12 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_11, x_1);
x_13 = lean_serialize_modifications(x_12, x_4);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_RBNode_fold___main___at_Lean_mkModuleData___spec__2(x_9, x_19);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_10);
lean_ctor_set(x_21, 3, x_15);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_ctor_get(x_1, 3);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_RBNode_fold___main___at_Lean_mkModuleData___spec__2(x_9, x_27);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_10);
lean_ctor_set(x_29, 3, x_22);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_10);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_13);
if (x_31 == 0)
{
return x_13;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_13, 0);
x_33 = lean_ctor_get(x_13, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_13);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_35 = lean_ctor_get(x_4, 0);
x_36 = lean_ctor_get(x_4, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_4);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_array_get_size(x_35);
x_40 = l_Array_empty___closed__1;
lean_inc(x_39);
x_41 = l_Nat_foldAux___main___at_Lean_mkModuleData___spec__1(x_1, x_35, x_39, x_39, x_40);
lean_dec(x_39);
lean_dec(x_35);
x_42 = l_Lean_modListExtension;
x_43 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_42, x_1);
x_44 = lean_serialize_modifications(x_43, x_38);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_47 = x_44;
} else {
 lean_dec_ref(x_44);
 x_47 = lean_box(0);
}
x_48 = lean_ctor_get(x_1, 3);
lean_inc(x_48);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_ctor_get(x_1, 1);
lean_inc(x_50);
lean_dec(x_1);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = l_RBNode_fold___main___at_Lean_mkModuleData___spec__2(x_40, x_51);
x_53 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_53, 2, x_41);
lean_ctor_set(x_53, 3, x_45);
if (lean_is_scalar(x_47)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_47;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_46);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_41);
lean_dec(x_1);
x_55 = lean_ctor_get(x_44, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_44, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_57 = x_44;
} else {
 lean_dec_ref(x_44);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_4);
if (x_59 == 0)
{
return x_4;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_4, 0);
x_61 = lean_ctor_get(x_4, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_4);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
lean_object* l_Nat_foldAux___main___at_Lean_mkModuleData___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_foldAux___main___at_Lean_mkModuleData___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* lean_write_module(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkModuleData(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_box(0);
lean_ctor_set(x_4, 0, x_7);
x_8 = lean_save_module_data(x_2, x_6, x_4);
lean_dec(x_2);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_save_module_data(x_2, x_9, x_12);
lean_dec(x_2);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_importModulesAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = l_Lean_NameSet_contains(x_10, x_8);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_2, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_2, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_inc(x_8);
x_17 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_10, x_8, x_16);
x_18 = l_Lean_findOLean___closed__1;
x_19 = l_Lean_findLeanFile(x_8, x_18, x_3);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_ctor_set(x_19, 0, x_16);
x_22 = lean_read_module_data(x_21, x_19);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_22, 0);
lean_ctor_set(x_22, 0, x_16);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = l_Array_toList___rarg(x_25);
lean_dec(x_25);
lean_ctor_set(x_2, 0, x_17);
x_27 = l_Lean_importModulesAux___main(x_26, x_2, x_22);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_ctor_set(x_27, 0, x_16);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 1);
x_32 = lean_array_push(x_31, x_24);
lean_ctor_set(x_29, 1, x_32);
x_1 = x_9;
x_2 = x_29;
x_3 = x_27;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = lean_array_push(x_35, x_24);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_1 = x_9;
x_2 = x_37;
x_3 = x_27;
goto _start;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_27, 0);
x_40 = lean_ctor_get(x_27, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_27);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_16);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_44 = x_39;
} else {
 lean_dec_ref(x_39);
 x_44 = lean_box(0);
}
x_45 = lean_array_push(x_43, x_24);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_45);
x_1 = x_9;
x_2 = x_46;
x_3 = x_41;
goto _start;
}
}
else
{
uint8_t x_48; 
lean_dec(x_24);
lean_dec(x_9);
x_48 = !lean_is_exclusive(x_27);
if (x_48 == 0)
{
return x_27;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_27, 0);
x_50 = lean_ctor_get(x_27, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_27);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_22, 0);
x_53 = lean_ctor_get(x_22, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_22);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_16);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
x_56 = l_Array_toList___rarg(x_55);
lean_dec(x_55);
lean_ctor_set(x_2, 0, x_17);
x_57 = l_Lean_importModulesAux___main(x_56, x_2, x_54);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_16);
lean_ctor_set(x_61, 1, x_59);
x_62 = lean_ctor_get(x_58, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_58, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_64 = x_58;
} else {
 lean_dec_ref(x_58);
 x_64 = lean_box(0);
}
x_65 = lean_array_push(x_63, x_52);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_62);
lean_ctor_set(x_66, 1, x_65);
x_1 = x_9;
x_2 = x_66;
x_3 = x_61;
goto _start;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_52);
lean_dec(x_9);
x_68 = lean_ctor_get(x_57, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_57, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_70 = x_57;
} else {
 lean_dec_ref(x_57);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_17);
lean_free_object(x_2);
lean_dec(x_11);
lean_dec(x_9);
x_72 = !lean_is_exclusive(x_22);
if (x_72 == 0)
{
return x_22;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_22, 0);
x_74 = lean_ctor_get(x_22, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_22);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_19, 0);
x_77 = lean_ctor_get(x_19, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_19);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_16);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_read_module_data(x_76, x_78);
lean_dec(x_76);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_16);
lean_ctor_set(x_83, 1, x_81);
x_84 = lean_ctor_get(x_80, 0);
lean_inc(x_84);
x_85 = l_Array_toList___rarg(x_84);
lean_dec(x_84);
lean_ctor_set(x_2, 0, x_17);
x_86 = l_Lean_importModulesAux___main(x_85, x_2, x_83);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_89 = x_86;
} else {
 lean_dec_ref(x_86);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_16);
lean_ctor_set(x_90, 1, x_88);
x_91 = lean_ctor_get(x_87, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_87, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_93 = x_87;
} else {
 lean_dec_ref(x_87);
 x_93 = lean_box(0);
}
x_94 = lean_array_push(x_92, x_80);
if (lean_is_scalar(x_93)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_93;
}
lean_ctor_set(x_95, 0, x_91);
lean_ctor_set(x_95, 1, x_94);
x_1 = x_9;
x_2 = x_95;
x_3 = x_90;
goto _start;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_80);
lean_dec(x_9);
x_97 = lean_ctor_get(x_86, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_86, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_99 = x_86;
} else {
 lean_dec_ref(x_86);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_17);
lean_free_object(x_2);
lean_dec(x_11);
lean_dec(x_9);
x_101 = lean_ctor_get(x_79, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_79, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_103 = x_79;
} else {
 lean_dec_ref(x_79);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_17);
lean_free_object(x_2);
lean_dec(x_11);
lean_dec(x_9);
x_105 = !lean_is_exclusive(x_19);
if (x_105 == 0)
{
return x_19;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_19, 0);
x_107 = lean_ctor_get(x_19, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_19);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_2);
x_109 = lean_box(0);
lean_inc(x_8);
x_110 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_10, x_8, x_109);
x_111 = l_Lean_findOLean___closed__1;
x_112 = l_Lean_findLeanFile(x_8, x_111, x_3);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_115 = x_112;
} else {
 lean_dec_ref(x_112);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_109);
lean_ctor_set(x_116, 1, x_114);
x_117 = lean_read_module_data(x_113, x_116);
lean_dec(x_113);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_120 = x_117;
} else {
 lean_dec_ref(x_117);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_109);
lean_ctor_set(x_121, 1, x_119);
x_122 = lean_ctor_get(x_118, 0);
lean_inc(x_122);
x_123 = l_Array_toList___rarg(x_122);
lean_dec(x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_110);
lean_ctor_set(x_124, 1, x_11);
x_125 = l_Lean_importModulesAux___main(x_123, x_124, x_121);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_128 = x_125;
} else {
 lean_dec_ref(x_125);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_109);
lean_ctor_set(x_129, 1, x_127);
x_130 = lean_ctor_get(x_126, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_126, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_132 = x_126;
} else {
 lean_dec_ref(x_126);
 x_132 = lean_box(0);
}
x_133 = lean_array_push(x_131, x_118);
if (lean_is_scalar(x_132)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_132;
}
lean_ctor_set(x_134, 0, x_130);
lean_ctor_set(x_134, 1, x_133);
x_1 = x_9;
x_2 = x_134;
x_3 = x_129;
goto _start;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_118);
lean_dec(x_9);
x_136 = lean_ctor_get(x_125, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_125, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_138 = x_125;
} else {
 lean_dec_ref(x_125);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_110);
lean_dec(x_11);
lean_dec(x_9);
x_140 = lean_ctor_get(x_117, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_117, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_142 = x_117;
} else {
 lean_dec_ref(x_117);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_110);
lean_dec(x_11);
lean_dec(x_9);
x_144 = lean_ctor_get(x_112, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_112, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_146 = x_112;
} else {
 lean_dec_ref(x_112);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_1 = x_9;
goto _start;
}
}
}
}
lean_object* l_Lean_importModulesAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_importModulesAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l___private_init_lean_environment_9__getEntriesFor___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Inhabited;
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_init_lean_environment_9__getEntriesFor___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = l_Array_empty___closed__1;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l___private_init_lean_environment_9__getEntriesFor___main___closed__1;
x_9 = lean_array_get(x_8, x_4, x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_name_dec_eq(x_10, x_2);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
x_3 = x_13;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec(x_3);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
return x_15;
}
}
}
}
lean_object* l___private_init_lean_environment_9__getEntriesFor___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_init_lean_environment_9__getEntriesFor___main(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_init_lean_environment_9__getEntriesFor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_init_lean_environment_9__getEntriesFor___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_init_lean_environment_9__getEntriesFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_init_lean_environment_9__getEntriesFor(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_miterateAux___main___at___private_init_lean_environment_10__setImportedEntries___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_init_lean_environment_9__getEntriesFor___main(x_2, x_9, x_10);
lean_dec(x_9);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_array_get_size(x_14);
x_17 = lean_nat_dec_lt(x_15, x_16);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_4, x_18);
lean_dec(x_4);
if (x_17 == 0)
{
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
x_4 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_array_fget(x_14, x_15);
x_22 = lean_array_fset(x_14, x_15, x_10);
x_23 = lean_ctor_get(x_12, 2);
lean_inc(x_23);
lean_dec(x_12);
x_24 = x_21;
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_array_push(x_26, x_11);
lean_ctor_set(x_24, 0, x_27);
x_28 = l_Lean_EnvExtensionState_inhabited;
x_29 = x_24;
x_30 = lean_array_fset(x_22, x_15, x_29);
lean_dec(x_15);
lean_ctor_set(x_5, 2, x_30);
x_4 = x_19;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_24, 0);
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_24);
x_34 = lean_array_push(x_32, x_11);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_EnvExtensionState_inhabited;
x_37 = x_35;
x_38 = lean_array_fset(x_22, x_15, x_37);
lean_dec(x_15);
lean_ctor_set(x_5, 2, x_38);
x_4 = x_19;
goto _start;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_5, 0);
x_41 = lean_ctor_get(x_5, 1);
x_42 = lean_ctor_get(x_5, 2);
x_43 = lean_ctor_get(x_5, 3);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_5);
x_44 = lean_ctor_get(x_12, 0);
lean_inc(x_44);
x_45 = lean_array_get_size(x_42);
x_46 = lean_nat_dec_lt(x_44, x_45);
lean_dec(x_45);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_4, x_47);
lean_dec(x_4);
if (x_46 == 0)
{
lean_object* x_49; 
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_11);
x_49 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_49, 0, x_40);
lean_ctor_set(x_49, 1, x_41);
lean_ctor_set(x_49, 2, x_42);
lean_ctor_set(x_49, 3, x_43);
x_4 = x_48;
x_5 = x_49;
goto _start;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_51 = lean_array_fget(x_42, x_44);
x_52 = lean_array_fset(x_42, x_44, x_10);
x_53 = lean_ctor_get(x_12, 2);
lean_inc(x_53);
lean_dec(x_12);
x_54 = x_51;
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
x_58 = lean_array_push(x_55, x_11);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
x_60 = l_Lean_EnvExtensionState_inhabited;
x_61 = x_59;
x_62 = lean_array_fset(x_52, x_44, x_61);
lean_dec(x_44);
x_63 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_63, 0, x_40);
lean_ctor_set(x_63, 1, x_41);
lean_ctor_set(x_63, 2, x_62);
lean_ctor_set(x_63, 3, x_43);
x_4 = x_48;
x_5 = x_63;
goto _start;
}
}
}
}
}
lean_object* l_Array_miterateAux___main___at___private_init_lean_environment_10__setImportedEntries___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_miterateAux___main___at___private_init_lean_environment_10__setImportedEntries___spec__1(x_2, x_8, x_2, x_9, x_5);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_4 = x_12;
x_5 = x_10;
goto _start;
}
}
}
lean_object* l___private_init_lean_environment_10__setImportedEntries(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_init_lean_environment_8__persistentEnvExtensionsRef;
x_5 = lean_io_ref_get(x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_miterateAux___main___at___private_init_lean_environment_10__setImportedEntries___spec__2(x_2, x_7, x_2, x_8, x_1);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_miterateAux___main___at___private_init_lean_environment_10__setImportedEntries___spec__2(x_2, x_10, x_2, x_12, x_1);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Array_miterateAux___main___at___private_init_lean_environment_10__setImportedEntries___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_miterateAux___main___at___private_init_lean_environment_10__setImportedEntries___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_miterateAux___main___at___private_init_lean_environment_10__setImportedEntries___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_miterateAux___main___at___private_init_lean_environment_10__setImportedEntries___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_init_lean_environment_10__setImportedEntries___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_init_lean_environment_10__setImportedEntries(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_miterateAux___main___at___private_init_lean_environment_11__finalizePersistentExtensions___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_array_fget(x_2, x_3);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
lean_dec(x_3);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_inc(x_15);
x_16 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_15, x_4);
x_17 = lean_ctor_get(x_12, 2);
lean_inc(x_17);
lean_dec(x_12);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
lean_dec(x_20);
lean_inc(x_19);
x_21 = lean_apply_2(x_17, x_19, x_5);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_16, 1, x_23);
x_24 = l_Lean_EnvExtension_setStateUnsafe___rarg(x_15, x_4, x_16);
lean_dec(x_15);
x_25 = lean_box(0);
lean_ctor_set(x_21, 0, x_25);
x_3 = x_14;
x_4 = x_24;
x_5 = x_21;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
lean_ctor_set(x_16, 1, x_27);
x_29 = l_Lean_EnvExtension_setStateUnsafe___rarg(x_15, x_4, x_16);
lean_dec(x_15);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
x_3 = x_14;
x_4 = x_29;
x_5 = x_31;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_16);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_21);
if (x_33 == 0)
{
return x_21;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_21, 0);
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_21);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_16, 0);
lean_inc(x_37);
lean_dec(x_16);
lean_inc(x_37);
x_38 = lean_apply_2(x_17, x_37, x_5);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_39);
x_43 = l_Lean_EnvExtension_setStateUnsafe___rarg(x_15, x_4, x_42);
lean_dec(x_15);
x_44 = lean_box(0);
if (lean_is_scalar(x_41)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_41;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
x_3 = x_14;
x_4 = x_43;
x_5 = x_45;
goto _start;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_37);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_4);
x_47 = lean_ctor_get(x_38, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_38, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_49 = x_38;
} else {
 lean_dec_ref(x_38);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
}
}
lean_object* l___private_init_lean_environment_11__finalizePersistentExtensions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_init_lean_environment_8__persistentEnvExtensionsRef;
x_4 = lean_io_ref_get(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_box(0);
lean_ctor_set(x_4, 0, x_7);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_miterateAux___main___at___private_init_lean_environment_11__finalizePersistentExtensions___spec__1(x_6, x_6, x_8, x_1, x_4);
lean_dec(x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Array_miterateAux___main___at___private_init_lean_environment_11__finalizePersistentExtensions___spec__1(x_10, x_10, x_14, x_1, x_13);
lean_dec(x_10);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
return x_4;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Array_miterateAux___main___at___private_init_lean_environment_11__finalizePersistentExtensions___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_miterateAux___main___at___private_init_lean_environment_11__finalizePersistentExtensions___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
uint8_t l_AssocList_contains___main___at_Lean_importModules___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_name_dec_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
lean_object* l_AssocList_mfoldl___main___at_Lean_importModules___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; size_t x_10; lean_object* x_11; size_t x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_name_hash_usize(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_box_usize(x_8);
x_10 = lean_unbox_usize(x_9);
x_11 = lean_array_uget(x_1, x_10);
lean_ctor_set(x_2, 2, x_11);
x_12 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_13 = lean_array_uset(x_1, x_12, x_2);
x_1 = x_13;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; size_t x_22; lean_object* x_23; lean_object* x_24; size_t x_25; lean_object* x_26; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_ctor_get(x_2, 2);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_2);
x_18 = lean_array_get_size(x_1);
x_19 = lean_name_hash_usize(x_15);
x_20 = lean_usize_modn(x_19, x_18);
lean_dec(x_18);
x_21 = lean_box_usize(x_20);
x_22 = lean_unbox_usize(x_21);
x_23 = lean_array_uget(x_1, x_22);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_unbox_usize(x_21);
lean_dec(x_21);
x_26 = lean_array_uset(x_1, x_25, x_24);
x_1 = x_26;
x_2 = x_17;
goto _start;
}
}
}
}
lean_object* l_HashMapImp_moveEntries___main___at_Lean_importModules___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_AssocList_mfoldl___main___at_Lean_importModules___spec__5(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
lean_object* l_HashMapImp_expand___at_Lean_importModules___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_HashMapImp_moveEntries___main___at_Lean_importModules___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_importModules___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_name_dec_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_AssocList_replace___main___at_Lean_importModules___spec__6(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_name_dec_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_AssocList_replace___main___at_Lean_importModules___spec__6(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
lean_object* l_HashMapImp_insert___at_Lean_importModules___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; size_t x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_name_hash_usize(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_box_usize(x_9);
x_11 = lean_unbox_usize(x_10);
x_12 = lean_array_uget(x_6, x_11);
x_13 = l_AssocList_contains___main___at_Lean_importModules___spec__2(x_2, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_5, x_14);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_3);
lean_ctor_set(x_16, 2, x_12);
x_17 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_18 = lean_array_uset(x_6, x_17, x_16);
x_19 = lean_nat_dec_le(x_15, x_7);
lean_dec(x_7);
if (x_19 == 0)
{
lean_object* x_20; 
lean_free_object(x_1);
x_20 = l_HashMapImp_expand___at_Lean_importModules___spec__3(x_15, x_18);
return x_20;
}
else
{
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
}
else
{
lean_object* x_21; size_t x_22; lean_object* x_23; 
lean_dec(x_7);
x_21 = l_AssocList_replace___main___at_Lean_importModules___spec__6(x_2, x_3, x_12);
x_22 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_23 = lean_array_uset(x_6, x_22, x_21);
lean_ctor_set(x_1, 1, x_23);
return x_1;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; size_t x_30; lean_object* x_31; uint8_t x_32; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_1);
x_26 = lean_array_get_size(x_25);
x_27 = lean_name_hash_usize(x_2);
x_28 = lean_usize_modn(x_27, x_26);
x_29 = lean_box_usize(x_28);
x_30 = lean_unbox_usize(x_29);
x_31 = lean_array_uget(x_25, x_30);
x_32 = l_AssocList_contains___main___at_Lean_importModules___spec__2(x_2, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_24, x_33);
lean_dec(x_24);
x_35 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set(x_35, 1, x_3);
lean_ctor_set(x_35, 2, x_31);
x_36 = lean_unbox_usize(x_29);
lean_dec(x_29);
x_37 = lean_array_uset(x_25, x_36, x_35);
x_38 = lean_nat_dec_le(x_34, x_26);
lean_dec(x_26);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = l_HashMapImp_expand___at_Lean_importModules___spec__3(x_34, x_37);
return x_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
lean_object* x_41; size_t x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_26);
x_41 = l_AssocList_replace___main___at_Lean_importModules___spec__6(x_2, x_3, x_31);
x_42 = lean_unbox_usize(x_29);
lean_dec(x_29);
x_43 = lean_array_uset(x_25, x_42, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_24);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
lean_object* l_Array_miterateAux___main___at_Lean_importModules___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_6, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_6);
lean_dec(x_3);
return x_7;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_fget(x_5, x_6);
x_11 = l_Lean_ConstantInfo_name(x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_6, x_12);
lean_dec(x_6);
lean_inc(x_3);
x_14 = l_HashMapImp_insert___at_Lean_importModules___spec__1(x_7, x_11, x_3);
x_6 = x_13;
x_7 = x_14;
goto _start;
}
}
}
lean_object* l_Array_miterateAux___main___at_Lean_importModules___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_11 = l_Array_miterateAux___main___at_Lean_importModules___spec__7(x_1, x_2, x_4, x_8, x_9, x_10, x_5);
lean_dec(x_9);
lean_dec(x_8);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_4 = x_13;
x_5 = x_11;
goto _start;
}
}
}
lean_object* _init_l_Array_miterateAux___main___at_Lean_importModules___spec__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("import failed, environment already contains '");
return x_1;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_importModules___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_lt(x_4, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_4);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_array_fget(x_3, x_4);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_4, x_14);
lean_dec(x_4);
x_16 = l_Lean_ConstantInfo_name(x_13);
x_17 = l_Lean_SMap_contains___at_Lean_Environment_contains___spec__1(x_5, x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_6, 0);
lean_dec(x_19);
x_20 = l_Lean_SMap_insert___at_Lean_Environment_addAux___spec__1(x_5, x_16, x_13);
x_21 = lean_box(0);
lean_ctor_set(x_6, 0, x_21);
x_4 = x_15;
x_5 = x_20;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
lean_dec(x_6);
x_24 = l_Lean_SMap_insert___at_Lean_Environment_addAux___spec__1(x_5, x_16, x_13);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
x_4 = x_15;
x_5 = x_24;
x_6 = x_26;
goto _start;
}
}
else
{
uint8_t x_28; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_6);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_6, 0);
lean_dec(x_29);
x_30 = l_Lean_Name_toString___closed__1;
x_31 = l_Lean_Name_toStringWithSep___main(x_30, x_16);
x_32 = l_Array_miterateAux___main___at_Lean_importModules___spec__9___closed__1;
x_33 = lean_string_append(x_32, x_31);
lean_dec(x_31);
x_34 = l_Char_HasRepr___closed__1;
x_35 = lean_string_append(x_33, x_34);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_35);
return x_6;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_6, 1);
lean_inc(x_36);
lean_dec(x_6);
x_37 = l_Lean_Name_toString___closed__1;
x_38 = l_Lean_Name_toStringWithSep___main(x_37, x_16);
x_39 = l_Array_miterateAux___main___at_Lean_importModules___spec__9___closed__1;
x_40 = lean_string_append(x_39, x_38);
lean_dec(x_38);
x_41 = l_Char_HasRepr___closed__1;
x_42 = lean_string_append(x_40, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_36);
return x_43;
}
}
}
}
}
lean_object* l_Array_miterateAux___main___at_Lean_importModules___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_lt(x_4, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_4);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_array_fget(x_3, x_4);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_4, x_14);
lean_dec(x_4);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_miterateAux___main___at_Lean_importModules___spec__9(x_2, x_13, x_16, x_17, x_5, x_6);
lean_dec(x_16);
lean_dec(x_13);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
x_4 = x_15;
x_5 = x_20;
x_6 = x_18;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_4 = x_15;
x_5 = x_23;
x_6 = x_26;
goto _start;
}
}
else
{
uint8_t x_28; 
lean_dec(x_15);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
lean_object* l_Lean_SMap_switch___at_Lean_importModules___spec__11(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_2 == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = 0;
x_8 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_7);
return x_8;
}
}
}
}
lean_object* l_Array_miterateAux___main___at_Lean_importModules___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_fget(x_2, x_3);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
lean_dec(x_3);
x_15 = lean_ctor_get(x_12, 3);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_perform_serialized_modifications(x_4, x_15, x_5);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
x_3 = x_14;
x_4 = x_18;
x_5 = x_16;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_3 = x_14;
x_4 = x_21;
x_5 = x_24;
goto _start;
}
}
else
{
uint8_t x_26; 
lean_dec(x_14);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* l_Array_miterateAux___main___at_Lean_importModules___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_fget(x_2, x_3);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
lean_dec(x_3);
x_15 = lean_ctor_get(x_12, 3);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_perform_serialized_modifications(x_4, x_15, x_5);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
x_3 = x_14;
x_4 = x_18;
x_5 = x_16;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_3 = x_14;
x_4 = x_21;
x_5 = x_24;
goto _start;
}
}
else
{
uint8_t x_26; 
lean_dec(x_14);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* _init_l_Lean_importModules___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* lean_import_modules(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_importModules___closed__1;
lean_inc(x_1);
x_5 = l_Lean_importModulesAux___main(x_1, x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_box(0);
lean_ctor_set(x_5, 0, x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__1;
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_HashMap_Inhabited___closed__1;
x_13 = l_Array_miterateAux___main___at_Lean_importModules___spec__8(x_9, x_10, x_9, x_11, x_12);
x_14 = l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2;
x_15 = l_Array_miterateAux___main___at_Lean_importModules___spec__10(x_9, x_10, x_9, x_11, x_14, x_5);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_15, 0, x_8);
x_18 = l_Lean_SMap_switch___at_Lean_importModules___spec__11(x_17);
x_19 = l___private_init_lean_environment_6__mkInitialExtensionStates(x_15);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_19, 0);
lean_ctor_set(x_19, 0, x_8);
x_22 = l_List_isEmpty___rarg(x_1);
x_23 = l_List_redLength___main___rarg(x_1);
x_24 = lean_mk_empty_array_with_capacity(x_23);
lean_dec(x_23);
x_25 = l_List_toArrayAux___main___rarg(x_1, x_24);
if (x_22 == 0)
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = 1;
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set_uint32(x_28, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_28, sizeof(void*)*2 + 4, x_26);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_13);
lean_ctor_set(x_29, 1, x_18);
lean_ctor_set(x_29, 2, x_21);
lean_ctor_set(x_29, 3, x_28);
x_30 = l___private_init_lean_environment_10__setImportedEntries(x_29, x_9, x_19);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_ctor_set(x_30, 0, x_8);
x_33 = l___private_init_lean_environment_11__finalizePersistentExtensions(x_32, x_30);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_ctor_set(x_33, 0, x_8);
x_36 = l_Array_miterateAux___main___at_Lean_importModules___spec__12(x_9, x_9, x_11, x_35, x_33);
lean_dec(x_9);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
return x_36;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_36, 0);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_36);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_33, 0);
x_46 = lean_ctor_get(x_33, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_33);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_8);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Array_miterateAux___main___at_Lean_importModules___spec__12(x_9, x_9, x_11, x_45, x_47);
lean_dec(x_9);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_48, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_55 = x_48;
} else {
 lean_dec_ref(x_48);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_9);
x_57 = !lean_is_exclusive(x_33);
if (x_57 == 0)
{
return x_33;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_33, 0);
x_59 = lean_ctor_get(x_33, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_33);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_30, 0);
x_62 = lean_ctor_get(x_30, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_30);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_8);
lean_ctor_set(x_63, 1, x_62);
x_64 = l___private_init_lean_environment_11__finalizePersistentExtensions(x_61, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_8);
lean_ctor_set(x_68, 1, x_66);
x_69 = l_Array_miterateAux___main___at_Lean_importModules___spec__12(x_9, x_9, x_11, x_65, x_68);
lean_dec(x_9);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_69, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_76 = x_69;
} else {
 lean_dec_ref(x_69);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_9);
x_78 = lean_ctor_get(x_64, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_64, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_80 = x_64;
} else {
 lean_dec_ref(x_64);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_9);
x_82 = !lean_is_exclusive(x_30);
if (x_82 == 0)
{
return x_30;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_30, 0);
x_84 = lean_ctor_get(x_30, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_30);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = 0;
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_25);
lean_ctor_set_uint32(x_88, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_88, sizeof(void*)*2 + 4, x_86);
x_89 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_89, 0, x_13);
lean_ctor_set(x_89, 1, x_18);
lean_ctor_set(x_89, 2, x_21);
lean_ctor_set(x_89, 3, x_88);
x_90 = l___private_init_lean_environment_10__setImportedEntries(x_89, x_9, x_19);
if (lean_obj_tag(x_90) == 0)
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_90, 0);
lean_ctor_set(x_90, 0, x_8);
x_93 = l___private_init_lean_environment_11__finalizePersistentExtensions(x_92, x_90);
if (lean_obj_tag(x_93) == 0)
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_93, 0);
lean_ctor_set(x_93, 0, x_8);
x_96 = l_Array_miterateAux___main___at_Lean_importModules___spec__13(x_9, x_9, x_11, x_95, x_93);
lean_dec(x_9);
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
return x_96;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_96);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
else
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_96);
if (x_101 == 0)
{
return x_96;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_96, 0);
x_103 = lean_ctor_get(x_96, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_96);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_93, 0);
x_106 = lean_ctor_get(x_93, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_93);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_8);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Array_miterateAux___main___at_Lean_importModules___spec__13(x_9, x_9, x_11, x_105, x_107);
lean_dec(x_9);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_111 = x_108;
} else {
 lean_dec_ref(x_108);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_108, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_108, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_115 = x_108;
} else {
 lean_dec_ref(x_108);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_9);
x_117 = !lean_is_exclusive(x_93);
if (x_117 == 0)
{
return x_93;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_93, 0);
x_119 = lean_ctor_get(x_93, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_93);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_90, 0);
x_122 = lean_ctor_get(x_90, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_90);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_8);
lean_ctor_set(x_123, 1, x_122);
x_124 = l___private_init_lean_environment_11__finalizePersistentExtensions(x_121, x_123);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_127 = x_124;
} else {
 lean_dec_ref(x_124);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_8);
lean_ctor_set(x_128, 1, x_126);
x_129 = l_Array_miterateAux___main___at_Lean_importModules___spec__13(x_9, x_9, x_11, x_125, x_128);
lean_dec(x_9);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_132 = x_129;
} else {
 lean_dec_ref(x_129);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_134 = lean_ctor_get(x_129, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_129, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_136 = x_129;
} else {
 lean_dec_ref(x_129);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_9);
x_138 = lean_ctor_get(x_124, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_124, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_140 = x_124;
} else {
 lean_dec_ref(x_124);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
}
else
{
uint8_t x_142; 
lean_dec(x_9);
x_142 = !lean_is_exclusive(x_90);
if (x_142 == 0)
{
return x_90;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_90, 0);
x_144 = lean_ctor_get(x_90, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_90);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_146 = lean_ctor_get(x_19, 0);
x_147 = lean_ctor_get(x_19, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_19);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_8);
lean_ctor_set(x_148, 1, x_147);
x_149 = l_List_isEmpty___rarg(x_1);
x_150 = l_List_redLength___main___rarg(x_1);
x_151 = lean_mk_empty_array_with_capacity(x_150);
lean_dec(x_150);
x_152 = l_List_toArrayAux___main___rarg(x_1, x_151);
if (x_149 == 0)
{
uint8_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_153 = 1;
x_154 = lean_box(0);
x_155 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_152);
lean_ctor_set_uint32(x_155, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_155, sizeof(void*)*2 + 4, x_153);
x_156 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_156, 0, x_13);
lean_ctor_set(x_156, 1, x_18);
lean_ctor_set(x_156, 2, x_146);
lean_ctor_set(x_156, 3, x_155);
x_157 = l___private_init_lean_environment_10__setImportedEntries(x_156, x_9, x_148);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_160 = x_157;
} else {
 lean_dec_ref(x_157);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_8);
lean_ctor_set(x_161, 1, x_159);
x_162 = l___private_init_lean_environment_11__finalizePersistentExtensions(x_158, x_161);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_165 = x_162;
} else {
 lean_dec_ref(x_162);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_8);
lean_ctor_set(x_166, 1, x_164);
x_167 = l_Array_miterateAux___main___at_Lean_importModules___spec__12(x_9, x_9, x_11, x_163, x_166);
lean_dec(x_9);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_170 = x_167;
} else {
 lean_dec_ref(x_167);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = lean_ctor_get(x_167, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_167, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_174 = x_167;
} else {
 lean_dec_ref(x_167);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_173);
return x_175;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_9);
x_176 = lean_ctor_get(x_162, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_162, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_178 = x_162;
} else {
 lean_dec_ref(x_162);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_177);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_9);
x_180 = lean_ctor_get(x_157, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_157, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_182 = x_157;
} else {
 lean_dec_ref(x_157);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
else
{
uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_184 = 0;
x_185 = lean_box(0);
x_186 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_152);
lean_ctor_set_uint32(x_186, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_186, sizeof(void*)*2 + 4, x_184);
x_187 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_187, 0, x_13);
lean_ctor_set(x_187, 1, x_18);
lean_ctor_set(x_187, 2, x_146);
lean_ctor_set(x_187, 3, x_186);
x_188 = l___private_init_lean_environment_10__setImportedEntries(x_187, x_9, x_148);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_191 = x_188;
} else {
 lean_dec_ref(x_188);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_8);
lean_ctor_set(x_192, 1, x_190);
x_193 = l___private_init_lean_environment_11__finalizePersistentExtensions(x_189, x_192);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_196 = x_193;
} else {
 lean_dec_ref(x_193);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_8);
lean_ctor_set(x_197, 1, x_195);
x_198 = l_Array_miterateAux___main___at_Lean_importModules___spec__13(x_9, x_9, x_11, x_194, x_197);
lean_dec(x_9);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_201 = x_198;
} else {
 lean_dec_ref(x_198);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
return x_202;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_203 = lean_ctor_get(x_198, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_198, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_205 = x_198;
} else {
 lean_dec_ref(x_198);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(1, 2, 0);
} else {
 x_206 = x_205;
}
lean_ctor_set(x_206, 0, x_203);
lean_ctor_set(x_206, 1, x_204);
return x_206;
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_9);
x_207 = lean_ctor_get(x_193, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_193, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_209 = x_193;
} else {
 lean_dec_ref(x_193);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_9);
x_211 = lean_ctor_get(x_188, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_188, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_213 = x_188;
} else {
 lean_dec_ref(x_188);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_212);
return x_214;
}
}
}
}
else
{
uint8_t x_215; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_1);
x_215 = !lean_is_exclusive(x_19);
if (x_215 == 0)
{
return x_19;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_19, 0);
x_217 = lean_ctor_get(x_19, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_19);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_219 = lean_ctor_get(x_15, 0);
x_220 = lean_ctor_get(x_15, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_15);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_8);
lean_ctor_set(x_221, 1, x_220);
x_222 = l_Lean_SMap_switch___at_Lean_importModules___spec__11(x_219);
x_223 = l___private_init_lean_environment_6__mkInitialExtensionStates(x_221);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_226 = x_223;
} else {
 lean_dec_ref(x_223);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_8);
lean_ctor_set(x_227, 1, x_225);
x_228 = l_List_isEmpty___rarg(x_1);
x_229 = l_List_redLength___main___rarg(x_1);
x_230 = lean_mk_empty_array_with_capacity(x_229);
lean_dec(x_229);
x_231 = l_List_toArrayAux___main___rarg(x_1, x_230);
if (x_228 == 0)
{
uint8_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_232 = 1;
x_233 = lean_box(0);
x_234 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_231);
lean_ctor_set_uint32(x_234, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_234, sizeof(void*)*2 + 4, x_232);
x_235 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_235, 0, x_13);
lean_ctor_set(x_235, 1, x_222);
lean_ctor_set(x_235, 2, x_224);
lean_ctor_set(x_235, 3, x_234);
x_236 = l___private_init_lean_environment_10__setImportedEntries(x_235, x_9, x_227);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_239 = x_236;
} else {
 lean_dec_ref(x_236);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_8);
lean_ctor_set(x_240, 1, x_238);
x_241 = l___private_init_lean_environment_11__finalizePersistentExtensions(x_237, x_240);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_244 = x_241;
} else {
 lean_dec_ref(x_241);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_8);
lean_ctor_set(x_245, 1, x_243);
x_246 = l_Array_miterateAux___main___at_Lean_importModules___spec__12(x_9, x_9, x_11, x_242, x_245);
lean_dec(x_9);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_249 = x_246;
} else {
 lean_dec_ref(x_246);
 x_249 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_250 = x_249;
}
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_248);
return x_250;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_251 = lean_ctor_get(x_246, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_246, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_253 = x_246;
} else {
 lean_dec_ref(x_246);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(1, 2, 0);
} else {
 x_254 = x_253;
}
lean_ctor_set(x_254, 0, x_251);
lean_ctor_set(x_254, 1, x_252);
return x_254;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_9);
x_255 = lean_ctor_get(x_241, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_241, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_257 = x_241;
} else {
 lean_dec_ref(x_241);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(1, 2, 0);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_255);
lean_ctor_set(x_258, 1, x_256);
return x_258;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_9);
x_259 = lean_ctor_get(x_236, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_236, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_261 = x_236;
} else {
 lean_dec_ref(x_236);
 x_261 = lean_box(0);
}
if (lean_is_scalar(x_261)) {
 x_262 = lean_alloc_ctor(1, 2, 0);
} else {
 x_262 = x_261;
}
lean_ctor_set(x_262, 0, x_259);
lean_ctor_set(x_262, 1, x_260);
return x_262;
}
}
else
{
uint8_t x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_263 = 0;
x_264 = lean_box(0);
x_265 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_231);
lean_ctor_set_uint32(x_265, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_265, sizeof(void*)*2 + 4, x_263);
x_266 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_266, 0, x_13);
lean_ctor_set(x_266, 1, x_222);
lean_ctor_set(x_266, 2, x_224);
lean_ctor_set(x_266, 3, x_265);
x_267 = l___private_init_lean_environment_10__setImportedEntries(x_266, x_9, x_227);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_270 = x_267;
} else {
 lean_dec_ref(x_267);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(0, 2, 0);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_8);
lean_ctor_set(x_271, 1, x_269);
x_272 = l___private_init_lean_environment_11__finalizePersistentExtensions(x_268, x_271);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_275 = x_272;
} else {
 lean_dec_ref(x_272);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_8);
lean_ctor_set(x_276, 1, x_274);
x_277 = l_Array_miterateAux___main___at_Lean_importModules___spec__13(x_9, x_9, x_11, x_273, x_276);
lean_dec(x_9);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_280 = x_277;
} else {
 lean_dec_ref(x_277);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_281 = lean_alloc_ctor(0, 2, 0);
} else {
 x_281 = x_280;
}
lean_ctor_set(x_281, 0, x_278);
lean_ctor_set(x_281, 1, x_279);
return x_281;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_282 = lean_ctor_get(x_277, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_277, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_284 = x_277;
} else {
 lean_dec_ref(x_277);
 x_284 = lean_box(0);
}
if (lean_is_scalar(x_284)) {
 x_285 = lean_alloc_ctor(1, 2, 0);
} else {
 x_285 = x_284;
}
lean_ctor_set(x_285, 0, x_282);
lean_ctor_set(x_285, 1, x_283);
return x_285;
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_9);
x_286 = lean_ctor_get(x_272, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_272, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_288 = x_272;
} else {
 lean_dec_ref(x_272);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(1, 2, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_286);
lean_ctor_set(x_289, 1, x_287);
return x_289;
}
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_9);
x_290 = lean_ctor_get(x_267, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_267, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_292 = x_267;
} else {
 lean_dec_ref(x_267);
 x_292 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(1, 2, 0);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_291);
return x_293;
}
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_222);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_1);
x_294 = lean_ctor_get(x_223, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_223, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_296 = x_223;
} else {
 lean_dec_ref(x_223);
 x_296 = lean_box(0);
}
if (lean_is_scalar(x_296)) {
 x_297 = lean_alloc_ctor(1, 2, 0);
} else {
 x_297 = x_296;
}
lean_ctor_set(x_297, 0, x_294);
lean_ctor_set(x_297, 1, x_295);
return x_297;
}
}
}
else
{
uint8_t x_298; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_1);
x_298 = !lean_is_exclusive(x_15);
if (x_298 == 0)
{
return x_15;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_ctor_get(x_15, 0);
x_300 = lean_ctor_get(x_15, 1);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_15);
x_301 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
return x_301;
}
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_302 = lean_ctor_get(x_5, 0);
x_303 = lean_ctor_get(x_5, 1);
lean_inc(x_303);
lean_inc(x_302);
lean_dec(x_5);
x_304 = lean_box(0);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_303);
x_306 = lean_ctor_get(x_302, 1);
lean_inc(x_306);
lean_dec(x_302);
x_307 = l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__1;
x_308 = lean_unsigned_to_nat(0u);
x_309 = l_HashMap_Inhabited___closed__1;
x_310 = l_Array_miterateAux___main___at_Lean_importModules___spec__8(x_306, x_307, x_306, x_308, x_309);
x_311 = l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2;
x_312 = l_Array_miterateAux___main___at_Lean_importModules___spec__10(x_306, x_307, x_306, x_308, x_311, x_305);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_312, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_315 = x_312;
} else {
 lean_dec_ref(x_312);
 x_315 = lean_box(0);
}
if (lean_is_scalar(x_315)) {
 x_316 = lean_alloc_ctor(0, 2, 0);
} else {
 x_316 = x_315;
}
lean_ctor_set(x_316, 0, x_304);
lean_ctor_set(x_316, 1, x_314);
x_317 = l_Lean_SMap_switch___at_Lean_importModules___spec__11(x_313);
x_318 = l___private_init_lean_environment_6__mkInitialExtensionStates(x_316);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 x_321 = x_318;
} else {
 lean_dec_ref(x_318);
 x_321 = lean_box(0);
}
if (lean_is_scalar(x_321)) {
 x_322 = lean_alloc_ctor(0, 2, 0);
} else {
 x_322 = x_321;
}
lean_ctor_set(x_322, 0, x_304);
lean_ctor_set(x_322, 1, x_320);
x_323 = l_List_isEmpty___rarg(x_1);
x_324 = l_List_redLength___main___rarg(x_1);
x_325 = lean_mk_empty_array_with_capacity(x_324);
lean_dec(x_324);
x_326 = l_List_toArrayAux___main___rarg(x_1, x_325);
if (x_323 == 0)
{
uint8_t x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_327 = 1;
x_328 = lean_box(0);
x_329 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_326);
lean_ctor_set_uint32(x_329, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_329, sizeof(void*)*2 + 4, x_327);
x_330 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_330, 0, x_310);
lean_ctor_set(x_330, 1, x_317);
lean_ctor_set(x_330, 2, x_319);
lean_ctor_set(x_330, 3, x_329);
x_331 = l___private_init_lean_environment_10__setImportedEntries(x_330, x_306, x_322);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_334 = x_331;
} else {
 lean_dec_ref(x_331);
 x_334 = lean_box(0);
}
if (lean_is_scalar(x_334)) {
 x_335 = lean_alloc_ctor(0, 2, 0);
} else {
 x_335 = x_334;
}
lean_ctor_set(x_335, 0, x_304);
lean_ctor_set(x_335, 1, x_333);
x_336 = l___private_init_lean_environment_11__finalizePersistentExtensions(x_332, x_335);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 x_339 = x_336;
} else {
 lean_dec_ref(x_336);
 x_339 = lean_box(0);
}
if (lean_is_scalar(x_339)) {
 x_340 = lean_alloc_ctor(0, 2, 0);
} else {
 x_340 = x_339;
}
lean_ctor_set(x_340, 0, x_304);
lean_ctor_set(x_340, 1, x_338);
x_341 = l_Array_miterateAux___main___at_Lean_importModules___spec__12(x_306, x_306, x_308, x_337, x_340);
lean_dec(x_306);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_341, 1);
lean_inc(x_343);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 x_344 = x_341;
} else {
 lean_dec_ref(x_341);
 x_344 = lean_box(0);
}
if (lean_is_scalar(x_344)) {
 x_345 = lean_alloc_ctor(0, 2, 0);
} else {
 x_345 = x_344;
}
lean_ctor_set(x_345, 0, x_342);
lean_ctor_set(x_345, 1, x_343);
return x_345;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_346 = lean_ctor_get(x_341, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_341, 1);
lean_inc(x_347);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 x_348 = x_341;
} else {
 lean_dec_ref(x_341);
 x_348 = lean_box(0);
}
if (lean_is_scalar(x_348)) {
 x_349 = lean_alloc_ctor(1, 2, 0);
} else {
 x_349 = x_348;
}
lean_ctor_set(x_349, 0, x_346);
lean_ctor_set(x_349, 1, x_347);
return x_349;
}
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_306);
x_350 = lean_ctor_get(x_336, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_336, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 x_352 = x_336;
} else {
 lean_dec_ref(x_336);
 x_352 = lean_box(0);
}
if (lean_is_scalar(x_352)) {
 x_353 = lean_alloc_ctor(1, 2, 0);
} else {
 x_353 = x_352;
}
lean_ctor_set(x_353, 0, x_350);
lean_ctor_set(x_353, 1, x_351);
return x_353;
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_dec(x_306);
x_354 = lean_ctor_get(x_331, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_331, 1);
lean_inc(x_355);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_356 = x_331;
} else {
 lean_dec_ref(x_331);
 x_356 = lean_box(0);
}
if (lean_is_scalar(x_356)) {
 x_357 = lean_alloc_ctor(1, 2, 0);
} else {
 x_357 = x_356;
}
lean_ctor_set(x_357, 0, x_354);
lean_ctor_set(x_357, 1, x_355);
return x_357;
}
}
else
{
uint8_t x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_358 = 0;
x_359 = lean_box(0);
x_360 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_326);
lean_ctor_set_uint32(x_360, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_360, sizeof(void*)*2 + 4, x_358);
x_361 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_361, 0, x_310);
lean_ctor_set(x_361, 1, x_317);
lean_ctor_set(x_361, 2, x_319);
lean_ctor_set(x_361, 3, x_360);
x_362 = l___private_init_lean_environment_10__setImportedEntries(x_361, x_306, x_322);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_362, 1);
lean_inc(x_364);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 lean_ctor_release(x_362, 1);
 x_365 = x_362;
} else {
 lean_dec_ref(x_362);
 x_365 = lean_box(0);
}
if (lean_is_scalar(x_365)) {
 x_366 = lean_alloc_ctor(0, 2, 0);
} else {
 x_366 = x_365;
}
lean_ctor_set(x_366, 0, x_304);
lean_ctor_set(x_366, 1, x_364);
x_367 = l___private_init_lean_environment_11__finalizePersistentExtensions(x_363, x_366);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_370 = x_367;
} else {
 lean_dec_ref(x_367);
 x_370 = lean_box(0);
}
if (lean_is_scalar(x_370)) {
 x_371 = lean_alloc_ctor(0, 2, 0);
} else {
 x_371 = x_370;
}
lean_ctor_set(x_371, 0, x_304);
lean_ctor_set(x_371, 1, x_369);
x_372 = l_Array_miterateAux___main___at_Lean_importModules___spec__13(x_306, x_306, x_308, x_368, x_371);
lean_dec(x_306);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_372, 1);
lean_inc(x_374);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 x_375 = x_372;
} else {
 lean_dec_ref(x_372);
 x_375 = lean_box(0);
}
if (lean_is_scalar(x_375)) {
 x_376 = lean_alloc_ctor(0, 2, 0);
} else {
 x_376 = x_375;
}
lean_ctor_set(x_376, 0, x_373);
lean_ctor_set(x_376, 1, x_374);
return x_376;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_377 = lean_ctor_get(x_372, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_372, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 x_379 = x_372;
} else {
 lean_dec_ref(x_372);
 x_379 = lean_box(0);
}
if (lean_is_scalar(x_379)) {
 x_380 = lean_alloc_ctor(1, 2, 0);
} else {
 x_380 = x_379;
}
lean_ctor_set(x_380, 0, x_377);
lean_ctor_set(x_380, 1, x_378);
return x_380;
}
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_dec(x_306);
x_381 = lean_ctor_get(x_367, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_367, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_383 = x_367;
} else {
 lean_dec_ref(x_367);
 x_383 = lean_box(0);
}
if (lean_is_scalar(x_383)) {
 x_384 = lean_alloc_ctor(1, 2, 0);
} else {
 x_384 = x_383;
}
lean_ctor_set(x_384, 0, x_381);
lean_ctor_set(x_384, 1, x_382);
return x_384;
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_306);
x_385 = lean_ctor_get(x_362, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_362, 1);
lean_inc(x_386);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 lean_ctor_release(x_362, 1);
 x_387 = x_362;
} else {
 lean_dec_ref(x_362);
 x_387 = lean_box(0);
}
if (lean_is_scalar(x_387)) {
 x_388 = lean_alloc_ctor(1, 2, 0);
} else {
 x_388 = x_387;
}
lean_ctor_set(x_388, 0, x_385);
lean_ctor_set(x_388, 1, x_386);
return x_388;
}
}
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
lean_dec(x_317);
lean_dec(x_310);
lean_dec(x_306);
lean_dec(x_1);
x_389 = lean_ctor_get(x_318, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_318, 1);
lean_inc(x_390);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 x_391 = x_318;
} else {
 lean_dec_ref(x_318);
 x_391 = lean_box(0);
}
if (lean_is_scalar(x_391)) {
 x_392 = lean_alloc_ctor(1, 2, 0);
} else {
 x_392 = x_391;
}
lean_ctor_set(x_392, 0, x_389);
lean_ctor_set(x_392, 1, x_390);
return x_392;
}
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
lean_dec(x_310);
lean_dec(x_306);
lean_dec(x_1);
x_393 = lean_ctor_get(x_312, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_312, 1);
lean_inc(x_394);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_395 = x_312;
} else {
 lean_dec_ref(x_312);
 x_395 = lean_box(0);
}
if (lean_is_scalar(x_395)) {
 x_396 = lean_alloc_ctor(1, 2, 0);
} else {
 x_396 = x_395;
}
lean_ctor_set(x_396, 0, x_393);
lean_ctor_set(x_396, 1, x_394);
return x_396;
}
}
}
else
{
uint8_t x_397; 
lean_dec(x_1);
x_397 = !lean_is_exclusive(x_5);
if (x_397 == 0)
{
return x_5;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_398 = lean_ctor_get(x_5, 0);
x_399 = lean_ctor_get(x_5, 1);
lean_inc(x_399);
lean_inc(x_398);
lean_dec(x_5);
x_400 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_400, 0, x_398);
lean_ctor_set(x_400, 1, x_399);
return x_400;
}
}
}
}
lean_object* l_AssocList_contains___main___at_Lean_importModules___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_importModules___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_importModules___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_miterateAux___main___at_Lean_importModules___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_importModules___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_importModules___spec__8(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_importModules___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_miterateAux___main___at_Lean_importModules___spec__9(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_importModules___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_miterateAux___main___at_Lean_importModules___spec__10(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_importModules___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_importModules___spec__12(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_importModules___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_importModules___spec__13(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_importModules___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_import_modules(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_regNamespacesExtension___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_box(0);
x_9 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_4, x_7, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
x_4 = x_9;
goto _start;
}
}
}
lean_object* l_Array_miterateAux___main___at_Lean_regNamespacesExtension___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_miterateAux___main___at_Lean_regNamespacesExtension___spec__2(x_7, x_7, x_8, x_4);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
x_4 = x_9;
goto _start;
}
}
}
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_regNamespacesExtension___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_miterateAux___main___at_Lean_regNamespacesExtension___spec__3(x_2, x_2, x_3, x_1);
return x_4;
}
}
uint8_t l_Array_anyMAux___main___at_Lean_regNamespacesExtension___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_name_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_3 = x_12;
goto _start;
}
else
{
lean_dec(x_3);
return x_10;
}
}
}
}
lean_object* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_initializing(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_3, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_3, 0, x_14);
x_15 = l___private_init_lean_environment_5__envExtensionsRef;
x_16 = lean_io_ref_get(x_15, x_3);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_16, 0, x_14);
x_19 = lean_array_get_size(x_18);
lean_dec(x_18);
x_20 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7___closed__2;
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_1);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_io_ref_get(x_15, x_16);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_ctor_set(x_22, 0, x_14);
x_25 = lean_io_ref_reset(x_15, x_22);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_14);
x_28 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_21);
x_29 = x_21;
x_30 = lean_array_push(x_24, x_29);
x_31 = lean_io_ref_set(x_15, x_30, x_25);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_21);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_21);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
lean_dec(x_25);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_14);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_21);
x_43 = x_21;
x_44 = lean_array_push(x_24, x_43);
x_45 = lean_io_ref_set(x_15, x_44, x_41);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_21);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_21);
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_51 = x_45;
} else {
 lean_dec_ref(x_45);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_24);
lean_dec(x_21);
x_53 = !lean_is_exclusive(x_25);
if (x_53 == 0)
{
return x_25;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_25, 0);
x_55 = lean_ctor_get(x_25, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_25);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_22, 0);
x_58 = lean_ctor_get(x_22, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_22);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_14);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_io_ref_reset(x_15, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_14);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_21);
x_65 = x_21;
x_66 = lean_array_push(x_57, x_65);
x_67 = lean_io_ref_set(x_15, x_66, x_63);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_21);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_21);
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_73 = x_67;
} else {
 lean_dec_ref(x_67);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_57);
lean_dec(x_21);
x_75 = lean_ctor_get(x_60, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_60, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_77 = x_60;
} else {
 lean_dec_ref(x_60);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_21);
x_79 = !lean_is_exclusive(x_22);
if (x_79 == 0)
{
return x_22;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_22, 0);
x_81 = lean_ctor_get(x_22, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_22);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_83 = lean_ctor_get(x_16, 0);
x_84 = lean_ctor_get(x_16, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_16);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_14);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_array_get_size(x_83);
lean_dec(x_83);
x_87 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7___closed__2;
x_88 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_1);
lean_ctor_set(x_88, 2, x_87);
x_89 = lean_io_ref_get(x_15, x_85);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_92 = x_89;
} else {
 lean_dec_ref(x_89);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_14);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_io_ref_reset(x_15, x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_96 = x_94;
} else {
 lean_dec_ref(x_94);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_14);
lean_ctor_set(x_97, 1, x_95);
x_98 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_88);
x_99 = x_88;
x_100 = lean_array_push(x_90, x_99);
x_101 = lean_io_ref_set(x_15, x_100, x_97);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_103 = x_101;
} else {
 lean_dec_ref(x_101);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_88);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_88);
x_105 = lean_ctor_get(x_101, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_101, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_107 = x_101;
} else {
 lean_dec_ref(x_101);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_90);
lean_dec(x_88);
x_109 = lean_ctor_get(x_94, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_94, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_111 = x_94;
} else {
 lean_dec_ref(x_94);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_88);
x_113 = lean_ctor_get(x_89, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_89, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_115 = x_89;
} else {
 lean_dec_ref(x_89);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_16);
if (x_117 == 0)
{
return x_16;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_16, 0);
x_119 = lean_ctor_get(x_16, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_16);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = lean_ctor_get(x_3, 1);
lean_inc(x_121);
lean_dec(x_3);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
x_124 = l___private_init_lean_environment_5__envExtensionsRef;
x_125 = lean_io_ref_get(x_124, x_123);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_128 = x_125;
} else {
 lean_dec_ref(x_125);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_122);
lean_ctor_set(x_129, 1, x_127);
x_130 = lean_array_get_size(x_126);
lean_dec(x_126);
x_131 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7___closed__2;
x_132 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_1);
lean_ctor_set(x_132, 2, x_131);
x_133 = lean_io_ref_get(x_124, x_129);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_136 = x_133;
} else {
 lean_dec_ref(x_133);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_122);
lean_ctor_set(x_137, 1, x_135);
x_138 = lean_io_ref_reset(x_124, x_137);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_140 = x_138;
} else {
 lean_dec_ref(x_138);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_122);
lean_ctor_set(x_141, 1, x_139);
x_142 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_132);
x_143 = x_132;
x_144 = lean_array_push(x_134, x_143);
x_145 = lean_io_ref_set(x_124, x_144, x_141);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_147 = x_145;
} else {
 lean_dec_ref(x_145);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_132);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_132);
x_149 = lean_ctor_get(x_145, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_145, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_151 = x_145;
} else {
 lean_dec_ref(x_145);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_134);
lean_dec(x_132);
x_153 = lean_ctor_get(x_138, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_138, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_155 = x_138;
} else {
 lean_dec_ref(x_138);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_132);
x_157 = lean_ctor_get(x_133, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_133, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_159 = x_133;
} else {
 lean_dec_ref(x_133);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_1);
x_161 = lean_ctor_get(x_125, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_125, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_163 = x_125;
} else {
 lean_dec_ref(x_125);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_1);
x_165 = !lean_is_exclusive(x_3);
if (x_165 == 0)
{
return x_3;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_3, 0);
x_167 = lean_ctor_get(x_3, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_3);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_init_lean_environment_8__persistentEnvExtensionsRef;
x_4 = lean_io_ref_get(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyMAux___main___at_Lean_regNamespacesExtension___spec__6(x_1, x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_box(0);
lean_ctor_set(x_4, 0, x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = l_Array_empty___closed__1;
lean_inc(x_10);
x_12 = lean_apply_1(x_10, x_11);
x_13 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_14 = lean_alloc_closure((void*)(l_EState_bind___rarg), 3, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7(x_14, x_4);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_15, 0, x_9);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 4);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_10);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set(x_22, 4, x_20);
lean_ctor_set(x_22, 5, x_21);
x_23 = lean_io_ref_get(x_3, x_15);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_23, 0, x_9);
x_26 = lean_io_ref_reset(x_3, x_23);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_9);
x_29 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_22);
x_30 = x_22;
x_31 = lean_array_push(x_25, x_30);
x_32 = lean_io_ref_set(x_3, x_31, x_26);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_22);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_22);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_22);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_32);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_26, 1);
lean_inc(x_41);
lean_dec(x_26);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_9);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_22);
x_44 = x_22;
x_45 = lean_array_push(x_25, x_44);
x_46 = lean_io_ref_set(x_3, x_45, x_42);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_22);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_22);
x_50 = lean_ctor_get(x_46, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_52 = x_46;
} else {
 lean_dec_ref(x_46);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_25);
lean_dec(x_22);
x_54 = !lean_is_exclusive(x_26);
if (x_54 == 0)
{
return x_26;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_26, 0);
x_56 = lean_ctor_get(x_26, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_26);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_23, 0);
x_59 = lean_ctor_get(x_23, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_23);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_9);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_io_ref_reset(x_3, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_9);
lean_ctor_set(x_64, 1, x_62);
x_65 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_22);
x_66 = x_22;
x_67 = lean_array_push(x_58, x_66);
x_68 = lean_io_ref_set(x_3, x_67, x_64);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_22);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_22);
x_72 = lean_ctor_get(x_68, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_68, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_74 = x_68;
} else {
 lean_dec_ref(x_68);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_58);
lean_dec(x_22);
x_76 = lean_ctor_get(x_61, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_61, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_78 = x_61;
} else {
 lean_dec_ref(x_61);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_22);
x_80 = !lean_is_exclusive(x_23);
if (x_80 == 0)
{
return x_23;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_23, 0);
x_82 = lean_ctor_get(x_23, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_23);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_84 = lean_ctor_get(x_15, 0);
x_85 = lean_ctor_get(x_15, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_15);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_9);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_ctor_get(x_1, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_1, 2);
lean_inc(x_88);
x_89 = lean_ctor_get(x_1, 3);
lean_inc(x_89);
x_90 = lean_ctor_get(x_1, 4);
lean_inc(x_90);
lean_dec(x_1);
x_91 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_91, 0, x_84);
lean_ctor_set(x_91, 1, x_87);
lean_ctor_set(x_91, 2, x_10);
lean_ctor_set(x_91, 3, x_88);
lean_ctor_set(x_91, 4, x_89);
lean_ctor_set(x_91, 5, x_90);
x_92 = lean_io_ref_get(x_3, x_86);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_95 = x_92;
} else {
 lean_dec_ref(x_92);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_9);
lean_ctor_set(x_96, 1, x_94);
x_97 = lean_io_ref_reset(x_3, x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_9);
lean_ctor_set(x_100, 1, x_98);
x_101 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_91);
x_102 = x_91;
x_103 = lean_array_push(x_93, x_102);
x_104 = lean_io_ref_set(x_3, x_103, x_100);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_106 = x_104;
} else {
 lean_dec_ref(x_104);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_91);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_91);
x_108 = lean_ctor_get(x_104, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_104, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_110 = x_104;
} else {
 lean_dec_ref(x_104);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_93);
lean_dec(x_91);
x_112 = lean_ctor_get(x_97, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_97, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_114 = x_97;
} else {
 lean_dec_ref(x_97);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_91);
x_116 = lean_ctor_get(x_92, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_92, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_118 = x_92;
} else {
 lean_dec_ref(x_92);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_10);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_15);
if (x_120 == 0)
{
return x_15;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_15, 0);
x_122 = lean_ctor_get(x_15, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_15);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_124 = lean_ctor_get(x_1, 0);
lean_inc(x_124);
lean_dec(x_1);
x_125 = l_Lean_Name_toString___closed__1;
x_126 = l_Lean_Name_toStringWithSep___main(x_125, x_124);
x_127 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_128 = lean_string_append(x_127, x_126);
lean_dec(x_126);
x_129 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_130 = lean_string_append(x_128, x_129);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_130);
return x_4;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_131 = lean_ctor_get(x_4, 0);
x_132 = lean_ctor_get(x_4, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_4);
x_133 = lean_unsigned_to_nat(0u);
x_134 = l_Array_anyMAux___main___at_Lean_regNamespacesExtension___spec__6(x_1, x_131, x_133);
lean_dec(x_131);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_132);
x_137 = lean_ctor_get(x_1, 1);
lean_inc(x_137);
x_138 = l_Array_empty___closed__1;
lean_inc(x_137);
x_139 = lean_apply_1(x_137, x_138);
x_140 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_141 = lean_alloc_closure((void*)(l_EState_bind___rarg), 3, 2);
lean_closure_set(x_141, 0, x_139);
lean_closure_set(x_141, 1, x_140);
x_142 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7(x_141, x_136);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_145 = x_142;
} else {
 lean_dec_ref(x_142);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_135);
lean_ctor_set(x_146, 1, x_144);
x_147 = lean_ctor_get(x_1, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_1, 2);
lean_inc(x_148);
x_149 = lean_ctor_get(x_1, 3);
lean_inc(x_149);
x_150 = lean_ctor_get(x_1, 4);
lean_inc(x_150);
lean_dec(x_1);
x_151 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_151, 0, x_143);
lean_ctor_set(x_151, 1, x_147);
lean_ctor_set(x_151, 2, x_137);
lean_ctor_set(x_151, 3, x_148);
lean_ctor_set(x_151, 4, x_149);
lean_ctor_set(x_151, 5, x_150);
x_152 = lean_io_ref_get(x_3, x_146);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_155 = x_152;
} else {
 lean_dec_ref(x_152);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_135);
lean_ctor_set(x_156, 1, x_154);
x_157 = lean_io_ref_reset(x_3, x_156);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_159 = x_157;
} else {
 lean_dec_ref(x_157);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_135);
lean_ctor_set(x_160, 1, x_158);
x_161 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_151);
x_162 = x_151;
x_163 = lean_array_push(x_153, x_162);
x_164 = lean_io_ref_set(x_3, x_163, x_160);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_166 = x_164;
} else {
 lean_dec_ref(x_164);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_151);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_151);
x_168 = lean_ctor_get(x_164, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_164, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_170 = x_164;
} else {
 lean_dec_ref(x_164);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_153);
lean_dec(x_151);
x_172 = lean_ctor_get(x_157, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_157, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_174 = x_157;
} else {
 lean_dec_ref(x_157);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_173);
return x_175;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_151);
x_176 = lean_ctor_get(x_152, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_152, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_178 = x_152;
} else {
 lean_dec_ref(x_152);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_177);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_137);
lean_dec(x_1);
x_180 = lean_ctor_get(x_142, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_142, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_182 = x_142;
} else {
 lean_dec_ref(x_142);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_184 = lean_ctor_get(x_1, 0);
lean_inc(x_184);
lean_dec(x_1);
x_185 = l_Lean_Name_toString___closed__1;
x_186 = l_Lean_Name_toStringWithSep___main(x_185, x_184);
x_187 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_188 = lean_string_append(x_187, x_186);
lean_dec(x_186);
x_189 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_190 = lean_string_append(x_188, x_189);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_132);
return x_191;
}
}
}
else
{
uint8_t x_192; 
lean_dec(x_1);
x_192 = !lean_is_exclusive(x_4);
if (x_192 == 0)
{
return x_4;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_4, 0);
x_194 = lean_ctor_get(x_4, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_4);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
}
lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_regNamespacesExtension___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1), 3, 1);
lean_closure_set(x_4, 0, x_1);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__2), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__3), 2, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1;
x_8 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_6);
lean_ctor_set(x_8, 4, x_7);
x_9 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__5(x_8, x_2);
return x_9;
}
}
lean_object* l_Lean_regNamespacesExtension___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_regNamespacesExtension___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_miterateAux___main___at_Lean_regNamespacesExtension___spec__3(x_1, x_1, x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_regNamespacesExtension___lambda__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_List_redLength___main___rarg(x_1);
x_3 = lean_mk_empty_array_with_capacity(x_2);
lean_dec(x_2);
x_4 = l_List_toArrayAux___main___rarg(x_1, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_regNamespacesExtension___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("namespaces");
return x_1;
}
}
lean_object* _init_l_Lean_regNamespacesExtension___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_regNamespacesExtension___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_regNamespacesExtension___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_regNamespacesExtension___lambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_regNamespacesExtension___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_regNamespacesExtension___lambda__2___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_regNamespacesExtension___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_regNamespacesExtension___lambda__3), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_regNamespacesExtension___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_regNamespacesExtension___closed__2;
x_2 = l_Lean_regNamespacesExtension___closed__3;
x_3 = l_Lean_regNamespacesExtension___closed__4;
x_4 = l_Lean_regNamespacesExtension___closed__5;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* l_Lean_regNamespacesExtension(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_regNamespacesExtension___closed__6;
x_3 = l_Lean_registerSimplePersistentEnvExtension___at_Lean_regNamespacesExtension___spec__4(x_2, x_1);
return x_3;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_regNamespacesExtension___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_regNamespacesExtension___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_regNamespacesExtension___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_regNamespacesExtension___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_regNamespacesExtension___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkStateFromImportedEntries___at_Lean_regNamespacesExtension___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_anyMAux___main___at_Lean_regNamespacesExtension___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_anyMAux___main___at_Lean_regNamespacesExtension___spec__6(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Lean_regNamespacesExtension___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_regNamespacesExtension___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_namespacesExt___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* l_Lean_namespacesExt___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_empty___closed__1;
return x_2;
}
}
lean_object* l_Lean_namespacesExt___elambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_namespacesExt___elambda__4___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_dec(x_3);
x_4 = l_String_splitAux___main___closed__1;
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_String_splitAux___main___closed__1;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
lean_object* l_Lean_namespacesExt___elambda__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_namespacesExt___elambda__4___rarg), 1, 0);
return x_2;
}
}
lean_object* _init_l_Lean_namespacesExt___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_3 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_namespacesExt___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_namespacesExt___elambda__4___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_namespacesExt___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_namespacesExt___elambda__3___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_namespacesExt___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_namespacesExt___elambda__2___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_namespacesExt___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_namespacesExt___elambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_namespacesExt___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_namespacesExt___closed__1;
x_2 = lean_box(0);
x_3 = l_Lean_namespacesExt___closed__2;
x_4 = l_Lean_namespacesExt___closed__3;
x_5 = l_Lean_namespacesExt___closed__4;
x_6 = l_Lean_namespacesExt___closed__5;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
lean_object* l_Lean_namespacesExt___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_namespacesExt___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_namespacesExt___elambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_namespacesExt___elambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_namespacesExt___elambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_namespacesExt___elambda__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_namespacesExt___elambda__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_namespacesExt___elambda__4(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_registerNamespace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_namespacesExt;
x_4 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_3, x_1);
x_5 = l_Lean_NameSet_contains(x_4, x_2);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_3, x_1, x_2);
return x_6;
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
uint8_t l_Lean_isNamespace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_namespacesExt;
x_4 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_3, x_1);
x_5 = l_Lean_NameSet_contains(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Lean_isNamespace___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_isNamespace(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_getNamespaceSet(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_namespacesExt;
x_3 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_getNamespaceSet___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_getNamespaceSet(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l___private_init_lean_environment_12__isNamespaceName___main(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_box(0);
x_4 = lean_name_dec_eq(x_2, x_3);
if (x_4 == 0)
{
x_1 = x_2;
goto _start;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
lean_object* l___private_init_lean_environment_12__isNamespaceName___main___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_init_lean_environment_12__isNamespaceName___main(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l___private_init_lean_environment_12__isNamespaceName(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l___private_init_lean_environment_12__isNamespaceName___main(x_1);
return x_2;
}
}
lean_object* l___private_init_lean_environment_12__isNamespaceName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_init_lean_environment_12__isNamespaceName(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_init_lean_environment_13__registerNamePrefixes___main(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l___private_init_lean_environment_12__isNamespaceName___main(x_3);
if (x_4 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_registerNamespace(x_1, x_3);
x_1 = x_5;
x_2 = x_3;
goto _start;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
lean_object* l___private_init_lean_environment_13__registerNamePrefixes(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_init_lean_environment_13__registerNamePrefixes___main(x_1, x_2);
return x_3;
}
}
lean_object* lean_environment_add(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_ConstantInfo_name(x_2);
x_4 = l___private_init_lean_environment_13__registerNamePrefixes___main(x_1, x_3);
x_5 = l_Lean_Environment_addAux(x_4, x_2);
return x_5;
}
}
lean_object* l_List_toStringAux___main___at_Lean_Environment_displayStats___spec__2(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_String_splitAux___main___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Name_toString___closed__1;
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_4);
x_8 = l_List_reprAux___main___rarg___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_List_toStringAux___main___at_Lean_Environment_displayStats___spec__2(x_1, x_5);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
return x_11;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; 
x_12 = l_String_splitAux___main___closed__1;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Lean_Name_toString___closed__1;
x_16 = l_Lean_Name_toStringWithSep___main(x_15, x_13);
x_17 = 0;
x_18 = l_List_toStringAux___main___at_Lean_Environment_displayStats___spec__2(x_17, x_14);
x_19 = lean_string_append(x_16, x_18);
lean_dec(x_18);
return x_19;
}
}
}
}
lean_object* l_List_toString___at_Lean_Environment_displayStats___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_repr___rarg___closed__1;
return x_2;
}
else
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = 1;
x_4 = l_List_toStringAux___main___at_Lean_Environment_displayStats___spec__2(x_3, x_1);
x_5 = l_List_repr___rarg___closed__2;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_List_repr___rarg___closed__3;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
}
}
lean_object* l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(x_4, x_3);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_nat_add(x_6, x_5);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(x_4, x_3);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
lean_object* l_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_array_get_size(x_2);
return x_3;
}
}
lean_object* l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__6(x_2);
return x_3;
}
}
lean_object* l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_RBMap_maxDepth___rarg___closed__1;
x_4 = l_RBNode_depth___main___rarg(x_3, x_2);
return x_4;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = lean_nat_add(x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_4 = x_12;
x_5 = x_10;
goto _start;
}
}
}
lean_object* l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = lean_nat_add(x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_4 = x_12;
x_5 = x_10;
goto _start;
}
}
}
lean_object* _init_l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("extension '");
return x_1;
}
}
lean_object* _init_l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  ");
return x_1;
}
}
lean_object* _init_l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  number of imported entries: ");
return x_1;
}
}
lean_object* l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_array_fget(x_2, x_3);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_3, x_14);
lean_dec(x_3);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
x_17 = l_Lean_Name_toString___closed__1;
x_18 = l_Lean_Name_toStringWithSep___main(x_17, x_16);
x_19 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = l_Char_HasRepr___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_IO_println___at_HasRepr_HasEval___spec__1(x_22, x_4);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_23, 0, x_26);
x_27 = lean_ctor_get(x_13, 0);
lean_inc(x_27);
x_28 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_27, x_1);
x_29 = lean_ctor_get(x_13, 5);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
x_31 = lean_apply_1(x_29, x_30);
x_32 = l_Lean_Format_isNil(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
x_35 = l_Lean_Options_empty;
x_36 = l_Lean_Format_pretty(x_34, x_35);
x_37 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__2;
x_38 = lean_string_append(x_37, x_36);
lean_dec(x_36);
x_39 = l_IO_println___at_HasRepr_HasEval___spec__1(x_38, x_23);
lean_dec(x_38);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_26);
x_42 = lean_ctor_get(x_28, 0);
lean_inc(x_42);
lean_dec(x_28);
x_43 = lean_unsigned_to_nat(0u);
x_44 = l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__8(x_1, x_13, x_42, x_43, x_43);
lean_dec(x_42);
lean_dec(x_13);
x_45 = l_Nat_repr(x_44);
x_46 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__3;
x_47 = lean_string_append(x_46, x_45);
lean_dec(x_45);
x_48 = l_IO_println___at_HasRepr_HasEval___spec__1(x_47, x_39);
lean_dec(x_47);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
lean_ctor_set(x_48, 0, x_26);
x_3 = x_15;
x_4 = x_48;
goto _start;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_26);
lean_ctor_set(x_53, 1, x_52);
x_3 = x_15;
x_4 = x_53;
goto _start;
}
}
else
{
uint8_t x_55; 
lean_dec(x_15);
x_55 = !lean_is_exclusive(x_48);
if (x_55 == 0)
{
return x_48;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_48, 0);
x_57 = lean_ctor_get(x_48, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_48);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_59 = lean_ctor_get(x_39, 1);
lean_inc(x_59);
lean_dec(x_39);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_26);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_ctor_get(x_28, 0);
lean_inc(x_61);
lean_dec(x_28);
x_62 = lean_unsigned_to_nat(0u);
x_63 = l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__8(x_1, x_13, x_61, x_62, x_62);
lean_dec(x_61);
lean_dec(x_13);
x_64 = l_Nat_repr(x_63);
x_65 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__3;
x_66 = lean_string_append(x_65, x_64);
lean_dec(x_64);
x_67 = l_IO_println___at_HasRepr_HasEval___spec__1(x_66, x_60);
lean_dec(x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_26);
lean_ctor_set(x_70, 1, x_68);
x_3 = x_15;
x_4 = x_70;
goto _start;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_15);
x_72 = lean_ctor_get(x_67, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_74 = x_67;
} else {
 lean_dec_ref(x_67);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_13);
x_76 = !lean_is_exclusive(x_39);
if (x_76 == 0)
{
return x_39;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_39, 0);
x_78 = lean_ctor_get(x_39, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_39);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_31);
x_80 = lean_ctor_get(x_28, 0);
lean_inc(x_80);
lean_dec(x_28);
x_81 = lean_unsigned_to_nat(0u);
x_82 = l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__9(x_1, x_13, x_80, x_81, x_81);
lean_dec(x_80);
lean_dec(x_13);
x_83 = l_Nat_repr(x_82);
x_84 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__3;
x_85 = lean_string_append(x_84, x_83);
lean_dec(x_83);
x_86 = l_IO_println___at_HasRepr_HasEval___spec__1(x_85, x_23);
lean_dec(x_85);
if (lean_obj_tag(x_86) == 0)
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_86, 0);
lean_dec(x_88);
lean_ctor_set(x_86, 0, x_26);
x_3 = x_15;
x_4 = x_86;
goto _start;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_90);
lean_dec(x_86);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_26);
lean_ctor_set(x_91, 1, x_90);
x_3 = x_15;
x_4 = x_91;
goto _start;
}
}
else
{
uint8_t x_93; 
lean_dec(x_15);
x_93 = !lean_is_exclusive(x_86);
if (x_93 == 0)
{
return x_86;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_86, 0);
x_95 = lean_ctor_get(x_86, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_86);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_97 = lean_ctor_get(x_23, 1);
lean_inc(x_97);
lean_dec(x_23);
x_98 = lean_box(0);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = lean_ctor_get(x_13, 0);
lean_inc(x_100);
x_101 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_100, x_1);
x_102 = lean_ctor_get(x_13, 5);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
x_104 = lean_apply_1(x_102, x_103);
x_105 = l_Lean_Format_isNil(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_106 = lean_unsigned_to_nat(2u);
x_107 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_104);
x_108 = l_Lean_Options_empty;
x_109 = l_Lean_Format_pretty(x_107, x_108);
x_110 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__2;
x_111 = lean_string_append(x_110, x_109);
lean_dec(x_109);
x_112 = l_IO_println___at_HasRepr_HasEval___spec__1(x_111, x_99);
lean_dec(x_111);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_114 = x_112;
} else {
 lean_dec_ref(x_112);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_98);
lean_ctor_set(x_115, 1, x_113);
x_116 = lean_ctor_get(x_101, 0);
lean_inc(x_116);
lean_dec(x_101);
x_117 = lean_unsigned_to_nat(0u);
x_118 = l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__8(x_1, x_13, x_116, x_117, x_117);
lean_dec(x_116);
lean_dec(x_13);
x_119 = l_Nat_repr(x_118);
x_120 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__3;
x_121 = lean_string_append(x_120, x_119);
lean_dec(x_119);
x_122 = l_IO_println___at_HasRepr_HasEval___spec__1(x_121, x_115);
lean_dec(x_121);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_124 = x_122;
} else {
 lean_dec_ref(x_122);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_98);
lean_ctor_set(x_125, 1, x_123);
x_3 = x_15;
x_4 = x_125;
goto _start;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_15);
x_127 = lean_ctor_get(x_122, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_122, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_129 = x_122;
} else {
 lean_dec_ref(x_122);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_101);
lean_dec(x_15);
lean_dec(x_13);
x_131 = lean_ctor_get(x_112, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_112, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_133 = x_112;
} else {
 lean_dec_ref(x_112);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_104);
x_135 = lean_ctor_get(x_101, 0);
lean_inc(x_135);
lean_dec(x_101);
x_136 = lean_unsigned_to_nat(0u);
x_137 = l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__9(x_1, x_13, x_135, x_136, x_136);
lean_dec(x_135);
lean_dec(x_13);
x_138 = l_Nat_repr(x_137);
x_139 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__3;
x_140 = lean_string_append(x_139, x_138);
lean_dec(x_138);
x_141 = l_IO_println___at_HasRepr_HasEval___spec__1(x_140, x_99);
lean_dec(x_140);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_98);
lean_ctor_set(x_144, 1, x_142);
x_3 = x_15;
x_4 = x_144;
goto _start;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_15);
x_146 = lean_ctor_get(x_141, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_141, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_148 = x_141;
} else {
 lean_dec_ref(x_141);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
}
}
else
{
uint8_t x_150; 
lean_dec(x_15);
lean_dec(x_13);
x_150 = !lean_is_exclusive(x_23);
if (x_150 == 0)
{
return x_23;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_23, 0);
x_152 = lean_ctor_get(x_23, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_23);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
}
}
lean_object* _init_l_Lean_Environment_displayStats___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("direct imports:                        ");
return x_1;
}
}
lean_object* _init_l_Lean_Environment_displayStats___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("number of imported modules:            ");
return x_1;
}
}
lean_object* _init_l_Lean_Environment_displayStats___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("number of consts:                      ");
return x_1;
}
}
lean_object* _init_l_Lean_Environment_displayStats___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("number of imported consts:             ");
return x_1;
}
}
lean_object* _init_l_Lean_Environment_displayStats___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("number of local consts:                ");
return x_1;
}
}
lean_object* _init_l_Lean_Environment_displayStats___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("number of buckets for imported consts: ");
return x_1;
}
}
lean_object* _init_l_Lean_Environment_displayStats___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("map depth for local consts:            ");
return x_1;
}
}
lean_object* _init_l_Lean_Environment_displayStats___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("trust level:                           ");
return x_1;
}
}
lean_object* _init_l_Lean_Environment_displayStats___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("number of extensions:                  ");
return x_1;
}
}
lean_object* lean_display_stats(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_init_lean_environment_8__persistentEnvExtensionsRef;
x_4 = lean_io_ref_get(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_box(0);
lean_ctor_set(x_4, 0, x_7);
x_8 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_get(x_8, x_6, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_11, x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_array_get_size(x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = l_Array_toList___rarg(x_16);
lean_dec(x_16);
x_18 = l_List_toString___at_Lean_Environment_displayStats___spec__1(x_17);
x_19 = l_Lean_Environment_displayStats___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = l_IO_println___at_HasRepr_HasEval___spec__1(x_20, x_4);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_7);
x_24 = l_Nat_repr(x_14);
x_25 = l_Lean_Environment_displayStats___closed__2;
x_26 = lean_string_append(x_25, x_24);
lean_dec(x_24);
x_27 = l_IO_println___at_HasRepr_HasEval___spec__1(x_26, x_21);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_7);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
x_31 = l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3(x_30);
x_32 = l_Nat_repr(x_31);
x_33 = l_Lean_Environment_displayStats___closed__3;
x_34 = lean_string_append(x_33, x_32);
lean_dec(x_32);
x_35 = l_IO_println___at_HasRepr_HasEval___spec__1(x_34, x_27);
lean_dec(x_34);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_7);
x_38 = l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4(x_30);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = l_Nat_repr(x_39);
x_41 = l_Lean_Environment_displayStats___closed__4;
x_42 = lean_string_append(x_41, x_40);
lean_dec(x_40);
x_43 = l_IO_println___at_HasRepr_HasEval___spec__1(x_42, x_35);
lean_dec(x_42);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
lean_ctor_set(x_43, 0, x_7);
x_46 = lean_ctor_get(x_38, 1);
lean_inc(x_46);
lean_dec(x_38);
x_47 = l_Nat_repr(x_46);
x_48 = l_Lean_Environment_displayStats___closed__5;
x_49 = lean_string_append(x_48, x_47);
lean_dec(x_47);
x_50 = l_IO_println___at_HasRepr_HasEval___spec__1(x_49, x_43);
lean_dec(x_49);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
lean_ctor_set(x_50, 0, x_7);
x_53 = l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(x_30);
x_54 = l_Nat_repr(x_53);
x_55 = l_Lean_Environment_displayStats___closed__6;
x_56 = lean_string_append(x_55, x_54);
lean_dec(x_54);
x_57 = l_IO_println___at_HasRepr_HasEval___spec__1(x_56, x_50);
lean_dec(x_56);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
lean_ctor_set(x_57, 0, x_7);
x_60 = l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(x_30);
lean_dec(x_30);
x_61 = l_Nat_repr(x_60);
x_62 = l_Lean_Environment_displayStats___closed__7;
x_63 = lean_string_append(x_62, x_61);
lean_dec(x_61);
x_64 = l_IO_println___at_HasRepr_HasEval___spec__1(x_63, x_57);
lean_dec(x_63);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; uint32_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
lean_ctor_set(x_64, 0, x_7);
x_67 = lean_ctor_get_uint32(x_15, sizeof(void*)*2);
lean_dec(x_15);
x_68 = lean_uint32_to_nat(x_67);
x_69 = l_Nat_repr(x_68);
x_70 = l_Lean_Environment_displayStats___closed__8;
x_71 = lean_string_append(x_70, x_69);
lean_dec(x_69);
x_72 = l_IO_println___at_HasRepr_HasEval___spec__1(x_71, x_64);
lean_dec(x_71);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_74 = lean_ctor_get(x_72, 0);
lean_dec(x_74);
lean_ctor_set(x_72, 0, x_7);
x_75 = lean_ctor_get(x_1, 2);
lean_inc(x_75);
x_76 = lean_array_get_size(x_75);
lean_dec(x_75);
x_77 = l_Nat_repr(x_76);
x_78 = l_Lean_Environment_displayStats___closed__9;
x_79 = lean_string_append(x_78, x_77);
lean_dec(x_77);
x_80 = l_IO_println___at_HasRepr_HasEval___spec__1(x_79, x_72);
lean_dec(x_79);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_80, 0);
lean_dec(x_82);
lean_ctor_set(x_80, 0, x_7);
x_83 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10(x_1, x_6, x_9, x_80);
lean_dec(x_6);
lean_dec(x_1);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_83, 0);
lean_dec(x_85);
lean_ctor_set(x_83, 0, x_7);
return x_83;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_dec(x_83);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_7);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
else
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_83);
if (x_88 == 0)
{
return x_83;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_83, 0);
x_90 = lean_ctor_get(x_83, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_83);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_80, 1);
lean_inc(x_92);
lean_dec(x_80);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_7);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10(x_1, x_6, x_9, x_93);
lean_dec(x_6);
lean_dec(x_1);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_96 = x_94;
} else {
 lean_dec_ref(x_94);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_7);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_94, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_94, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_100 = x_94;
} else {
 lean_dec_ref(x_94);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_6);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_80);
if (x_102 == 0)
{
return x_80;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_80, 0);
x_104 = lean_ctor_get(x_80, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_80);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_106 = lean_ctor_get(x_72, 1);
lean_inc(x_106);
lean_dec(x_72);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_7);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_ctor_get(x_1, 2);
lean_inc(x_108);
x_109 = lean_array_get_size(x_108);
lean_dec(x_108);
x_110 = l_Nat_repr(x_109);
x_111 = l_Lean_Environment_displayStats___closed__9;
x_112 = lean_string_append(x_111, x_110);
lean_dec(x_110);
x_113 = l_IO_println___at_HasRepr_HasEval___spec__1(x_112, x_107);
lean_dec(x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_115 = x_113;
} else {
 lean_dec_ref(x_113);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_7);
lean_ctor_set(x_116, 1, x_114);
x_117 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10(x_1, x_6, x_9, x_116);
lean_dec(x_6);
lean_dec(x_1);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_7);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_117, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_117, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_123 = x_117;
} else {
 lean_dec_ref(x_117);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_6);
lean_dec(x_1);
x_125 = lean_ctor_get(x_113, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_113, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_127 = x_113;
} else {
 lean_dec_ref(x_113);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_6);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_72);
if (x_129 == 0)
{
return x_72;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_72, 0);
x_131 = lean_ctor_get(x_72, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_72);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
lean_object* x_133; lean_object* x_134; uint32_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_133 = lean_ctor_get(x_64, 1);
lean_inc(x_133);
lean_dec(x_64);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_7);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_ctor_get_uint32(x_15, sizeof(void*)*2);
lean_dec(x_15);
x_136 = lean_uint32_to_nat(x_135);
x_137 = l_Nat_repr(x_136);
x_138 = l_Lean_Environment_displayStats___closed__8;
x_139 = lean_string_append(x_138, x_137);
lean_dec(x_137);
x_140 = l_IO_println___at_HasRepr_HasEval___spec__1(x_139, x_134);
lean_dec(x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_142 = x_140;
} else {
 lean_dec_ref(x_140);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_7);
lean_ctor_set(x_143, 1, x_141);
x_144 = lean_ctor_get(x_1, 2);
lean_inc(x_144);
x_145 = lean_array_get_size(x_144);
lean_dec(x_144);
x_146 = l_Nat_repr(x_145);
x_147 = l_Lean_Environment_displayStats___closed__9;
x_148 = lean_string_append(x_147, x_146);
lean_dec(x_146);
x_149 = l_IO_println___at_HasRepr_HasEval___spec__1(x_148, x_143);
lean_dec(x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_151 = x_149;
} else {
 lean_dec_ref(x_149);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_7);
lean_ctor_set(x_152, 1, x_150);
x_153 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10(x_1, x_6, x_9, x_152);
lean_dec(x_6);
lean_dec(x_1);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_155 = x_153;
} else {
 lean_dec_ref(x_153);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_7);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_ctor_get(x_153, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_153, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_159 = x_153;
} else {
 lean_dec_ref(x_153);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_6);
lean_dec(x_1);
x_161 = lean_ctor_get(x_149, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_149, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_163 = x_149;
} else {
 lean_dec_ref(x_149);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_6);
lean_dec(x_1);
x_165 = lean_ctor_get(x_140, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_140, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_167 = x_140;
} else {
 lean_dec_ref(x_140);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
}
}
else
{
uint8_t x_169; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_169 = !lean_is_exclusive(x_64);
if (x_169 == 0)
{
return x_64;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_64, 0);
x_171 = lean_ctor_get(x_64, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_64);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_173 = lean_ctor_get(x_57, 1);
lean_inc(x_173);
lean_dec(x_57);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_7);
lean_ctor_set(x_174, 1, x_173);
x_175 = l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(x_30);
lean_dec(x_30);
x_176 = l_Nat_repr(x_175);
x_177 = l_Lean_Environment_displayStats___closed__7;
x_178 = lean_string_append(x_177, x_176);
lean_dec(x_176);
x_179 = l_IO_println___at_HasRepr_HasEval___spec__1(x_178, x_174);
lean_dec(x_178);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; uint32_t x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_181 = x_179;
} else {
 lean_dec_ref(x_179);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_7);
lean_ctor_set(x_182, 1, x_180);
x_183 = lean_ctor_get_uint32(x_15, sizeof(void*)*2);
lean_dec(x_15);
x_184 = lean_uint32_to_nat(x_183);
x_185 = l_Nat_repr(x_184);
x_186 = l_Lean_Environment_displayStats___closed__8;
x_187 = lean_string_append(x_186, x_185);
lean_dec(x_185);
x_188 = l_IO_println___at_HasRepr_HasEval___spec__1(x_187, x_182);
lean_dec(x_187);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_190 = x_188;
} else {
 lean_dec_ref(x_188);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_7);
lean_ctor_set(x_191, 1, x_189);
x_192 = lean_ctor_get(x_1, 2);
lean_inc(x_192);
x_193 = lean_array_get_size(x_192);
lean_dec(x_192);
x_194 = l_Nat_repr(x_193);
x_195 = l_Lean_Environment_displayStats___closed__9;
x_196 = lean_string_append(x_195, x_194);
lean_dec(x_194);
x_197 = l_IO_println___at_HasRepr_HasEval___spec__1(x_196, x_191);
lean_dec(x_196);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_199 = x_197;
} else {
 lean_dec_ref(x_197);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_7);
lean_ctor_set(x_200, 1, x_198);
x_201 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10(x_1, x_6, x_9, x_200);
lean_dec(x_6);
lean_dec(x_1);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_203 = x_201;
} else {
 lean_dec_ref(x_201);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_7);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_205 = lean_ctor_get(x_201, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_201, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_207 = x_201;
} else {
 lean_dec_ref(x_201);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_6);
lean_dec(x_1);
x_209 = lean_ctor_get(x_197, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_197, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_211 = x_197;
} else {
 lean_dec_ref(x_197);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_210);
return x_212;
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_6);
lean_dec(x_1);
x_213 = lean_ctor_get(x_188, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_188, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_215 = x_188;
} else {
 lean_dec_ref(x_188);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(1, 2, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_213);
lean_ctor_set(x_216, 1, x_214);
return x_216;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_217 = lean_ctor_get(x_179, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_179, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_219 = x_179;
} else {
 lean_dec_ref(x_179);
 x_219 = lean_box(0);
}
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(1, 2, 0);
} else {
 x_220 = x_219;
}
lean_ctor_set(x_220, 0, x_217);
lean_ctor_set(x_220, 1, x_218);
return x_220;
}
}
}
else
{
uint8_t x_221; 
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_221 = !lean_is_exclusive(x_57);
if (x_221 == 0)
{
return x_57;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_57, 0);
x_223 = lean_ctor_get(x_57, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_57);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_225 = lean_ctor_get(x_50, 1);
lean_inc(x_225);
lean_dec(x_50);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_7);
lean_ctor_set(x_226, 1, x_225);
x_227 = l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(x_30);
x_228 = l_Nat_repr(x_227);
x_229 = l_Lean_Environment_displayStats___closed__6;
x_230 = lean_string_append(x_229, x_228);
lean_dec(x_228);
x_231 = l_IO_println___at_HasRepr_HasEval___spec__1(x_230, x_226);
lean_dec(x_230);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_233 = x_231;
} else {
 lean_dec_ref(x_231);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(0, 2, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_7);
lean_ctor_set(x_234, 1, x_232);
x_235 = l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(x_30);
lean_dec(x_30);
x_236 = l_Nat_repr(x_235);
x_237 = l_Lean_Environment_displayStats___closed__7;
x_238 = lean_string_append(x_237, x_236);
lean_dec(x_236);
x_239 = l_IO_println___at_HasRepr_HasEval___spec__1(x_238, x_234);
lean_dec(x_238);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; uint32_t x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_240 = lean_ctor_get(x_239, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_241 = x_239;
} else {
 lean_dec_ref(x_239);
 x_241 = lean_box(0);
}
if (lean_is_scalar(x_241)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_241;
}
lean_ctor_set(x_242, 0, x_7);
lean_ctor_set(x_242, 1, x_240);
x_243 = lean_ctor_get_uint32(x_15, sizeof(void*)*2);
lean_dec(x_15);
x_244 = lean_uint32_to_nat(x_243);
x_245 = l_Nat_repr(x_244);
x_246 = l_Lean_Environment_displayStats___closed__8;
x_247 = lean_string_append(x_246, x_245);
lean_dec(x_245);
x_248 = l_IO_println___at_HasRepr_HasEval___spec__1(x_247, x_242);
lean_dec(x_247);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_250 = x_248;
} else {
 lean_dec_ref(x_248);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_7);
lean_ctor_set(x_251, 1, x_249);
x_252 = lean_ctor_get(x_1, 2);
lean_inc(x_252);
x_253 = lean_array_get_size(x_252);
lean_dec(x_252);
x_254 = l_Nat_repr(x_253);
x_255 = l_Lean_Environment_displayStats___closed__9;
x_256 = lean_string_append(x_255, x_254);
lean_dec(x_254);
x_257 = l_IO_println___at_HasRepr_HasEval___spec__1(x_256, x_251);
lean_dec(x_256);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_258 = lean_ctor_get(x_257, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_259 = x_257;
} else {
 lean_dec_ref(x_257);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_7);
lean_ctor_set(x_260, 1, x_258);
x_261 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10(x_1, x_6, x_9, x_260);
lean_dec(x_6);
lean_dec(x_1);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_261, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_263 = x_261;
} else {
 lean_dec_ref(x_261);
 x_263 = lean_box(0);
}
if (lean_is_scalar(x_263)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_263;
}
lean_ctor_set(x_264, 0, x_7);
lean_ctor_set(x_264, 1, x_262);
return x_264;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_265 = lean_ctor_get(x_261, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_261, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_267 = x_261;
} else {
 lean_dec_ref(x_261);
 x_267 = lean_box(0);
}
if (lean_is_scalar(x_267)) {
 x_268 = lean_alloc_ctor(1, 2, 0);
} else {
 x_268 = x_267;
}
lean_ctor_set(x_268, 0, x_265);
lean_ctor_set(x_268, 1, x_266);
return x_268;
}
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_6);
lean_dec(x_1);
x_269 = lean_ctor_get(x_257, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_257, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_271 = x_257;
} else {
 lean_dec_ref(x_257);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(1, 2, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_269);
lean_ctor_set(x_272, 1, x_270);
return x_272;
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_6);
lean_dec(x_1);
x_273 = lean_ctor_get(x_248, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_248, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_275 = x_248;
} else {
 lean_dec_ref(x_248);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(1, 2, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_273);
lean_ctor_set(x_276, 1, x_274);
return x_276;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_277 = lean_ctor_get(x_239, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_239, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_279 = x_239;
} else {
 lean_dec_ref(x_239);
 x_279 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_280 = lean_alloc_ctor(1, 2, 0);
} else {
 x_280 = x_279;
}
lean_ctor_set(x_280, 0, x_277);
lean_ctor_set(x_280, 1, x_278);
return x_280;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_281 = lean_ctor_get(x_231, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_231, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_283 = x_231;
} else {
 lean_dec_ref(x_231);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_281);
lean_ctor_set(x_284, 1, x_282);
return x_284;
}
}
}
else
{
uint8_t x_285; 
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_285 = !lean_is_exclusive(x_50);
if (x_285 == 0)
{
return x_50;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_50, 0);
x_287 = lean_ctor_get(x_50, 1);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_50);
x_288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
return x_288;
}
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_289 = lean_ctor_get(x_43, 1);
lean_inc(x_289);
lean_dec(x_43);
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_7);
lean_ctor_set(x_290, 1, x_289);
x_291 = lean_ctor_get(x_38, 1);
lean_inc(x_291);
lean_dec(x_38);
x_292 = l_Nat_repr(x_291);
x_293 = l_Lean_Environment_displayStats___closed__5;
x_294 = lean_string_append(x_293, x_292);
lean_dec(x_292);
x_295 = l_IO_println___at_HasRepr_HasEval___spec__1(x_294, x_290);
lean_dec(x_294);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_296 = lean_ctor_get(x_295, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 x_297 = x_295;
} else {
 lean_dec_ref(x_295);
 x_297 = lean_box(0);
}
if (lean_is_scalar(x_297)) {
 x_298 = lean_alloc_ctor(0, 2, 0);
} else {
 x_298 = x_297;
}
lean_ctor_set(x_298, 0, x_7);
lean_ctor_set(x_298, 1, x_296);
x_299 = l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(x_30);
x_300 = l_Nat_repr(x_299);
x_301 = l_Lean_Environment_displayStats___closed__6;
x_302 = lean_string_append(x_301, x_300);
lean_dec(x_300);
x_303 = l_IO_println___at_HasRepr_HasEval___spec__1(x_302, x_298);
lean_dec(x_302);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_304 = lean_ctor_get(x_303, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 x_305 = x_303;
} else {
 lean_dec_ref(x_303);
 x_305 = lean_box(0);
}
if (lean_is_scalar(x_305)) {
 x_306 = lean_alloc_ctor(0, 2, 0);
} else {
 x_306 = x_305;
}
lean_ctor_set(x_306, 0, x_7);
lean_ctor_set(x_306, 1, x_304);
x_307 = l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(x_30);
lean_dec(x_30);
x_308 = l_Nat_repr(x_307);
x_309 = l_Lean_Environment_displayStats___closed__7;
x_310 = lean_string_append(x_309, x_308);
lean_dec(x_308);
x_311 = l_IO_println___at_HasRepr_HasEval___spec__1(x_310, x_306);
lean_dec(x_310);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; uint32_t x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_312 = lean_ctor_get(x_311, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 x_313 = x_311;
} else {
 lean_dec_ref(x_311);
 x_313 = lean_box(0);
}
if (lean_is_scalar(x_313)) {
 x_314 = lean_alloc_ctor(0, 2, 0);
} else {
 x_314 = x_313;
}
lean_ctor_set(x_314, 0, x_7);
lean_ctor_set(x_314, 1, x_312);
x_315 = lean_ctor_get_uint32(x_15, sizeof(void*)*2);
lean_dec(x_15);
x_316 = lean_uint32_to_nat(x_315);
x_317 = l_Nat_repr(x_316);
x_318 = l_Lean_Environment_displayStats___closed__8;
x_319 = lean_string_append(x_318, x_317);
lean_dec(x_317);
x_320 = l_IO_println___at_HasRepr_HasEval___spec__1(x_319, x_314);
lean_dec(x_319);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_321 = lean_ctor_get(x_320, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 x_322 = x_320;
} else {
 lean_dec_ref(x_320);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(0, 2, 0);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_7);
lean_ctor_set(x_323, 1, x_321);
x_324 = lean_ctor_get(x_1, 2);
lean_inc(x_324);
x_325 = lean_array_get_size(x_324);
lean_dec(x_324);
x_326 = l_Nat_repr(x_325);
x_327 = l_Lean_Environment_displayStats___closed__9;
x_328 = lean_string_append(x_327, x_326);
lean_dec(x_326);
x_329 = l_IO_println___at_HasRepr_HasEval___spec__1(x_328, x_323);
lean_dec(x_328);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_330 = lean_ctor_get(x_329, 1);
lean_inc(x_330);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 x_331 = x_329;
} else {
 lean_dec_ref(x_329);
 x_331 = lean_box(0);
}
if (lean_is_scalar(x_331)) {
 x_332 = lean_alloc_ctor(0, 2, 0);
} else {
 x_332 = x_331;
}
lean_ctor_set(x_332, 0, x_7);
lean_ctor_set(x_332, 1, x_330);
x_333 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10(x_1, x_6, x_9, x_332);
lean_dec(x_6);
lean_dec(x_1);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_333, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_335 = x_333;
} else {
 lean_dec_ref(x_333);
 x_335 = lean_box(0);
}
if (lean_is_scalar(x_335)) {
 x_336 = lean_alloc_ctor(0, 2, 0);
} else {
 x_336 = x_335;
}
lean_ctor_set(x_336, 0, x_7);
lean_ctor_set(x_336, 1, x_334);
return x_336;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_337 = lean_ctor_get(x_333, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_333, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_339 = x_333;
} else {
 lean_dec_ref(x_333);
 x_339 = lean_box(0);
}
if (lean_is_scalar(x_339)) {
 x_340 = lean_alloc_ctor(1, 2, 0);
} else {
 x_340 = x_339;
}
lean_ctor_set(x_340, 0, x_337);
lean_ctor_set(x_340, 1, x_338);
return x_340;
}
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_dec(x_6);
lean_dec(x_1);
x_341 = lean_ctor_get(x_329, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_329, 1);
lean_inc(x_342);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 x_343 = x_329;
} else {
 lean_dec_ref(x_329);
 x_343 = lean_box(0);
}
if (lean_is_scalar(x_343)) {
 x_344 = lean_alloc_ctor(1, 2, 0);
} else {
 x_344 = x_343;
}
lean_ctor_set(x_344, 0, x_341);
lean_ctor_set(x_344, 1, x_342);
return x_344;
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_dec(x_6);
lean_dec(x_1);
x_345 = lean_ctor_get(x_320, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_320, 1);
lean_inc(x_346);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 x_347 = x_320;
} else {
 lean_dec_ref(x_320);
 x_347 = lean_box(0);
}
if (lean_is_scalar(x_347)) {
 x_348 = lean_alloc_ctor(1, 2, 0);
} else {
 x_348 = x_347;
}
lean_ctor_set(x_348, 0, x_345);
lean_ctor_set(x_348, 1, x_346);
return x_348;
}
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_349 = lean_ctor_get(x_311, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_311, 1);
lean_inc(x_350);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 x_351 = x_311;
} else {
 lean_dec_ref(x_311);
 x_351 = lean_box(0);
}
if (lean_is_scalar(x_351)) {
 x_352 = lean_alloc_ctor(1, 2, 0);
} else {
 x_352 = x_351;
}
lean_ctor_set(x_352, 0, x_349);
lean_ctor_set(x_352, 1, x_350);
return x_352;
}
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_353 = lean_ctor_get(x_303, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_303, 1);
lean_inc(x_354);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 x_355 = x_303;
} else {
 lean_dec_ref(x_303);
 x_355 = lean_box(0);
}
if (lean_is_scalar(x_355)) {
 x_356 = lean_alloc_ctor(1, 2, 0);
} else {
 x_356 = x_355;
}
lean_ctor_set(x_356, 0, x_353);
lean_ctor_set(x_356, 1, x_354);
return x_356;
}
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_357 = lean_ctor_get(x_295, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_295, 1);
lean_inc(x_358);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 x_359 = x_295;
} else {
 lean_dec_ref(x_295);
 x_359 = lean_box(0);
}
if (lean_is_scalar(x_359)) {
 x_360 = lean_alloc_ctor(1, 2, 0);
} else {
 x_360 = x_359;
}
lean_ctor_set(x_360, 0, x_357);
lean_ctor_set(x_360, 1, x_358);
return x_360;
}
}
}
else
{
uint8_t x_361; 
lean_dec(x_38);
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_361 = !lean_is_exclusive(x_43);
if (x_361 == 0)
{
return x_43;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_ctor_get(x_43, 0);
x_363 = lean_ctor_get(x_43, 1);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_43);
x_364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set(x_364, 1, x_363);
return x_364;
}
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_365 = lean_ctor_get(x_35, 1);
lean_inc(x_365);
lean_dec(x_35);
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_7);
lean_ctor_set(x_366, 1, x_365);
x_367 = l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4(x_30);
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = l_Nat_repr(x_368);
x_370 = l_Lean_Environment_displayStats___closed__4;
x_371 = lean_string_append(x_370, x_369);
lean_dec(x_369);
x_372 = l_IO_println___at_HasRepr_HasEval___spec__1(x_371, x_366);
lean_dec(x_371);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_373 = lean_ctor_get(x_372, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 x_374 = x_372;
} else {
 lean_dec_ref(x_372);
 x_374 = lean_box(0);
}
if (lean_is_scalar(x_374)) {
 x_375 = lean_alloc_ctor(0, 2, 0);
} else {
 x_375 = x_374;
}
lean_ctor_set(x_375, 0, x_7);
lean_ctor_set(x_375, 1, x_373);
x_376 = lean_ctor_get(x_367, 1);
lean_inc(x_376);
lean_dec(x_367);
x_377 = l_Nat_repr(x_376);
x_378 = l_Lean_Environment_displayStats___closed__5;
x_379 = lean_string_append(x_378, x_377);
lean_dec(x_377);
x_380 = l_IO_println___at_HasRepr_HasEval___spec__1(x_379, x_375);
lean_dec(x_379);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_381 = lean_ctor_get(x_380, 1);
lean_inc(x_381);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_382 = x_380;
} else {
 lean_dec_ref(x_380);
 x_382 = lean_box(0);
}
if (lean_is_scalar(x_382)) {
 x_383 = lean_alloc_ctor(0, 2, 0);
} else {
 x_383 = x_382;
}
lean_ctor_set(x_383, 0, x_7);
lean_ctor_set(x_383, 1, x_381);
x_384 = l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(x_30);
x_385 = l_Nat_repr(x_384);
x_386 = l_Lean_Environment_displayStats___closed__6;
x_387 = lean_string_append(x_386, x_385);
lean_dec(x_385);
x_388 = l_IO_println___at_HasRepr_HasEval___spec__1(x_387, x_383);
lean_dec(x_387);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_389 = lean_ctor_get(x_388, 1);
lean_inc(x_389);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 lean_ctor_release(x_388, 1);
 x_390 = x_388;
} else {
 lean_dec_ref(x_388);
 x_390 = lean_box(0);
}
if (lean_is_scalar(x_390)) {
 x_391 = lean_alloc_ctor(0, 2, 0);
} else {
 x_391 = x_390;
}
lean_ctor_set(x_391, 0, x_7);
lean_ctor_set(x_391, 1, x_389);
x_392 = l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(x_30);
lean_dec(x_30);
x_393 = l_Nat_repr(x_392);
x_394 = l_Lean_Environment_displayStats___closed__7;
x_395 = lean_string_append(x_394, x_393);
lean_dec(x_393);
x_396 = l_IO_println___at_HasRepr_HasEval___spec__1(x_395, x_391);
lean_dec(x_395);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; uint32_t x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_397 = lean_ctor_get(x_396, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 x_398 = x_396;
} else {
 lean_dec_ref(x_396);
 x_398 = lean_box(0);
}
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(0, 2, 0);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_7);
lean_ctor_set(x_399, 1, x_397);
x_400 = lean_ctor_get_uint32(x_15, sizeof(void*)*2);
lean_dec(x_15);
x_401 = lean_uint32_to_nat(x_400);
x_402 = l_Nat_repr(x_401);
x_403 = l_Lean_Environment_displayStats___closed__8;
x_404 = lean_string_append(x_403, x_402);
lean_dec(x_402);
x_405 = l_IO_println___at_HasRepr_HasEval___spec__1(x_404, x_399);
lean_dec(x_404);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_406 = lean_ctor_get(x_405, 1);
lean_inc(x_406);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 x_407 = x_405;
} else {
 lean_dec_ref(x_405);
 x_407 = lean_box(0);
}
if (lean_is_scalar(x_407)) {
 x_408 = lean_alloc_ctor(0, 2, 0);
} else {
 x_408 = x_407;
}
lean_ctor_set(x_408, 0, x_7);
lean_ctor_set(x_408, 1, x_406);
x_409 = lean_ctor_get(x_1, 2);
lean_inc(x_409);
x_410 = lean_array_get_size(x_409);
lean_dec(x_409);
x_411 = l_Nat_repr(x_410);
x_412 = l_Lean_Environment_displayStats___closed__9;
x_413 = lean_string_append(x_412, x_411);
lean_dec(x_411);
x_414 = l_IO_println___at_HasRepr_HasEval___spec__1(x_413, x_408);
lean_dec(x_413);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_415 = lean_ctor_get(x_414, 1);
lean_inc(x_415);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_416 = x_414;
} else {
 lean_dec_ref(x_414);
 x_416 = lean_box(0);
}
if (lean_is_scalar(x_416)) {
 x_417 = lean_alloc_ctor(0, 2, 0);
} else {
 x_417 = x_416;
}
lean_ctor_set(x_417, 0, x_7);
lean_ctor_set(x_417, 1, x_415);
x_418 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10(x_1, x_6, x_9, x_417);
lean_dec(x_6);
lean_dec(x_1);
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_419 = lean_ctor_get(x_418, 1);
lean_inc(x_419);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 lean_ctor_release(x_418, 1);
 x_420 = x_418;
} else {
 lean_dec_ref(x_418);
 x_420 = lean_box(0);
}
if (lean_is_scalar(x_420)) {
 x_421 = lean_alloc_ctor(0, 2, 0);
} else {
 x_421 = x_420;
}
lean_ctor_set(x_421, 0, x_7);
lean_ctor_set(x_421, 1, x_419);
return x_421;
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_422 = lean_ctor_get(x_418, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_418, 1);
lean_inc(x_423);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 lean_ctor_release(x_418, 1);
 x_424 = x_418;
} else {
 lean_dec_ref(x_418);
 x_424 = lean_box(0);
}
if (lean_is_scalar(x_424)) {
 x_425 = lean_alloc_ctor(1, 2, 0);
} else {
 x_425 = x_424;
}
lean_ctor_set(x_425, 0, x_422);
lean_ctor_set(x_425, 1, x_423);
return x_425;
}
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
lean_dec(x_6);
lean_dec(x_1);
x_426 = lean_ctor_get(x_414, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_414, 1);
lean_inc(x_427);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_428 = x_414;
} else {
 lean_dec_ref(x_414);
 x_428 = lean_box(0);
}
if (lean_is_scalar(x_428)) {
 x_429 = lean_alloc_ctor(1, 2, 0);
} else {
 x_429 = x_428;
}
lean_ctor_set(x_429, 0, x_426);
lean_ctor_set(x_429, 1, x_427);
return x_429;
}
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
lean_dec(x_6);
lean_dec(x_1);
x_430 = lean_ctor_get(x_405, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_405, 1);
lean_inc(x_431);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 x_432 = x_405;
} else {
 lean_dec_ref(x_405);
 x_432 = lean_box(0);
}
if (lean_is_scalar(x_432)) {
 x_433 = lean_alloc_ctor(1, 2, 0);
} else {
 x_433 = x_432;
}
lean_ctor_set(x_433, 0, x_430);
lean_ctor_set(x_433, 1, x_431);
return x_433;
}
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_434 = lean_ctor_get(x_396, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_396, 1);
lean_inc(x_435);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 x_436 = x_396;
} else {
 lean_dec_ref(x_396);
 x_436 = lean_box(0);
}
if (lean_is_scalar(x_436)) {
 x_437 = lean_alloc_ctor(1, 2, 0);
} else {
 x_437 = x_436;
}
lean_ctor_set(x_437, 0, x_434);
lean_ctor_set(x_437, 1, x_435);
return x_437;
}
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_438 = lean_ctor_get(x_388, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_388, 1);
lean_inc(x_439);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 lean_ctor_release(x_388, 1);
 x_440 = x_388;
} else {
 lean_dec_ref(x_388);
 x_440 = lean_box(0);
}
if (lean_is_scalar(x_440)) {
 x_441 = lean_alloc_ctor(1, 2, 0);
} else {
 x_441 = x_440;
}
lean_ctor_set(x_441, 0, x_438);
lean_ctor_set(x_441, 1, x_439);
return x_441;
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_442 = lean_ctor_get(x_380, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_380, 1);
lean_inc(x_443);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_444 = x_380;
} else {
 lean_dec_ref(x_380);
 x_444 = lean_box(0);
}
if (lean_is_scalar(x_444)) {
 x_445 = lean_alloc_ctor(1, 2, 0);
} else {
 x_445 = x_444;
}
lean_ctor_set(x_445, 0, x_442);
lean_ctor_set(x_445, 1, x_443);
return x_445;
}
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_367);
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_446 = lean_ctor_get(x_372, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_372, 1);
lean_inc(x_447);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 x_448 = x_372;
} else {
 lean_dec_ref(x_372);
 x_448 = lean_box(0);
}
if (lean_is_scalar(x_448)) {
 x_449 = lean_alloc_ctor(1, 2, 0);
} else {
 x_449 = x_448;
}
lean_ctor_set(x_449, 0, x_446);
lean_ctor_set(x_449, 1, x_447);
return x_449;
}
}
}
else
{
uint8_t x_450; 
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_450 = !lean_is_exclusive(x_35);
if (x_450 == 0)
{
return x_35;
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_451 = lean_ctor_get(x_35, 0);
x_452 = lean_ctor_get(x_35, 1);
lean_inc(x_452);
lean_inc(x_451);
lean_dec(x_35);
x_453 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_453, 0, x_451);
lean_ctor_set(x_453, 1, x_452);
return x_453;
}
}
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_454 = lean_ctor_get(x_27, 1);
lean_inc(x_454);
lean_dec(x_27);
x_455 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_455, 0, x_7);
lean_ctor_set(x_455, 1, x_454);
x_456 = lean_ctor_get(x_1, 1);
lean_inc(x_456);
x_457 = l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3(x_456);
x_458 = l_Nat_repr(x_457);
x_459 = l_Lean_Environment_displayStats___closed__3;
x_460 = lean_string_append(x_459, x_458);
lean_dec(x_458);
x_461 = l_IO_println___at_HasRepr_HasEval___spec__1(x_460, x_455);
lean_dec(x_460);
if (lean_obj_tag(x_461) == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_462 = lean_ctor_get(x_461, 1);
lean_inc(x_462);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 lean_ctor_release(x_461, 1);
 x_463 = x_461;
} else {
 lean_dec_ref(x_461);
 x_463 = lean_box(0);
}
if (lean_is_scalar(x_463)) {
 x_464 = lean_alloc_ctor(0, 2, 0);
} else {
 x_464 = x_463;
}
lean_ctor_set(x_464, 0, x_7);
lean_ctor_set(x_464, 1, x_462);
x_465 = l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4(x_456);
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
x_467 = l_Nat_repr(x_466);
x_468 = l_Lean_Environment_displayStats___closed__4;
x_469 = lean_string_append(x_468, x_467);
lean_dec(x_467);
x_470 = l_IO_println___at_HasRepr_HasEval___spec__1(x_469, x_464);
lean_dec(x_469);
if (lean_obj_tag(x_470) == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_471 = lean_ctor_get(x_470, 1);
lean_inc(x_471);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 x_472 = x_470;
} else {
 lean_dec_ref(x_470);
 x_472 = lean_box(0);
}
if (lean_is_scalar(x_472)) {
 x_473 = lean_alloc_ctor(0, 2, 0);
} else {
 x_473 = x_472;
}
lean_ctor_set(x_473, 0, x_7);
lean_ctor_set(x_473, 1, x_471);
x_474 = lean_ctor_get(x_465, 1);
lean_inc(x_474);
lean_dec(x_465);
x_475 = l_Nat_repr(x_474);
x_476 = l_Lean_Environment_displayStats___closed__5;
x_477 = lean_string_append(x_476, x_475);
lean_dec(x_475);
x_478 = l_IO_println___at_HasRepr_HasEval___spec__1(x_477, x_473);
lean_dec(x_477);
if (lean_obj_tag(x_478) == 0)
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_479 = lean_ctor_get(x_478, 1);
lean_inc(x_479);
if (lean_is_exclusive(x_478)) {
 lean_ctor_release(x_478, 0);
 lean_ctor_release(x_478, 1);
 x_480 = x_478;
} else {
 lean_dec_ref(x_478);
 x_480 = lean_box(0);
}
if (lean_is_scalar(x_480)) {
 x_481 = lean_alloc_ctor(0, 2, 0);
} else {
 x_481 = x_480;
}
lean_ctor_set(x_481, 0, x_7);
lean_ctor_set(x_481, 1, x_479);
x_482 = l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(x_456);
x_483 = l_Nat_repr(x_482);
x_484 = l_Lean_Environment_displayStats___closed__6;
x_485 = lean_string_append(x_484, x_483);
lean_dec(x_483);
x_486 = l_IO_println___at_HasRepr_HasEval___spec__1(x_485, x_481);
lean_dec(x_485);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_487 = lean_ctor_get(x_486, 1);
lean_inc(x_487);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 x_488 = x_486;
} else {
 lean_dec_ref(x_486);
 x_488 = lean_box(0);
}
if (lean_is_scalar(x_488)) {
 x_489 = lean_alloc_ctor(0, 2, 0);
} else {
 x_489 = x_488;
}
lean_ctor_set(x_489, 0, x_7);
lean_ctor_set(x_489, 1, x_487);
x_490 = l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(x_456);
lean_dec(x_456);
x_491 = l_Nat_repr(x_490);
x_492 = l_Lean_Environment_displayStats___closed__7;
x_493 = lean_string_append(x_492, x_491);
lean_dec(x_491);
x_494 = l_IO_println___at_HasRepr_HasEval___spec__1(x_493, x_489);
lean_dec(x_493);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; uint32_t x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_495 = lean_ctor_get(x_494, 1);
lean_inc(x_495);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 lean_ctor_release(x_494, 1);
 x_496 = x_494;
} else {
 lean_dec_ref(x_494);
 x_496 = lean_box(0);
}
if (lean_is_scalar(x_496)) {
 x_497 = lean_alloc_ctor(0, 2, 0);
} else {
 x_497 = x_496;
}
lean_ctor_set(x_497, 0, x_7);
lean_ctor_set(x_497, 1, x_495);
x_498 = lean_ctor_get_uint32(x_15, sizeof(void*)*2);
lean_dec(x_15);
x_499 = lean_uint32_to_nat(x_498);
x_500 = l_Nat_repr(x_499);
x_501 = l_Lean_Environment_displayStats___closed__8;
x_502 = lean_string_append(x_501, x_500);
lean_dec(x_500);
x_503 = l_IO_println___at_HasRepr_HasEval___spec__1(x_502, x_497);
lean_dec(x_502);
if (lean_obj_tag(x_503) == 0)
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_504 = lean_ctor_get(x_503, 1);
lean_inc(x_504);
if (lean_is_exclusive(x_503)) {
 lean_ctor_release(x_503, 0);
 lean_ctor_release(x_503, 1);
 x_505 = x_503;
} else {
 lean_dec_ref(x_503);
 x_505 = lean_box(0);
}
if (lean_is_scalar(x_505)) {
 x_506 = lean_alloc_ctor(0, 2, 0);
} else {
 x_506 = x_505;
}
lean_ctor_set(x_506, 0, x_7);
lean_ctor_set(x_506, 1, x_504);
x_507 = lean_ctor_get(x_1, 2);
lean_inc(x_507);
x_508 = lean_array_get_size(x_507);
lean_dec(x_507);
x_509 = l_Nat_repr(x_508);
x_510 = l_Lean_Environment_displayStats___closed__9;
x_511 = lean_string_append(x_510, x_509);
lean_dec(x_509);
x_512 = l_IO_println___at_HasRepr_HasEval___spec__1(x_511, x_506);
lean_dec(x_511);
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_513 = lean_ctor_get(x_512, 1);
lean_inc(x_513);
if (lean_is_exclusive(x_512)) {
 lean_ctor_release(x_512, 0);
 lean_ctor_release(x_512, 1);
 x_514 = x_512;
} else {
 lean_dec_ref(x_512);
 x_514 = lean_box(0);
}
if (lean_is_scalar(x_514)) {
 x_515 = lean_alloc_ctor(0, 2, 0);
} else {
 x_515 = x_514;
}
lean_ctor_set(x_515, 0, x_7);
lean_ctor_set(x_515, 1, x_513);
x_516 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10(x_1, x_6, x_9, x_515);
lean_dec(x_6);
lean_dec(x_1);
if (lean_obj_tag(x_516) == 0)
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_517 = lean_ctor_get(x_516, 1);
lean_inc(x_517);
if (lean_is_exclusive(x_516)) {
 lean_ctor_release(x_516, 0);
 lean_ctor_release(x_516, 1);
 x_518 = x_516;
} else {
 lean_dec_ref(x_516);
 x_518 = lean_box(0);
}
if (lean_is_scalar(x_518)) {
 x_519 = lean_alloc_ctor(0, 2, 0);
} else {
 x_519 = x_518;
}
lean_ctor_set(x_519, 0, x_7);
lean_ctor_set(x_519, 1, x_517);
return x_519;
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; 
x_520 = lean_ctor_get(x_516, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_516, 1);
lean_inc(x_521);
if (lean_is_exclusive(x_516)) {
 lean_ctor_release(x_516, 0);
 lean_ctor_release(x_516, 1);
 x_522 = x_516;
} else {
 lean_dec_ref(x_516);
 x_522 = lean_box(0);
}
if (lean_is_scalar(x_522)) {
 x_523 = lean_alloc_ctor(1, 2, 0);
} else {
 x_523 = x_522;
}
lean_ctor_set(x_523, 0, x_520);
lean_ctor_set(x_523, 1, x_521);
return x_523;
}
}
else
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; 
lean_dec(x_6);
lean_dec(x_1);
x_524 = lean_ctor_get(x_512, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_512, 1);
lean_inc(x_525);
if (lean_is_exclusive(x_512)) {
 lean_ctor_release(x_512, 0);
 lean_ctor_release(x_512, 1);
 x_526 = x_512;
} else {
 lean_dec_ref(x_512);
 x_526 = lean_box(0);
}
if (lean_is_scalar(x_526)) {
 x_527 = lean_alloc_ctor(1, 2, 0);
} else {
 x_527 = x_526;
}
lean_ctor_set(x_527, 0, x_524);
lean_ctor_set(x_527, 1, x_525);
return x_527;
}
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
lean_dec(x_6);
lean_dec(x_1);
x_528 = lean_ctor_get(x_503, 0);
lean_inc(x_528);
x_529 = lean_ctor_get(x_503, 1);
lean_inc(x_529);
if (lean_is_exclusive(x_503)) {
 lean_ctor_release(x_503, 0);
 lean_ctor_release(x_503, 1);
 x_530 = x_503;
} else {
 lean_dec_ref(x_503);
 x_530 = lean_box(0);
}
if (lean_is_scalar(x_530)) {
 x_531 = lean_alloc_ctor(1, 2, 0);
} else {
 x_531 = x_530;
}
lean_ctor_set(x_531, 0, x_528);
lean_ctor_set(x_531, 1, x_529);
return x_531;
}
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_532 = lean_ctor_get(x_494, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_494, 1);
lean_inc(x_533);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 lean_ctor_release(x_494, 1);
 x_534 = x_494;
} else {
 lean_dec_ref(x_494);
 x_534 = lean_box(0);
}
if (lean_is_scalar(x_534)) {
 x_535 = lean_alloc_ctor(1, 2, 0);
} else {
 x_535 = x_534;
}
lean_ctor_set(x_535, 0, x_532);
lean_ctor_set(x_535, 1, x_533);
return x_535;
}
}
else
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
lean_dec(x_456);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_536 = lean_ctor_get(x_486, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_486, 1);
lean_inc(x_537);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 x_538 = x_486;
} else {
 lean_dec_ref(x_486);
 x_538 = lean_box(0);
}
if (lean_is_scalar(x_538)) {
 x_539 = lean_alloc_ctor(1, 2, 0);
} else {
 x_539 = x_538;
}
lean_ctor_set(x_539, 0, x_536);
lean_ctor_set(x_539, 1, x_537);
return x_539;
}
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; 
lean_dec(x_456);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_540 = lean_ctor_get(x_478, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_478, 1);
lean_inc(x_541);
if (lean_is_exclusive(x_478)) {
 lean_ctor_release(x_478, 0);
 lean_ctor_release(x_478, 1);
 x_542 = x_478;
} else {
 lean_dec_ref(x_478);
 x_542 = lean_box(0);
}
if (lean_is_scalar(x_542)) {
 x_543 = lean_alloc_ctor(1, 2, 0);
} else {
 x_543 = x_542;
}
lean_ctor_set(x_543, 0, x_540);
lean_ctor_set(x_543, 1, x_541);
return x_543;
}
}
else
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; 
lean_dec(x_465);
lean_dec(x_456);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_544 = lean_ctor_get(x_470, 0);
lean_inc(x_544);
x_545 = lean_ctor_get(x_470, 1);
lean_inc(x_545);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 x_546 = x_470;
} else {
 lean_dec_ref(x_470);
 x_546 = lean_box(0);
}
if (lean_is_scalar(x_546)) {
 x_547 = lean_alloc_ctor(1, 2, 0);
} else {
 x_547 = x_546;
}
lean_ctor_set(x_547, 0, x_544);
lean_ctor_set(x_547, 1, x_545);
return x_547;
}
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; 
lean_dec(x_456);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_548 = lean_ctor_get(x_461, 0);
lean_inc(x_548);
x_549 = lean_ctor_get(x_461, 1);
lean_inc(x_549);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 lean_ctor_release(x_461, 1);
 x_550 = x_461;
} else {
 lean_dec_ref(x_461);
 x_550 = lean_box(0);
}
if (lean_is_scalar(x_550)) {
 x_551 = lean_alloc_ctor(1, 2, 0);
} else {
 x_551 = x_550;
}
lean_ctor_set(x_551, 0, x_548);
lean_ctor_set(x_551, 1, x_549);
return x_551;
}
}
}
else
{
uint8_t x_552; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_552 = !lean_is_exclusive(x_27);
if (x_552 == 0)
{
return x_27;
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_553 = lean_ctor_get(x_27, 0);
x_554 = lean_ctor_get(x_27, 1);
lean_inc(x_554);
lean_inc(x_553);
lean_dec(x_27);
x_555 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_555, 0, x_553);
lean_ctor_set(x_555, 1, x_554);
return x_555;
}
}
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; 
x_556 = lean_ctor_get(x_21, 1);
lean_inc(x_556);
lean_dec(x_21);
x_557 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_557, 0, x_7);
lean_ctor_set(x_557, 1, x_556);
x_558 = l_Nat_repr(x_14);
x_559 = l_Lean_Environment_displayStats___closed__2;
x_560 = lean_string_append(x_559, x_558);
lean_dec(x_558);
x_561 = l_IO_println___at_HasRepr_HasEval___spec__1(x_560, x_557);
lean_dec(x_560);
if (lean_obj_tag(x_561) == 0)
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; 
x_562 = lean_ctor_get(x_561, 1);
lean_inc(x_562);
if (lean_is_exclusive(x_561)) {
 lean_ctor_release(x_561, 0);
 lean_ctor_release(x_561, 1);
 x_563 = x_561;
} else {
 lean_dec_ref(x_561);
 x_563 = lean_box(0);
}
if (lean_is_scalar(x_563)) {
 x_564 = lean_alloc_ctor(0, 2, 0);
} else {
 x_564 = x_563;
}
lean_ctor_set(x_564, 0, x_7);
lean_ctor_set(x_564, 1, x_562);
x_565 = lean_ctor_get(x_1, 1);
lean_inc(x_565);
x_566 = l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3(x_565);
x_567 = l_Nat_repr(x_566);
x_568 = l_Lean_Environment_displayStats___closed__3;
x_569 = lean_string_append(x_568, x_567);
lean_dec(x_567);
x_570 = l_IO_println___at_HasRepr_HasEval___spec__1(x_569, x_564);
lean_dec(x_569);
if (lean_obj_tag(x_570) == 0)
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; 
x_571 = lean_ctor_get(x_570, 1);
lean_inc(x_571);
if (lean_is_exclusive(x_570)) {
 lean_ctor_release(x_570, 0);
 lean_ctor_release(x_570, 1);
 x_572 = x_570;
} else {
 lean_dec_ref(x_570);
 x_572 = lean_box(0);
}
if (lean_is_scalar(x_572)) {
 x_573 = lean_alloc_ctor(0, 2, 0);
} else {
 x_573 = x_572;
}
lean_ctor_set(x_573, 0, x_7);
lean_ctor_set(x_573, 1, x_571);
x_574 = l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4(x_565);
x_575 = lean_ctor_get(x_574, 0);
lean_inc(x_575);
x_576 = l_Nat_repr(x_575);
x_577 = l_Lean_Environment_displayStats___closed__4;
x_578 = lean_string_append(x_577, x_576);
lean_dec(x_576);
x_579 = l_IO_println___at_HasRepr_HasEval___spec__1(x_578, x_573);
lean_dec(x_578);
if (lean_obj_tag(x_579) == 0)
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_580 = lean_ctor_get(x_579, 1);
lean_inc(x_580);
if (lean_is_exclusive(x_579)) {
 lean_ctor_release(x_579, 0);
 lean_ctor_release(x_579, 1);
 x_581 = x_579;
} else {
 lean_dec_ref(x_579);
 x_581 = lean_box(0);
}
if (lean_is_scalar(x_581)) {
 x_582 = lean_alloc_ctor(0, 2, 0);
} else {
 x_582 = x_581;
}
lean_ctor_set(x_582, 0, x_7);
lean_ctor_set(x_582, 1, x_580);
x_583 = lean_ctor_get(x_574, 1);
lean_inc(x_583);
lean_dec(x_574);
x_584 = l_Nat_repr(x_583);
x_585 = l_Lean_Environment_displayStats___closed__5;
x_586 = lean_string_append(x_585, x_584);
lean_dec(x_584);
x_587 = l_IO_println___at_HasRepr_HasEval___spec__1(x_586, x_582);
lean_dec(x_586);
if (lean_obj_tag(x_587) == 0)
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
x_588 = lean_ctor_get(x_587, 1);
lean_inc(x_588);
if (lean_is_exclusive(x_587)) {
 lean_ctor_release(x_587, 0);
 lean_ctor_release(x_587, 1);
 x_589 = x_587;
} else {
 lean_dec_ref(x_587);
 x_589 = lean_box(0);
}
if (lean_is_scalar(x_589)) {
 x_590 = lean_alloc_ctor(0, 2, 0);
} else {
 x_590 = x_589;
}
lean_ctor_set(x_590, 0, x_7);
lean_ctor_set(x_590, 1, x_588);
x_591 = l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(x_565);
x_592 = l_Nat_repr(x_591);
x_593 = l_Lean_Environment_displayStats___closed__6;
x_594 = lean_string_append(x_593, x_592);
lean_dec(x_592);
x_595 = l_IO_println___at_HasRepr_HasEval___spec__1(x_594, x_590);
lean_dec(x_594);
if (lean_obj_tag(x_595) == 0)
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_596 = lean_ctor_get(x_595, 1);
lean_inc(x_596);
if (lean_is_exclusive(x_595)) {
 lean_ctor_release(x_595, 0);
 lean_ctor_release(x_595, 1);
 x_597 = x_595;
} else {
 lean_dec_ref(x_595);
 x_597 = lean_box(0);
}
if (lean_is_scalar(x_597)) {
 x_598 = lean_alloc_ctor(0, 2, 0);
} else {
 x_598 = x_597;
}
lean_ctor_set(x_598, 0, x_7);
lean_ctor_set(x_598, 1, x_596);
x_599 = l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(x_565);
lean_dec(x_565);
x_600 = l_Nat_repr(x_599);
x_601 = l_Lean_Environment_displayStats___closed__7;
x_602 = lean_string_append(x_601, x_600);
lean_dec(x_600);
x_603 = l_IO_println___at_HasRepr_HasEval___spec__1(x_602, x_598);
lean_dec(x_602);
if (lean_obj_tag(x_603) == 0)
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; uint32_t x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; 
x_604 = lean_ctor_get(x_603, 1);
lean_inc(x_604);
if (lean_is_exclusive(x_603)) {
 lean_ctor_release(x_603, 0);
 lean_ctor_release(x_603, 1);
 x_605 = x_603;
} else {
 lean_dec_ref(x_603);
 x_605 = lean_box(0);
}
if (lean_is_scalar(x_605)) {
 x_606 = lean_alloc_ctor(0, 2, 0);
} else {
 x_606 = x_605;
}
lean_ctor_set(x_606, 0, x_7);
lean_ctor_set(x_606, 1, x_604);
x_607 = lean_ctor_get_uint32(x_15, sizeof(void*)*2);
lean_dec(x_15);
x_608 = lean_uint32_to_nat(x_607);
x_609 = l_Nat_repr(x_608);
x_610 = l_Lean_Environment_displayStats___closed__8;
x_611 = lean_string_append(x_610, x_609);
lean_dec(x_609);
x_612 = l_IO_println___at_HasRepr_HasEval___spec__1(x_611, x_606);
lean_dec(x_611);
if (lean_obj_tag(x_612) == 0)
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; 
x_613 = lean_ctor_get(x_612, 1);
lean_inc(x_613);
if (lean_is_exclusive(x_612)) {
 lean_ctor_release(x_612, 0);
 lean_ctor_release(x_612, 1);
 x_614 = x_612;
} else {
 lean_dec_ref(x_612);
 x_614 = lean_box(0);
}
if (lean_is_scalar(x_614)) {
 x_615 = lean_alloc_ctor(0, 2, 0);
} else {
 x_615 = x_614;
}
lean_ctor_set(x_615, 0, x_7);
lean_ctor_set(x_615, 1, x_613);
x_616 = lean_ctor_get(x_1, 2);
lean_inc(x_616);
x_617 = lean_array_get_size(x_616);
lean_dec(x_616);
x_618 = l_Nat_repr(x_617);
x_619 = l_Lean_Environment_displayStats___closed__9;
x_620 = lean_string_append(x_619, x_618);
lean_dec(x_618);
x_621 = l_IO_println___at_HasRepr_HasEval___spec__1(x_620, x_615);
lean_dec(x_620);
if (lean_obj_tag(x_621) == 0)
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
x_622 = lean_ctor_get(x_621, 1);
lean_inc(x_622);
if (lean_is_exclusive(x_621)) {
 lean_ctor_release(x_621, 0);
 lean_ctor_release(x_621, 1);
 x_623 = x_621;
} else {
 lean_dec_ref(x_621);
 x_623 = lean_box(0);
}
if (lean_is_scalar(x_623)) {
 x_624 = lean_alloc_ctor(0, 2, 0);
} else {
 x_624 = x_623;
}
lean_ctor_set(x_624, 0, x_7);
lean_ctor_set(x_624, 1, x_622);
x_625 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10(x_1, x_6, x_9, x_624);
lean_dec(x_6);
lean_dec(x_1);
if (lean_obj_tag(x_625) == 0)
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; 
x_626 = lean_ctor_get(x_625, 1);
lean_inc(x_626);
if (lean_is_exclusive(x_625)) {
 lean_ctor_release(x_625, 0);
 lean_ctor_release(x_625, 1);
 x_627 = x_625;
} else {
 lean_dec_ref(x_625);
 x_627 = lean_box(0);
}
if (lean_is_scalar(x_627)) {
 x_628 = lean_alloc_ctor(0, 2, 0);
} else {
 x_628 = x_627;
}
lean_ctor_set(x_628, 0, x_7);
lean_ctor_set(x_628, 1, x_626);
return x_628;
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
x_629 = lean_ctor_get(x_625, 0);
lean_inc(x_629);
x_630 = lean_ctor_get(x_625, 1);
lean_inc(x_630);
if (lean_is_exclusive(x_625)) {
 lean_ctor_release(x_625, 0);
 lean_ctor_release(x_625, 1);
 x_631 = x_625;
} else {
 lean_dec_ref(x_625);
 x_631 = lean_box(0);
}
if (lean_is_scalar(x_631)) {
 x_632 = lean_alloc_ctor(1, 2, 0);
} else {
 x_632 = x_631;
}
lean_ctor_set(x_632, 0, x_629);
lean_ctor_set(x_632, 1, x_630);
return x_632;
}
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; 
lean_dec(x_6);
lean_dec(x_1);
x_633 = lean_ctor_get(x_621, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_621, 1);
lean_inc(x_634);
if (lean_is_exclusive(x_621)) {
 lean_ctor_release(x_621, 0);
 lean_ctor_release(x_621, 1);
 x_635 = x_621;
} else {
 lean_dec_ref(x_621);
 x_635 = lean_box(0);
}
if (lean_is_scalar(x_635)) {
 x_636 = lean_alloc_ctor(1, 2, 0);
} else {
 x_636 = x_635;
}
lean_ctor_set(x_636, 0, x_633);
lean_ctor_set(x_636, 1, x_634);
return x_636;
}
}
else
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; 
lean_dec(x_6);
lean_dec(x_1);
x_637 = lean_ctor_get(x_612, 0);
lean_inc(x_637);
x_638 = lean_ctor_get(x_612, 1);
lean_inc(x_638);
if (lean_is_exclusive(x_612)) {
 lean_ctor_release(x_612, 0);
 lean_ctor_release(x_612, 1);
 x_639 = x_612;
} else {
 lean_dec_ref(x_612);
 x_639 = lean_box(0);
}
if (lean_is_scalar(x_639)) {
 x_640 = lean_alloc_ctor(1, 2, 0);
} else {
 x_640 = x_639;
}
lean_ctor_set(x_640, 0, x_637);
lean_ctor_set(x_640, 1, x_638);
return x_640;
}
}
else
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_641 = lean_ctor_get(x_603, 0);
lean_inc(x_641);
x_642 = lean_ctor_get(x_603, 1);
lean_inc(x_642);
if (lean_is_exclusive(x_603)) {
 lean_ctor_release(x_603, 0);
 lean_ctor_release(x_603, 1);
 x_643 = x_603;
} else {
 lean_dec_ref(x_603);
 x_643 = lean_box(0);
}
if (lean_is_scalar(x_643)) {
 x_644 = lean_alloc_ctor(1, 2, 0);
} else {
 x_644 = x_643;
}
lean_ctor_set(x_644, 0, x_641);
lean_ctor_set(x_644, 1, x_642);
return x_644;
}
}
else
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
lean_dec(x_565);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_645 = lean_ctor_get(x_595, 0);
lean_inc(x_645);
x_646 = lean_ctor_get(x_595, 1);
lean_inc(x_646);
if (lean_is_exclusive(x_595)) {
 lean_ctor_release(x_595, 0);
 lean_ctor_release(x_595, 1);
 x_647 = x_595;
} else {
 lean_dec_ref(x_595);
 x_647 = lean_box(0);
}
if (lean_is_scalar(x_647)) {
 x_648 = lean_alloc_ctor(1, 2, 0);
} else {
 x_648 = x_647;
}
lean_ctor_set(x_648, 0, x_645);
lean_ctor_set(x_648, 1, x_646);
return x_648;
}
}
else
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; 
lean_dec(x_565);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_649 = lean_ctor_get(x_587, 0);
lean_inc(x_649);
x_650 = lean_ctor_get(x_587, 1);
lean_inc(x_650);
if (lean_is_exclusive(x_587)) {
 lean_ctor_release(x_587, 0);
 lean_ctor_release(x_587, 1);
 x_651 = x_587;
} else {
 lean_dec_ref(x_587);
 x_651 = lean_box(0);
}
if (lean_is_scalar(x_651)) {
 x_652 = lean_alloc_ctor(1, 2, 0);
} else {
 x_652 = x_651;
}
lean_ctor_set(x_652, 0, x_649);
lean_ctor_set(x_652, 1, x_650);
return x_652;
}
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; 
lean_dec(x_574);
lean_dec(x_565);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_653 = lean_ctor_get(x_579, 0);
lean_inc(x_653);
x_654 = lean_ctor_get(x_579, 1);
lean_inc(x_654);
if (lean_is_exclusive(x_579)) {
 lean_ctor_release(x_579, 0);
 lean_ctor_release(x_579, 1);
 x_655 = x_579;
} else {
 lean_dec_ref(x_579);
 x_655 = lean_box(0);
}
if (lean_is_scalar(x_655)) {
 x_656 = lean_alloc_ctor(1, 2, 0);
} else {
 x_656 = x_655;
}
lean_ctor_set(x_656, 0, x_653);
lean_ctor_set(x_656, 1, x_654);
return x_656;
}
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; 
lean_dec(x_565);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_657 = lean_ctor_get(x_570, 0);
lean_inc(x_657);
x_658 = lean_ctor_get(x_570, 1);
lean_inc(x_658);
if (lean_is_exclusive(x_570)) {
 lean_ctor_release(x_570, 0);
 lean_ctor_release(x_570, 1);
 x_659 = x_570;
} else {
 lean_dec_ref(x_570);
 x_659 = lean_box(0);
}
if (lean_is_scalar(x_659)) {
 x_660 = lean_alloc_ctor(1, 2, 0);
} else {
 x_660 = x_659;
}
lean_ctor_set(x_660, 0, x_657);
lean_ctor_set(x_660, 1, x_658);
return x_660;
}
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_661 = lean_ctor_get(x_561, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_561, 1);
lean_inc(x_662);
if (lean_is_exclusive(x_561)) {
 lean_ctor_release(x_561, 0);
 lean_ctor_release(x_561, 1);
 x_663 = x_561;
} else {
 lean_dec_ref(x_561);
 x_663 = lean_box(0);
}
if (lean_is_scalar(x_663)) {
 x_664 = lean_alloc_ctor(1, 2, 0);
} else {
 x_664 = x_663;
}
lean_ctor_set(x_664, 0, x_661);
lean_ctor_set(x_664, 1, x_662);
return x_664;
}
}
}
else
{
uint8_t x_665; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_1);
x_665 = !lean_is_exclusive(x_21);
if (x_665 == 0)
{
return x_21;
}
else
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_666 = lean_ctor_get(x_21, 0);
x_667 = lean_ctor_get(x_21, 1);
lean_inc(x_667);
lean_inc(x_666);
lean_dec(x_21);
x_668 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_668, 0, x_666);
lean_ctor_set(x_668, 1, x_667);
return x_668;
}
}
}
else
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; 
x_669 = lean_ctor_get(x_4, 0);
x_670 = lean_ctor_get(x_4, 1);
lean_inc(x_670);
lean_inc(x_669);
lean_dec(x_4);
x_671 = lean_box(0);
x_672 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_672, 0, x_671);
lean_ctor_set(x_672, 1, x_670);
x_673 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_674 = lean_unsigned_to_nat(0u);
x_675 = lean_array_get(x_673, x_669, x_674);
x_676 = lean_ctor_get(x_675, 0);
lean_inc(x_676);
lean_dec(x_675);
x_677 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_676, x_1);
x_678 = lean_ctor_get(x_677, 0);
lean_inc(x_678);
lean_dec(x_677);
x_679 = lean_array_get_size(x_678);
lean_dec(x_678);
x_680 = lean_ctor_get(x_1, 3);
lean_inc(x_680);
x_681 = lean_ctor_get(x_680, 1);
lean_inc(x_681);
x_682 = l_Array_toList___rarg(x_681);
lean_dec(x_681);
x_683 = l_List_toString___at_Lean_Environment_displayStats___spec__1(x_682);
x_684 = l_Lean_Environment_displayStats___closed__1;
x_685 = lean_string_append(x_684, x_683);
lean_dec(x_683);
x_686 = l_IO_println___at_HasRepr_HasEval___spec__1(x_685, x_672);
lean_dec(x_685);
if (lean_obj_tag(x_686) == 0)
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_687 = lean_ctor_get(x_686, 1);
lean_inc(x_687);
if (lean_is_exclusive(x_686)) {
 lean_ctor_release(x_686, 0);
 lean_ctor_release(x_686, 1);
 x_688 = x_686;
} else {
 lean_dec_ref(x_686);
 x_688 = lean_box(0);
}
if (lean_is_scalar(x_688)) {
 x_689 = lean_alloc_ctor(0, 2, 0);
} else {
 x_689 = x_688;
}
lean_ctor_set(x_689, 0, x_671);
lean_ctor_set(x_689, 1, x_687);
x_690 = l_Nat_repr(x_679);
x_691 = l_Lean_Environment_displayStats___closed__2;
x_692 = lean_string_append(x_691, x_690);
lean_dec(x_690);
x_693 = l_IO_println___at_HasRepr_HasEval___spec__1(x_692, x_689);
lean_dec(x_692);
if (lean_obj_tag(x_693) == 0)
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; 
x_694 = lean_ctor_get(x_693, 1);
lean_inc(x_694);
if (lean_is_exclusive(x_693)) {
 lean_ctor_release(x_693, 0);
 lean_ctor_release(x_693, 1);
 x_695 = x_693;
} else {
 lean_dec_ref(x_693);
 x_695 = lean_box(0);
}
if (lean_is_scalar(x_695)) {
 x_696 = lean_alloc_ctor(0, 2, 0);
} else {
 x_696 = x_695;
}
lean_ctor_set(x_696, 0, x_671);
lean_ctor_set(x_696, 1, x_694);
x_697 = lean_ctor_get(x_1, 1);
lean_inc(x_697);
x_698 = l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3(x_697);
x_699 = l_Nat_repr(x_698);
x_700 = l_Lean_Environment_displayStats___closed__3;
x_701 = lean_string_append(x_700, x_699);
lean_dec(x_699);
x_702 = l_IO_println___at_HasRepr_HasEval___spec__1(x_701, x_696);
lean_dec(x_701);
if (lean_obj_tag(x_702) == 0)
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_703 = lean_ctor_get(x_702, 1);
lean_inc(x_703);
if (lean_is_exclusive(x_702)) {
 lean_ctor_release(x_702, 0);
 lean_ctor_release(x_702, 1);
 x_704 = x_702;
} else {
 lean_dec_ref(x_702);
 x_704 = lean_box(0);
}
if (lean_is_scalar(x_704)) {
 x_705 = lean_alloc_ctor(0, 2, 0);
} else {
 x_705 = x_704;
}
lean_ctor_set(x_705, 0, x_671);
lean_ctor_set(x_705, 1, x_703);
x_706 = l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4(x_697);
x_707 = lean_ctor_get(x_706, 0);
lean_inc(x_707);
x_708 = l_Nat_repr(x_707);
x_709 = l_Lean_Environment_displayStats___closed__4;
x_710 = lean_string_append(x_709, x_708);
lean_dec(x_708);
x_711 = l_IO_println___at_HasRepr_HasEval___spec__1(x_710, x_705);
lean_dec(x_710);
if (lean_obj_tag(x_711) == 0)
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; 
x_712 = lean_ctor_get(x_711, 1);
lean_inc(x_712);
if (lean_is_exclusive(x_711)) {
 lean_ctor_release(x_711, 0);
 lean_ctor_release(x_711, 1);
 x_713 = x_711;
} else {
 lean_dec_ref(x_711);
 x_713 = lean_box(0);
}
if (lean_is_scalar(x_713)) {
 x_714 = lean_alloc_ctor(0, 2, 0);
} else {
 x_714 = x_713;
}
lean_ctor_set(x_714, 0, x_671);
lean_ctor_set(x_714, 1, x_712);
x_715 = lean_ctor_get(x_706, 1);
lean_inc(x_715);
lean_dec(x_706);
x_716 = l_Nat_repr(x_715);
x_717 = l_Lean_Environment_displayStats___closed__5;
x_718 = lean_string_append(x_717, x_716);
lean_dec(x_716);
x_719 = l_IO_println___at_HasRepr_HasEval___spec__1(x_718, x_714);
lean_dec(x_718);
if (lean_obj_tag(x_719) == 0)
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; 
x_720 = lean_ctor_get(x_719, 1);
lean_inc(x_720);
if (lean_is_exclusive(x_719)) {
 lean_ctor_release(x_719, 0);
 lean_ctor_release(x_719, 1);
 x_721 = x_719;
} else {
 lean_dec_ref(x_719);
 x_721 = lean_box(0);
}
if (lean_is_scalar(x_721)) {
 x_722 = lean_alloc_ctor(0, 2, 0);
} else {
 x_722 = x_721;
}
lean_ctor_set(x_722, 0, x_671);
lean_ctor_set(x_722, 1, x_720);
x_723 = l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(x_697);
x_724 = l_Nat_repr(x_723);
x_725 = l_Lean_Environment_displayStats___closed__6;
x_726 = lean_string_append(x_725, x_724);
lean_dec(x_724);
x_727 = l_IO_println___at_HasRepr_HasEval___spec__1(x_726, x_722);
lean_dec(x_726);
if (lean_obj_tag(x_727) == 0)
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; 
x_728 = lean_ctor_get(x_727, 1);
lean_inc(x_728);
if (lean_is_exclusive(x_727)) {
 lean_ctor_release(x_727, 0);
 lean_ctor_release(x_727, 1);
 x_729 = x_727;
} else {
 lean_dec_ref(x_727);
 x_729 = lean_box(0);
}
if (lean_is_scalar(x_729)) {
 x_730 = lean_alloc_ctor(0, 2, 0);
} else {
 x_730 = x_729;
}
lean_ctor_set(x_730, 0, x_671);
lean_ctor_set(x_730, 1, x_728);
x_731 = l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(x_697);
lean_dec(x_697);
x_732 = l_Nat_repr(x_731);
x_733 = l_Lean_Environment_displayStats___closed__7;
x_734 = lean_string_append(x_733, x_732);
lean_dec(x_732);
x_735 = l_IO_println___at_HasRepr_HasEval___spec__1(x_734, x_730);
lean_dec(x_734);
if (lean_obj_tag(x_735) == 0)
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; uint32_t x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; 
x_736 = lean_ctor_get(x_735, 1);
lean_inc(x_736);
if (lean_is_exclusive(x_735)) {
 lean_ctor_release(x_735, 0);
 lean_ctor_release(x_735, 1);
 x_737 = x_735;
} else {
 lean_dec_ref(x_735);
 x_737 = lean_box(0);
}
if (lean_is_scalar(x_737)) {
 x_738 = lean_alloc_ctor(0, 2, 0);
} else {
 x_738 = x_737;
}
lean_ctor_set(x_738, 0, x_671);
lean_ctor_set(x_738, 1, x_736);
x_739 = lean_ctor_get_uint32(x_680, sizeof(void*)*2);
lean_dec(x_680);
x_740 = lean_uint32_to_nat(x_739);
x_741 = l_Nat_repr(x_740);
x_742 = l_Lean_Environment_displayStats___closed__8;
x_743 = lean_string_append(x_742, x_741);
lean_dec(x_741);
x_744 = l_IO_println___at_HasRepr_HasEval___spec__1(x_743, x_738);
lean_dec(x_743);
if (lean_obj_tag(x_744) == 0)
{
lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; 
x_745 = lean_ctor_get(x_744, 1);
lean_inc(x_745);
if (lean_is_exclusive(x_744)) {
 lean_ctor_release(x_744, 0);
 lean_ctor_release(x_744, 1);
 x_746 = x_744;
} else {
 lean_dec_ref(x_744);
 x_746 = lean_box(0);
}
if (lean_is_scalar(x_746)) {
 x_747 = lean_alloc_ctor(0, 2, 0);
} else {
 x_747 = x_746;
}
lean_ctor_set(x_747, 0, x_671);
lean_ctor_set(x_747, 1, x_745);
x_748 = lean_ctor_get(x_1, 2);
lean_inc(x_748);
x_749 = lean_array_get_size(x_748);
lean_dec(x_748);
x_750 = l_Nat_repr(x_749);
x_751 = l_Lean_Environment_displayStats___closed__9;
x_752 = lean_string_append(x_751, x_750);
lean_dec(x_750);
x_753 = l_IO_println___at_HasRepr_HasEval___spec__1(x_752, x_747);
lean_dec(x_752);
if (lean_obj_tag(x_753) == 0)
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; 
x_754 = lean_ctor_get(x_753, 1);
lean_inc(x_754);
if (lean_is_exclusive(x_753)) {
 lean_ctor_release(x_753, 0);
 lean_ctor_release(x_753, 1);
 x_755 = x_753;
} else {
 lean_dec_ref(x_753);
 x_755 = lean_box(0);
}
if (lean_is_scalar(x_755)) {
 x_756 = lean_alloc_ctor(0, 2, 0);
} else {
 x_756 = x_755;
}
lean_ctor_set(x_756, 0, x_671);
lean_ctor_set(x_756, 1, x_754);
x_757 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10(x_1, x_669, x_674, x_756);
lean_dec(x_669);
lean_dec(x_1);
if (lean_obj_tag(x_757) == 0)
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; 
x_758 = lean_ctor_get(x_757, 1);
lean_inc(x_758);
if (lean_is_exclusive(x_757)) {
 lean_ctor_release(x_757, 0);
 lean_ctor_release(x_757, 1);
 x_759 = x_757;
} else {
 lean_dec_ref(x_757);
 x_759 = lean_box(0);
}
if (lean_is_scalar(x_759)) {
 x_760 = lean_alloc_ctor(0, 2, 0);
} else {
 x_760 = x_759;
}
lean_ctor_set(x_760, 0, x_671);
lean_ctor_set(x_760, 1, x_758);
return x_760;
}
else
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; 
x_761 = lean_ctor_get(x_757, 0);
lean_inc(x_761);
x_762 = lean_ctor_get(x_757, 1);
lean_inc(x_762);
if (lean_is_exclusive(x_757)) {
 lean_ctor_release(x_757, 0);
 lean_ctor_release(x_757, 1);
 x_763 = x_757;
} else {
 lean_dec_ref(x_757);
 x_763 = lean_box(0);
}
if (lean_is_scalar(x_763)) {
 x_764 = lean_alloc_ctor(1, 2, 0);
} else {
 x_764 = x_763;
}
lean_ctor_set(x_764, 0, x_761);
lean_ctor_set(x_764, 1, x_762);
return x_764;
}
}
else
{
lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; 
lean_dec(x_669);
lean_dec(x_1);
x_765 = lean_ctor_get(x_753, 0);
lean_inc(x_765);
x_766 = lean_ctor_get(x_753, 1);
lean_inc(x_766);
if (lean_is_exclusive(x_753)) {
 lean_ctor_release(x_753, 0);
 lean_ctor_release(x_753, 1);
 x_767 = x_753;
} else {
 lean_dec_ref(x_753);
 x_767 = lean_box(0);
}
if (lean_is_scalar(x_767)) {
 x_768 = lean_alloc_ctor(1, 2, 0);
} else {
 x_768 = x_767;
}
lean_ctor_set(x_768, 0, x_765);
lean_ctor_set(x_768, 1, x_766);
return x_768;
}
}
else
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; 
lean_dec(x_669);
lean_dec(x_1);
x_769 = lean_ctor_get(x_744, 0);
lean_inc(x_769);
x_770 = lean_ctor_get(x_744, 1);
lean_inc(x_770);
if (lean_is_exclusive(x_744)) {
 lean_ctor_release(x_744, 0);
 lean_ctor_release(x_744, 1);
 x_771 = x_744;
} else {
 lean_dec_ref(x_744);
 x_771 = lean_box(0);
}
if (lean_is_scalar(x_771)) {
 x_772 = lean_alloc_ctor(1, 2, 0);
} else {
 x_772 = x_771;
}
lean_ctor_set(x_772, 0, x_769);
lean_ctor_set(x_772, 1, x_770);
return x_772;
}
}
else
{
lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; 
lean_dec(x_680);
lean_dec(x_669);
lean_dec(x_1);
x_773 = lean_ctor_get(x_735, 0);
lean_inc(x_773);
x_774 = lean_ctor_get(x_735, 1);
lean_inc(x_774);
if (lean_is_exclusive(x_735)) {
 lean_ctor_release(x_735, 0);
 lean_ctor_release(x_735, 1);
 x_775 = x_735;
} else {
 lean_dec_ref(x_735);
 x_775 = lean_box(0);
}
if (lean_is_scalar(x_775)) {
 x_776 = lean_alloc_ctor(1, 2, 0);
} else {
 x_776 = x_775;
}
lean_ctor_set(x_776, 0, x_773);
lean_ctor_set(x_776, 1, x_774);
return x_776;
}
}
else
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; 
lean_dec(x_697);
lean_dec(x_680);
lean_dec(x_669);
lean_dec(x_1);
x_777 = lean_ctor_get(x_727, 0);
lean_inc(x_777);
x_778 = lean_ctor_get(x_727, 1);
lean_inc(x_778);
if (lean_is_exclusive(x_727)) {
 lean_ctor_release(x_727, 0);
 lean_ctor_release(x_727, 1);
 x_779 = x_727;
} else {
 lean_dec_ref(x_727);
 x_779 = lean_box(0);
}
if (lean_is_scalar(x_779)) {
 x_780 = lean_alloc_ctor(1, 2, 0);
} else {
 x_780 = x_779;
}
lean_ctor_set(x_780, 0, x_777);
lean_ctor_set(x_780, 1, x_778);
return x_780;
}
}
else
{
lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; 
lean_dec(x_697);
lean_dec(x_680);
lean_dec(x_669);
lean_dec(x_1);
x_781 = lean_ctor_get(x_719, 0);
lean_inc(x_781);
x_782 = lean_ctor_get(x_719, 1);
lean_inc(x_782);
if (lean_is_exclusive(x_719)) {
 lean_ctor_release(x_719, 0);
 lean_ctor_release(x_719, 1);
 x_783 = x_719;
} else {
 lean_dec_ref(x_719);
 x_783 = lean_box(0);
}
if (lean_is_scalar(x_783)) {
 x_784 = lean_alloc_ctor(1, 2, 0);
} else {
 x_784 = x_783;
}
lean_ctor_set(x_784, 0, x_781);
lean_ctor_set(x_784, 1, x_782);
return x_784;
}
}
else
{
lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; 
lean_dec(x_706);
lean_dec(x_697);
lean_dec(x_680);
lean_dec(x_669);
lean_dec(x_1);
x_785 = lean_ctor_get(x_711, 0);
lean_inc(x_785);
x_786 = lean_ctor_get(x_711, 1);
lean_inc(x_786);
if (lean_is_exclusive(x_711)) {
 lean_ctor_release(x_711, 0);
 lean_ctor_release(x_711, 1);
 x_787 = x_711;
} else {
 lean_dec_ref(x_711);
 x_787 = lean_box(0);
}
if (lean_is_scalar(x_787)) {
 x_788 = lean_alloc_ctor(1, 2, 0);
} else {
 x_788 = x_787;
}
lean_ctor_set(x_788, 0, x_785);
lean_ctor_set(x_788, 1, x_786);
return x_788;
}
}
else
{
lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; 
lean_dec(x_697);
lean_dec(x_680);
lean_dec(x_669);
lean_dec(x_1);
x_789 = lean_ctor_get(x_702, 0);
lean_inc(x_789);
x_790 = lean_ctor_get(x_702, 1);
lean_inc(x_790);
if (lean_is_exclusive(x_702)) {
 lean_ctor_release(x_702, 0);
 lean_ctor_release(x_702, 1);
 x_791 = x_702;
} else {
 lean_dec_ref(x_702);
 x_791 = lean_box(0);
}
if (lean_is_scalar(x_791)) {
 x_792 = lean_alloc_ctor(1, 2, 0);
} else {
 x_792 = x_791;
}
lean_ctor_set(x_792, 0, x_789);
lean_ctor_set(x_792, 1, x_790);
return x_792;
}
}
else
{
lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; 
lean_dec(x_680);
lean_dec(x_669);
lean_dec(x_1);
x_793 = lean_ctor_get(x_693, 0);
lean_inc(x_793);
x_794 = lean_ctor_get(x_693, 1);
lean_inc(x_794);
if (lean_is_exclusive(x_693)) {
 lean_ctor_release(x_693, 0);
 lean_ctor_release(x_693, 1);
 x_795 = x_693;
} else {
 lean_dec_ref(x_693);
 x_795 = lean_box(0);
}
if (lean_is_scalar(x_795)) {
 x_796 = lean_alloc_ctor(1, 2, 0);
} else {
 x_796 = x_795;
}
lean_ctor_set(x_796, 0, x_793);
lean_ctor_set(x_796, 1, x_794);
return x_796;
}
}
else
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; 
lean_dec(x_680);
lean_dec(x_679);
lean_dec(x_669);
lean_dec(x_1);
x_797 = lean_ctor_get(x_686, 0);
lean_inc(x_797);
x_798 = lean_ctor_get(x_686, 1);
lean_inc(x_798);
if (lean_is_exclusive(x_686)) {
 lean_ctor_release(x_686, 0);
 lean_ctor_release(x_686, 1);
 x_799 = x_686;
} else {
 lean_dec_ref(x_686);
 x_799 = lean_box(0);
}
if (lean_is_scalar(x_799)) {
 x_800 = lean_alloc_ctor(1, 2, 0);
} else {
 x_800 = x_799;
}
lean_ctor_set(x_800, 0, x_797);
lean_ctor_set(x_800, 1, x_798);
return x_800;
}
}
}
else
{
uint8_t x_801; 
lean_dec(x_1);
x_801 = !lean_is_exclusive(x_4);
if (x_801 == 0)
{
return x_4;
}
else
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; 
x_802 = lean_ctor_get(x_4, 0);
x_803 = lean_ctor_get(x_4, 1);
lean_inc(x_803);
lean_inc(x_802);
lean_dec(x_4);
x_804 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_804, 0, x_802);
lean_ctor_set(x_804, 1, x_803);
return x_804;
}
}
}
}
lean_object* l_List_toStringAux___main___at_Lean_Environment_displayStats___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_toStringAux___main___at_Lean_Environment_displayStats___spec__2(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__6___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__6(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__8(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__9(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_init_system_io(lean_object*);
lean_object* initialize_init_util(lean_object*);
lean_object* initialize_init_data_bytearray_default(lean_object*);
lean_object* initialize_init_lean_declaration(lean_object*);
lean_object* initialize_init_lean_smap(lean_object*);
lean_object* initialize_init_lean_path(lean_object*);
lean_object* initialize_init_lean_localcontext(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_init_lean_environment(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_init_system_io(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_util(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_bytearray_default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_declaration(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_smap(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_path(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_localcontext(w);
if (lean_io_result_is_error(w)) return w;
l_Lean_EnvExtensionState_inhabited = _init_l_Lean_EnvExtensionState_inhabited();
lean_mark_persistent(l_Lean_EnvExtensionState_inhabited);
l_Lean_ModuleIdx_inhabited = _init_l_Lean_ModuleIdx_inhabited();
lean_mark_persistent(l_Lean_ModuleIdx_inhabited);
l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__1 = _init_l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__1);
l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__2 = _init_l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__2();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__2);
l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__3 = _init_l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__3();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__3);
l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__4 = _init_l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__4();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2___closed__4);
l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2 = _init_l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2);
l_Lean_Environment_Inhabited___closed__1 = _init_l_Lean_Environment_Inhabited___closed__1();
lean_mark_persistent(l_Lean_Environment_Inhabited___closed__1);
l_Lean_Environment_Inhabited___closed__2 = _init_l_Lean_Environment_Inhabited___closed__2();
lean_mark_persistent(l_Lean_Environment_Inhabited___closed__2);
l_Lean_Environment_Inhabited___closed__3 = _init_l_Lean_Environment_Inhabited___closed__3();
lean_mark_persistent(l_Lean_Environment_Inhabited___closed__3);
l_Lean_Environment_Inhabited = _init_l_Lean_Environment_Inhabited();
lean_mark_persistent(l_Lean_Environment_Inhabited);
l_Lean_EnvExtension_setState___closed__1 = _init_l_Lean_EnvExtension_setState___closed__1();
lean_mark_persistent(l_Lean_EnvExtension_setState___closed__1);
w = l___private_init_lean_environment_4__mkEnvExtensionsRef(w);
if (lean_io_result_is_error(w)) return w;
l___private_init_lean_environment_5__envExtensionsRef = lean_io_result_get_value(w);
lean_mark_persistent(l___private_init_lean_environment_5__envExtensionsRef);
l_Lean_EnvExtension_Inhabited___rarg___closed__1 = _init_l_Lean_EnvExtension_Inhabited___rarg___closed__1();
lean_mark_persistent(l_Lean_EnvExtension_Inhabited___rarg___closed__1);
l_Lean_registerEnvExtensionUnsafe___rarg___closed__1 = _init_l_Lean_registerEnvExtensionUnsafe___rarg___closed__1();
lean_mark_persistent(l_Lean_registerEnvExtensionUnsafe___rarg___closed__1);
l_Lean_registerEnvExtensionUnsafe___rarg___closed__2 = _init_l_Lean_registerEnvExtensionUnsafe___rarg___closed__2();
lean_mark_persistent(l_Lean_registerEnvExtensionUnsafe___rarg___closed__2);
l_Lean_mkEmptyEnvironment___closed__1 = _init_l_Lean_mkEmptyEnvironment___closed__1();
lean_mark_persistent(l_Lean_mkEmptyEnvironment___closed__1);
l_Lean_EnvExtensionEntry_inhabited = _init_l_Lean_EnvExtensionEntry_inhabited();
lean_mark_persistent(l_Lean_EnvExtensionEntry_inhabited);
l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1 = _init_l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1();
lean_mark_persistent(l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1);
l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2 = _init_l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2();
lean_mark_persistent(l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2);
l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3 = _init_l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3();
lean_mark_persistent(l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3);
l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4 = _init_l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4();
lean_mark_persistent(l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4);
w = l___private_init_lean_environment_7__mkPersistentEnvExtensionsRef(w);
if (lean_io_result_is_error(w)) return w;
l___private_init_lean_environment_8__persistentEnvExtensionsRef = lean_io_result_get_value(w);
lean_mark_persistent(l___private_init_lean_environment_8__persistentEnvExtensionsRef);
l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1 = _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1();
lean_mark_persistent(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1);
l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2 = _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2();
lean_mark_persistent(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2);
l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3 = _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3();
lean_mark_persistent(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3);
l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4 = _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4();
lean_mark_persistent(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4);
l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__1 = _init_l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__1();
lean_mark_persistent(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__1);
l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__2 = _init_l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__2();
lean_mark_persistent(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__2);
l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1 = _init_l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1();
lean_mark_persistent(l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1);
l_Lean_CPPExtensionState_inhabited = _init_l_Lean_CPPExtensionState_inhabited();
lean_mark_persistent(l_Lean_CPPExtensionState_inhabited);
l_Lean_Modification_inhabited = _init_l_Lean_Modification_inhabited();
lean_mark_persistent(l_Lean_Modification_inhabited);
l_Lean_registerEnvExtensionUnsafe___at_Lean_regModListExtension___spec__1___closed__1 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_regModListExtension___spec__1___closed__1();
lean_mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_regModListExtension___spec__1___closed__1);
l_Lean_regModListExtension___closed__1 = _init_l_Lean_regModListExtension___closed__1();
lean_mark_persistent(l_Lean_regModListExtension___closed__1);
l_Lean_modListExtension___closed__1 = _init_l_Lean_modListExtension___closed__1();
lean_mark_persistent(l_Lean_modListExtension___closed__1);
l_Lean_modListExtension___closed__2 = _init_l_Lean_modListExtension___closed__2();
lean_mark_persistent(l_Lean_modListExtension___closed__2);
w = l_Lean_regModListExtension(w);
if (lean_io_result_is_error(w)) return w;
l_Lean_modListExtension = lean_io_result_get_value(w);
lean_mark_persistent(l_Lean_modListExtension);
l_Lean_ModuleData_inhabited___closed__1 = _init_l_Lean_ModuleData_inhabited___closed__1();
lean_mark_persistent(l_Lean_ModuleData_inhabited___closed__1);
l_Lean_ModuleData_inhabited = _init_l_Lean_ModuleData_inhabited();
lean_mark_persistent(l_Lean_ModuleData_inhabited);
l___private_init_lean_environment_9__getEntriesFor___main___closed__1 = _init_l___private_init_lean_environment_9__getEntriesFor___main___closed__1();
lean_mark_persistent(l___private_init_lean_environment_9__getEntriesFor___main___closed__1);
l_Array_miterateAux___main___at_Lean_importModules___spec__9___closed__1 = _init_l_Array_miterateAux___main___at_Lean_importModules___spec__9___closed__1();
lean_mark_persistent(l_Array_miterateAux___main___at_Lean_importModules___spec__9___closed__1);
l_Lean_importModules___closed__1 = _init_l_Lean_importModules___closed__1();
lean_mark_persistent(l_Lean_importModules___closed__1);
l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7___closed__1 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7___closed__1();
lean_mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7___closed__1);
l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7___closed__2 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7___closed__2();
lean_mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_regNamespacesExtension___spec__7___closed__2);
l_Lean_regNamespacesExtension___closed__1 = _init_l_Lean_regNamespacesExtension___closed__1();
lean_mark_persistent(l_Lean_regNamespacesExtension___closed__1);
l_Lean_regNamespacesExtension___closed__2 = _init_l_Lean_regNamespacesExtension___closed__2();
lean_mark_persistent(l_Lean_regNamespacesExtension___closed__2);
l_Lean_regNamespacesExtension___closed__3 = _init_l_Lean_regNamespacesExtension___closed__3();
lean_mark_persistent(l_Lean_regNamespacesExtension___closed__3);
l_Lean_regNamespacesExtension___closed__4 = _init_l_Lean_regNamespacesExtension___closed__4();
lean_mark_persistent(l_Lean_regNamespacesExtension___closed__4);
l_Lean_regNamespacesExtension___closed__5 = _init_l_Lean_regNamespacesExtension___closed__5();
lean_mark_persistent(l_Lean_regNamespacesExtension___closed__5);
l_Lean_regNamespacesExtension___closed__6 = _init_l_Lean_regNamespacesExtension___closed__6();
lean_mark_persistent(l_Lean_regNamespacesExtension___closed__6);
l_Lean_namespacesExt___closed__1 = _init_l_Lean_namespacesExt___closed__1();
lean_mark_persistent(l_Lean_namespacesExt___closed__1);
l_Lean_namespacesExt___closed__2 = _init_l_Lean_namespacesExt___closed__2();
lean_mark_persistent(l_Lean_namespacesExt___closed__2);
l_Lean_namespacesExt___closed__3 = _init_l_Lean_namespacesExt___closed__3();
lean_mark_persistent(l_Lean_namespacesExt___closed__3);
l_Lean_namespacesExt___closed__4 = _init_l_Lean_namespacesExt___closed__4();
lean_mark_persistent(l_Lean_namespacesExt___closed__4);
l_Lean_namespacesExt___closed__5 = _init_l_Lean_namespacesExt___closed__5();
lean_mark_persistent(l_Lean_namespacesExt___closed__5);
l_Lean_namespacesExt___closed__6 = _init_l_Lean_namespacesExt___closed__6();
lean_mark_persistent(l_Lean_namespacesExt___closed__6);
w = l_Lean_regNamespacesExtension(w);
if (lean_io_result_is_error(w)) return w;
l_Lean_namespacesExt = lean_io_result_get_value(w);
lean_mark_persistent(l_Lean_namespacesExt);
l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__1 = _init_l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__1();
lean_mark_persistent(l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__1);
l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__2 = _init_l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__2();
lean_mark_persistent(l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__2);
l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__3 = _init_l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__3();
lean_mark_persistent(l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__3);
l_Lean_Environment_displayStats___closed__1 = _init_l_Lean_Environment_displayStats___closed__1();
lean_mark_persistent(l_Lean_Environment_displayStats___closed__1);
l_Lean_Environment_displayStats___closed__2 = _init_l_Lean_Environment_displayStats___closed__2();
lean_mark_persistent(l_Lean_Environment_displayStats___closed__2);
l_Lean_Environment_displayStats___closed__3 = _init_l_Lean_Environment_displayStats___closed__3();
lean_mark_persistent(l_Lean_Environment_displayStats___closed__3);
l_Lean_Environment_displayStats___closed__4 = _init_l_Lean_Environment_displayStats___closed__4();
lean_mark_persistent(l_Lean_Environment_displayStats___closed__4);
l_Lean_Environment_displayStats___closed__5 = _init_l_Lean_Environment_displayStats___closed__5();
lean_mark_persistent(l_Lean_Environment_displayStats___closed__5);
l_Lean_Environment_displayStats___closed__6 = _init_l_Lean_Environment_displayStats___closed__6();
lean_mark_persistent(l_Lean_Environment_displayStats___closed__6);
l_Lean_Environment_displayStats___closed__7 = _init_l_Lean_Environment_displayStats___closed__7();
lean_mark_persistent(l_Lean_Environment_displayStats___closed__7);
l_Lean_Environment_displayStats___closed__8 = _init_l_Lean_Environment_displayStats___closed__8();
lean_mark_persistent(l_Lean_Environment_displayStats___closed__8);
l_Lean_Environment_displayStats___closed__9 = _init_l_Lean_Environment_displayStats___closed__9();
lean_mark_persistent(l_Lean_Environment_displayStats___closed__9);
return w;
}
#ifdef __cplusplus
}
#endif

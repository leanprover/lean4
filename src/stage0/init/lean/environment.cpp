// Lean compiler output
// Module: init.lean.environment
// Imports: init.io init.util init.data.bytearray.default init.lean.declaration init.lean.smap
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
obj* l_Lean_EnvExtension_modifyState___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Environment_getModuleIdxFor___boxed(obj*, obj*);
obj* l_RBNode_setBlack___main___rarg(obj*);
obj* l_unsafeCast(obj*, obj*, obj*, obj*);
obj* l_Lean_EnvExtension_setStateUnsafe___rarg___boxed(obj*, obj*, obj*);
obj* l_mkHashMap___at_Lean_Environment_Inhabited___spec__1(obj*);
obj* l_Lean_ConstantInfo_name(obj*);
obj* l_Lean_PersistentEnvExtension_inhabited(obj*, obj*);
namespace lean {
obj* write_module_core(obj*, obj*, obj*);
}
obj* l_Lean_Environment_displayStats___closed__7;
obj* l_Lean_Environment_displayStats___closed__6;
obj* l_Lean_performModifications___boxed(obj*, obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__12___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_find_x27___main___at_Lean_Environment_find___spec__1___boxed(obj*, obj*);
obj* l_Lean_PersistentEnvExtension_inhabited___rarg(obj*, obj*);
obj* l_HashMapImp_find___at_Lean_Environment_find___spec__2___boxed(obj*, obj*);
obj* l_Lean_EnvExtension_modifyStateUnsafe___rarg(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__8___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Environment_displayStats___closed__4;
extern obj* l_Nat_Inhabited;
obj* l_Lean_EnvExtension_Inhabited___rarg(obj*);
obj* l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(obj*);
extern obj* l_Array_empty___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
obj* l_Lean_importModulesAux(obj*, obj*, obj*);
obj* l_Lean_EnvExtension_getState(obj*);
obj* l___private_init_lean_environment_12__mkImportedStateThunk___elambda__1(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__9(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__6___boxed(obj*);
obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
obj* l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__4;
obj* l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__1;
obj* l_Array_mkArray(obj*, obj*, obj*);
obj* l_Lean_CPPExtensionState_Inhabited;
obj* l_Lean_PersistentEnvExtension_forceStateAux___rarg(obj*, obj*);
namespace lean {
obj* environment_add_modification_core(obj*, obj*);
}
extern "C" obj* lean_find_olean(obj*, obj*);
obj* l_List_lengthAux___main___rarg(obj*, obj*);
obj* l_Lean_Environment_displayStats___closed__5;
obj* l_Lean_PersistentEnvExtension_getModuleEntries___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__9___closed__1;
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_EnvExtension_getStateUnsafe___rarg(obj*, obj*);
obj* l_AssocList_replace___main___at_Lean_importModules___spec__6(obj*, obj*, obj*);
obj* l_Nat_foldAux___main___at_Lean_mkModuleData___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Thunk_pure(obj*, obj*);
uint8 l_Lean_SMap_contains___main___at_Lean_Environment_contains___spec__1(obj*, obj*);
obj* l_Lean_PersistentEnvExtension_getEntries___rarg(obj*, obj*);
obj* l___private_init_lean_environment_11__setImportedEntries___boxed(obj*, obj*, obj*);
obj* l_Lean_EnvExtension_modifyStateUnsafe(obj*);
obj* l___private_init_lean_environment_4__getTrustLevel___boxed(obj*);
uint8 l_AssocList_contains___main___at_Lean_Environment_add___spec__5(obj*, obj*);
uint8 l_HashMapImp_contains___at_Lean_Environment_contains___spec__2(obj*, obj*);
obj* l_Array_anyMAux___main___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
namespace lean {
obj* import_modules_core(obj*, uint32, obj*);
}
obj* l_Lean_SMap_insert___main___at_Lean_Environment_add___spec__1___closed__1;
obj* l_Array_miterateAux___main___at___private_init_lean_environment_13__finalizePersistentExtensions___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_insert___main___at_Lean_Environment_add___spec__1(obj*, obj*, obj*);
obj* l_List_reverse___rarg(obj*);
obj* l_List_toStringAux___main___at_Lean_Environment_displayStats___spec__2___boxed(obj*, obj*);
uint8 l_List_isEmpty___main___rarg(obj*);
obj* l_List_foldr___main___at_Lean_PersistentEnvExtension_forceStateAux___spec__1___rarg___boxed(obj*, obj*, obj*);
obj* l_HashMapImp_moveEntries___main___at_Lean_Environment_add___spec__7(obj*, obj*, obj*);
obj* l_AssocList_foldl___main___at_Lean_Environment_add___spec__8(obj*, obj*);
obj* l_Lean_mkEmptyEnvironment___closed__1;
obj* l_Lean_importModules___closed__1;
obj* l_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__6(obj*);
obj* l_List_toArrayAux___main___rarg(obj*, obj*);
obj* l_Array_uget(obj*, obj*, usize, obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l_Lean_PersistentEnvExtensionState_inhabited___rarg(obj*);
obj* l_Lean_EnvExtension_setState(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Inhabited;
obj* l_Array_uset(obj*, obj*, usize, obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_environment_12__mkImportedStateThunk___elambda__1___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_List_redLength___main___rarg(obj*);
obj* l_Lean_PersistentEnvExtension_getState___rarg___boxed(obj*, obj*);
obj* l_Lean_PersistentEnvExtension_forceState(obj*, obj*);
obj* l_IO_Prim_Ref_set(obj*, obj*, obj*, obj*);
obj* l_AssocList_find___main___at_Lean_Environment_find___spec__3(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__8___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_environment_12__mkImportedStateThunk___elambda__1___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_AssocList_find___main___at_Lean_Environment_getModuleIdxFor___spec__2___boxed(obj*, obj*);
obj* l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(obj*, obj*);
obj* l_Lean_Environment_displayStats___closed__3;
obj* l_Lean_Name_quickLt___boxed(obj*, obj*);
obj* l___private_init_lean_environment_12__mkImportedStateThunk___elambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_depth___main___rarg(obj*, obj*);
obj* l_Lean_EnvExtension_setState___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_environment_10__getEntriesFor___main___closed__1;
extern "C" obj* lean_io_initializing(obj*);
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__8(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mkEmpty(obj*, obj*);
extern obj* l_Bool_HasRepr___closed__2;
obj* l_Array_ummapAux___main___at___private_init_lean_environment_7__mkInitialExtensionStates___spec__1(obj*, obj*);
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__2(obj*);
obj* l_RBNode_ins___main___at_Lean_Environment_add___spec__3(obj*, obj*, obj*);
uint8 l_AssocList_contains___main___at_Lean_importModules___spec__2(obj*, obj*);
obj* l_Lean_EnvExtension_setState___closed__1;
obj* l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__2;
namespace lean {
obj* mk_empty_environment_core(uint32, obj*);
}
extern obj* l_Lean_Name_DecidableEq;
obj* l___private_init_lean_environment_9__persistentEnvExtensionsRef;
obj* l_Thunk_mk(obj*, obj*);
obj* l_Array_toList___rarg(obj*);
obj* l_Lean_EnvExtensionEntry_Inhabited;
uint8 l_Lean_NameSet_contains(obj*, obj*);
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__1(uint8, obj*, obj*);
obj* l_Nat_repr(obj*);
obj* l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4___boxed(obj*);
obj* l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__6;
extern "C" obj* lean_perform_serialized_modifications(obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_NameSet_insert___spec__1(obj*, obj*, obj*);
obj* l_HashMapImp_find___at_Lean_Environment_getModuleIdxFor___spec__1(obj*, obj*);
obj* l_Lean_registerEnvExtensionUnsafe___rarg(obj*, obj*);
obj* l_AssocList_contains___main___at_Lean_Environment_add___spec__5___boxed(obj*, obj*);
obj* l___private_init_lean_environment_10__getEntriesFor(obj*, obj*, obj*);
obj* l_Lean_Environment_displayStats___closed__1;
obj* l_Lean_Environment_displayStats___closed__2;
extern "C" usize lean_name_hash_usize(obj*);
obj* l_Lean_readModuleData___boxed(obj*, obj*);
obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
extern obj* l_List_repr___main___rarg___closed__3;
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__10(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_PersistentEnvExtension_getState___rarg(obj*, obj*);
obj* l_Lean_EnvExtension_getStateUnsafe___rarg___boxed(obj*, obj*);
obj* l_List_foldr___main___at_Lean_PersistentEnvExtension_forceStateAux___spec__1(obj*, obj*);
obj* l_Lean_registerEnvExtensionUnsafe(obj*);
obj* l_List_toStringAux___main___at_Lean_Environment_displayStats___spec__2(uint8, obj*);
obj* l_HashMapImp_insert___at_Lean_importModules___spec__1(obj*, obj*, obj*);
obj* l_Lean_Environment_getModuleIdxFor(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__7___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_beqOfEq___rarg(obj*, obj*, obj*);
uint8 l_Array_anyMAux___main___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg(obj*, obj*, obj*, obj*);
namespace lean {
obj* display_stats_core(obj*, obj*);
}
obj* l_Lean_registerPersistentEnvExtension___rarg(obj*);
obj* l_Lean_Environment_Inhabited;
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_PersistentEnvExtension_getModuleEntries(obj*, obj*);
obj* l_Lean_PersistentEnvExtension_getEntries(obj*, obj*);
obj* l_Lean_PersistentEnvExtensionState_inhabited(obj*, obj*, obj*);
extern obj* l_List_reprAux___main___rarg___closed__1;
obj* l___private_init_lean_environment_6__envExtensionsRef;
obj* l_HashMapImp_moveEntries___main___at_Lean_importModules___spec__4(obj*, obj*, obj*);
extern obj* l_ByteArray_empty;
extern "C" obj* lean_save_module_data(obj*, obj*, obj*);
obj* l_Lean_EnvExtension_getState___rarg(obj*, obj*);
obj* l_Lean_PersistentEnvExtension_forceStateAux(obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
obj* l_Lean_EnvExtensionState_Inhabited;
extern "C" obj* lean_serialize_modifications(obj*, obj*);
extern obj* l_Char_HasRepr___closed__1;
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__11___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3___boxed(obj*);
obj* l___private_init_lean_environment_5__mkEnvExtensionsRef(obj*);
obj* l_Array_fget(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__10___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_environment_12__mkImportedStateThunk(obj*, obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_AssocList_replace___main___at_Lean_Environment_add___spec__9(obj*, obj*, obj*);
obj* l_Lean_PersistentEnvExtension_getModuleEntries___rarg(obj*, obj*, obj*);
extern obj* l_RBMap_maxDepth___rarg___closed__1;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(obj*);
obj* l_Lean_EnvExtension_setStateUnsafe___rarg(obj*, obj*, obj*);
obj* l_Lean_Environment_displayStats___closed__9;
obj* l_Lean_SMap_contains___main___at_Lean_Environment_contains___spec__1___boxed(obj*, obj*);
obj* l_Lean_saveModuleData___boxed(obj*, obj*, obj*);
obj* l_Array_push(obj*, obj*, obj*);
uint8 l_RBNode_isRed___main___rarg(obj*);
namespace lean {
obj* set_extension_core(obj*, obj*, obj*);
}
obj* l___private_init_lean_environment_10__getEntriesFor___main___boxed(obj*, obj*, obj*);
obj* l_Lean_PersistentEnvExtensionState_inhabited___boxed(obj*, obj*, obj*);
obj* l_Lean_regModListExtension(obj*);
obj* l_RBNode_find___main___at_Lean_Environment_find___spec__4___boxed(obj*, obj*);
obj* l_Array_anyMAux___main___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1(obj*, obj*);
obj* l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4(obj*);
obj* l___private_init_lean_environment_10__getEntriesFor___boxed(obj*, obj*, obj*);
obj* l_Lean_registerEnvExtension(obj*, obj*);
obj* l_Lean_importModulesAux___main(obj*, obj*, obj*);
extern obj* l_unsafeIO___rarg___closed__1;
obj* l_Lean_EnvExtension_getState___rarg___boxed(obj*, obj*);
obj* l_Lean_registerPersistentEnvExtension(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_environment_7__mkInitialExtensionStates(obj*);
obj* l_RBNode_find___main___at_Lean_Environment_find___spec__4(obj*, obj*);
obj* l_Lean_registerPersistentEnvExtensionUnsafe(obj*, obj*);
obj* l_AssocList_find___main___at_Lean_Environment_getModuleIdxFor___spec__2(obj*, obj*);
obj* l_Lean_PersistentEnvExtension_getEntries___rarg___boxed(obj*, obj*);
obj* l_Lean_mkModuleData(obj*, obj*);
obj* l___private_init_lean_environment_8__mkPersistentEnvExtensionsRef(obj*);
obj* l_IO_Prim_mkRef(obj*, obj*, obj*);
obj* l_Lean_PersistentEnvExtension_getState(obj*, obj*);
obj* l_Lean_EnvExtension_modifyState(obj*, obj*, obj*, obj*);
obj* l_Nat_foldAux___main___at_Lean_mkModuleData___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_environment_12__mkImportedStateThunk___elambda__1___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_HashMapImp_find___at_Lean_Environment_getModuleIdxFor___spec__1___boxed(obj*, obj*);
obj* l_Lean_Modification_Inhabited;
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__11(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_importModules___boxed(obj*, obj*, obj*);
namespace lean {
uint8 environment_quot_init_core(obj*);
}
obj* l_Lean_SMap_switch___at___private_init_lean_environment_1__switch___spec__1(obj*);
extern obj* l_NonScalar_Inhabited;
obj* l_Lean_Environment_contains___boxed(obj*, obj*);
obj* l___private_init_lean_environment_3__isQuotInit___boxed(obj*);
extern "C" obj* lean_read_module_data(obj*, obj*);
obj* l_IO_println___at_HasRepr_HasEval___spec__1(obj*, obj*);
obj* l_Lean_SMap_insert___main___at_Lean_Environment_add___spec__1___closed__2;
obj* l_AssocList_foldl___main___at_Lean_importModules___spec__5(obj*, obj*);
obj* l_Lean_findOLean___boxed(obj*, obj*);
obj* l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5___boxed(obj*);
obj* l_Lean_addModification___closed__2;
obj* l_RBNode_fold___main___at_Lean_mkModuleData___spec__2(obj*, obj*);
obj* l_RBNode_insert___at_Lean_Environment_add___spec__2(obj*, obj*, obj*);
obj* l_Lean_PersistentEnvExtension_addEntry___rarg(obj*, obj*, obj*);
obj* l_IO_Prim_Ref_get(obj*, obj*, obj*);
extern obj* l_List_repr___main___rarg___closed__1;
namespace lean {
obj* environment_switch_core(obj*);
}
uint8 l_Lean_Name_quickLt(obj*, obj*);
namespace lean {
obj* register_extension_core(obj*);
}
namespace lean {
usize usize_modn(usize, obj*);
}
obj* l_Array_miterateAux___main___at___private_init_lean_environment_11__setImportedEntries___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_environment_13__finalizePersistentExtensions(obj*, obj*);
namespace lean {
obj* environment_find_core(obj*, obj*);
}
obj* l_Lean_PersistentEnvExtension_forceState___rarg(obj*, obj*);
obj* l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2;
obj* l___private_init_lean_environment_11__setImportedEntries(obj*, obj*, obj*);
extern obj* l_HashMap_Inhabited___closed__1;
obj* l_Lean_modListExtension;
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__12(obj*, obj*, obj*, obj*, obj*);
obj* l_HashMapImp_expand___at_Lean_Environment_add___spec__6(obj*, obj*);
namespace lean {
obj* environment_add_core(obj*, obj*);
}
obj* l_Lean_EnvExtension_setStateUnsafe(obj*);
obj* l_Array_size(obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_environment_12__mkImportedStateThunk___elambda__1___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_ModuleIdx_Inhabited;
obj* l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9(obj*, obj*, obj*, obj*);
obj* l_Lean_EnvExtension_Inhabited(obj*);
obj* l_Array_fset(obj*, obj*, obj*, obj*);
obj* l_List_foldr___main___at_Lean_PersistentEnvExtension_forceStateAux___spec__1___rarg(obj*, obj*, obj*);
obj* l_Array_get(obj*, obj*, obj*, obj*);
obj* l_mkHashMapImp___rarg(obj*);
obj* l_Lean_EnvExtension_getStateUnsafe(obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_environment_11__setImportedEntries___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_AssocList_contains___main___at_Lean_importModules___spec__2___boxed(obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__5;
obj* l_AssocList_find___main___at_Lean_Environment_find___spec__3___boxed(obj*, obj*);
namespace lean {
obj* get_extension_core(obj*, obj*);
}
obj* l_Lean_mkEmptyEnvironment___boxed(obj*, obj*);
obj* l_HashMapImp_insert___at_Lean_Environment_add___spec__4(obj*, obj*, obj*);
obj* l_Lean_registerPersistentEnvExtension___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
extern obj* l_Lean_Name_toString___closed__1;
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
uint8 l_Lean_Environment_contains(obj*, obj*);
namespace lean {
uint32 environment_trust_level_core(obj*);
}
obj* l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___boxed(obj*, obj*, obj*, obj*);
namespace lean {
obj* uint32_to_nat(uint32);
}
obj* l_Lean_serializeModifications___boxed(obj*, obj*);
obj* l_Lean_PersistentEnvExtension_addEntry(obj*, obj*);
obj* l_Array_set(obj*, obj*, obj*, obj*);
obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___boxed(obj*, obj*, obj*);
obj* l_mkHashMap___at_Lean_Environment_Inhabited___spec__3(obj*);
obj* l_Lean_addModification___closed__1;
obj* l_HashMapImp_find___at_Lean_Environment_find___spec__2(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__8(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_registerEnvExtension___rarg(obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_environment_11__setImportedEntries___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg(obj*, obj*, obj*);
obj* l_Lean_registerEnvExtension___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_environment_13__finalizePersistentExtensions___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Environment_displayStats___closed__8;
extern obj* l_List_repr___main___rarg___closed__2;
obj* l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3(obj*);
obj* l_Lean_ModuleData_inhabited;
namespace lean {
obj* environment_mark_quot_init_core(obj*);
}
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l___private_init_lean_environment_10__getEntriesFor___main(obj*, obj*, obj*);
obj* l_Thunk_get(obj*, obj*);
obj* l_Lean_SMap_find_x27___main___at_Lean_Environment_find___spec__1(obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__3;
obj* l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
extern obj* l_Bool_HasRepr___closed__1;
obj* l_Array_miterateAux___main___at___private_init_lean_environment_11__setImportedEntries___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_IO_Prim_Ref_reset(obj*, obj*, obj*);
obj* l_HashMapImp_expand___at_Lean_importModules___spec__3(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__9___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__7(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7___boxed(obj*);
extern obj* l_String_splitAux___main___closed__1;
obj* l_List_toString___main___at_Lean_Environment_displayStats___spec__1(obj*);
obj* l_HashMapImp_contains___at_Lean_Environment_contains___spec__2___boxed(obj*, obj*);
obj* _init_l_Lean_EnvExtensionState_Inhabited() {
_start:
{
obj* x_1; 
x_1 = l_NonScalar_Inhabited;
return x_1;
}
}
obj* _init_l_Lean_ModuleIdx_Inhabited() {
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
obj* _init_l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; uint8 x_4; obj* x_5; 
x_1 = lean::mk_nat_obj(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
x_3 = lean::box(0);
x_4 = 1;
x_5 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_3);
lean::cnstr_set_scalar(x_5, sizeof(void*)*2, x_4);
return x_5;
}
}
obj* _init_l_Lean_Environment_Inhabited() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; uint32 x_5; obj* x_6; uint8 x_7; obj* x_8; 
x_1 = lean::mk_nat_obj(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::mk_empty_array(x_3);
x_5 = 0;
x_6 = l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2;
x_7 = 0;
lean::inc(x_4);
x_8 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_8, 0, x_2);
lean::cnstr_set(x_8, 1, x_6);
lean::cnstr_set(x_8, 2, x_4);
lean::cnstr_set(x_8, 3, x_4);
lean::cnstr_set_scalar(x_8, sizeof(void*)*4, x_5);
lean::cnstr_set_scalar(x_8, sizeof(void*)*4 + 4, x_7);
return x_8;
}
}
obj* l_RBNode_ins___main___at_Lean_Environment_add___spec__3(obj* x_1, obj* x_2, obj* x_3) {
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
x_14 = l_RBNode_ins___main___at_Lean_Environment_add___spec__3(x_11, x_2, x_3);
lean::cnstr_set(x_1, 3, x_14);
return x_1;
}
}
else
{
obj* x_15; 
x_15 = l_RBNode_ins___main___at_Lean_Environment_add___spec__3(x_8, x_2, x_3);
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
x_23 = l_RBNode_ins___main___at_Lean_Environment_add___spec__3(x_19, x_2, x_3);
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
x_25 = l_RBNode_ins___main___at_Lean_Environment_add___spec__3(x_16, x_2, x_3);
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
x_35 = l_RBNode_ins___main___at_Lean_Environment_add___spec__3(x_31, x_2, x_3);
lean::cnstr_set(x_1, 3, x_35);
return x_1;
}
else
{
obj* x_36; 
x_36 = l_RBNode_ins___main___at_Lean_Environment_add___spec__3(x_31, x_2, x_3);
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
x_175 = l_RBNode_ins___main___at_Lean_Environment_add___spec__3(x_28, x_2, x_3);
lean::cnstr_set(x_1, 0, x_175);
return x_1;
}
else
{
obj* x_176; 
x_176 = l_RBNode_ins___main___at_Lean_Environment_add___spec__3(x_28, x_2, x_3);
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
x_323 = l_RBNode_ins___main___at_Lean_Environment_add___spec__3(x_318, x_2, x_3);
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
x_325 = l_RBNode_ins___main___at_Lean_Environment_add___spec__3(x_318, x_2, x_3);
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
x_401 = l_RBNode_ins___main___at_Lean_Environment_add___spec__3(x_315, x_2, x_3);
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
x_403 = l_RBNode_ins___main___at_Lean_Environment_add___spec__3(x_315, x_2, x_3);
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
obj* l_RBNode_insert___at_Lean_Environment_add___spec__2(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at_Lean_Environment_add___spec__3(x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at_Lean_Environment_add___spec__3(x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
uint8 l_AssocList_contains___main___at_Lean_Environment_add___spec__5(obj* x_1, obj* x_2) {
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
uint8 x_7; 
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
obj* l_AssocList_foldl___main___at_Lean_Environment_add___spec__8(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_2);
return x_1;
}
else
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; usize x_7; usize x_8; obj* x_9; usize x_10; obj* x_11; usize x_12; obj* x_13; obj* x_14; 
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
obj* x_15; obj* x_16; obj* x_17; obj* x_18; usize x_19; usize x_20; obj* x_21; usize x_22; obj* x_23; obj* x_24; usize x_25; obj* x_26; obj* x_27; 
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
obj* l_HashMapImp_moveEntries___main___at_Lean_Environment_add___spec__7(obj* x_1, obj* x_2, obj* x_3) {
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
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_6 = lean::array_fget(x_2, x_1);
x_7 = lean::box(0);
x_8 = lean::array_fset(x_2, x_1, x_7);
x_9 = l_AssocList_foldl___main___at_Lean_Environment_add___spec__8(x_3, x_6);
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
obj* l_HashMapImp_expand___at_Lean_Environment_add___spec__6(obj* x_1, obj* x_2) {
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
x_9 = l_HashMapImp_moveEntries___main___at_Lean_Environment_add___spec__7(x_8, x_2, x_7);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_AssocList_replace___main___at_Lean_Environment_add___spec__9(obj* x_1, obj* x_2, obj* x_3) {
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
x_9 = l_AssocList_replace___main___at_Lean_Environment_add___spec__9(x_1, x_2, x_7);
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
x_14 = l_AssocList_replace___main___at_Lean_Environment_add___spec__9(x_1, x_2, x_12);
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
obj* l_HashMapImp_insert___at_Lean_Environment_add___spec__4(obj* x_1, obj* x_2, obj* x_3) {
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
x_13 = l_AssocList_contains___main___at_Lean_Environment_add___spec__5(x_2, x_12);
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
x_20 = l_HashMapImp_expand___at_Lean_Environment_add___spec__6(x_15, x_18);
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
x_21 = l_AssocList_replace___main___at_Lean_Environment_add___spec__9(x_2, x_3, x_12);
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
x_32 = l_AssocList_contains___main___at_Lean_Environment_add___spec__5(x_2, x_31);
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
x_39 = l_HashMapImp_expand___at_Lean_Environment_add___spec__6(x_34, x_37);
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
x_41 = l_AssocList_replace___main___at_Lean_Environment_add___spec__9(x_2, x_3, x_31);
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
obj* _init_l_Lean_SMap_insert___main___at_Lean_Environment_add___spec__1___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Name_quickLt___boxed), 2, 0);
return x_1;
}
}
obj* _init_l_Lean_SMap_insert___main___at_Lean_Environment_add___spec__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Name_DecidableEq;
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_beqOfEq___rarg), 3, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_SMap_insert___main___at_Lean_Environment_add___spec__1(obj* x_1, obj* x_2, obj* x_3) {
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
x_7 = l_RBNode_insert___at_Lean_Environment_add___spec__2(x_6, x_2, x_3);
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
x_10 = l_RBNode_insert___at_Lean_Environment_add___spec__2(x_9, x_2, x_3);
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
x_14 = l_HashMapImp_insert___at_Lean_Environment_add___spec__4(x_13, x_2, x_3);
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
x_17 = l_HashMapImp_insert___at_Lean_Environment_add___spec__4(x_15, x_2, x_3);
x_18 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_16);
lean::cnstr_set_scalar(x_18, sizeof(void*)*2, x_4);
return x_18;
}
}
}
}
namespace lean {
obj* environment_add_core(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_1, 1);
x_5 = l_Lean_ConstantInfo_name(x_2);
x_6 = l_Lean_SMap_insert___main___at_Lean_Environment_add___spec__1(x_4, x_5, x_2);
lean::cnstr_set(x_1, 1, x_6);
return x_1;
}
else
{
obj* x_7; obj* x_8; obj* x_9; uint32 x_10; uint8 x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_7 = lean::cnstr_get(x_1, 0);
x_8 = lean::cnstr_get(x_1, 1);
x_9 = lean::cnstr_get(x_1, 2);
x_10 = lean::cnstr_get_scalar<uint32>(x_1, sizeof(void*)*4);
x_11 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4 + 4);
x_12 = lean::cnstr_get(x_1, 3);
lean::inc(x_12);
lean::inc(x_9);
lean::inc(x_8);
lean::inc(x_7);
lean::dec(x_1);
x_13 = l_Lean_ConstantInfo_name(x_2);
x_14 = l_Lean_SMap_insert___main___at_Lean_Environment_add___spec__1(x_8, x_13, x_2);
x_15 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_15, 0, x_7);
lean::cnstr_set(x_15, 1, x_14);
lean::cnstr_set(x_15, 2, x_9);
lean::cnstr_set(x_15, 3, x_12);
lean::cnstr_set_scalar(x_15, sizeof(void*)*4, x_10);
lean::cnstr_set_scalar(x_15, sizeof(void*)*4 + 4, x_11);
return x_15;
}
}
}
}
obj* l_AssocList_contains___main___at_Lean_Environment_add___spec__5___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_Environment_add___spec__5(x_1, x_2);
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
obj* x_8; 
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
x_4 = lean::array_get_size(x_3);
x_5 = lean_name_hash_usize(x_2);
x_6 = lean::usize_modn(x_5, x_4);
lean::dec(x_4);
x_7 = lean::box_size_t(x_6);
x_8 = lean::unbox_size_t(x_7);
lean::dec(x_7);
x_9 = lean::array_uget(x_3, x_8);
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
obj* x_11; 
x_1 = x_7;
goto _start;
}
}
else
{
obj* x_12; 
x_1 = x_4;
goto _start;
}
}
}
}
obj* l_Lean_SMap_find_x27___main___at_Lean_Environment_find___spec__1(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = l_HashMapImp_find___at_Lean_Environment_find___spec__2(x_4, x_2);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; 
lean::dec(x_6);
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
namespace lean {
obj* environment_find_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_Lean_SMap_find_x27___main___at_Lean_Environment_find___spec__1(x_3, x_2);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
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
obj* l_Lean_SMap_find_x27___main___at_Lean_Environment_find___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_SMap_find_x27___main___at_Lean_Environment_find___spec__1(x_1, x_2);
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
x_4 = lean::array_get_size(x_3);
x_5 = lean_name_hash_usize(x_2);
x_6 = lean::usize_modn(x_5, x_4);
lean::dec(x_4);
x_7 = lean::box_size_t(x_6);
x_8 = lean::unbox_size_t(x_7);
lean::dec(x_7);
x_9 = lean::array_uget(x_3, x_8);
x_10 = l_AssocList_contains___main___at_Lean_Environment_add___spec__5(x_2, x_9);
lean::dec(x_9);
return x_10;
}
}
uint8 l_Lean_SMap_contains___main___at_Lean_Environment_contains___spec__1(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*2);
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
lean::dec(x_7);
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
x_4 = l_Lean_SMap_contains___main___at_Lean_Environment_contains___spec__1(x_3, x_2);
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
obj* l_Lean_SMap_contains___main___at_Lean_Environment_contains___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_SMap_contains___main___at_Lean_Environment_contains___spec__1(x_1, x_2);
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
obj* l_Lean_SMap_switch___at___private_init_lean_environment_1__switch___spec__1(obj* x_1) {
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
namespace lean {
obj* environment_switch_core(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = l_Lean_SMap_switch___at___private_init_lean_environment_1__switch___spec__1(x_3);
lean::cnstr_set(x_1, 1, x_4);
return x_1;
}
else
{
obj* x_5; obj* x_6; obj* x_7; uint32 x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
x_7 = lean::cnstr_get(x_1, 2);
x_8 = lean::cnstr_get_scalar<uint32>(x_1, sizeof(void*)*4);
x_9 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4 + 4);
x_10 = lean::cnstr_get(x_1, 3);
lean::inc(x_10);
lean::inc(x_7);
lean::inc(x_6);
lean::inc(x_5);
lean::dec(x_1);
x_11 = l_Lean_SMap_switch___at___private_init_lean_environment_1__switch___spec__1(x_6);
x_12 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_12, 0, x_5);
lean::cnstr_set(x_12, 1, x_11);
lean::cnstr_set(x_12, 2, x_7);
lean::cnstr_set(x_12, 3, x_10);
lean::cnstr_set_scalar(x_12, sizeof(void*)*4, x_8);
lean::cnstr_set_scalar(x_12, sizeof(void*)*4 + 4, x_9);
return x_12;
}
}
}
}
namespace lean {
obj* environment_mark_quot_init_core(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
uint8 x_3; 
x_3 = 1;
lean::cnstr_set_scalar(x_1, sizeof(void*)*4 + 4, x_3);
return x_1;
}
else
{
obj* x_4; obj* x_5; obj* x_6; uint32 x_7; obj* x_8; uint8 x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_7 = lean::cnstr_get_scalar<uint32>(x_1, sizeof(void*)*4);
x_8 = lean::cnstr_get(x_1, 3);
lean::inc(x_8);
lean::inc(x_6);
lean::inc(x_5);
lean::inc(x_4);
lean::dec(x_1);
x_9 = 1;
x_10 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_10, 0, x_4);
lean::cnstr_set(x_10, 1, x_5);
lean::cnstr_set(x_10, 2, x_6);
lean::cnstr_set(x_10, 3, x_8);
lean::cnstr_set_scalar(x_10, sizeof(void*)*4, x_7);
lean::cnstr_set_scalar(x_10, sizeof(void*)*4 + 4, x_9);
return x_10;
}
}
}
}
namespace lean {
uint8 environment_quot_init_core(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4 + 4);
lean::dec(x_1);
return x_2;
}
}
}
obj* l___private_init_lean_environment_3__isQuotInit___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::environment_quot_init_core(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
namespace lean {
uint32 environment_trust_level_core(obj* x_1) {
_start:
{
uint32 x_2; 
x_2 = lean::cnstr_get_scalar<uint32>(x_1, sizeof(void*)*4);
lean::dec(x_1);
return x_2;
}
}
}
obj* l___private_init_lean_environment_4__getTrustLevel___boxed(obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::environment_trust_level_core(x_1);
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
obj* x_8; 
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
x_4 = lean::array_get_size(x_3);
x_5 = lean_name_hash_usize(x_2);
x_6 = lean::usize_modn(x_5, x_4);
lean::dec(x_4);
x_7 = lean::box_size_t(x_6);
x_8 = lean::unbox_size_t(x_7);
lean::dec(x_7);
x_9 = lean::array_uget(x_3, x_8);
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
x_7 = l_Lean_EnvExtensionState_Inhabited;
x_8 = x_3;
x_9 = lean::array_set(x_5, x_6, x_8);
lean::cnstr_set(x_2, 2, x_9);
return x_2;
}
else
{
obj* x_10; obj* x_11; obj* x_12; uint32 x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_10 = lean::cnstr_get(x_2, 0);
x_11 = lean::cnstr_get(x_2, 1);
x_12 = lean::cnstr_get(x_2, 2);
x_13 = lean::cnstr_get_scalar<uint32>(x_2, sizeof(void*)*4);
x_14 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*4 + 4);
x_15 = lean::cnstr_get(x_2, 3);
lean::inc(x_15);
lean::inc(x_12);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_2);
x_16 = lean::cnstr_get(x_1, 0);
x_17 = l_Lean_EnvExtensionState_Inhabited;
x_18 = x_3;
x_19 = lean::array_set(x_12, x_16, x_18);
x_20 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_20, 0, x_10);
lean::cnstr_set(x_20, 1, x_11);
lean::cnstr_set(x_20, 2, x_19);
lean::cnstr_set(x_20, 3, x_15);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_13);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4 + 4, x_14);
return x_20;
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
obj* x_1; obj* x_2; obj* x_3; obj* x_4; uint32 x_5; obj* x_6; uint8 x_7; obj* x_8; 
x_1 = lean::mk_nat_obj(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::mk_empty_array(x_3);
x_5 = 0;
x_6 = l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2;
x_7 = 0;
lean::inc(x_4);
x_8 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_8, 0, x_2);
lean::cnstr_set(x_8, 1, x_6);
lean::cnstr_set(x_8, 2, x_4);
lean::cnstr_set(x_8, 3, x_4);
lean::cnstr_set_scalar(x_8, sizeof(void*)*4, x_5);
lean::cnstr_set_scalar(x_8, sizeof(void*)*4 + 4, x_7);
return x_8;
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
x_5 = l_Lean_EnvExtensionState_Inhabited;
x_6 = lean::array_get(x_5, x_3, x_4);
lean::dec(x_4);
x_7 = lean::cnstr_get(x_1, 1);
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
x_3 = lean::cnstr_get(x_1, 1);
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
x_7 = lean::array_get_size(x_5);
x_8 = lean::nat_dec_lt(x_6, x_7);
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
x_9 = lean::array_fget(x_5, x_6);
x_10 = lean::mk_nat_obj(0u);
x_11 = lean::array_fset(x_5, x_6, x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::dec(x_1);
x_13 = x_9;
x_14 = lean::apply_1(x_3, x_13);
x_15 = l_Lean_EnvExtensionState_Inhabited;
x_16 = x_14;
x_17 = lean::array_fset(x_11, x_6, x_16);
lean::dec(x_6);
lean::cnstr_set(x_2, 2, x_17);
return x_2;
}
}
else
{
obj* x_18; obj* x_19; obj* x_20; uint32 x_21; uint8 x_22; obj* x_23; obj* x_24; obj* x_25; uint8 x_26; 
x_18 = lean::cnstr_get(x_2, 0);
x_19 = lean::cnstr_get(x_2, 1);
x_20 = lean::cnstr_get(x_2, 2);
x_21 = lean::cnstr_get_scalar<uint32>(x_2, sizeof(void*)*4);
x_22 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*4 + 4);
x_23 = lean::cnstr_get(x_2, 3);
lean::inc(x_23);
lean::inc(x_20);
lean::inc(x_19);
lean::inc(x_18);
lean::dec(x_2);
x_24 = lean::cnstr_get(x_1, 0);
lean::inc(x_24);
x_25 = lean::array_get_size(x_20);
x_26 = lean::nat_dec_lt(x_24, x_25);
lean::dec(x_25);
if (x_26 == 0)
{
obj* x_27; 
lean::dec(x_24);
lean::dec(x_3);
lean::dec(x_1);
x_27 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_27, 0, x_18);
lean::cnstr_set(x_27, 1, x_19);
lean::cnstr_set(x_27, 2, x_20);
lean::cnstr_set(x_27, 3, x_23);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_21);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4 + 4, x_22);
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_28 = lean::array_fget(x_20, x_24);
x_29 = lean::mk_nat_obj(0u);
x_30 = lean::array_fset(x_20, x_24, x_29);
x_31 = lean::cnstr_get(x_1, 1);
lean::inc(x_31);
lean::dec(x_1);
x_32 = x_28;
x_33 = lean::apply_1(x_3, x_32);
x_34 = l_Lean_EnvExtensionState_Inhabited;
x_35 = x_33;
x_36 = lean::array_fset(x_30, x_24, x_35);
lean::dec(x_24);
x_37 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_37, 0, x_18);
lean::cnstr_set(x_37, 1, x_19);
lean::cnstr_set(x_37, 2, x_36);
lean::cnstr_set(x_37, 3, x_23);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_21);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4 + 4, x_22);
return x_37;
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
obj* l___private_init_lean_environment_5__mkEnvExtensionsRef(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Array_empty___closed__1;
x_3 = lean::io_mk_ref(x_2, x_1);
return x_3;
}
}
obj* l_Lean_EnvExtension_Inhabited___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
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
x_1 = lean::mk_string("Failed to register environment, extensions can only be registered during initialization");
return x_1;
}
}
obj* _init_l_Lean_registerEnvExtensionUnsafe___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_nat_obj(0u);
x_2 = l_Lean_EnvExtensionState_Inhabited;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_registerEnvExtensionUnsafe___rarg(obj* x_1, obj* x_2) {
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
x_15 = l___private_init_lean_environment_6__envExtensionsRef;
x_16 = lean::io_ref_get(x_15, x_3);
if (lean::obj_tag(x_16) == 0)
{
uint8 x_17; 
x_17 = !lean::is_exclusive(x_16);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_18 = lean::cnstr_get(x_16, 0);
lean::cnstr_set(x_16, 0, x_14);
x_19 = lean::array_get_size(x_18);
lean::dec(x_18);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_1);
x_21 = lean::io_ref_get(x_15, x_16);
if (lean::obj_tag(x_21) == 0)
{
uint8 x_22; 
x_22 = !lean::is_exclusive(x_21);
if (x_22 == 0)
{
obj* x_23; obj* x_24; 
x_23 = lean::cnstr_get(x_21, 0);
lean::cnstr_set(x_21, 0, x_14);
x_24 = lean::io_ref_reset(x_15, x_21);
if (lean::obj_tag(x_24) == 0)
{
uint8 x_25; 
x_25 = !lean::is_exclusive(x_24);
if (x_25 == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_26 = lean::cnstr_get(x_24, 0);
lean::dec(x_26);
lean::cnstr_set(x_24, 0, x_14);
x_27 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_20);
x_28 = x_20;
x_29 = lean::array_push(x_23, x_28);
x_30 = lean::io_ref_set(x_15, x_29, x_24);
if (lean::obj_tag(x_30) == 0)
{
uint8 x_31; 
x_31 = !lean::is_exclusive(x_30);
if (x_31 == 0)
{
obj* x_32; 
x_32 = lean::cnstr_get(x_30, 0);
lean::dec(x_32);
lean::cnstr_set(x_30, 0, x_20);
return x_30;
}
else
{
obj* x_33; obj* x_34; 
x_33 = lean::cnstr_get(x_30, 1);
lean::inc(x_33);
lean::dec(x_30);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_20);
lean::cnstr_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8 x_35; 
lean::dec(x_20);
x_35 = !lean::is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = lean::cnstr_get(x_30, 0);
x_37 = lean::cnstr_get(x_30, 1);
lean::inc(x_37);
lean::inc(x_36);
lean::dec(x_30);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_39 = lean::cnstr_get(x_24, 1);
lean::inc(x_39);
lean::dec(x_24);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_14);
lean::cnstr_set(x_40, 1, x_39);
x_41 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_20);
x_42 = x_20;
x_43 = lean::array_push(x_23, x_42);
x_44 = lean::io_ref_set(x_15, x_43, x_40);
if (lean::obj_tag(x_44) == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = lean::cnstr_get(x_44, 1);
lean::inc(x_45);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 lean::cnstr_release(x_44, 1);
 x_46 = x_44;
} else {
 lean::dec_ref(x_44);
 x_46 = lean::box(0);
}
if (lean::is_scalar(x_46)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_46;
}
lean::cnstr_set(x_47, 0, x_20);
lean::cnstr_set(x_47, 1, x_45);
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
lean::dec(x_20);
x_48 = lean::cnstr_get(x_44, 0);
lean::inc(x_48);
x_49 = lean::cnstr_get(x_44, 1);
lean::inc(x_49);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 lean::cnstr_release(x_44, 1);
 x_50 = x_44;
} else {
 lean::dec_ref(x_44);
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
lean::dec(x_23);
lean::dec(x_20);
x_52 = !lean::is_exclusive(x_24);
if (x_52 == 0)
{
return x_24;
}
else
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = lean::cnstr_get(x_24, 0);
x_54 = lean::cnstr_get(x_24, 1);
lean::inc(x_54);
lean::inc(x_53);
lean::dec(x_24);
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_53);
lean::cnstr_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_56 = lean::cnstr_get(x_21, 0);
x_57 = lean::cnstr_get(x_21, 1);
lean::inc(x_57);
lean::inc(x_56);
lean::dec(x_21);
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_14);
lean::cnstr_set(x_58, 1, x_57);
x_59 = lean::io_ref_reset(x_15, x_58);
if (lean::obj_tag(x_59) == 0)
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_60 = lean::cnstr_get(x_59, 1);
lean::inc(x_60);
if (lean::is_exclusive(x_59)) {
 lean::cnstr_release(x_59, 0);
 lean::cnstr_release(x_59, 1);
 x_61 = x_59;
} else {
 lean::dec_ref(x_59);
 x_61 = lean::box(0);
}
if (lean::is_scalar(x_61)) {
 x_62 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_62 = x_61;
}
lean::cnstr_set(x_62, 0, x_14);
lean::cnstr_set(x_62, 1, x_60);
x_63 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_20);
x_64 = x_20;
x_65 = lean::array_push(x_56, x_64);
x_66 = lean::io_ref_set(x_15, x_65, x_62);
if (lean::obj_tag(x_66) == 0)
{
obj* x_67; obj* x_68; obj* x_69; 
x_67 = lean::cnstr_get(x_66, 1);
lean::inc(x_67);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_release(x_66, 0);
 lean::cnstr_release(x_66, 1);
 x_68 = x_66;
} else {
 lean::dec_ref(x_66);
 x_68 = lean::box(0);
}
if (lean::is_scalar(x_68)) {
 x_69 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_69 = x_68;
}
lean::cnstr_set(x_69, 0, x_20);
lean::cnstr_set(x_69, 1, x_67);
return x_69;
}
else
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_20);
x_70 = lean::cnstr_get(x_66, 0);
lean::inc(x_70);
x_71 = lean::cnstr_get(x_66, 1);
lean::inc(x_71);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_release(x_66, 0);
 lean::cnstr_release(x_66, 1);
 x_72 = x_66;
} else {
 lean::dec_ref(x_66);
 x_72 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_70);
lean::cnstr_set(x_73, 1, x_71);
return x_73;
}
}
else
{
obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
lean::dec(x_56);
lean::dec(x_20);
x_74 = lean::cnstr_get(x_59, 0);
lean::inc(x_74);
x_75 = lean::cnstr_get(x_59, 1);
lean::inc(x_75);
if (lean::is_exclusive(x_59)) {
 lean::cnstr_release(x_59, 0);
 lean::cnstr_release(x_59, 1);
 x_76 = x_59;
} else {
 lean::dec_ref(x_59);
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
}
else
{
uint8 x_78; 
lean::dec(x_20);
x_78 = !lean::is_exclusive(x_21);
if (x_78 == 0)
{
return x_21;
}
else
{
obj* x_79; obj* x_80; obj* x_81; 
x_79 = lean::cnstr_get(x_21, 0);
x_80 = lean::cnstr_get(x_21, 1);
lean::inc(x_80);
lean::inc(x_79);
lean::dec(x_21);
x_81 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_81, 0, x_79);
lean::cnstr_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
x_82 = lean::cnstr_get(x_16, 0);
x_83 = lean::cnstr_get(x_16, 1);
lean::inc(x_83);
lean::inc(x_82);
lean::dec(x_16);
x_84 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_84, 0, x_14);
lean::cnstr_set(x_84, 1, x_83);
x_85 = lean::array_get_size(x_82);
lean::dec(x_82);
x_86 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_1);
x_87 = lean::io_ref_get(x_15, x_84);
if (lean::obj_tag(x_87) == 0)
{
obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_88 = lean::cnstr_get(x_87, 0);
lean::inc(x_88);
x_89 = lean::cnstr_get(x_87, 1);
lean::inc(x_89);
if (lean::is_exclusive(x_87)) {
 lean::cnstr_release(x_87, 0);
 lean::cnstr_release(x_87, 1);
 x_90 = x_87;
} else {
 lean::dec_ref(x_87);
 x_90 = lean::box(0);
}
if (lean::is_scalar(x_90)) {
 x_91 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_91 = x_90;
}
lean::cnstr_set(x_91, 0, x_14);
lean::cnstr_set(x_91, 1, x_89);
x_92 = lean::io_ref_reset(x_15, x_91);
if (lean::obj_tag(x_92) == 0)
{
obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
x_93 = lean::cnstr_get(x_92, 1);
lean::inc(x_93);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 lean::cnstr_release(x_92, 1);
 x_94 = x_92;
} else {
 lean::dec_ref(x_92);
 x_94 = lean::box(0);
}
if (lean::is_scalar(x_94)) {
 x_95 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_95 = x_94;
}
lean::cnstr_set(x_95, 0, x_14);
lean::cnstr_set(x_95, 1, x_93);
x_96 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_86);
x_97 = x_86;
x_98 = lean::array_push(x_88, x_97);
x_99 = lean::io_ref_set(x_15, x_98, x_95);
if (lean::obj_tag(x_99) == 0)
{
obj* x_100; obj* x_101; obj* x_102; 
x_100 = lean::cnstr_get(x_99, 1);
lean::inc(x_100);
if (lean::is_exclusive(x_99)) {
 lean::cnstr_release(x_99, 0);
 lean::cnstr_release(x_99, 1);
 x_101 = x_99;
} else {
 lean::dec_ref(x_99);
 x_101 = lean::box(0);
}
if (lean::is_scalar(x_101)) {
 x_102 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_102 = x_101;
}
lean::cnstr_set(x_102, 0, x_86);
lean::cnstr_set(x_102, 1, x_100);
return x_102;
}
else
{
obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
lean::dec(x_86);
x_103 = lean::cnstr_get(x_99, 0);
lean::inc(x_103);
x_104 = lean::cnstr_get(x_99, 1);
lean::inc(x_104);
if (lean::is_exclusive(x_99)) {
 lean::cnstr_release(x_99, 0);
 lean::cnstr_release(x_99, 1);
 x_105 = x_99;
} else {
 lean::dec_ref(x_99);
 x_105 = lean::box(0);
}
if (lean::is_scalar(x_105)) {
 x_106 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_106 = x_105;
}
lean::cnstr_set(x_106, 0, x_103);
lean::cnstr_set(x_106, 1, x_104);
return x_106;
}
}
else
{
obj* x_107; obj* x_108; obj* x_109; obj* x_110; 
lean::dec(x_88);
lean::dec(x_86);
x_107 = lean::cnstr_get(x_92, 0);
lean::inc(x_107);
x_108 = lean::cnstr_get(x_92, 1);
lean::inc(x_108);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 lean::cnstr_release(x_92, 1);
 x_109 = x_92;
} else {
 lean::dec_ref(x_92);
 x_109 = lean::box(0);
}
if (lean::is_scalar(x_109)) {
 x_110 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_110 = x_109;
}
lean::cnstr_set(x_110, 0, x_107);
lean::cnstr_set(x_110, 1, x_108);
return x_110;
}
}
else
{
obj* x_111; obj* x_112; obj* x_113; obj* x_114; 
lean::dec(x_86);
x_111 = lean::cnstr_get(x_87, 0);
lean::inc(x_111);
x_112 = lean::cnstr_get(x_87, 1);
lean::inc(x_112);
if (lean::is_exclusive(x_87)) {
 lean::cnstr_release(x_87, 0);
 lean::cnstr_release(x_87, 1);
 x_113 = x_87;
} else {
 lean::dec_ref(x_87);
 x_113 = lean::box(0);
}
if (lean::is_scalar(x_113)) {
 x_114 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_114 = x_113;
}
lean::cnstr_set(x_114, 0, x_111);
lean::cnstr_set(x_114, 1, x_112);
return x_114;
}
}
}
else
{
uint8 x_115; 
lean::dec(x_1);
x_115 = !lean::is_exclusive(x_16);
if (x_115 == 0)
{
return x_16;
}
else
{
obj* x_116; obj* x_117; obj* x_118; 
x_116 = lean::cnstr_get(x_16, 0);
x_117 = lean::cnstr_get(x_16, 1);
lean::inc(x_117);
lean::inc(x_116);
lean::dec(x_16);
x_118 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_118, 0, x_116);
lean::cnstr_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; 
x_119 = lean::cnstr_get(x_3, 1);
lean::inc(x_119);
lean::dec(x_3);
x_120 = lean::box(0);
x_121 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_121, 0, x_120);
lean::cnstr_set(x_121, 1, x_119);
x_122 = l___private_init_lean_environment_6__envExtensionsRef;
x_123 = lean::io_ref_get(x_122, x_121);
if (lean::obj_tag(x_123) == 0)
{
obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; 
x_124 = lean::cnstr_get(x_123, 0);
lean::inc(x_124);
x_125 = lean::cnstr_get(x_123, 1);
lean::inc(x_125);
if (lean::is_exclusive(x_123)) {
 lean::cnstr_release(x_123, 0);
 lean::cnstr_release(x_123, 1);
 x_126 = x_123;
} else {
 lean::dec_ref(x_123);
 x_126 = lean::box(0);
}
if (lean::is_scalar(x_126)) {
 x_127 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_127 = x_126;
}
lean::cnstr_set(x_127, 0, x_120);
lean::cnstr_set(x_127, 1, x_125);
x_128 = lean::array_get_size(x_124);
lean::dec(x_124);
x_129 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_129, 0, x_128);
lean::cnstr_set(x_129, 1, x_1);
x_130 = lean::io_ref_get(x_122, x_127);
if (lean::obj_tag(x_130) == 0)
{
obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; 
x_131 = lean::cnstr_get(x_130, 0);
lean::inc(x_131);
x_132 = lean::cnstr_get(x_130, 1);
lean::inc(x_132);
if (lean::is_exclusive(x_130)) {
 lean::cnstr_release(x_130, 0);
 lean::cnstr_release(x_130, 1);
 x_133 = x_130;
} else {
 lean::dec_ref(x_130);
 x_133 = lean::box(0);
}
if (lean::is_scalar(x_133)) {
 x_134 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_134 = x_133;
}
lean::cnstr_set(x_134, 0, x_120);
lean::cnstr_set(x_134, 1, x_132);
x_135 = lean::io_ref_reset(x_122, x_134);
if (lean::obj_tag(x_135) == 0)
{
obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; 
x_136 = lean::cnstr_get(x_135, 1);
lean::inc(x_136);
if (lean::is_exclusive(x_135)) {
 lean::cnstr_release(x_135, 0);
 lean::cnstr_release(x_135, 1);
 x_137 = x_135;
} else {
 lean::dec_ref(x_135);
 x_137 = lean::box(0);
}
if (lean::is_scalar(x_137)) {
 x_138 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_138 = x_137;
}
lean::cnstr_set(x_138, 0, x_120);
lean::cnstr_set(x_138, 1, x_136);
x_139 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_129);
x_140 = x_129;
x_141 = lean::array_push(x_131, x_140);
x_142 = lean::io_ref_set(x_122, x_141, x_138);
if (lean::obj_tag(x_142) == 0)
{
obj* x_143; obj* x_144; obj* x_145; 
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
lean::cnstr_set(x_145, 0, x_129);
lean::cnstr_set(x_145, 1, x_143);
return x_145;
}
else
{
obj* x_146; obj* x_147; obj* x_148; obj* x_149; 
lean::dec(x_129);
x_146 = lean::cnstr_get(x_142, 0);
lean::inc(x_146);
x_147 = lean::cnstr_get(x_142, 1);
lean::inc(x_147);
if (lean::is_exclusive(x_142)) {
 lean::cnstr_release(x_142, 0);
 lean::cnstr_release(x_142, 1);
 x_148 = x_142;
} else {
 lean::dec_ref(x_142);
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
else
{
obj* x_150; obj* x_151; obj* x_152; obj* x_153; 
lean::dec(x_131);
lean::dec(x_129);
x_150 = lean::cnstr_get(x_135, 0);
lean::inc(x_150);
x_151 = lean::cnstr_get(x_135, 1);
lean::inc(x_151);
if (lean::is_exclusive(x_135)) {
 lean::cnstr_release(x_135, 0);
 lean::cnstr_release(x_135, 1);
 x_152 = x_135;
} else {
 lean::dec_ref(x_135);
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
lean::dec(x_129);
x_154 = lean::cnstr_get(x_130, 0);
lean::inc(x_154);
x_155 = lean::cnstr_get(x_130, 1);
lean::inc(x_155);
if (lean::is_exclusive(x_130)) {
 lean::cnstr_release(x_130, 0);
 lean::cnstr_release(x_130, 1);
 x_156 = x_130;
} else {
 lean::dec_ref(x_130);
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
x_158 = lean::cnstr_get(x_123, 0);
lean::inc(x_158);
x_159 = lean::cnstr_get(x_123, 1);
lean::inc(x_159);
if (lean::is_exclusive(x_123)) {
 lean::cnstr_release(x_123, 0);
 lean::cnstr_release(x_123, 1);
 x_160 = x_123;
} else {
 lean::dec_ref(x_123);
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
}
}
else
{
uint8 x_162; 
lean::dec(x_1);
x_162 = !lean::is_exclusive(x_3);
if (x_162 == 0)
{
return x_3;
}
else
{
obj* x_163; obj* x_164; obj* x_165; 
x_163 = lean::cnstr_get(x_3, 0);
x_164 = lean::cnstr_get(x_3, 1);
lean::inc(x_164);
lean::inc(x_163);
lean::dec(x_3);
x_165 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_165, 0, x_163);
lean::cnstr_set(x_165, 1, x_164);
return x_165;
}
}
}
}
obj* l_Lean_registerEnvExtensionUnsafe(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerEnvExtensionUnsafe___rarg), 2, 0);
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
obj* l_Lean_registerEnvExtension(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerEnvExtension___rarg), 1, 0);
return x_3;
}
}
obj* l_Lean_registerEnvExtension___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_registerEnvExtension(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_ummapAux___main___at___private_init_lean_environment_7__mkInitialExtensionStates___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_2);
x_4 = lean::nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
lean::dec(x_1);
x_5 = l_Array_empty___closed__1;
x_6 = x_2;
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_7 = lean::array_fget(x_2, x_1);
x_8 = lean::box(0);
lean::inc(x_7);
x_9 = x_8;
x_10 = lean::array_fset(x_2, x_1, x_9);
x_11 = lean::cnstr_get(x_7, 1);
lean::inc(x_11);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_1, x_12);
x_14 = x_11;
x_15 = lean::array_fset(x_10, x_1, x_14);
lean::dec(x_1);
x_1 = x_13;
x_2 = x_15;
goto _start;
}
}
}
obj* l___private_init_lean_environment_7__mkInitialExtensionStates(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l___private_init_lean_environment_6__envExtensionsRef;
x_3 = lean::io_ref_get(x_2, x_1);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::mk_nat_obj(0u);
x_7 = l_Array_ummapAux___main___at___private_init_lean_environment_7__mkInitialExtensionStates___spec__1(x_6, x_5);
lean::cnstr_set(x_3, 0, x_7);
return x_3;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_3, 0);
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_3);
x_10 = lean::mk_nat_obj(0u);
x_11 = l_Array_ummapAux___main___at___private_init_lean_environment_7__mkInitialExtensionStates___spec__1(x_10, x_8);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_9);
return x_12;
}
}
else
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_3);
if (x_13 == 0)
{
return x_3;
}
else
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = lean::cnstr_get(x_3, 0);
x_15 = lean::cnstr_get(x_3, 1);
lean::inc(x_15);
lean::inc(x_14);
lean::dec(x_3);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
}
}
obj* _init_l_Lean_mkEmptyEnvironment___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("Environment objects cannot be created during initialization");
return x_1;
}
}
namespace lean {
obj* mk_empty_environment_core(uint32 x_1, obj* x_2) {
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
x_9 = l___private_init_lean_environment_7__mkInitialExtensionStates(x_3);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; 
x_11 = lean::cnstr_get(x_9, 0);
x_12 = l_HashMap_Inhabited___closed__1;
x_13 = l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2;
x_14 = 0;
x_15 = l_Array_empty___closed__1;
x_16 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_16, 0, x_12);
lean::cnstr_set(x_16, 1, x_13);
lean::cnstr_set(x_16, 2, x_11);
lean::cnstr_set(x_16, 3, x_15);
lean::cnstr_set_scalar(x_16, sizeof(void*)*4, x_1);
lean::cnstr_set_scalar(x_16, sizeof(void*)*4 + 4, x_14);
lean::cnstr_set(x_9, 0, x_16);
return x_9;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; uint8 x_21; obj* x_22; obj* x_23; obj* x_24; 
x_17 = lean::cnstr_get(x_9, 0);
x_18 = lean::cnstr_get(x_9, 1);
lean::inc(x_18);
lean::inc(x_17);
lean::dec(x_9);
x_19 = l_HashMap_Inhabited___closed__1;
x_20 = l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2;
x_21 = 0;
x_22 = l_Array_empty___closed__1;
x_23 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_23, 0, x_19);
lean::cnstr_set(x_23, 1, x_20);
lean::cnstr_set(x_23, 2, x_17);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*4, x_1);
lean::cnstr_set_scalar(x_23, sizeof(void*)*4 + 4, x_21);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_18);
return x_24;
}
}
else
{
uint8 x_25; 
x_25 = !lean::is_exclusive(x_9);
if (x_25 == 0)
{
return x_9;
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = lean::cnstr_get(x_9, 0);
x_27 = lean::cnstr_get(x_9, 1);
lean::inc(x_27);
lean::inc(x_26);
lean::dec(x_9);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_29 = lean::cnstr_get(x_3, 1);
lean::inc(x_29);
lean::dec(x_3);
x_30 = lean::box(0);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_29);
x_32 = l___private_init_lean_environment_7__mkInitialExtensionStates(x_31);
if (lean::obj_tag(x_32) == 0)
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; uint8 x_38; obj* x_39; obj* x_40; obj* x_41; 
x_33 = lean::cnstr_get(x_32, 0);
lean::inc(x_33);
x_34 = lean::cnstr_get(x_32, 1);
lean::inc(x_34);
if (lean::is_exclusive(x_32)) {
 lean::cnstr_release(x_32, 0);
 lean::cnstr_release(x_32, 1);
 x_35 = x_32;
} else {
 lean::dec_ref(x_32);
 x_35 = lean::box(0);
}
x_36 = l_HashMap_Inhabited___closed__1;
x_37 = l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2;
x_38 = 0;
x_39 = l_Array_empty___closed__1;
x_40 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_40, 0, x_36);
lean::cnstr_set(x_40, 1, x_37);
lean::cnstr_set(x_40, 2, x_33);
lean::cnstr_set(x_40, 3, x_39);
lean::cnstr_set_scalar(x_40, sizeof(void*)*4, x_1);
lean::cnstr_set_scalar(x_40, sizeof(void*)*4 + 4, x_38);
if (lean::is_scalar(x_35)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_35;
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_34);
return x_41;
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_42 = lean::cnstr_get(x_32, 0);
lean::inc(x_42);
x_43 = lean::cnstr_get(x_32, 1);
lean::inc(x_43);
if (lean::is_exclusive(x_32)) {
 lean::cnstr_release(x_32, 0);
 lean::cnstr_release(x_32, 1);
 x_44 = x_32;
} else {
 lean::dec_ref(x_32);
 x_44 = lean::box(0);
}
if (lean::is_scalar(x_44)) {
 x_45 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_45 = x_44;
}
lean::cnstr_set(x_45, 0, x_42);
lean::cnstr_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
uint8 x_46; 
x_46 = !lean::is_exclusive(x_3);
if (x_46 == 0)
{
obj* x_47; obj* x_48; 
x_47 = lean::cnstr_get(x_3, 0);
lean::dec(x_47);
x_48 = l_Lean_mkEmptyEnvironment___closed__1;
lean::cnstr_set_tag(x_3, 1);
lean::cnstr_set(x_3, 0, x_48);
return x_3;
}
else
{
obj* x_49; obj* x_50; obj* x_51; 
x_49 = lean::cnstr_get(x_3, 1);
lean::inc(x_49);
lean::dec(x_3);
x_50 = l_Lean_mkEmptyEnvironment___closed__1;
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
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
return x_3;
}
else
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = lean::cnstr_get(x_3, 0);
x_54 = lean::cnstr_get(x_3, 1);
lean::inc(x_54);
lean::inc(x_53);
lean::dec(x_3);
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_53);
lean::cnstr_set(x_55, 1, x_54);
return x_55;
}
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
x_4 = lean::mk_empty_environment_core(x_3, x_2);
return x_4;
}
}
obj* _init_l_Lean_EnvExtensionEntry_Inhabited() {
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
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::thunk_pure(x_1);
x_3 = lean::box(0);
x_4 = lean::box(0);
x_5 = l_Array_empty___closed__1;
x_6 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_4);
return x_6;
}
}
obj* l_Lean_PersistentEnvExtensionState_inhabited(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_PersistentEnvExtensionState_inhabited___rarg), 1, 0);
return x_4;
}
}
obj* l_Lean_PersistentEnvExtensionState_inhabited___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_PersistentEnvExtensionState_inhabited(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__1(uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
lean::inc(x_2);
return x_2;
}
}
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__2(obj* x_1) {
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
obj* _init_l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__1___boxed), 3, 0);
return x_1;
}
}
obj* _init_l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__2), 1, 0);
return x_1;
}
}
obj* l_Lean_PersistentEnvExtension_inhabited___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; obj* x_14; 
x_3 = lean::thunk_pure(x_2);
x_4 = lean::box(0);
x_5 = lean::box(0);
x_6 = l_Array_empty___closed__1;
x_7 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
lean::cnstr_set(x_7, 2, x_4);
lean::cnstr_set(x_7, 3, x_5);
x_8 = lean::mk_nat_obj(0u);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_7);
x_10 = lean::box(0);
x_11 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
x_12 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
x_13 = 1;
x_14 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_14, 0, x_9);
lean::cnstr_set(x_14, 1, x_10);
lean::cnstr_set(x_14, 2, x_1);
lean::cnstr_set(x_14, 3, x_11);
lean::cnstr_set(x_14, 4, x_12);
lean::cnstr_set_scalar(x_14, sizeof(void*)*5, x_13);
return x_14;
}
}
obj* l_Lean_PersistentEnvExtension_inhabited(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_PersistentEnvExtension_inhabited___rarg), 2, 0);
return x_3;
}
}
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
lean::dec(x_1);
x_5 = l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__1(x_4, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_PersistentEnvExtension_getEntries___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_3, x_2);
x_5 = lean::cnstr_get(x_4, 2);
lean::inc(x_5);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_PersistentEnvExtension_getEntries(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_PersistentEnvExtension_getEntries___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_Lean_PersistentEnvExtension_getEntries___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_PersistentEnvExtension_getEntries___rarg(x_1, x_2);
lean::dec(x_2);
return x_3;
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
x_8 = lean::array_get(x_7, x_6, x_3);
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
x_8 = lean::array_get_size(x_6);
x_9 = lean::nat_dec_lt(x_7, x_8);
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
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; uint8 x_15; 
x_10 = lean::array_fget(x_6, x_7);
x_11 = lean::mk_nat_obj(0u);
x_12 = lean::array_fset(x_6, x_7, x_11);
x_13 = lean::cnstr_get(x_4, 1);
lean::inc(x_13);
lean::dec(x_4);
x_14 = x_10;
x_15 = !lean::is_exclusive(x_14);
if (x_15 == 0)
{
obj* x_16; obj* x_17; obj* x_18; 
x_16 = lean::cnstr_get(x_14, 2);
x_17 = lean::cnstr_get(x_14, 3);
lean::inc(x_3);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_3);
lean::cnstr_set(x_18, 1, x_16);
if (lean::obj_tag(x_17) == 0)
{
obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_3);
lean::dec(x_1);
lean::cnstr_set(x_14, 2, x_18);
x_19 = l_Lean_EnvExtensionState_Inhabited;
x_20 = x_14;
x_21 = lean::array_fset(x_12, x_7, x_20);
lean::dec(x_7);
lean::cnstr_set(x_2, 2, x_21);
return x_2;
}
else
{
uint8 x_22; 
x_22 = !lean::is_exclusive(x_17);
if (x_22 == 0)
{
obj* x_23; obj* x_24; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_23 = lean::cnstr_get(x_17, 0);
x_24 = lean::cnstr_get(x_1, 3);
lean::inc(x_24);
lean::dec(x_1);
x_25 = 0;
x_26 = lean::box(x_25);
x_27 = lean::apply_3(x_24, x_26, x_23, x_3);
lean::cnstr_set(x_17, 0, x_27);
lean::cnstr_set(x_14, 2, x_18);
x_28 = l_Lean_EnvExtensionState_Inhabited;
x_29 = x_14;
x_30 = lean::array_fset(x_12, x_7, x_29);
lean::dec(x_7);
lean::cnstr_set(x_2, 2, x_30);
return x_2;
}
else
{
obj* x_31; obj* x_32; uint8 x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_31 = lean::cnstr_get(x_17, 0);
lean::inc(x_31);
lean::dec(x_17);
x_32 = lean::cnstr_get(x_1, 3);
lean::inc(x_32);
lean::dec(x_1);
x_33 = 0;
x_34 = lean::box(x_33);
x_35 = lean::apply_3(x_32, x_34, x_31, x_3);
x_36 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_14, 3, x_36);
lean::cnstr_set(x_14, 2, x_18);
x_37 = l_Lean_EnvExtensionState_Inhabited;
x_38 = x_14;
x_39 = lean::array_fset(x_12, x_7, x_38);
lean::dec(x_7);
lean::cnstr_set(x_2, 2, x_39);
return x_2;
}
}
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_40 = lean::cnstr_get(x_14, 0);
x_41 = lean::cnstr_get(x_14, 1);
x_42 = lean::cnstr_get(x_14, 2);
x_43 = lean::cnstr_get(x_14, 3);
lean::inc(x_43);
lean::inc(x_42);
lean::inc(x_41);
lean::inc(x_40);
lean::dec(x_14);
lean::inc(x_3);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_3);
lean::cnstr_set(x_44, 1, x_42);
if (lean::obj_tag(x_43) == 0)
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
lean::dec(x_3);
lean::dec(x_1);
x_45 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_45, 0, x_40);
lean::cnstr_set(x_45, 1, x_41);
lean::cnstr_set(x_45, 2, x_44);
lean::cnstr_set(x_45, 3, x_43);
x_46 = l_Lean_EnvExtensionState_Inhabited;
x_47 = x_45;
x_48 = lean::array_fset(x_12, x_7, x_47);
lean::dec(x_7);
lean::cnstr_set(x_2, 2, x_48);
return x_2;
}
else
{
obj* x_49; obj* x_50; obj* x_51; uint8 x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_49 = lean::cnstr_get(x_43, 0);
lean::inc(x_49);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_release(x_43, 0);
 x_50 = x_43;
} else {
 lean::dec_ref(x_43);
 x_50 = lean::box(0);
}
x_51 = lean::cnstr_get(x_1, 3);
lean::inc(x_51);
lean::dec(x_1);
x_52 = 0;
x_53 = lean::box(x_52);
x_54 = lean::apply_3(x_51, x_53, x_49, x_3);
if (lean::is_scalar(x_50)) {
 x_55 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_55 = x_50;
}
lean::cnstr_set(x_55, 0, x_54);
x_56 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_56, 0, x_40);
lean::cnstr_set(x_56, 1, x_41);
lean::cnstr_set(x_56, 2, x_44);
lean::cnstr_set(x_56, 3, x_55);
x_57 = l_Lean_EnvExtensionState_Inhabited;
x_58 = x_56;
x_59 = lean::array_fset(x_12, x_7, x_58);
lean::dec(x_7);
lean::cnstr_set(x_2, 2, x_59);
return x_2;
}
}
}
}
else
{
obj* x_60; obj* x_61; obj* x_62; uint32 x_63; uint8 x_64; obj* x_65; obj* x_66; obj* x_67; uint8 x_68; 
x_60 = lean::cnstr_get(x_2, 0);
x_61 = lean::cnstr_get(x_2, 1);
x_62 = lean::cnstr_get(x_2, 2);
x_63 = lean::cnstr_get_scalar<uint32>(x_2, sizeof(void*)*4);
x_64 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*4 + 4);
x_65 = lean::cnstr_get(x_2, 3);
lean::inc(x_65);
lean::inc(x_62);
lean::inc(x_61);
lean::inc(x_60);
lean::dec(x_2);
x_66 = lean::cnstr_get(x_4, 0);
lean::inc(x_66);
x_67 = lean::array_get_size(x_62);
x_68 = lean::nat_dec_lt(x_66, x_67);
lean::dec(x_67);
if (x_68 == 0)
{
obj* x_69; 
lean::dec(x_66);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_69 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_69, 0, x_60);
lean::cnstr_set(x_69, 1, x_61);
lean::cnstr_set(x_69, 2, x_62);
lean::cnstr_set(x_69, 3, x_65);
lean::cnstr_set_scalar(x_69, sizeof(void*)*4, x_63);
lean::cnstr_set_scalar(x_69, sizeof(void*)*4 + 4, x_64);
return x_69;
}
else
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_70 = lean::array_fget(x_62, x_66);
x_71 = lean::mk_nat_obj(0u);
x_72 = lean::array_fset(x_62, x_66, x_71);
x_73 = lean::cnstr_get(x_4, 1);
lean::inc(x_73);
lean::dec(x_4);
x_74 = x_70;
x_75 = lean::cnstr_get(x_74, 0);
lean::inc(x_75);
x_76 = lean::cnstr_get(x_74, 1);
lean::inc(x_76);
x_77 = lean::cnstr_get(x_74, 2);
lean::inc(x_77);
x_78 = lean::cnstr_get(x_74, 3);
lean::inc(x_78);
if (lean::is_exclusive(x_74)) {
 lean::cnstr_release(x_74, 0);
 lean::cnstr_release(x_74, 1);
 lean::cnstr_release(x_74, 2);
 lean::cnstr_release(x_74, 3);
 x_79 = x_74;
} else {
 lean::dec_ref(x_74);
 x_79 = lean::box(0);
}
lean::inc(x_3);
x_80 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_80, 0, x_3);
lean::cnstr_set(x_80, 1, x_77);
if (lean::obj_tag(x_78) == 0)
{
obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
lean::dec(x_3);
lean::dec(x_1);
if (lean::is_scalar(x_79)) {
 x_81 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_81 = x_79;
}
lean::cnstr_set(x_81, 0, x_75);
lean::cnstr_set(x_81, 1, x_76);
lean::cnstr_set(x_81, 2, x_80);
lean::cnstr_set(x_81, 3, x_78);
x_82 = l_Lean_EnvExtensionState_Inhabited;
x_83 = x_81;
x_84 = lean::array_fset(x_72, x_66, x_83);
lean::dec(x_66);
x_85 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_85, 0, x_60);
lean::cnstr_set(x_85, 1, x_61);
lean::cnstr_set(x_85, 2, x_84);
lean::cnstr_set(x_85, 3, x_65);
lean::cnstr_set_scalar(x_85, sizeof(void*)*4, x_63);
lean::cnstr_set_scalar(x_85, sizeof(void*)*4 + 4, x_64);
return x_85;
}
else
{
obj* x_86; obj* x_87; obj* x_88; uint8 x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_86 = lean::cnstr_get(x_78, 0);
lean::inc(x_86);
if (lean::is_exclusive(x_78)) {
 lean::cnstr_release(x_78, 0);
 x_87 = x_78;
} else {
 lean::dec_ref(x_78);
 x_87 = lean::box(0);
}
x_88 = lean::cnstr_get(x_1, 3);
lean::inc(x_88);
lean::dec(x_1);
x_89 = 0;
x_90 = lean::box(x_89);
x_91 = lean::apply_3(x_88, x_90, x_86, x_3);
if (lean::is_scalar(x_87)) {
 x_92 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_92 = x_87;
}
lean::cnstr_set(x_92, 0, x_91);
if (lean::is_scalar(x_79)) {
 x_93 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_93 = x_79;
}
lean::cnstr_set(x_93, 0, x_75);
lean::cnstr_set(x_93, 1, x_76);
lean::cnstr_set(x_93, 2, x_80);
lean::cnstr_set(x_93, 3, x_92);
x_94 = l_Lean_EnvExtensionState_Inhabited;
x_95 = x_93;
x_96 = lean::array_fset(x_72, x_66, x_95);
lean::dec(x_66);
x_97 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_97, 0, x_60);
lean::cnstr_set(x_97, 1, x_61);
lean::cnstr_set(x_97, 2, x_96);
lean::cnstr_set(x_97, 3, x_65);
lean::cnstr_set_scalar(x_97, sizeof(void*)*4, x_63);
lean::cnstr_set_scalar(x_97, sizeof(void*)*4 + 4, x_64);
return x_97;
}
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
obj* l_List_foldr___main___at_Lean_PersistentEnvExtension_forceStateAux___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_3);
lean::dec(x_1);
lean::inc(x_2);
return x_2;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
lean::dec(x_3);
lean::inc(x_1);
x_6 = l_List_foldr___main___at_Lean_PersistentEnvExtension_forceStateAux___spec__1___rarg(x_1, x_2, x_5);
x_7 = lean::cnstr_get(x_1, 3);
lean::inc(x_7);
lean::dec(x_1);
x_8 = 0;
x_9 = lean::box(x_8);
x_10 = lean::apply_3(x_7, x_9, x_6, x_4);
return x_10;
}
}
}
obj* l_List_foldr___main___at_Lean_PersistentEnvExtension_forceStateAux___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_foldr___main___at_Lean_PersistentEnvExtension_forceStateAux___spec__1___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_Lean_PersistentEnvExtension_forceStateAux___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::cnstr_get(x_2, 3);
lean::inc(x_3);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_3);
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
x_5 = lean::thunk_get_own(x_4);
lean::dec(x_4);
x_6 = lean::cnstr_get(x_2, 2);
lean::inc(x_6);
lean::dec(x_2);
x_7 = l_List_foldr___main___at_Lean_PersistentEnvExtension_forceStateAux___spec__1___rarg(x_1, x_5, x_6);
lean::dec(x_5);
return x_7;
}
else
{
obj* x_8; 
lean::dec(x_2);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
lean::dec(x_3);
return x_8;
}
}
}
obj* l_Lean_PersistentEnvExtension_forceStateAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_PersistentEnvExtension_forceStateAux___rarg), 2, 0);
return x_3;
}
}
obj* l_List_foldr___main___at_Lean_PersistentEnvExtension_forceStateAux___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_foldr___main___at_Lean_PersistentEnvExtension_forceStateAux___spec__1___rarg(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_PersistentEnvExtension_forceState___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_5 = lean::cnstr_get(x_2, 2);
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_5);
x_8 = lean::nat_dec_lt(x_6, x_7);
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
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; 
x_9 = lean::array_fget(x_5, x_6);
x_10 = lean::mk_nat_obj(0u);
x_11 = lean::array_fset(x_5, x_6, x_10);
x_12 = lean::cnstr_get(x_3, 1);
lean::inc(x_12);
lean::dec(x_3);
x_13 = x_9;
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_15 = lean::cnstr_get(x_13, 1);
lean::inc(x_15);
x_16 = lean::cnstr_get(x_13, 2);
lean::inc(x_16);
lean::inc(x_13);
x_17 = l_Lean_PersistentEnvExtension_forceStateAux___rarg(x_1, x_13);
x_18 = !lean::is_exclusive(x_13);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_19 = lean::cnstr_get(x_13, 3);
lean::dec(x_19);
x_20 = lean::cnstr_get(x_13, 2);
lean::dec(x_20);
x_21 = lean::cnstr_get(x_13, 1);
lean::dec(x_21);
x_22 = lean::cnstr_get(x_13, 0);
lean::dec(x_22);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_17);
lean::cnstr_set(x_13, 3, x_23);
x_24 = l_Lean_EnvExtensionState_Inhabited;
x_25 = x_13;
x_26 = lean::array_fset(x_11, x_6, x_25);
lean::dec(x_6);
lean::cnstr_set(x_2, 2, x_26);
return x_2;
}
else
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_13);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_17);
x_28 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_28, 0, x_14);
lean::cnstr_set(x_28, 1, x_15);
lean::cnstr_set(x_28, 2, x_16);
lean::cnstr_set(x_28, 3, x_27);
x_29 = l_Lean_EnvExtensionState_Inhabited;
x_30 = x_28;
x_31 = lean::array_fset(x_11, x_6, x_30);
lean::dec(x_6);
lean::cnstr_set(x_2, 2, x_31);
return x_2;
}
}
}
else
{
obj* x_32; obj* x_33; obj* x_34; uint32 x_35; uint8 x_36; obj* x_37; obj* x_38; obj* x_39; uint8 x_40; 
x_32 = lean::cnstr_get(x_2, 0);
x_33 = lean::cnstr_get(x_2, 1);
x_34 = lean::cnstr_get(x_2, 2);
x_35 = lean::cnstr_get_scalar<uint32>(x_2, sizeof(void*)*4);
x_36 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*4 + 4);
x_37 = lean::cnstr_get(x_2, 3);
lean::inc(x_37);
lean::inc(x_34);
lean::inc(x_33);
lean::inc(x_32);
lean::dec(x_2);
x_38 = lean::cnstr_get(x_3, 0);
lean::inc(x_38);
x_39 = lean::array_get_size(x_34);
x_40 = lean::nat_dec_lt(x_38, x_39);
lean::dec(x_39);
if (x_40 == 0)
{
obj* x_41; 
lean::dec(x_38);
lean::dec(x_3);
lean::dec(x_1);
x_41 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_41, 0, x_32);
lean::cnstr_set(x_41, 1, x_33);
lean::cnstr_set(x_41, 2, x_34);
lean::cnstr_set(x_41, 3, x_37);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4, x_35);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4 + 4, x_36);
return x_41;
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_42 = lean::array_fget(x_34, x_38);
x_43 = lean::mk_nat_obj(0u);
x_44 = lean::array_fset(x_34, x_38, x_43);
x_45 = lean::cnstr_get(x_3, 1);
lean::inc(x_45);
lean::dec(x_3);
x_46 = x_42;
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
x_48 = lean::cnstr_get(x_46, 1);
lean::inc(x_48);
x_49 = lean::cnstr_get(x_46, 2);
lean::inc(x_49);
lean::inc(x_46);
x_50 = l_Lean_PersistentEnvExtension_forceStateAux___rarg(x_1, x_46);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 lean::cnstr_release(x_46, 1);
 lean::cnstr_release(x_46, 2);
 lean::cnstr_release(x_46, 3);
 x_51 = x_46;
} else {
 lean::dec_ref(x_46);
 x_51 = lean::box(0);
}
x_52 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_52, 0, x_50);
if (lean::is_scalar(x_51)) {
 x_53 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_53 = x_51;
}
lean::cnstr_set(x_53, 0, x_47);
lean::cnstr_set(x_53, 1, x_48);
lean::cnstr_set(x_53, 2, x_49);
lean::cnstr_set(x_53, 3, x_52);
x_54 = l_Lean_EnvExtensionState_Inhabited;
x_55 = x_53;
x_56 = lean::array_fset(x_44, x_38, x_55);
lean::dec(x_38);
x_57 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_57, 0, x_32);
lean::cnstr_set(x_57, 1, x_33);
lean::cnstr_set(x_57, 2, x_56);
lean::cnstr_set(x_57, 3, x_37);
lean::cnstr_set_scalar(x_57, sizeof(void*)*4, x_35);
lean::cnstr_set_scalar(x_57, sizeof(void*)*4 + 4, x_36);
return x_57;
}
}
}
}
obj* l_Lean_PersistentEnvExtension_forceState(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_PersistentEnvExtension_forceState___rarg), 2, 0);
return x_3;
}
}
obj* l_Lean_PersistentEnvExtension_getState___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_4 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_3, x_2);
x_5 = l_Lean_PersistentEnvExtension_forceStateAux___rarg(x_1, x_4);
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
obj* l___private_init_lean_environment_8__mkPersistentEnvExtensionsRef(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Array_empty___closed__1;
x_3 = lean::io_mk_ref(x_2, x_1);
return x_3;
}
}
uint8 l_Array_anyMAux___main___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_3);
x_6 = lean::nat_dec_lt(x_4, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
uint8 x_7; 
lean::dec(x_4);
x_7 = 0;
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; uint8 x_11; 
x_8 = lean::array_fget(x_3, x_4);
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_10 = lean::cnstr_get(x_2, 0);
x_11 = lean_name_dec_eq(x_9, x_10);
lean::dec(x_9);
if (x_11 == 0)
{
obj* x_12; obj* x_13; uint8 x_14; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_4, x_12);
lean::dec(x_4);
x_4 = x_13;
goto _start;
}
else
{
lean::dec(x_4);
return x_11;
}
}
}
}
obj* l_Array_anyMAux___main___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_anyMAux___main___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg___boxed), 4, 0);
return x_3;
}
}
obj* _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_EnvExtensionEntry_Inhabited;
x_2 = l_Lean_EnvExtensionState_Inhabited;
x_3 = l_Lean_PersistentEnvExtension_inhabited___rarg(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("invalid environment extension, '");
return x_1;
}
}
obj* _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3() {
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
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_2, 2);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_2, 3);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_2, 4);
lean::inc(x_8);
x_9 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*5);
lean::inc(x_5);
x_10 = lean::thunk_pure(x_5);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_5);
x_13 = l_Array_empty___closed__1;
x_14 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_10);
lean::cnstr_set(x_14, 2, x_11);
lean::cnstr_set(x_14, 3, x_12);
x_15 = l___private_init_lean_environment_9__persistentEnvExtensionsRef;
x_16 = lean::io_ref_get(x_15, x_3);
if (lean::obj_tag(x_16) == 0)
{
uint8 x_17; 
x_17 = !lean::is_exclusive(x_16);
if (x_17 == 0)
{
obj* x_18; obj* x_19; uint8 x_20; 
x_18 = lean::cnstr_get(x_16, 0);
x_19 = lean::mk_nat_obj(0u);
x_20 = l_Array_anyMAux___main___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg(x_1, x_2, x_18, x_19);
lean::dec(x_18);
lean::dec(x_2);
if (x_20 == 0)
{
obj* x_21; obj* x_22; 
x_21 = lean::box(0);
lean::cnstr_set(x_16, 0, x_21);
x_22 = l_Lean_registerEnvExtensionUnsafe___rarg(x_14, x_16);
if (lean::obj_tag(x_22) == 0)
{
uint8 x_23; 
x_23 = !lean::is_exclusive(x_22);
if (x_23 == 0)
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = lean::cnstr_get(x_22, 0);
lean::cnstr_set(x_22, 0, x_21);
x_25 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_4);
lean::cnstr_set(x_25, 2, x_6);
lean::cnstr_set(x_25, 3, x_7);
lean::cnstr_set(x_25, 4, x_8);
lean::cnstr_set_scalar(x_25, sizeof(void*)*5, x_9);
x_26 = lean::io_ref_get(x_15, x_22);
if (lean::obj_tag(x_26) == 0)
{
uint8 x_27; 
x_27 = !lean::is_exclusive(x_26);
if (x_27 == 0)
{
obj* x_28; obj* x_29; 
x_28 = lean::cnstr_get(x_26, 0);
lean::cnstr_set(x_26, 0, x_21);
x_29 = lean::io_ref_reset(x_15, x_26);
if (lean::obj_tag(x_29) == 0)
{
uint8 x_30; 
x_30 = !lean::is_exclusive(x_29);
if (x_30 == 0)
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_31 = lean::cnstr_get(x_29, 0);
lean::dec(x_31);
lean::cnstr_set(x_29, 0, x_21);
x_32 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
lean::inc(x_25);
x_33 = x_25;
x_34 = lean::array_push(x_28, x_33);
x_35 = lean::io_ref_set(x_15, x_34, x_29);
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
lean::cnstr_set(x_45, 0, x_21);
lean::cnstr_set(x_45, 1, x_44);
x_46 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
lean::inc(x_25);
x_47 = x_25;
x_48 = lean::array_push(x_28, x_47);
x_49 = lean::io_ref_set(x_15, x_48, x_45);
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
lean::cnstr_set(x_63, 0, x_21);
lean::cnstr_set(x_63, 1, x_62);
x_64 = lean::io_ref_reset(x_15, x_63);
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
lean::cnstr_set(x_67, 0, x_21);
lean::cnstr_set(x_67, 1, x_65);
x_68 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
lean::inc(x_25);
x_69 = x_25;
x_70 = lean::array_push(x_61, x_69);
x_71 = lean::io_ref_set(x_15, x_70, x_67);
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
obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
x_87 = lean::cnstr_get(x_22, 0);
x_88 = lean::cnstr_get(x_22, 1);
lean::inc(x_88);
lean::inc(x_87);
lean::dec(x_22);
x_89 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_89, 0, x_21);
lean::cnstr_set(x_89, 1, x_88);
x_90 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_90, 0, x_87);
lean::cnstr_set(x_90, 1, x_4);
lean::cnstr_set(x_90, 2, x_6);
lean::cnstr_set(x_90, 3, x_7);
lean::cnstr_set(x_90, 4, x_8);
lean::cnstr_set_scalar(x_90, sizeof(void*)*5, x_9);
x_91 = lean::io_ref_get(x_15, x_89);
if (lean::obj_tag(x_91) == 0)
{
obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; 
x_92 = lean::cnstr_get(x_91, 0);
lean::inc(x_92);
x_93 = lean::cnstr_get(x_91, 1);
lean::inc(x_93);
if (lean::is_exclusive(x_91)) {
 lean::cnstr_release(x_91, 0);
 lean::cnstr_release(x_91, 1);
 x_94 = x_91;
} else {
 lean::dec_ref(x_91);
 x_94 = lean::box(0);
}
if (lean::is_scalar(x_94)) {
 x_95 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_95 = x_94;
}
lean::cnstr_set(x_95, 0, x_21);
lean::cnstr_set(x_95, 1, x_93);
x_96 = lean::io_ref_reset(x_15, x_95);
if (lean::obj_tag(x_96) == 0)
{
obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; 
x_97 = lean::cnstr_get(x_96, 1);
lean::inc(x_97);
if (lean::is_exclusive(x_96)) {
 lean::cnstr_release(x_96, 0);
 lean::cnstr_release(x_96, 1);
 x_98 = x_96;
} else {
 lean::dec_ref(x_96);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_98)) {
 x_99 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_99 = x_98;
}
lean::cnstr_set(x_99, 0, x_21);
lean::cnstr_set(x_99, 1, x_97);
x_100 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
lean::inc(x_90);
x_101 = x_90;
x_102 = lean::array_push(x_92, x_101);
x_103 = lean::io_ref_set(x_15, x_102, x_99);
if (lean::obj_tag(x_103) == 0)
{
obj* x_104; obj* x_105; obj* x_106; 
x_104 = lean::cnstr_get(x_103, 1);
lean::inc(x_104);
if (lean::is_exclusive(x_103)) {
 lean::cnstr_release(x_103, 0);
 lean::cnstr_release(x_103, 1);
 x_105 = x_103;
} else {
 lean::dec_ref(x_103);
 x_105 = lean::box(0);
}
if (lean::is_scalar(x_105)) {
 x_106 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_106 = x_105;
}
lean::cnstr_set(x_106, 0, x_90);
lean::cnstr_set(x_106, 1, x_104);
return x_106;
}
else
{
obj* x_107; obj* x_108; obj* x_109; obj* x_110; 
lean::dec(x_90);
x_107 = lean::cnstr_get(x_103, 0);
lean::inc(x_107);
x_108 = lean::cnstr_get(x_103, 1);
lean::inc(x_108);
if (lean::is_exclusive(x_103)) {
 lean::cnstr_release(x_103, 0);
 lean::cnstr_release(x_103, 1);
 x_109 = x_103;
} else {
 lean::dec_ref(x_103);
 x_109 = lean::box(0);
}
if (lean::is_scalar(x_109)) {
 x_110 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_110 = x_109;
}
lean::cnstr_set(x_110, 0, x_107);
lean::cnstr_set(x_110, 1, x_108);
return x_110;
}
}
else
{
obj* x_111; obj* x_112; obj* x_113; obj* x_114; 
lean::dec(x_92);
lean::dec(x_90);
x_111 = lean::cnstr_get(x_96, 0);
lean::inc(x_111);
x_112 = lean::cnstr_get(x_96, 1);
lean::inc(x_112);
if (lean::is_exclusive(x_96)) {
 lean::cnstr_release(x_96, 0);
 lean::cnstr_release(x_96, 1);
 x_113 = x_96;
} else {
 lean::dec_ref(x_96);
 x_113 = lean::box(0);
}
if (lean::is_scalar(x_113)) {
 x_114 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_114 = x_113;
}
lean::cnstr_set(x_114, 0, x_111);
lean::cnstr_set(x_114, 1, x_112);
return x_114;
}
}
else
{
obj* x_115; obj* x_116; obj* x_117; obj* x_118; 
lean::dec(x_90);
x_115 = lean::cnstr_get(x_91, 0);
lean::inc(x_115);
x_116 = lean::cnstr_get(x_91, 1);
lean::inc(x_116);
if (lean::is_exclusive(x_91)) {
 lean::cnstr_release(x_91, 0);
 lean::cnstr_release(x_91, 1);
 x_117 = x_91;
} else {
 lean::dec_ref(x_91);
 x_117 = lean::box(0);
}
if (lean::is_scalar(x_117)) {
 x_118 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_118 = x_117;
}
lean::cnstr_set(x_118, 0, x_115);
lean::cnstr_set(x_118, 1, x_116);
return x_118;
}
}
}
else
{
uint8 x_119; 
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_4);
x_119 = !lean::is_exclusive(x_22);
if (x_119 == 0)
{
return x_22;
}
else
{
obj* x_120; obj* x_121; obj* x_122; 
x_120 = lean::cnstr_get(x_22, 0);
x_121 = lean::cnstr_get(x_22, 1);
lean::inc(x_121);
lean::inc(x_120);
lean::dec(x_22);
x_122 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_122, 0, x_120);
lean::cnstr_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; 
lean::dec(x_14);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_6);
x_123 = l_Lean_Name_toString___closed__1;
x_124 = l_Lean_Name_toStringWithSep___main(x_123, x_4);
x_125 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_126 = lean::string_append(x_125, x_124);
lean::dec(x_124);
x_127 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_128 = lean::string_append(x_126, x_127);
lean::cnstr_set_tag(x_16, 1);
lean::cnstr_set(x_16, 0, x_128);
return x_16;
}
}
else
{
obj* x_129; obj* x_130; obj* x_131; uint8 x_132; 
x_129 = lean::cnstr_get(x_16, 0);
x_130 = lean::cnstr_get(x_16, 1);
lean::inc(x_130);
lean::inc(x_129);
lean::dec(x_16);
x_131 = lean::mk_nat_obj(0u);
x_132 = l_Array_anyMAux___main___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg(x_1, x_2, x_129, x_131);
lean::dec(x_129);
lean::dec(x_2);
if (x_132 == 0)
{
obj* x_133; obj* x_134; obj* x_135; 
x_133 = lean::box(0);
x_134 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_134, 0, x_133);
lean::cnstr_set(x_134, 1, x_130);
x_135 = l_Lean_registerEnvExtensionUnsafe___rarg(x_14, x_134);
if (lean::obj_tag(x_135) == 0)
{
obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; 
x_136 = lean::cnstr_get(x_135, 0);
lean::inc(x_136);
x_137 = lean::cnstr_get(x_135, 1);
lean::inc(x_137);
if (lean::is_exclusive(x_135)) {
 lean::cnstr_release(x_135, 0);
 lean::cnstr_release(x_135, 1);
 x_138 = x_135;
} else {
 lean::dec_ref(x_135);
 x_138 = lean::box(0);
}
if (lean::is_scalar(x_138)) {
 x_139 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_139 = x_138;
}
lean::cnstr_set(x_139, 0, x_133);
lean::cnstr_set(x_139, 1, x_137);
x_140 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_140, 0, x_136);
lean::cnstr_set(x_140, 1, x_4);
lean::cnstr_set(x_140, 2, x_6);
lean::cnstr_set(x_140, 3, x_7);
lean::cnstr_set(x_140, 4, x_8);
lean::cnstr_set_scalar(x_140, sizeof(void*)*5, x_9);
x_141 = lean::io_ref_get(x_15, x_139);
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
lean::cnstr_set(x_145, 0, x_133);
lean::cnstr_set(x_145, 1, x_143);
x_146 = lean::io_ref_reset(x_15, x_145);
if (lean::obj_tag(x_146) == 0)
{
obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; 
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
lean::cnstr_set(x_149, 0, x_133);
lean::cnstr_set(x_149, 1, x_147);
x_150 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
lean::inc(x_140);
x_151 = x_140;
x_152 = lean::array_push(x_142, x_151);
x_153 = lean::io_ref_set(x_15, x_152, x_149);
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
lean::cnstr_set(x_156, 0, x_140);
lean::cnstr_set(x_156, 1, x_154);
return x_156;
}
else
{
obj* x_157; obj* x_158; obj* x_159; obj* x_160; 
lean::dec(x_140);
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
lean::dec(x_142);
lean::dec(x_140);
x_161 = lean::cnstr_get(x_146, 0);
lean::inc(x_161);
x_162 = lean::cnstr_get(x_146, 1);
lean::inc(x_162);
if (lean::is_exclusive(x_146)) {
 lean::cnstr_release(x_146, 0);
 lean::cnstr_release(x_146, 1);
 x_163 = x_146;
} else {
 lean::dec_ref(x_146);
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
lean::dec(x_140);
x_165 = lean::cnstr_get(x_141, 0);
lean::inc(x_165);
x_166 = lean::cnstr_get(x_141, 1);
lean::inc(x_166);
if (lean::is_exclusive(x_141)) {
 lean::cnstr_release(x_141, 0);
 lean::cnstr_release(x_141, 1);
 x_167 = x_141;
} else {
 lean::dec_ref(x_141);
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
else
{
obj* x_169; obj* x_170; obj* x_171; obj* x_172; 
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_4);
x_169 = lean::cnstr_get(x_135, 0);
lean::inc(x_169);
x_170 = lean::cnstr_get(x_135, 1);
lean::inc(x_170);
if (lean::is_exclusive(x_135)) {
 lean::cnstr_release(x_135, 0);
 lean::cnstr_release(x_135, 1);
 x_171 = x_135;
} else {
 lean::dec_ref(x_135);
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
obj* x_173; obj* x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; 
lean::dec(x_14);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_6);
x_173 = l_Lean_Name_toString___closed__1;
x_174 = l_Lean_Name_toStringWithSep___main(x_173, x_4);
x_175 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_176 = lean::string_append(x_175, x_174);
lean::dec(x_174);
x_177 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_178 = lean::string_append(x_176, x_177);
x_179 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_179, 0, x_178);
lean::cnstr_set(x_179, 1, x_130);
return x_179;
}
}
}
else
{
uint8 x_180; 
lean::dec(x_14);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_4);
lean::dec(x_2);
x_180 = !lean::is_exclusive(x_16);
if (x_180 == 0)
{
return x_16;
}
else
{
obj* x_181; obj* x_182; obj* x_183; 
x_181 = lean::cnstr_get(x_16, 0);
x_182 = lean::cnstr_get(x_16, 1);
lean::inc(x_182);
lean::inc(x_181);
lean::dec(x_16);
x_183 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_183, 0, x_181);
lean::cnstr_set(x_183, 1, x_182);
return x_183;
}
}
}
}
obj* l_Lean_registerPersistentEnvExtensionUnsafe(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_Array_anyMAux___main___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = l_Array_anyMAux___main___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_6 = lean::box(x_5);
return x_6;
}
}
obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
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
obj* _init_l_Lean_CPPExtensionState_Inhabited() {
_start:
{
obj* x_1; 
x_1 = l_NonScalar_Inhabited;
return x_1;
}
}
namespace lean {
obj* register_extension_core(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_unsafeIO___rarg___closed__1;
x_3 = l_Lean_registerEnvExtensionUnsafe___rarg(x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
else
{
obj* x_7; 
lean::dec(x_3);
x_7 = lean::box(0);
return x_7;
}
}
}
}
namespace lean {
obj* set_extension_core(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::box(0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_4);
x_6 = l___private_init_lean_environment_6__envExtensionsRef;
x_7 = lean::io_ref_get(x_6, x_5);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
lean::dec(x_7);
x_9 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
x_10 = lean::array_get(x_9, x_8, x_2);
lean::dec(x_2);
lean::dec(x_8);
x_11 = l_Lean_EnvExtension_setStateUnsafe___rarg(x_10, x_1, x_3);
lean::dec(x_10);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
else
{
obj* x_13; 
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_13 = lean::box(0);
return x_13;
}
}
}
}
namespace lean {
obj* get_extension_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::box(0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_3);
x_5 = l___private_init_lean_environment_6__envExtensionsRef;
x_6 = lean::io_ref_get(x_5, x_4);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
lean::dec(x_6);
x_8 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
x_9 = lean::array_get(x_8, x_7, x_2);
lean::dec(x_2);
lean::dec(x_7);
x_10 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_9, x_1);
lean::dec(x_1);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
else
{
obj* x_12; 
lean::dec(x_6);
lean::dec(x_2);
lean::dec(x_1);
x_12 = lean::box(0);
return x_12;
}
}
}
}
obj* _init_l_Lean_Modification_Inhabited() {
_start:
{
obj* x_1; 
x_1 = l_NonScalar_Inhabited;
return x_1;
}
}
obj* l_Lean_regModListExtension(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = l_Lean_registerEnvExtensionUnsafe___rarg(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_addModification___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_modListExtension;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
return x_2;
}
}
obj* _init_l_Lean_addModification___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_modListExtension;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
return x_2;
}
}
namespace lean {
obj* environment_add_modification_core(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_4 = lean::cnstr_get(x_1, 2);
x_5 = lean::array_get_size(x_4);
x_6 = l_Lean_addModification___closed__1;
x_7 = lean::nat_dec_lt(x_6, x_5);
lean::dec(x_5);
if (x_7 == 0)
{
lean::dec(x_2);
return x_1;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_8 = lean::array_fget(x_4, x_6);
x_9 = lean::mk_nat_obj(0u);
x_10 = lean::array_fset(x_4, x_6, x_9);
x_11 = l_Lean_addModification___closed__2;
x_12 = x_8;
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_2);
lean::cnstr_set(x_13, 1, x_12);
x_14 = l_Lean_EnvExtensionState_Inhabited;
x_15 = x_13;
x_16 = lean::array_fset(x_10, x_6, x_15);
lean::cnstr_set(x_1, 2, x_16);
return x_1;
}
}
else
{
obj* x_17; obj* x_18; obj* x_19; uint32 x_20; uint8 x_21; obj* x_22; obj* x_23; obj* x_24; uint8 x_25; 
x_17 = lean::cnstr_get(x_1, 0);
x_18 = lean::cnstr_get(x_1, 1);
x_19 = lean::cnstr_get(x_1, 2);
x_20 = lean::cnstr_get_scalar<uint32>(x_1, sizeof(void*)*4);
x_21 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4 + 4);
x_22 = lean::cnstr_get(x_1, 3);
lean::inc(x_22);
lean::inc(x_19);
lean::inc(x_18);
lean::inc(x_17);
lean::dec(x_1);
x_23 = lean::array_get_size(x_19);
x_24 = l_Lean_addModification___closed__1;
x_25 = lean::nat_dec_lt(x_24, x_23);
lean::dec(x_23);
if (x_25 == 0)
{
obj* x_26; 
lean::dec(x_2);
x_26 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_26, 0, x_17);
lean::cnstr_set(x_26, 1, x_18);
lean::cnstr_set(x_26, 2, x_19);
lean::cnstr_set(x_26, 3, x_22);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_20);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4 + 4, x_21);
return x_26;
}
else
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_27 = lean::array_fget(x_19, x_24);
x_28 = lean::mk_nat_obj(0u);
x_29 = lean::array_fset(x_19, x_24, x_28);
x_30 = l_Lean_addModification___closed__2;
x_31 = x_27;
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_2);
lean::cnstr_set(x_32, 1, x_31);
x_33 = l_Lean_EnvExtensionState_Inhabited;
x_34 = x_32;
x_35 = lean::array_fset(x_29, x_24, x_34);
x_36 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_36, 0, x_17);
lean::cnstr_set(x_36, 1, x_18);
lean::cnstr_set(x_36, 2, x_35);
lean::cnstr_set(x_36, 3, x_22);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_20);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4 + 4, x_21);
return x_36;
}
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
obj* _init_l_Lean_ModuleData_inhabited() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::mk_empty_array(x_1);
x_3 = l_ByteArray_empty;
lean::inc(x_2, 2);
x_4 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_3);
return x_4;
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
x_7 = lean::nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_4, x_8);
x_10 = lean::nat_sub(x_3, x_4);
lean::dec(x_4);
x_11 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_12 = lean::array_get(x_11, x_2, x_10);
lean::dec(x_10);
lean::inc(x_12);
x_13 = l_Lean_PersistentEnvExtension_getEntries___rarg(x_12, x_1);
x_14 = lean::cnstr_get(x_12, 4);
lean::inc(x_14);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
x_16 = l_List_reverse___rarg(x_13);
x_17 = lean::apply_1(x_14, x_16);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_15);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::array_push(x_5, x_18);
x_4 = x_9;
x_5 = x_19;
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
lean::dec(x_2);
return x_1;
}
else
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_2, 2);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_2, 3);
lean::inc(x_5);
lean::dec(x_2);
x_6 = l_RBNode_fold___main___at_Lean_mkModuleData___spec__2(x_1, x_3);
x_7 = lean::array_push(x_6, x_4);
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
x_3 = l___private_init_lean_environment_9__persistentEnvExtensionsRef;
x_4 = lean::io_ref_get(x_3, x_2);
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
x_8 = lean::array_get_size(x_6);
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
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_15 = lean::cnstr_get(x_13, 0);
x_16 = lean::cnstr_get(x_1, 3);
lean::inc(x_16);
x_17 = lean::cnstr_get(x_1, 1);
lean::inc(x_17);
lean::dec(x_1);
x_18 = lean::cnstr_get(x_17, 1);
lean::inc(x_18);
lean::dec(x_17);
x_19 = l_RBNode_fold___main___at_Lean_mkModuleData___spec__2(x_9, x_18);
x_20 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_20, 0, x_16);
lean::cnstr_set(x_20, 1, x_19);
lean::cnstr_set(x_20, 2, x_10);
lean::cnstr_set(x_20, 3, x_15);
lean::cnstr_set(x_13, 0, x_20);
return x_13;
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_21 = lean::cnstr_get(x_13, 0);
x_22 = lean::cnstr_get(x_13, 1);
lean::inc(x_22);
lean::inc(x_21);
lean::dec(x_13);
x_23 = lean::cnstr_get(x_1, 3);
lean::inc(x_23);
x_24 = lean::cnstr_get(x_1, 1);
lean::inc(x_24);
lean::dec(x_1);
x_25 = lean::cnstr_get(x_24, 1);
lean::inc(x_25);
lean::dec(x_24);
x_26 = l_RBNode_fold___main___at_Lean_mkModuleData___spec__2(x_9, x_25);
x_27 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set(x_27, 1, x_26);
lean::cnstr_set(x_27, 2, x_10);
lean::cnstr_set(x_27, 3, x_21);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_22);
return x_28;
}
}
else
{
uint8 x_29; 
lean::dec(x_10);
lean::dec(x_1);
x_29 = !lean::is_exclusive(x_13);
if (x_29 == 0)
{
return x_13;
}
else
{
obj* x_30; obj* x_31; obj* x_32; 
x_30 = lean::cnstr_get(x_13, 0);
x_31 = lean::cnstr_get(x_13, 1);
lean::inc(x_31);
lean::inc(x_30);
lean::dec(x_13);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_33 = lean::cnstr_get(x_4, 0);
x_34 = lean::cnstr_get(x_4, 1);
lean::inc(x_34);
lean::inc(x_33);
lean::dec(x_4);
x_35 = lean::box(0);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_34);
x_37 = lean::array_get_size(x_33);
x_38 = l_Array_empty___closed__1;
lean::inc(x_37);
x_39 = l_Nat_foldAux___main___at_Lean_mkModuleData___spec__1(x_1, x_33, x_37, x_37, x_38);
lean::dec(x_37);
lean::dec(x_33);
x_40 = l_Lean_modListExtension;
x_41 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_40, x_1);
x_42 = lean_serialize_modifications(x_41, x_36);
if (lean::obj_tag(x_42) == 0)
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
x_44 = lean::cnstr_get(x_42, 1);
lean::inc(x_44);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_release(x_42, 0);
 lean::cnstr_release(x_42, 1);
 x_45 = x_42;
} else {
 lean::dec_ref(x_42);
 x_45 = lean::box(0);
}
x_46 = lean::cnstr_get(x_1, 3);
lean::inc(x_46);
x_47 = lean::cnstr_get(x_1, 1);
lean::inc(x_47);
lean::dec(x_1);
x_48 = lean::cnstr_get(x_47, 1);
lean::inc(x_48);
lean::dec(x_47);
x_49 = l_RBNode_fold___main___at_Lean_mkModuleData___spec__2(x_38, x_48);
x_50 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_50, 0, x_46);
lean::cnstr_set(x_50, 1, x_49);
lean::cnstr_set(x_50, 2, x_39);
lean::cnstr_set(x_50, 3, x_43);
if (lean::is_scalar(x_45)) {
 x_51 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_51 = x_45;
}
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_44);
return x_51;
}
else
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_39);
lean::dec(x_1);
x_52 = lean::cnstr_get(x_42, 0);
lean::inc(x_52);
x_53 = lean::cnstr_get(x_42, 1);
lean::inc(x_53);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_release(x_42, 0);
 lean::cnstr_release(x_42, 1);
 x_54 = x_42;
} else {
 lean::dec_ref(x_42);
 x_54 = lean::box(0);
}
if (lean::is_scalar(x_54)) {
 x_55 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_55 = x_54;
}
lean::cnstr_set(x_55, 0, x_52);
lean::cnstr_set(x_55, 1, x_53);
return x_55;
}
}
}
else
{
uint8 x_56; 
lean::dec(x_1);
x_56 = !lean::is_exclusive(x_4);
if (x_56 == 0)
{
return x_4;
}
else
{
obj* x_57; obj* x_58; obj* x_59; 
x_57 = lean::cnstr_get(x_4, 0);
x_58 = lean::cnstr_get(x_4, 1);
lean::inc(x_58);
lean::inc(x_57);
lean::dec(x_4);
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_57);
lean::cnstr_set(x_59, 1, x_58);
return x_59;
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
namespace lean {
obj* write_module_core(obj* x_1, obj* x_2, obj* x_3) {
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
}
obj* l_Lean_findOLean___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_find_olean(x_1, x_2);
return x_3;
}
}
obj* l_Lean_importModulesAux___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; 
lean::dec(x_1);
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
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_14 = lean::cnstr_get(x_2, 1);
lean::dec(x_14);
x_15 = lean::cnstr_get(x_2, 0);
lean::dec(x_15);
x_16 = lean::box(0);
lean::inc(x_8);
x_17 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_10, x_8, x_16);
x_18 = lean_find_olean(x_8, x_3);
if (lean::obj_tag(x_18) == 0)
{
uint8 x_19; 
x_19 = !lean::is_exclusive(x_18);
if (x_19 == 0)
{
obj* x_20; obj* x_21; 
x_20 = lean::cnstr_get(x_18, 0);
lean::cnstr_set(x_18, 0, x_16);
x_21 = lean_read_module_data(x_20, x_18);
lean::dec(x_20);
if (lean::obj_tag(x_21) == 0)
{
uint8 x_22; 
x_22 = !lean::is_exclusive(x_21);
if (x_22 == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_23 = lean::cnstr_get(x_21, 0);
lean::cnstr_set(x_21, 0, x_16);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
x_25 = l_Array_toList___rarg(x_24);
lean::dec(x_24);
lean::cnstr_set(x_2, 0, x_17);
x_26 = l_Lean_importModulesAux___main(x_25, x_2, x_21);
if (lean::obj_tag(x_26) == 0)
{
uint8 x_27; 
x_27 = !lean::is_exclusive(x_26);
if (x_27 == 0)
{
obj* x_28; uint8 x_29; 
x_28 = lean::cnstr_get(x_26, 0);
lean::cnstr_set(x_26, 0, x_16);
x_29 = !lean::is_exclusive(x_28);
if (x_29 == 0)
{
obj* x_30; obj* x_31; obj* x_32; 
x_30 = lean::cnstr_get(x_28, 1);
x_31 = lean::array_push(x_30, x_23);
lean::cnstr_set(x_28, 1, x_31);
x_1 = x_9;
x_2 = x_28;
x_3 = x_26;
goto _start;
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_33 = lean::cnstr_get(x_28, 0);
x_34 = lean::cnstr_get(x_28, 1);
lean::inc(x_34);
lean::inc(x_33);
lean::dec(x_28);
x_35 = lean::array_push(x_34, x_23);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_33);
lean::cnstr_set(x_36, 1, x_35);
x_1 = x_9;
x_2 = x_36;
x_3 = x_26;
goto _start;
}
}
else
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_38 = lean::cnstr_get(x_26, 0);
x_39 = lean::cnstr_get(x_26, 1);
lean::inc(x_39);
lean::inc(x_38);
lean::dec(x_26);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_16);
lean::cnstr_set(x_40, 1, x_39);
x_41 = lean::cnstr_get(x_38, 0);
lean::inc(x_41);
x_42 = lean::cnstr_get(x_38, 1);
lean::inc(x_42);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 lean::cnstr_release(x_38, 1);
 x_43 = x_38;
} else {
 lean::dec_ref(x_38);
 x_43 = lean::box(0);
}
x_44 = lean::array_push(x_42, x_23);
if (lean::is_scalar(x_43)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_43;
}
lean::cnstr_set(x_45, 0, x_41);
lean::cnstr_set(x_45, 1, x_44);
x_1 = x_9;
x_2 = x_45;
x_3 = x_40;
goto _start;
}
}
else
{
uint8 x_47; 
lean::dec(x_23);
lean::dec(x_9);
x_47 = !lean::is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
obj* x_48; obj* x_49; obj* x_50; 
x_48 = lean::cnstr_get(x_26, 0);
x_49 = lean::cnstr_get(x_26, 1);
lean::inc(x_49);
lean::inc(x_48);
lean::dec(x_26);
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_51 = lean::cnstr_get(x_21, 0);
x_52 = lean::cnstr_get(x_21, 1);
lean::inc(x_52);
lean::inc(x_51);
lean::dec(x_21);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_16);
lean::cnstr_set(x_53, 1, x_52);
x_54 = lean::cnstr_get(x_51, 0);
lean::inc(x_54);
x_55 = l_Array_toList___rarg(x_54);
lean::dec(x_54);
lean::cnstr_set(x_2, 0, x_17);
x_56 = l_Lean_importModulesAux___main(x_55, x_2, x_53);
if (lean::obj_tag(x_56) == 0)
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_57 = lean::cnstr_get(x_56, 0);
lean::inc(x_57);
x_58 = lean::cnstr_get(x_56, 1);
lean::inc(x_58);
if (lean::is_exclusive(x_56)) {
 lean::cnstr_release(x_56, 0);
 lean::cnstr_release(x_56, 1);
 x_59 = x_56;
} else {
 lean::dec_ref(x_56);
 x_59 = lean::box(0);
}
if (lean::is_scalar(x_59)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_59;
}
lean::cnstr_set(x_60, 0, x_16);
lean::cnstr_set(x_60, 1, x_58);
x_61 = lean::cnstr_get(x_57, 0);
lean::inc(x_61);
x_62 = lean::cnstr_get(x_57, 1);
lean::inc(x_62);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 lean::cnstr_release(x_57, 1);
 x_63 = x_57;
} else {
 lean::dec_ref(x_57);
 x_63 = lean::box(0);
}
x_64 = lean::array_push(x_62, x_51);
if (lean::is_scalar(x_63)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_63;
}
lean::cnstr_set(x_65, 0, x_61);
lean::cnstr_set(x_65, 1, x_64);
x_1 = x_9;
x_2 = x_65;
x_3 = x_60;
goto _start;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
lean::dec(x_51);
lean::dec(x_9);
x_67 = lean::cnstr_get(x_56, 0);
lean::inc(x_67);
x_68 = lean::cnstr_get(x_56, 1);
lean::inc(x_68);
if (lean::is_exclusive(x_56)) {
 lean::cnstr_release(x_56, 0);
 lean::cnstr_release(x_56, 1);
 x_69 = x_56;
} else {
 lean::dec_ref(x_56);
 x_69 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_70 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_70 = x_69;
}
lean::cnstr_set(x_70, 0, x_67);
lean::cnstr_set(x_70, 1, x_68);
return x_70;
}
}
}
else
{
uint8 x_71; 
lean::dec(x_17);
lean::free_heap_obj(x_2);
lean::dec(x_11);
lean::dec(x_9);
x_71 = !lean::is_exclusive(x_21);
if (x_71 == 0)
{
return x_21;
}
else
{
obj* x_72; obj* x_73; obj* x_74; 
x_72 = lean::cnstr_get(x_21, 0);
x_73 = lean::cnstr_get(x_21, 1);
lean::inc(x_73);
lean::inc(x_72);
lean::dec(x_21);
x_74 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_74, 0, x_72);
lean::cnstr_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_75 = lean::cnstr_get(x_18, 0);
x_76 = lean::cnstr_get(x_18, 1);
lean::inc(x_76);
lean::inc(x_75);
lean::dec(x_18);
x_77 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_77, 0, x_16);
lean::cnstr_set(x_77, 1, x_76);
x_78 = lean_read_module_data(x_75, x_77);
lean::dec(x_75);
if (lean::obj_tag(x_78) == 0)
{
obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_79 = lean::cnstr_get(x_78, 0);
lean::inc(x_79);
x_80 = lean::cnstr_get(x_78, 1);
lean::inc(x_80);
if (lean::is_exclusive(x_78)) {
 lean::cnstr_release(x_78, 0);
 lean::cnstr_release(x_78, 1);
 x_81 = x_78;
} else {
 lean::dec_ref(x_78);
 x_81 = lean::box(0);
}
if (lean::is_scalar(x_81)) {
 x_82 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_82 = x_81;
}
lean::cnstr_set(x_82, 0, x_16);
lean::cnstr_set(x_82, 1, x_80);
x_83 = lean::cnstr_get(x_79, 0);
lean::inc(x_83);
x_84 = l_Array_toList___rarg(x_83);
lean::dec(x_83);
lean::cnstr_set(x_2, 0, x_17);
x_85 = l_Lean_importModulesAux___main(x_84, x_2, x_82);
if (lean::obj_tag(x_85) == 0)
{
obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_86 = lean::cnstr_get(x_85, 0);
lean::inc(x_86);
x_87 = lean::cnstr_get(x_85, 1);
lean::inc(x_87);
if (lean::is_exclusive(x_85)) {
 lean::cnstr_release(x_85, 0);
 lean::cnstr_release(x_85, 1);
 x_88 = x_85;
} else {
 lean::dec_ref(x_85);
 x_88 = lean::box(0);
}
if (lean::is_scalar(x_88)) {
 x_89 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_89 = x_88;
}
lean::cnstr_set(x_89, 0, x_16);
lean::cnstr_set(x_89, 1, x_87);
x_90 = lean::cnstr_get(x_86, 0);
lean::inc(x_90);
x_91 = lean::cnstr_get(x_86, 1);
lean::inc(x_91);
if (lean::is_exclusive(x_86)) {
 lean::cnstr_release(x_86, 0);
 lean::cnstr_release(x_86, 1);
 x_92 = x_86;
} else {
 lean::dec_ref(x_86);
 x_92 = lean::box(0);
}
x_93 = lean::array_push(x_91, x_79);
if (lean::is_scalar(x_92)) {
 x_94 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_94 = x_92;
}
lean::cnstr_set(x_94, 0, x_90);
lean::cnstr_set(x_94, 1, x_93);
x_1 = x_9;
x_2 = x_94;
x_3 = x_89;
goto _start;
}
else
{
obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
lean::dec(x_79);
lean::dec(x_9);
x_96 = lean::cnstr_get(x_85, 0);
lean::inc(x_96);
x_97 = lean::cnstr_get(x_85, 1);
lean::inc(x_97);
if (lean::is_exclusive(x_85)) {
 lean::cnstr_release(x_85, 0);
 lean::cnstr_release(x_85, 1);
 x_98 = x_85;
} else {
 lean::dec_ref(x_85);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_98)) {
 x_99 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_99 = x_98;
}
lean::cnstr_set(x_99, 0, x_96);
lean::cnstr_set(x_99, 1, x_97);
return x_99;
}
}
else
{
obj* x_100; obj* x_101; obj* x_102; obj* x_103; 
lean::dec(x_17);
lean::free_heap_obj(x_2);
lean::dec(x_11);
lean::dec(x_9);
x_100 = lean::cnstr_get(x_78, 0);
lean::inc(x_100);
x_101 = lean::cnstr_get(x_78, 1);
lean::inc(x_101);
if (lean::is_exclusive(x_78)) {
 lean::cnstr_release(x_78, 0);
 lean::cnstr_release(x_78, 1);
 x_102 = x_78;
} else {
 lean::dec_ref(x_78);
 x_102 = lean::box(0);
}
if (lean::is_scalar(x_102)) {
 x_103 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_103 = x_102;
}
lean::cnstr_set(x_103, 0, x_100);
lean::cnstr_set(x_103, 1, x_101);
return x_103;
}
}
}
else
{
uint8 x_104; 
lean::dec(x_17);
lean::free_heap_obj(x_2);
lean::dec(x_11);
lean::dec(x_9);
x_104 = !lean::is_exclusive(x_18);
if (x_104 == 0)
{
return x_18;
}
else
{
obj* x_105; obj* x_106; obj* x_107; 
x_105 = lean::cnstr_get(x_18, 0);
x_106 = lean::cnstr_get(x_18, 1);
lean::inc(x_106);
lean::inc(x_105);
lean::dec(x_18);
x_107 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_107, 0, x_105);
lean::cnstr_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
obj* x_108; obj* x_109; obj* x_110; 
lean::dec(x_2);
x_108 = lean::box(0);
lean::inc(x_8);
x_109 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_10, x_8, x_108);
x_110 = lean_find_olean(x_8, x_3);
if (lean::obj_tag(x_110) == 0)
{
obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; 
x_111 = lean::cnstr_get(x_110, 0);
lean::inc(x_111);
x_112 = lean::cnstr_get(x_110, 1);
lean::inc(x_112);
if (lean::is_exclusive(x_110)) {
 lean::cnstr_release(x_110, 0);
 lean::cnstr_release(x_110, 1);
 x_113 = x_110;
} else {
 lean::dec_ref(x_110);
 x_113 = lean::box(0);
}
if (lean::is_scalar(x_113)) {
 x_114 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_114 = x_113;
}
lean::cnstr_set(x_114, 0, x_108);
lean::cnstr_set(x_114, 1, x_112);
x_115 = lean_read_module_data(x_111, x_114);
lean::dec(x_111);
if (lean::obj_tag(x_115) == 0)
{
obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; 
x_116 = lean::cnstr_get(x_115, 0);
lean::inc(x_116);
x_117 = lean::cnstr_get(x_115, 1);
lean::inc(x_117);
if (lean::is_exclusive(x_115)) {
 lean::cnstr_release(x_115, 0);
 lean::cnstr_release(x_115, 1);
 x_118 = x_115;
} else {
 lean::dec_ref(x_115);
 x_118 = lean::box(0);
}
if (lean::is_scalar(x_118)) {
 x_119 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_119 = x_118;
}
lean::cnstr_set(x_119, 0, x_108);
lean::cnstr_set(x_119, 1, x_117);
x_120 = lean::cnstr_get(x_116, 0);
lean::inc(x_120);
x_121 = l_Array_toList___rarg(x_120);
lean::dec(x_120);
x_122 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_122, 0, x_109);
lean::cnstr_set(x_122, 1, x_11);
x_123 = l_Lean_importModulesAux___main(x_121, x_122, x_119);
if (lean::obj_tag(x_123) == 0)
{
obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
x_124 = lean::cnstr_get(x_123, 0);
lean::inc(x_124);
x_125 = lean::cnstr_get(x_123, 1);
lean::inc(x_125);
if (lean::is_exclusive(x_123)) {
 lean::cnstr_release(x_123, 0);
 lean::cnstr_release(x_123, 1);
 x_126 = x_123;
} else {
 lean::dec_ref(x_123);
 x_126 = lean::box(0);
}
if (lean::is_scalar(x_126)) {
 x_127 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_127 = x_126;
}
lean::cnstr_set(x_127, 0, x_108);
lean::cnstr_set(x_127, 1, x_125);
x_128 = lean::cnstr_get(x_124, 0);
lean::inc(x_128);
x_129 = lean::cnstr_get(x_124, 1);
lean::inc(x_129);
if (lean::is_exclusive(x_124)) {
 lean::cnstr_release(x_124, 0);
 lean::cnstr_release(x_124, 1);
 x_130 = x_124;
} else {
 lean::dec_ref(x_124);
 x_130 = lean::box(0);
}
x_131 = lean::array_push(x_129, x_116);
if (lean::is_scalar(x_130)) {
 x_132 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_132 = x_130;
}
lean::cnstr_set(x_132, 0, x_128);
lean::cnstr_set(x_132, 1, x_131);
x_1 = x_9;
x_2 = x_132;
x_3 = x_127;
goto _start;
}
else
{
obj* x_134; obj* x_135; obj* x_136; obj* x_137; 
lean::dec(x_116);
lean::dec(x_9);
x_134 = lean::cnstr_get(x_123, 0);
lean::inc(x_134);
x_135 = lean::cnstr_get(x_123, 1);
lean::inc(x_135);
if (lean::is_exclusive(x_123)) {
 lean::cnstr_release(x_123, 0);
 lean::cnstr_release(x_123, 1);
 x_136 = x_123;
} else {
 lean::dec_ref(x_123);
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
lean::dec(x_109);
lean::dec(x_11);
lean::dec(x_9);
x_138 = lean::cnstr_get(x_115, 0);
lean::inc(x_138);
x_139 = lean::cnstr_get(x_115, 1);
lean::inc(x_139);
if (lean::is_exclusive(x_115)) {
 lean::cnstr_release(x_115, 0);
 lean::cnstr_release(x_115, 1);
 x_140 = x_115;
} else {
 lean::dec_ref(x_115);
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
else
{
obj* x_142; obj* x_143; obj* x_144; obj* x_145; 
lean::dec(x_109);
lean::dec(x_11);
lean::dec(x_9);
x_142 = lean::cnstr_get(x_110, 0);
lean::inc(x_142);
x_143 = lean::cnstr_get(x_110, 1);
lean::inc(x_143);
if (lean::is_exclusive(x_110)) {
 lean::cnstr_release(x_110, 0);
 lean::cnstr_release(x_110, 1);
 x_144 = x_110;
} else {
 lean::dec_ref(x_110);
 x_144 = lean::box(0);
}
if (lean::is_scalar(x_144)) {
 x_145 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_145 = x_144;
}
lean::cnstr_set(x_145, 0, x_142);
lean::cnstr_set(x_145, 1, x_143);
return x_145;
}
}
}
else
{
obj* x_146; 
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
obj* _init_l___private_init_lean_environment_10__getEntriesFor___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::mk_empty_array(x_1);
x_3 = l_Lean_Inhabited;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
}
obj* l___private_init_lean_environment_10__getEntriesFor___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::cnstr_get(x_1, 2);
x_5 = lean::array_get_size(x_4);
x_6 = lean::nat_dec_lt(x_3, x_5);
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
x_8 = l___private_init_lean_environment_10__getEntriesFor___main___closed__1;
x_9 = lean::array_get(x_8, x_4, x_3);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_11 = lean_name_dec_eq(x_10, x_2);
lean::dec(x_10);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; 
lean::dec(x_9);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_3, x_12);
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
obj* l___private_init_lean_environment_10__getEntriesFor___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_environment_10__getEntriesFor___main(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_environment_10__getEntriesFor(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_environment_10__getEntriesFor___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_lean_environment_10__getEntriesFor___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_environment_10__getEntriesFor(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_environment_11__setImportedEntries___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_3);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
return x_5;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_8 = lean::array_fget(x_3, x_4);
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
x_10 = lean::mk_nat_obj(0u);
x_11 = l___private_init_lean_environment_10__getEntriesFor___main(x_2, x_9, x_10);
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
x_16 = lean::array_get_size(x_14);
x_17 = lean::nat_dec_lt(x_15, x_16);
lean::dec(x_16);
x_18 = lean::mk_nat_obj(1u);
x_19 = lean::nat_add(x_4, x_18);
lean::dec(x_4);
if (x_17 == 0)
{
obj* x_20; 
lean::dec(x_15);
lean::dec(x_12);
lean::dec(x_11);
x_4 = x_19;
goto _start;
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; uint8 x_25; 
x_21 = lean::array_fget(x_14, x_15);
x_22 = lean::array_fset(x_14, x_15, x_10);
x_23 = lean::cnstr_get(x_12, 1);
lean::inc(x_23);
lean::dec(x_12);
x_24 = x_21;
x_25 = !lean::is_exclusive(x_24);
if (x_25 == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_26 = lean::cnstr_get(x_24, 0);
x_27 = lean::array_push(x_26, x_11);
lean::cnstr_set(x_24, 0, x_27);
x_28 = l_Lean_EnvExtensionState_Inhabited;
x_29 = x_24;
x_30 = lean::array_fset(x_22, x_15, x_29);
lean::dec(x_15);
lean::cnstr_set(x_5, 2, x_30);
x_4 = x_19;
goto _start;
}
else
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_32 = lean::cnstr_get(x_24, 0);
x_33 = lean::cnstr_get(x_24, 1);
x_34 = lean::cnstr_get(x_24, 2);
x_35 = lean::cnstr_get(x_24, 3);
lean::inc(x_35);
lean::inc(x_34);
lean::inc(x_33);
lean::inc(x_32);
lean::dec(x_24);
x_36 = lean::array_push(x_32, x_11);
x_37 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_33);
lean::cnstr_set(x_37, 2, x_34);
lean::cnstr_set(x_37, 3, x_35);
x_38 = l_Lean_EnvExtensionState_Inhabited;
x_39 = x_37;
x_40 = lean::array_fset(x_22, x_15, x_39);
lean::dec(x_15);
lean::cnstr_set(x_5, 2, x_40);
x_4 = x_19;
goto _start;
}
}
}
else
{
obj* x_42; obj* x_43; obj* x_44; uint32 x_45; uint8 x_46; obj* x_47; obj* x_48; obj* x_49; uint8 x_50; obj* x_51; obj* x_52; 
x_42 = lean::cnstr_get(x_5, 0);
x_43 = lean::cnstr_get(x_5, 1);
x_44 = lean::cnstr_get(x_5, 2);
x_45 = lean::cnstr_get_scalar<uint32>(x_5, sizeof(void*)*4);
x_46 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*4 + 4);
x_47 = lean::cnstr_get(x_5, 3);
lean::inc(x_47);
lean::inc(x_44);
lean::inc(x_43);
lean::inc(x_42);
lean::dec(x_5);
x_48 = lean::cnstr_get(x_12, 0);
lean::inc(x_48);
x_49 = lean::array_get_size(x_44);
x_50 = lean::nat_dec_lt(x_48, x_49);
lean::dec(x_49);
x_51 = lean::mk_nat_obj(1u);
x_52 = lean::nat_add(x_4, x_51);
lean::dec(x_4);
if (x_50 == 0)
{
obj* x_53; obj* x_54; 
lean::dec(x_48);
lean::dec(x_12);
lean::dec(x_11);
x_53 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_53, 0, x_42);
lean::cnstr_set(x_53, 1, x_43);
lean::cnstr_set(x_53, 2, x_44);
lean::cnstr_set(x_53, 3, x_47);
lean::cnstr_set_scalar(x_53, sizeof(void*)*4, x_45);
lean::cnstr_set_scalar(x_53, sizeof(void*)*4 + 4, x_46);
x_4 = x_52;
x_5 = x_53;
goto _start;
}
else
{
obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_55 = lean::array_fget(x_44, x_48);
x_56 = lean::array_fset(x_44, x_48, x_10);
x_57 = lean::cnstr_get(x_12, 1);
lean::inc(x_57);
lean::dec(x_12);
x_58 = x_55;
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
x_60 = lean::cnstr_get(x_58, 1);
lean::inc(x_60);
x_61 = lean::cnstr_get(x_58, 2);
lean::inc(x_61);
x_62 = lean::cnstr_get(x_58, 3);
lean::inc(x_62);
if (lean::is_exclusive(x_58)) {
 lean::cnstr_release(x_58, 0);
 lean::cnstr_release(x_58, 1);
 lean::cnstr_release(x_58, 2);
 lean::cnstr_release(x_58, 3);
 x_63 = x_58;
} else {
 lean::dec_ref(x_58);
 x_63 = lean::box(0);
}
x_64 = lean::array_push(x_59, x_11);
if (lean::is_scalar(x_63)) {
 x_65 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_65 = x_63;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_60);
lean::cnstr_set(x_65, 2, x_61);
lean::cnstr_set(x_65, 3, x_62);
x_66 = l_Lean_EnvExtensionState_Inhabited;
x_67 = x_65;
x_68 = lean::array_fset(x_56, x_48, x_67);
lean::dec(x_48);
x_69 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_69, 0, x_42);
lean::cnstr_set(x_69, 1, x_43);
lean::cnstr_set(x_69, 2, x_68);
lean::cnstr_set(x_69, 3, x_47);
lean::cnstr_set_scalar(x_69, sizeof(void*)*4, x_45);
lean::cnstr_set_scalar(x_69, sizeof(void*)*4 + 4, x_46);
x_4 = x_52;
x_5 = x_69;
goto _start;
}
}
}
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_environment_11__setImportedEntries___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_3);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
return x_5;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_8 = lean::array_fget(x_3, x_4);
x_9 = lean::mk_nat_obj(0u);
x_10 = l_Array_miterateAux___main___at___private_init_lean_environment_11__setImportedEntries___spec__1(x_2, x_8, x_2, x_9, x_5);
lean::dec(x_8);
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_add(x_4, x_11);
lean::dec(x_4);
x_4 = x_12;
x_5 = x_10;
goto _start;
}
}
}
obj* l___private_init_lean_environment_11__setImportedEntries(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l___private_init_lean_environment_9__persistentEnvExtensionsRef;
x_5 = lean::io_ref_get(x_4, x_3);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_5, 0);
x_8 = lean::mk_nat_obj(0u);
x_9 = l_Array_miterateAux___main___at___private_init_lean_environment_11__setImportedEntries___spec__2(x_2, x_7, x_2, x_8, x_1);
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
x_13 = l_Array_miterateAux___main___at___private_init_lean_environment_11__setImportedEntries___spec__2(x_2, x_10, x_2, x_12, x_1);
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
obj* l_Array_miterateAux___main___at___private_init_lean_environment_11__setImportedEntries___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at___private_init_lean_environment_11__setImportedEntries___spec__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_environment_11__setImportedEntries___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at___private_init_lean_environment_11__setImportedEntries___spec__2(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l___private_init_lean_environment_11__setImportedEntries___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_environment_11__setImportedEntries(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_environment_12__mkImportedStateThunk___elambda__1___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_3);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
lean::dec(x_1);
return x_5;
}
else
{
obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_8 = lean::array_fget(x_3, x_4);
x_9 = 1;
x_10 = lean::box(x_9);
lean::inc(x_1);
x_11 = lean::apply_3(x_1, x_10, x_5, x_8);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_4, x_12);
lean::dec(x_4);
x_4 = x_13;
x_5 = x_11;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_environment_12__mkImportedStateThunk___elambda__1___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_3);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
lean::dec(x_2);
return x_5;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_8 = lean::array_fget(x_3, x_4);
x_9 = lean::mk_nat_obj(0u);
lean::inc(x_2);
x_10 = l_Array_miterateAux___main___at___private_init_lean_environment_12__mkImportedStateThunk___elambda__1___spec__1(x_2, x_8, x_8, x_9, x_5);
lean::dec(x_8);
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_add(x_4, x_11);
lean::dec(x_4);
x_4 = x_12;
x_5 = x_10;
goto _start;
}
}
}
obj* l___private_init_lean_environment_12__mkImportedStateThunk___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = l_Array_miterateAux___main___at___private_init_lean_environment_12__mkImportedStateThunk___elambda__1___spec__2(x_1, x_3, x_1, x_5, x_2);
return x_6;
}
}
obj* l___private_init_lean_environment_12__mkImportedStateThunk(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_environment_12__mkImportedStateThunk___elambda__1___boxed), 4, 3);
lean::closure_set(x_4, 0, x_1);
lean::closure_set(x_4, 1, x_2);
lean::closure_set(x_4, 2, x_3);
x_5 = lean::mk_thunk(x_4);
return x_5;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_environment_12__mkImportedStateThunk___elambda__1___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at___private_init_lean_environment_12__mkImportedStateThunk___elambda__1___spec__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_environment_12__mkImportedStateThunk___elambda__1___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at___private_init_lean_environment_12__mkImportedStateThunk___elambda__1___spec__2(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_1);
return x_6;
}
}
obj* l___private_init_lean_environment_12__mkImportedStateThunk___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_environment_12__mkImportedStateThunk___elambda__1(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_environment_13__finalizePersistentExtensions___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* x_7; obj* x_8; uint8 x_9; 
x_7 = lean::array_fget(x_2, x_3);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_9 = !lean::is_exclusive(x_4);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; uint8 x_13; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_4, 2);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_12 = lean::array_get_size(x_10);
x_13 = lean::nat_dec_lt(x_11, x_12);
lean::dec(x_12);
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_3, x_14);
lean::dec(x_3);
if (x_13 == 0)
{
obj* x_16; 
lean::dec(x_11);
lean::dec(x_8);
lean::dec(x_7);
x_3 = x_15;
goto _start;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; uint8 x_22; 
x_17 = lean::array_fget(x_10, x_11);
x_18 = lean::mk_nat_obj(0u);
x_19 = lean::array_fset(x_10, x_11, x_18);
x_20 = lean::cnstr_get(x_8, 1);
lean::inc(x_20);
lean::dec(x_8);
lean::inc(x_20);
x_21 = x_17;
x_22 = !lean::is_exclusive(x_21);
if (x_22 == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; uint8 x_32; 
x_23 = lean::cnstr_get(x_21, 0);
x_24 = lean::cnstr_get(x_21, 3);
lean::dec(x_24);
x_25 = lean::cnstr_get(x_21, 2);
lean::dec(x_25);
x_26 = lean::cnstr_get(x_21, 1);
lean::dec(x_26);
x_27 = lean::cnstr_get(x_20, 1);
lean::inc(x_27);
lean::dec(x_20);
x_28 = lean::thunk_get_own(x_27);
lean::dec(x_27);
x_29 = lean::cnstr_get(x_7, 3);
lean::inc(x_29);
lean::inc(x_23);
x_30 = l___private_init_lean_environment_12__mkImportedStateThunk(x_23, x_28, x_29);
x_31 = lean::box(0);
x_32 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*5);
lean::dec(x_7);
if (x_32 == 0)
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_33 = lean::thunk_get_own(x_30);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_21, 3, x_34);
lean::cnstr_set(x_21, 2, x_31);
lean::cnstr_set(x_21, 1, x_30);
x_35 = l_Lean_EnvExtensionState_Inhabited;
x_36 = x_21;
x_37 = lean::array_fset(x_19, x_11, x_36);
lean::dec(x_11);
lean::cnstr_set(x_4, 2, x_37);
x_3 = x_15;
goto _start;
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_39 = lean::box(0);
lean::cnstr_set(x_21, 3, x_39);
lean::cnstr_set(x_21, 2, x_31);
lean::cnstr_set(x_21, 1, x_30);
x_40 = l_Lean_EnvExtensionState_Inhabited;
x_41 = x_21;
x_42 = lean::array_fset(x_19, x_11, x_41);
lean::dec(x_11);
lean::cnstr_set(x_4, 2, x_42);
x_3 = x_15;
goto _start;
}
}
else
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; uint8 x_50; 
x_44 = lean::cnstr_get(x_21, 0);
lean::inc(x_44);
lean::dec(x_21);
x_45 = lean::cnstr_get(x_20, 1);
lean::inc(x_45);
lean::dec(x_20);
x_46 = lean::thunk_get_own(x_45);
lean::dec(x_45);
x_47 = lean::cnstr_get(x_7, 3);
lean::inc(x_47);
lean::inc(x_44);
x_48 = l___private_init_lean_environment_12__mkImportedStateThunk(x_44, x_46, x_47);
x_49 = lean::box(0);
x_50 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*5);
lean::dec(x_7);
if (x_50 == 0)
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_51 = lean::thunk_get_own(x_48);
x_52 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_52, 0, x_51);
x_53 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_53, 0, x_44);
lean::cnstr_set(x_53, 1, x_48);
lean::cnstr_set(x_53, 2, x_49);
lean::cnstr_set(x_53, 3, x_52);
x_54 = l_Lean_EnvExtensionState_Inhabited;
x_55 = x_53;
x_56 = lean::array_fset(x_19, x_11, x_55);
lean::dec(x_11);
lean::cnstr_set(x_4, 2, x_56);
x_3 = x_15;
goto _start;
}
else
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_58 = lean::box(0);
x_59 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_59, 0, x_44);
lean::cnstr_set(x_59, 1, x_48);
lean::cnstr_set(x_59, 2, x_49);
lean::cnstr_set(x_59, 3, x_58);
x_60 = l_Lean_EnvExtensionState_Inhabited;
x_61 = x_59;
x_62 = lean::array_fset(x_19, x_11, x_61);
lean::dec(x_11);
lean::cnstr_set(x_4, 2, x_62);
x_3 = x_15;
goto _start;
}
}
}
}
else
{
obj* x_64; obj* x_65; obj* x_66; uint32 x_67; uint8 x_68; obj* x_69; obj* x_70; obj* x_71; uint8 x_72; obj* x_73; obj* x_74; 
x_64 = lean::cnstr_get(x_4, 0);
x_65 = lean::cnstr_get(x_4, 1);
x_66 = lean::cnstr_get(x_4, 2);
x_67 = lean::cnstr_get_scalar<uint32>(x_4, sizeof(void*)*4);
x_68 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*4 + 4);
x_69 = lean::cnstr_get(x_4, 3);
lean::inc(x_69);
lean::inc(x_66);
lean::inc(x_65);
lean::inc(x_64);
lean::dec(x_4);
x_70 = lean::cnstr_get(x_8, 0);
lean::inc(x_70);
x_71 = lean::array_get_size(x_66);
x_72 = lean::nat_dec_lt(x_70, x_71);
lean::dec(x_71);
x_73 = lean::mk_nat_obj(1u);
x_74 = lean::nat_add(x_3, x_73);
lean::dec(x_3);
if (x_72 == 0)
{
obj* x_75; obj* x_76; 
lean::dec(x_70);
lean::dec(x_8);
lean::dec(x_7);
x_75 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_75, 0, x_64);
lean::cnstr_set(x_75, 1, x_65);
lean::cnstr_set(x_75, 2, x_66);
lean::cnstr_set(x_75, 3, x_69);
lean::cnstr_set_scalar(x_75, sizeof(void*)*4, x_67);
lean::cnstr_set_scalar(x_75, sizeof(void*)*4 + 4, x_68);
x_3 = x_74;
x_4 = x_75;
goto _start;
}
else
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; uint8 x_89; 
x_77 = lean::array_fget(x_66, x_70);
x_78 = lean::mk_nat_obj(0u);
x_79 = lean::array_fset(x_66, x_70, x_78);
x_80 = lean::cnstr_get(x_8, 1);
lean::inc(x_80);
lean::dec(x_8);
lean::inc(x_80);
x_81 = x_77;
x_82 = lean::cnstr_get(x_81, 0);
lean::inc(x_82);
if (lean::is_exclusive(x_81)) {
 lean::cnstr_release(x_81, 0);
 lean::cnstr_release(x_81, 1);
 lean::cnstr_release(x_81, 2);
 lean::cnstr_release(x_81, 3);
 x_83 = x_81;
} else {
 lean::dec_ref(x_81);
 x_83 = lean::box(0);
}
x_84 = lean::cnstr_get(x_80, 1);
lean::inc(x_84);
lean::dec(x_80);
x_85 = lean::thunk_get_own(x_84);
lean::dec(x_84);
x_86 = lean::cnstr_get(x_7, 3);
lean::inc(x_86);
lean::inc(x_82);
x_87 = l___private_init_lean_environment_12__mkImportedStateThunk(x_82, x_85, x_86);
x_88 = lean::box(0);
x_89 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*5);
lean::dec(x_7);
if (x_89 == 0)
{
obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_90 = lean::thunk_get_own(x_87);
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_90);
if (lean::is_scalar(x_83)) {
 x_92 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_92 = x_83;
}
lean::cnstr_set(x_92, 0, x_82);
lean::cnstr_set(x_92, 1, x_87);
lean::cnstr_set(x_92, 2, x_88);
lean::cnstr_set(x_92, 3, x_91);
x_93 = l_Lean_EnvExtensionState_Inhabited;
x_94 = x_92;
x_95 = lean::array_fset(x_79, x_70, x_94);
lean::dec(x_70);
x_96 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_96, 0, x_64);
lean::cnstr_set(x_96, 1, x_65);
lean::cnstr_set(x_96, 2, x_95);
lean::cnstr_set(x_96, 3, x_69);
lean::cnstr_set_scalar(x_96, sizeof(void*)*4, x_67);
lean::cnstr_set_scalar(x_96, sizeof(void*)*4 + 4, x_68);
x_3 = x_74;
x_4 = x_96;
goto _start;
}
else
{
obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
x_98 = lean::box(0);
if (lean::is_scalar(x_83)) {
 x_99 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_99 = x_83;
}
lean::cnstr_set(x_99, 0, x_82);
lean::cnstr_set(x_99, 1, x_87);
lean::cnstr_set(x_99, 2, x_88);
lean::cnstr_set(x_99, 3, x_98);
x_100 = l_Lean_EnvExtensionState_Inhabited;
x_101 = x_99;
x_102 = lean::array_fset(x_79, x_70, x_101);
lean::dec(x_70);
x_103 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_103, 0, x_64);
lean::cnstr_set(x_103, 1, x_65);
lean::cnstr_set(x_103, 2, x_102);
lean::cnstr_set(x_103, 3, x_69);
lean::cnstr_set_scalar(x_103, sizeof(void*)*4, x_67);
lean::cnstr_set_scalar(x_103, sizeof(void*)*4 + 4, x_68);
x_3 = x_74;
x_4 = x_103;
goto _start;
}
}
}
}
}
}
obj* l___private_init_lean_environment_13__finalizePersistentExtensions(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l___private_init_lean_environment_9__persistentEnvExtensionsRef;
x_4 = lean::io_ref_get(x_3, x_2);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_4, 0);
x_7 = lean::mk_nat_obj(0u);
x_8 = l_Array_miterateAux___main___at___private_init_lean_environment_13__finalizePersistentExtensions___spec__1(x_6, x_6, x_7, x_1);
lean::dec(x_6);
lean::cnstr_set(x_4, 0, x_8);
return x_4;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_4, 0);
x_10 = lean::cnstr_get(x_4, 1);
lean::inc(x_10);
lean::inc(x_9);
lean::dec(x_4);
x_11 = lean::mk_nat_obj(0u);
x_12 = l_Array_miterateAux___main___at___private_init_lean_environment_13__finalizePersistentExtensions___spec__1(x_9, x_9, x_11, x_1);
lean::dec(x_9);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_10);
return x_13;
}
}
else
{
uint8 x_14; 
lean::dec(x_1);
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
obj* l_Array_miterateAux___main___at___private_init_lean_environment_13__finalizePersistentExtensions___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at___private_init_lean_environment_13__finalizePersistentExtensions___spec__1(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
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
uint8 x_7; 
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
obj* l_AssocList_foldl___main___at_Lean_importModules___spec__5(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_2);
return x_1;
}
else
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; usize x_7; usize x_8; obj* x_9; usize x_10; obj* x_11; usize x_12; obj* x_13; obj* x_14; 
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
obj* x_15; obj* x_16; obj* x_17; obj* x_18; usize x_19; usize x_20; obj* x_21; usize x_22; obj* x_23; obj* x_24; usize x_25; obj* x_26; obj* x_27; 
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
obj* l_HashMapImp_moveEntries___main___at_Lean_importModules___spec__4(obj* x_1, obj* x_2, obj* x_3) {
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
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_6 = lean::array_fget(x_2, x_1);
x_7 = lean::box(0);
x_8 = lean::array_fset(x_2, x_1, x_7);
x_9 = l_AssocList_foldl___main___at_Lean_importModules___spec__5(x_3, x_6);
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
obj* l_HashMapImp_expand___at_Lean_importModules___spec__3(obj* x_1, obj* x_2) {
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
x_7 = lean::array_get_size(x_6);
x_8 = lean_name_hash_usize(x_2);
x_9 = lean::usize_modn(x_8, x_7);
x_10 = lean::box_size_t(x_9);
x_11 = lean::unbox_size_t(x_10);
x_12 = lean::array_uget(x_6, x_11);
x_13 = l_AssocList_contains___main___at_Lean_importModules___spec__2(x_2, x_12);
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
x_32 = l_AssocList_contains___main___at_Lean_importModules___spec__2(x_2, x_31);
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
x_43 = lean::array_uset(x_25, x_42, x_41);
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
x_8 = lean::array_get_size(x_5);
x_9 = lean::nat_dec_lt(x_6, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
lean::dec(x_6);
lean::dec(x_3);
return x_7;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::array_fget(x_5, x_6);
x_11 = l_Lean_ConstantInfo_name(x_10);
lean::dec(x_10);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_6, x_12);
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
x_6 = lean::array_get_size(x_3);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
return x_5;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_8 = lean::array_fget(x_3, x_4);
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
x_10 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_11 = l_Array_miterateAux___main___at_Lean_importModules___spec__7(x_1, x_2, x_4, x_8, x_9, x_10, x_5);
lean::dec(x_9);
lean::dec(x_8);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_4, x_12);
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
x_7 = lean::array_get_size(x_3);
x_8 = lean::nat_dec_lt(x_4, x_7);
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
x_13 = lean::array_fget(x_3, x_4);
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_4, x_14);
lean::dec(x_4);
x_16 = l_Lean_ConstantInfo_name(x_13);
x_17 = l_Lean_SMap_contains___main___at_Lean_Environment_contains___spec__1(x_5, x_16);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_6);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_19 = lean::cnstr_get(x_6, 0);
lean::dec(x_19);
x_20 = l_Lean_SMap_insert___main___at_Lean_Environment_add___spec__1(x_5, x_16, x_13);
x_21 = lean::box(0);
lean::cnstr_set(x_6, 0, x_21);
x_4 = x_15;
x_5 = x_20;
goto _start;
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_23 = lean::cnstr_get(x_6, 1);
lean::inc(x_23);
lean::dec(x_6);
x_24 = l_Lean_SMap_insert___main___at_Lean_Environment_add___spec__1(x_5, x_16, x_13);
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
x_33 = lean::string_append(x_32, x_31);
lean::dec(x_31);
x_34 = l_Char_HasRepr___closed__1;
x_35 = lean::string_append(x_33, x_34);
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
x_40 = lean::string_append(x_39, x_38);
lean::dec(x_38);
x_41 = l_Char_HasRepr___closed__1;
x_42 = lean::string_append(x_40, x_41);
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
x_7 = lean::array_get_size(x_3);
x_8 = lean::nat_dec_lt(x_4, x_7);
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
x_13 = lean::array_fget(x_3, x_4);
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_4, x_14);
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
obj* x_20; obj* x_21; obj* x_22; 
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
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
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
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__11(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* x_18; obj* x_19; obj* x_20; 
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
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
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
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__12(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* x_18; obj* x_19; obj* x_20; 
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
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
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
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::mk_empty_array(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
namespace lean {
obj* import_modules_core(obj* x_1, uint32 x_2, obj* x_3) {
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
x_10 = l_Lean_SMap_insert___main___at_Lean_Environment_add___spec__1___closed__2;
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
x_18 = l_Lean_SMap_switch___at___private_init_lean_environment_1__switch___spec__1(x_17);
x_19 = l___private_init_lean_environment_7__mkInitialExtensionStates(x_15);
if (lean::obj_tag(x_19) == 0)
{
uint8 x_20; 
x_20 = !lean::is_exclusive(x_19);
if (x_20 == 0)
{
obj* x_21; uint8 x_22; obj* x_23; obj* x_24; obj* x_25; 
x_21 = lean::cnstr_get(x_19, 0);
lean::cnstr_set(x_19, 0, x_8);
x_22 = l_List_isEmpty___main___rarg(x_1);
x_23 = l_List_redLength___main___rarg(x_1);
x_24 = lean::mk_empty_array(x_23);
lean::dec(x_23);
x_25 = l_List_toArrayAux___main___rarg(x_1, x_24);
if (x_22 == 0)
{
uint8 x_26; obj* x_27; obj* x_28; 
x_26 = 1;
x_27 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_27, 0, x_13);
lean::cnstr_set(x_27, 1, x_18);
lean::cnstr_set(x_27, 2, x_21);
lean::cnstr_set(x_27, 3, x_25);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_2);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4 + 4, x_26);
x_28 = l___private_init_lean_environment_11__setImportedEntries(x_27, x_9, x_19);
if (lean::obj_tag(x_28) == 0)
{
uint8 x_29; 
x_29 = !lean::is_exclusive(x_28);
if (x_29 == 0)
{
obj* x_30; obj* x_31; 
x_30 = lean::cnstr_get(x_28, 0);
lean::cnstr_set(x_28, 0, x_8);
x_31 = l___private_init_lean_environment_13__finalizePersistentExtensions(x_30, x_28);
if (lean::obj_tag(x_31) == 0)
{
uint8 x_32; 
x_32 = !lean::is_exclusive(x_31);
if (x_32 == 0)
{
obj* x_33; obj* x_34; 
x_33 = lean::cnstr_get(x_31, 0);
lean::cnstr_set(x_31, 0, x_8);
x_34 = l_Array_miterateAux___main___at_Lean_importModules___spec__11(x_9, x_9, x_11, x_33, x_31);
lean::dec(x_9);
if (lean::obj_tag(x_34) == 0)
{
uint8 x_35; 
x_35 = !lean::is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = lean::cnstr_get(x_34, 0);
x_37 = lean::cnstr_get(x_34, 1);
lean::inc(x_37);
lean::inc(x_36);
lean::dec(x_34);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_37);
return x_38;
}
}
else
{
uint8 x_39; 
x_39 = !lean::is_exclusive(x_34);
if (x_39 == 0)
{
return x_34;
}
else
{
obj* x_40; obj* x_41; obj* x_42; 
x_40 = lean::cnstr_get(x_34, 0);
x_41 = lean::cnstr_get(x_34, 1);
lean::inc(x_41);
lean::inc(x_40);
lean::dec(x_34);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_40);
lean::cnstr_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_43 = lean::cnstr_get(x_31, 0);
x_44 = lean::cnstr_get(x_31, 1);
lean::inc(x_44);
lean::inc(x_43);
lean::dec(x_31);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_8);
lean::cnstr_set(x_45, 1, x_44);
x_46 = l_Array_miterateAux___main___at_Lean_importModules___spec__11(x_9, x_9, x_11, x_43, x_45);
lean::dec(x_9);
if (lean::obj_tag(x_46) == 0)
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
x_48 = lean::cnstr_get(x_46, 1);
lean::inc(x_48);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 lean::cnstr_release(x_46, 1);
 x_49 = x_46;
} else {
 lean::dec_ref(x_46);
 x_49 = lean::box(0);
}
if (lean::is_scalar(x_49)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_49;
}
lean::cnstr_set(x_50, 0, x_47);
lean::cnstr_set(x_50, 1, x_48);
return x_50;
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_51 = lean::cnstr_get(x_46, 0);
lean::inc(x_51);
x_52 = lean::cnstr_get(x_46, 1);
lean::inc(x_52);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 lean::cnstr_release(x_46, 1);
 x_53 = x_46;
} else {
 lean::dec_ref(x_46);
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
lean::dec(x_9);
x_55 = !lean::is_exclusive(x_31);
if (x_55 == 0)
{
return x_31;
}
else
{
obj* x_56; obj* x_57; obj* x_58; 
x_56 = lean::cnstr_get(x_31, 0);
x_57 = lean::cnstr_get(x_31, 1);
lean::inc(x_57);
lean::inc(x_56);
lean::dec(x_31);
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
x_59 = lean::cnstr_get(x_28, 0);
x_60 = lean::cnstr_get(x_28, 1);
lean::inc(x_60);
lean::inc(x_59);
lean::dec(x_28);
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_8);
lean::cnstr_set(x_61, 1, x_60);
x_62 = l___private_init_lean_environment_13__finalizePersistentExtensions(x_59, x_61);
if (lean::obj_tag(x_62) == 0)
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_63 = lean::cnstr_get(x_62, 0);
lean::inc(x_63);
x_64 = lean::cnstr_get(x_62, 1);
lean::inc(x_64);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 lean::cnstr_release(x_62, 1);
 x_65 = x_62;
} else {
 lean::dec_ref(x_62);
 x_65 = lean::box(0);
}
if (lean::is_scalar(x_65)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_65;
}
lean::cnstr_set(x_66, 0, x_8);
lean::cnstr_set(x_66, 1, x_64);
x_67 = l_Array_miterateAux___main___at_Lean_importModules___spec__11(x_9, x_9, x_11, x_63, x_66);
lean::dec(x_9);
if (lean::obj_tag(x_67) == 0)
{
obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_68 = lean::cnstr_get(x_67, 0);
lean::inc(x_68);
x_69 = lean::cnstr_get(x_67, 1);
lean::inc(x_69);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_release(x_67, 0);
 lean::cnstr_release(x_67, 1);
 x_70 = x_67;
} else {
 lean::dec_ref(x_67);
 x_70 = lean::box(0);
}
if (lean::is_scalar(x_70)) {
 x_71 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_71 = x_70;
}
lean::cnstr_set(x_71, 0, x_68);
lean::cnstr_set(x_71, 1, x_69);
return x_71;
}
else
{
obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
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
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_9);
x_76 = lean::cnstr_get(x_62, 0);
lean::inc(x_76);
x_77 = lean::cnstr_get(x_62, 1);
lean::inc(x_77);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 lean::cnstr_release(x_62, 1);
 x_78 = x_62;
} else {
 lean::dec_ref(x_62);
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
lean::dec(x_9);
x_80 = !lean::is_exclusive(x_28);
if (x_80 == 0)
{
return x_28;
}
else
{
obj* x_81; obj* x_82; obj* x_83; 
x_81 = lean::cnstr_get(x_28, 0);
x_82 = lean::cnstr_get(x_28, 1);
lean::inc(x_82);
lean::inc(x_81);
lean::dec(x_28);
x_83 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_83, 0, x_81);
lean::cnstr_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8 x_84; obj* x_85; obj* x_86; 
x_84 = 0;
x_85 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_85, 0, x_13);
lean::cnstr_set(x_85, 1, x_18);
lean::cnstr_set(x_85, 2, x_21);
lean::cnstr_set(x_85, 3, x_25);
lean::cnstr_set_scalar(x_85, sizeof(void*)*4, x_2);
lean::cnstr_set_scalar(x_85, sizeof(void*)*4 + 4, x_84);
x_86 = l___private_init_lean_environment_11__setImportedEntries(x_85, x_9, x_19);
if (lean::obj_tag(x_86) == 0)
{
uint8 x_87; 
x_87 = !lean::is_exclusive(x_86);
if (x_87 == 0)
{
obj* x_88; obj* x_89; 
x_88 = lean::cnstr_get(x_86, 0);
lean::cnstr_set(x_86, 0, x_8);
x_89 = l___private_init_lean_environment_13__finalizePersistentExtensions(x_88, x_86);
if (lean::obj_tag(x_89) == 0)
{
uint8 x_90; 
x_90 = !lean::is_exclusive(x_89);
if (x_90 == 0)
{
obj* x_91; obj* x_92; 
x_91 = lean::cnstr_get(x_89, 0);
lean::cnstr_set(x_89, 0, x_8);
x_92 = l_Array_miterateAux___main___at_Lean_importModules___spec__12(x_9, x_9, x_11, x_91, x_89);
lean::dec(x_9);
if (lean::obj_tag(x_92) == 0)
{
uint8 x_93; 
x_93 = !lean::is_exclusive(x_92);
if (x_93 == 0)
{
return x_92;
}
else
{
obj* x_94; obj* x_95; obj* x_96; 
x_94 = lean::cnstr_get(x_92, 0);
x_95 = lean::cnstr_get(x_92, 1);
lean::inc(x_95);
lean::inc(x_94);
lean::dec(x_92);
x_96 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_96, 0, x_94);
lean::cnstr_set(x_96, 1, x_95);
return x_96;
}
}
else
{
uint8 x_97; 
x_97 = !lean::is_exclusive(x_92);
if (x_97 == 0)
{
return x_92;
}
else
{
obj* x_98; obj* x_99; obj* x_100; 
x_98 = lean::cnstr_get(x_92, 0);
x_99 = lean::cnstr_get(x_92, 1);
lean::inc(x_99);
lean::inc(x_98);
lean::dec(x_92);
x_100 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_100, 0, x_98);
lean::cnstr_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
x_101 = lean::cnstr_get(x_89, 0);
x_102 = lean::cnstr_get(x_89, 1);
lean::inc(x_102);
lean::inc(x_101);
lean::dec(x_89);
x_103 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_103, 0, x_8);
lean::cnstr_set(x_103, 1, x_102);
x_104 = l_Array_miterateAux___main___at_Lean_importModules___spec__12(x_9, x_9, x_11, x_101, x_103);
lean::dec(x_9);
if (lean::obj_tag(x_104) == 0)
{
obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
x_105 = lean::cnstr_get(x_104, 0);
lean::inc(x_105);
x_106 = lean::cnstr_get(x_104, 1);
lean::inc(x_106);
if (lean::is_exclusive(x_104)) {
 lean::cnstr_release(x_104, 0);
 lean::cnstr_release(x_104, 1);
 x_107 = x_104;
} else {
 lean::dec_ref(x_104);
 x_107 = lean::box(0);
}
if (lean::is_scalar(x_107)) {
 x_108 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_108 = x_107;
}
lean::cnstr_set(x_108, 0, x_105);
lean::cnstr_set(x_108, 1, x_106);
return x_108;
}
else
{
obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
x_109 = lean::cnstr_get(x_104, 0);
lean::inc(x_109);
x_110 = lean::cnstr_get(x_104, 1);
lean::inc(x_110);
if (lean::is_exclusive(x_104)) {
 lean::cnstr_release(x_104, 0);
 lean::cnstr_release(x_104, 1);
 x_111 = x_104;
} else {
 lean::dec_ref(x_104);
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
}
else
{
uint8 x_113; 
lean::dec(x_9);
x_113 = !lean::is_exclusive(x_89);
if (x_113 == 0)
{
return x_89;
}
else
{
obj* x_114; obj* x_115; obj* x_116; 
x_114 = lean::cnstr_get(x_89, 0);
x_115 = lean::cnstr_get(x_89, 1);
lean::inc(x_115);
lean::inc(x_114);
lean::dec(x_89);
x_116 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_116, 0, x_114);
lean::cnstr_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
obj* x_117; obj* x_118; obj* x_119; obj* x_120; 
x_117 = lean::cnstr_get(x_86, 0);
x_118 = lean::cnstr_get(x_86, 1);
lean::inc(x_118);
lean::inc(x_117);
lean::dec(x_86);
x_119 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_119, 0, x_8);
lean::cnstr_set(x_119, 1, x_118);
x_120 = l___private_init_lean_environment_13__finalizePersistentExtensions(x_117, x_119);
if (lean::obj_tag(x_120) == 0)
{
obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; 
x_121 = lean::cnstr_get(x_120, 0);
lean::inc(x_121);
x_122 = lean::cnstr_get(x_120, 1);
lean::inc(x_122);
if (lean::is_exclusive(x_120)) {
 lean::cnstr_release(x_120, 0);
 lean::cnstr_release(x_120, 1);
 x_123 = x_120;
} else {
 lean::dec_ref(x_120);
 x_123 = lean::box(0);
}
if (lean::is_scalar(x_123)) {
 x_124 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_124 = x_123;
}
lean::cnstr_set(x_124, 0, x_8);
lean::cnstr_set(x_124, 1, x_122);
x_125 = l_Array_miterateAux___main___at_Lean_importModules___spec__12(x_9, x_9, x_11, x_121, x_124);
lean::dec(x_9);
if (lean::obj_tag(x_125) == 0)
{
obj* x_126; obj* x_127; obj* x_128; obj* x_129; 
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
lean::cnstr_set(x_129, 0, x_126);
lean::cnstr_set(x_129, 1, x_127);
return x_129;
}
else
{
obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
x_130 = lean::cnstr_get(x_125, 0);
lean::inc(x_130);
x_131 = lean::cnstr_get(x_125, 1);
lean::inc(x_131);
if (lean::is_exclusive(x_125)) {
 lean::cnstr_release(x_125, 0);
 lean::cnstr_release(x_125, 1);
 x_132 = x_125;
} else {
 lean::dec_ref(x_125);
 x_132 = lean::box(0);
}
if (lean::is_scalar(x_132)) {
 x_133 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_133 = x_132;
}
lean::cnstr_set(x_133, 0, x_130);
lean::cnstr_set(x_133, 1, x_131);
return x_133;
}
}
else
{
obj* x_134; obj* x_135; obj* x_136; obj* x_137; 
lean::dec(x_9);
x_134 = lean::cnstr_get(x_120, 0);
lean::inc(x_134);
x_135 = lean::cnstr_get(x_120, 1);
lean::inc(x_135);
if (lean::is_exclusive(x_120)) {
 lean::cnstr_release(x_120, 0);
 lean::cnstr_release(x_120, 1);
 x_136 = x_120;
} else {
 lean::dec_ref(x_120);
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
}
else
{
uint8 x_138; 
lean::dec(x_9);
x_138 = !lean::is_exclusive(x_86);
if (x_138 == 0)
{
return x_86;
}
else
{
obj* x_139; obj* x_140; obj* x_141; 
x_139 = lean::cnstr_get(x_86, 0);
x_140 = lean::cnstr_get(x_86, 1);
lean::inc(x_140);
lean::inc(x_139);
lean::dec(x_86);
x_141 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_141, 0, x_139);
lean::cnstr_set(x_141, 1, x_140);
return x_141;
}
}
}
}
else
{
obj* x_142; obj* x_143; obj* x_144; uint8 x_145; obj* x_146; obj* x_147; obj* x_148; 
x_142 = lean::cnstr_get(x_19, 0);
x_143 = lean::cnstr_get(x_19, 1);
lean::inc(x_143);
lean::inc(x_142);
lean::dec(x_19);
x_144 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_144, 0, x_8);
lean::cnstr_set(x_144, 1, x_143);
x_145 = l_List_isEmpty___main___rarg(x_1);
x_146 = l_List_redLength___main___rarg(x_1);
x_147 = lean::mk_empty_array(x_146);
lean::dec(x_146);
x_148 = l_List_toArrayAux___main___rarg(x_1, x_147);
if (x_145 == 0)
{
uint8 x_149; obj* x_150; obj* x_151; 
x_149 = 1;
x_150 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_150, 0, x_13);
lean::cnstr_set(x_150, 1, x_18);
lean::cnstr_set(x_150, 2, x_142);
lean::cnstr_set(x_150, 3, x_148);
lean::cnstr_set_scalar(x_150, sizeof(void*)*4, x_2);
lean::cnstr_set_scalar(x_150, sizeof(void*)*4 + 4, x_149);
x_151 = l___private_init_lean_environment_11__setImportedEntries(x_150, x_9, x_144);
if (lean::obj_tag(x_151) == 0)
{
obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; 
x_152 = lean::cnstr_get(x_151, 0);
lean::inc(x_152);
x_153 = lean::cnstr_get(x_151, 1);
lean::inc(x_153);
if (lean::is_exclusive(x_151)) {
 lean::cnstr_release(x_151, 0);
 lean::cnstr_release(x_151, 1);
 x_154 = x_151;
} else {
 lean::dec_ref(x_151);
 x_154 = lean::box(0);
}
if (lean::is_scalar(x_154)) {
 x_155 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_155 = x_154;
}
lean::cnstr_set(x_155, 0, x_8);
lean::cnstr_set(x_155, 1, x_153);
x_156 = l___private_init_lean_environment_13__finalizePersistentExtensions(x_152, x_155);
if (lean::obj_tag(x_156) == 0)
{
obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; 
x_157 = lean::cnstr_get(x_156, 0);
lean::inc(x_157);
x_158 = lean::cnstr_get(x_156, 1);
lean::inc(x_158);
if (lean::is_exclusive(x_156)) {
 lean::cnstr_release(x_156, 0);
 lean::cnstr_release(x_156, 1);
 x_159 = x_156;
} else {
 lean::dec_ref(x_156);
 x_159 = lean::box(0);
}
if (lean::is_scalar(x_159)) {
 x_160 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_160 = x_159;
}
lean::cnstr_set(x_160, 0, x_8);
lean::cnstr_set(x_160, 1, x_158);
x_161 = l_Array_miterateAux___main___at_Lean_importModules___spec__11(x_9, x_9, x_11, x_157, x_160);
lean::dec(x_9);
if (lean::obj_tag(x_161) == 0)
{
obj* x_162; obj* x_163; obj* x_164; obj* x_165; 
x_162 = lean::cnstr_get(x_161, 0);
lean::inc(x_162);
x_163 = lean::cnstr_get(x_161, 1);
lean::inc(x_163);
if (lean::is_exclusive(x_161)) {
 lean::cnstr_release(x_161, 0);
 lean::cnstr_release(x_161, 1);
 x_164 = x_161;
} else {
 lean::dec_ref(x_161);
 x_164 = lean::box(0);
}
if (lean::is_scalar(x_164)) {
 x_165 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_165 = x_164;
}
lean::cnstr_set(x_165, 0, x_162);
lean::cnstr_set(x_165, 1, x_163);
return x_165;
}
else
{
obj* x_166; obj* x_167; obj* x_168; obj* x_169; 
x_166 = lean::cnstr_get(x_161, 0);
lean::inc(x_166);
x_167 = lean::cnstr_get(x_161, 1);
lean::inc(x_167);
if (lean::is_exclusive(x_161)) {
 lean::cnstr_release(x_161, 0);
 lean::cnstr_release(x_161, 1);
 x_168 = x_161;
} else {
 lean::dec_ref(x_161);
 x_168 = lean::box(0);
}
if (lean::is_scalar(x_168)) {
 x_169 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_169 = x_168;
}
lean::cnstr_set(x_169, 0, x_166);
lean::cnstr_set(x_169, 1, x_167);
return x_169;
}
}
else
{
obj* x_170; obj* x_171; obj* x_172; obj* x_173; 
lean::dec(x_9);
x_170 = lean::cnstr_get(x_156, 0);
lean::inc(x_170);
x_171 = lean::cnstr_get(x_156, 1);
lean::inc(x_171);
if (lean::is_exclusive(x_156)) {
 lean::cnstr_release(x_156, 0);
 lean::cnstr_release(x_156, 1);
 x_172 = x_156;
} else {
 lean::dec_ref(x_156);
 x_172 = lean::box(0);
}
if (lean::is_scalar(x_172)) {
 x_173 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_173 = x_172;
}
lean::cnstr_set(x_173, 0, x_170);
lean::cnstr_set(x_173, 1, x_171);
return x_173;
}
}
else
{
obj* x_174; obj* x_175; obj* x_176; obj* x_177; 
lean::dec(x_9);
x_174 = lean::cnstr_get(x_151, 0);
lean::inc(x_174);
x_175 = lean::cnstr_get(x_151, 1);
lean::inc(x_175);
if (lean::is_exclusive(x_151)) {
 lean::cnstr_release(x_151, 0);
 lean::cnstr_release(x_151, 1);
 x_176 = x_151;
} else {
 lean::dec_ref(x_151);
 x_176 = lean::box(0);
}
if (lean::is_scalar(x_176)) {
 x_177 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_177 = x_176;
}
lean::cnstr_set(x_177, 0, x_174);
lean::cnstr_set(x_177, 1, x_175);
return x_177;
}
}
else
{
uint8 x_178; obj* x_179; obj* x_180; 
x_178 = 0;
x_179 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_179, 0, x_13);
lean::cnstr_set(x_179, 1, x_18);
lean::cnstr_set(x_179, 2, x_142);
lean::cnstr_set(x_179, 3, x_148);
lean::cnstr_set_scalar(x_179, sizeof(void*)*4, x_2);
lean::cnstr_set_scalar(x_179, sizeof(void*)*4 + 4, x_178);
x_180 = l___private_init_lean_environment_11__setImportedEntries(x_179, x_9, x_144);
if (lean::obj_tag(x_180) == 0)
{
obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; 
x_181 = lean::cnstr_get(x_180, 0);
lean::inc(x_181);
x_182 = lean::cnstr_get(x_180, 1);
lean::inc(x_182);
if (lean::is_exclusive(x_180)) {
 lean::cnstr_release(x_180, 0);
 lean::cnstr_release(x_180, 1);
 x_183 = x_180;
} else {
 lean::dec_ref(x_180);
 x_183 = lean::box(0);
}
if (lean::is_scalar(x_183)) {
 x_184 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_184 = x_183;
}
lean::cnstr_set(x_184, 0, x_8);
lean::cnstr_set(x_184, 1, x_182);
x_185 = l___private_init_lean_environment_13__finalizePersistentExtensions(x_181, x_184);
if (lean::obj_tag(x_185) == 0)
{
obj* x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; 
x_186 = lean::cnstr_get(x_185, 0);
lean::inc(x_186);
x_187 = lean::cnstr_get(x_185, 1);
lean::inc(x_187);
if (lean::is_exclusive(x_185)) {
 lean::cnstr_release(x_185, 0);
 lean::cnstr_release(x_185, 1);
 x_188 = x_185;
} else {
 lean::dec_ref(x_185);
 x_188 = lean::box(0);
}
if (lean::is_scalar(x_188)) {
 x_189 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_189 = x_188;
}
lean::cnstr_set(x_189, 0, x_8);
lean::cnstr_set(x_189, 1, x_187);
x_190 = l_Array_miterateAux___main___at_Lean_importModules___spec__12(x_9, x_9, x_11, x_186, x_189);
lean::dec(x_9);
if (lean::obj_tag(x_190) == 0)
{
obj* x_191; obj* x_192; obj* x_193; obj* x_194; 
x_191 = lean::cnstr_get(x_190, 0);
lean::inc(x_191);
x_192 = lean::cnstr_get(x_190, 1);
lean::inc(x_192);
if (lean::is_exclusive(x_190)) {
 lean::cnstr_release(x_190, 0);
 lean::cnstr_release(x_190, 1);
 x_193 = x_190;
} else {
 lean::dec_ref(x_190);
 x_193 = lean::box(0);
}
if (lean::is_scalar(x_193)) {
 x_194 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_194 = x_193;
}
lean::cnstr_set(x_194, 0, x_191);
lean::cnstr_set(x_194, 1, x_192);
return x_194;
}
else
{
obj* x_195; obj* x_196; obj* x_197; obj* x_198; 
x_195 = lean::cnstr_get(x_190, 0);
lean::inc(x_195);
x_196 = lean::cnstr_get(x_190, 1);
lean::inc(x_196);
if (lean::is_exclusive(x_190)) {
 lean::cnstr_release(x_190, 0);
 lean::cnstr_release(x_190, 1);
 x_197 = x_190;
} else {
 lean::dec_ref(x_190);
 x_197 = lean::box(0);
}
if (lean::is_scalar(x_197)) {
 x_198 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_198 = x_197;
}
lean::cnstr_set(x_198, 0, x_195);
lean::cnstr_set(x_198, 1, x_196);
return x_198;
}
}
else
{
obj* x_199; obj* x_200; obj* x_201; obj* x_202; 
lean::dec(x_9);
x_199 = lean::cnstr_get(x_185, 0);
lean::inc(x_199);
x_200 = lean::cnstr_get(x_185, 1);
lean::inc(x_200);
if (lean::is_exclusive(x_185)) {
 lean::cnstr_release(x_185, 0);
 lean::cnstr_release(x_185, 1);
 x_201 = x_185;
} else {
 lean::dec_ref(x_185);
 x_201 = lean::box(0);
}
if (lean::is_scalar(x_201)) {
 x_202 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_202 = x_201;
}
lean::cnstr_set(x_202, 0, x_199);
lean::cnstr_set(x_202, 1, x_200);
return x_202;
}
}
else
{
obj* x_203; obj* x_204; obj* x_205; obj* x_206; 
lean::dec(x_9);
x_203 = lean::cnstr_get(x_180, 0);
lean::inc(x_203);
x_204 = lean::cnstr_get(x_180, 1);
lean::inc(x_204);
if (lean::is_exclusive(x_180)) {
 lean::cnstr_release(x_180, 0);
 lean::cnstr_release(x_180, 1);
 x_205 = x_180;
} else {
 lean::dec_ref(x_180);
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
}
}
else
{
uint8 x_207; 
lean::dec(x_18);
lean::dec(x_13);
lean::dec(x_9);
lean::dec(x_1);
x_207 = !lean::is_exclusive(x_19);
if (x_207 == 0)
{
return x_19;
}
else
{
obj* x_208; obj* x_209; obj* x_210; 
x_208 = lean::cnstr_get(x_19, 0);
x_209 = lean::cnstr_get(x_19, 1);
lean::inc(x_209);
lean::inc(x_208);
lean::dec(x_19);
x_210 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_210, 0, x_208);
lean::cnstr_set(x_210, 1, x_209);
return x_210;
}
}
}
else
{
obj* x_211; obj* x_212; obj* x_213; obj* x_214; obj* x_215; 
x_211 = lean::cnstr_get(x_15, 0);
x_212 = lean::cnstr_get(x_15, 1);
lean::inc(x_212);
lean::inc(x_211);
lean::dec(x_15);
x_213 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_213, 0, x_8);
lean::cnstr_set(x_213, 1, x_212);
x_214 = l_Lean_SMap_switch___at___private_init_lean_environment_1__switch___spec__1(x_211);
x_215 = l___private_init_lean_environment_7__mkInitialExtensionStates(x_213);
if (lean::obj_tag(x_215) == 0)
{
obj* x_216; obj* x_217; obj* x_218; obj* x_219; uint8 x_220; obj* x_221; obj* x_222; obj* x_223; 
x_216 = lean::cnstr_get(x_215, 0);
lean::inc(x_216);
x_217 = lean::cnstr_get(x_215, 1);
lean::inc(x_217);
if (lean::is_exclusive(x_215)) {
 lean::cnstr_release(x_215, 0);
 lean::cnstr_release(x_215, 1);
 x_218 = x_215;
} else {
 lean::dec_ref(x_215);
 x_218 = lean::box(0);
}
if (lean::is_scalar(x_218)) {
 x_219 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_219 = x_218;
}
lean::cnstr_set(x_219, 0, x_8);
lean::cnstr_set(x_219, 1, x_217);
x_220 = l_List_isEmpty___main___rarg(x_1);
x_221 = l_List_redLength___main___rarg(x_1);
x_222 = lean::mk_empty_array(x_221);
lean::dec(x_221);
x_223 = l_List_toArrayAux___main___rarg(x_1, x_222);
if (x_220 == 0)
{
uint8 x_224; obj* x_225; obj* x_226; 
x_224 = 1;
x_225 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_225, 0, x_13);
lean::cnstr_set(x_225, 1, x_214);
lean::cnstr_set(x_225, 2, x_216);
lean::cnstr_set(x_225, 3, x_223);
lean::cnstr_set_scalar(x_225, sizeof(void*)*4, x_2);
lean::cnstr_set_scalar(x_225, sizeof(void*)*4 + 4, x_224);
x_226 = l___private_init_lean_environment_11__setImportedEntries(x_225, x_9, x_219);
if (lean::obj_tag(x_226) == 0)
{
obj* x_227; obj* x_228; obj* x_229; obj* x_230; obj* x_231; 
x_227 = lean::cnstr_get(x_226, 0);
lean::inc(x_227);
x_228 = lean::cnstr_get(x_226, 1);
lean::inc(x_228);
if (lean::is_exclusive(x_226)) {
 lean::cnstr_release(x_226, 0);
 lean::cnstr_release(x_226, 1);
 x_229 = x_226;
} else {
 lean::dec_ref(x_226);
 x_229 = lean::box(0);
}
if (lean::is_scalar(x_229)) {
 x_230 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_230 = x_229;
}
lean::cnstr_set(x_230, 0, x_8);
lean::cnstr_set(x_230, 1, x_228);
x_231 = l___private_init_lean_environment_13__finalizePersistentExtensions(x_227, x_230);
if (lean::obj_tag(x_231) == 0)
{
obj* x_232; obj* x_233; obj* x_234; obj* x_235; obj* x_236; 
x_232 = lean::cnstr_get(x_231, 0);
lean::inc(x_232);
x_233 = lean::cnstr_get(x_231, 1);
lean::inc(x_233);
if (lean::is_exclusive(x_231)) {
 lean::cnstr_release(x_231, 0);
 lean::cnstr_release(x_231, 1);
 x_234 = x_231;
} else {
 lean::dec_ref(x_231);
 x_234 = lean::box(0);
}
if (lean::is_scalar(x_234)) {
 x_235 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_235 = x_234;
}
lean::cnstr_set(x_235, 0, x_8);
lean::cnstr_set(x_235, 1, x_233);
x_236 = l_Array_miterateAux___main___at_Lean_importModules___spec__11(x_9, x_9, x_11, x_232, x_235);
lean::dec(x_9);
if (lean::obj_tag(x_236) == 0)
{
obj* x_237; obj* x_238; obj* x_239; obj* x_240; 
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
lean::cnstr_set(x_240, 0, x_237);
lean::cnstr_set(x_240, 1, x_238);
return x_240;
}
else
{
obj* x_241; obj* x_242; obj* x_243; obj* x_244; 
x_241 = lean::cnstr_get(x_236, 0);
lean::inc(x_241);
x_242 = lean::cnstr_get(x_236, 1);
lean::inc(x_242);
if (lean::is_exclusive(x_236)) {
 lean::cnstr_release(x_236, 0);
 lean::cnstr_release(x_236, 1);
 x_243 = x_236;
} else {
 lean::dec_ref(x_236);
 x_243 = lean::box(0);
}
if (lean::is_scalar(x_243)) {
 x_244 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_244 = x_243;
}
lean::cnstr_set(x_244, 0, x_241);
lean::cnstr_set(x_244, 1, x_242);
return x_244;
}
}
else
{
obj* x_245; obj* x_246; obj* x_247; obj* x_248; 
lean::dec(x_9);
x_245 = lean::cnstr_get(x_231, 0);
lean::inc(x_245);
x_246 = lean::cnstr_get(x_231, 1);
lean::inc(x_246);
if (lean::is_exclusive(x_231)) {
 lean::cnstr_release(x_231, 0);
 lean::cnstr_release(x_231, 1);
 x_247 = x_231;
} else {
 lean::dec_ref(x_231);
 x_247 = lean::box(0);
}
if (lean::is_scalar(x_247)) {
 x_248 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_248 = x_247;
}
lean::cnstr_set(x_248, 0, x_245);
lean::cnstr_set(x_248, 1, x_246);
return x_248;
}
}
else
{
obj* x_249; obj* x_250; obj* x_251; obj* x_252; 
lean::dec(x_9);
x_249 = lean::cnstr_get(x_226, 0);
lean::inc(x_249);
x_250 = lean::cnstr_get(x_226, 1);
lean::inc(x_250);
if (lean::is_exclusive(x_226)) {
 lean::cnstr_release(x_226, 0);
 lean::cnstr_release(x_226, 1);
 x_251 = x_226;
} else {
 lean::dec_ref(x_226);
 x_251 = lean::box(0);
}
if (lean::is_scalar(x_251)) {
 x_252 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_252 = x_251;
}
lean::cnstr_set(x_252, 0, x_249);
lean::cnstr_set(x_252, 1, x_250);
return x_252;
}
}
else
{
uint8 x_253; obj* x_254; obj* x_255; 
x_253 = 0;
x_254 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_254, 0, x_13);
lean::cnstr_set(x_254, 1, x_214);
lean::cnstr_set(x_254, 2, x_216);
lean::cnstr_set(x_254, 3, x_223);
lean::cnstr_set_scalar(x_254, sizeof(void*)*4, x_2);
lean::cnstr_set_scalar(x_254, sizeof(void*)*4 + 4, x_253);
x_255 = l___private_init_lean_environment_11__setImportedEntries(x_254, x_9, x_219);
if (lean::obj_tag(x_255) == 0)
{
obj* x_256; obj* x_257; obj* x_258; obj* x_259; obj* x_260; 
x_256 = lean::cnstr_get(x_255, 0);
lean::inc(x_256);
x_257 = lean::cnstr_get(x_255, 1);
lean::inc(x_257);
if (lean::is_exclusive(x_255)) {
 lean::cnstr_release(x_255, 0);
 lean::cnstr_release(x_255, 1);
 x_258 = x_255;
} else {
 lean::dec_ref(x_255);
 x_258 = lean::box(0);
}
if (lean::is_scalar(x_258)) {
 x_259 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_259 = x_258;
}
lean::cnstr_set(x_259, 0, x_8);
lean::cnstr_set(x_259, 1, x_257);
x_260 = l___private_init_lean_environment_13__finalizePersistentExtensions(x_256, x_259);
if (lean::obj_tag(x_260) == 0)
{
obj* x_261; obj* x_262; obj* x_263; obj* x_264; obj* x_265; 
x_261 = lean::cnstr_get(x_260, 0);
lean::inc(x_261);
x_262 = lean::cnstr_get(x_260, 1);
lean::inc(x_262);
if (lean::is_exclusive(x_260)) {
 lean::cnstr_release(x_260, 0);
 lean::cnstr_release(x_260, 1);
 x_263 = x_260;
} else {
 lean::dec_ref(x_260);
 x_263 = lean::box(0);
}
if (lean::is_scalar(x_263)) {
 x_264 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_264 = x_263;
}
lean::cnstr_set(x_264, 0, x_8);
lean::cnstr_set(x_264, 1, x_262);
x_265 = l_Array_miterateAux___main___at_Lean_importModules___spec__12(x_9, x_9, x_11, x_261, x_264);
lean::dec(x_9);
if (lean::obj_tag(x_265) == 0)
{
obj* x_266; obj* x_267; obj* x_268; obj* x_269; 
x_266 = lean::cnstr_get(x_265, 0);
lean::inc(x_266);
x_267 = lean::cnstr_get(x_265, 1);
lean::inc(x_267);
if (lean::is_exclusive(x_265)) {
 lean::cnstr_release(x_265, 0);
 lean::cnstr_release(x_265, 1);
 x_268 = x_265;
} else {
 lean::dec_ref(x_265);
 x_268 = lean::box(0);
}
if (lean::is_scalar(x_268)) {
 x_269 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_269 = x_268;
}
lean::cnstr_set(x_269, 0, x_266);
lean::cnstr_set(x_269, 1, x_267);
return x_269;
}
else
{
obj* x_270; obj* x_271; obj* x_272; obj* x_273; 
x_270 = lean::cnstr_get(x_265, 0);
lean::inc(x_270);
x_271 = lean::cnstr_get(x_265, 1);
lean::inc(x_271);
if (lean::is_exclusive(x_265)) {
 lean::cnstr_release(x_265, 0);
 lean::cnstr_release(x_265, 1);
 x_272 = x_265;
} else {
 lean::dec_ref(x_265);
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
lean::dec(x_9);
x_274 = lean::cnstr_get(x_260, 0);
lean::inc(x_274);
x_275 = lean::cnstr_get(x_260, 1);
lean::inc(x_275);
if (lean::is_exclusive(x_260)) {
 lean::cnstr_release(x_260, 0);
 lean::cnstr_release(x_260, 1);
 x_276 = x_260;
} else {
 lean::dec_ref(x_260);
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
lean::dec(x_9);
x_278 = lean::cnstr_get(x_255, 0);
lean::inc(x_278);
x_279 = lean::cnstr_get(x_255, 1);
lean::inc(x_279);
if (lean::is_exclusive(x_255)) {
 lean::cnstr_release(x_255, 0);
 lean::cnstr_release(x_255, 1);
 x_280 = x_255;
} else {
 lean::dec_ref(x_255);
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
}
else
{
obj* x_282; obj* x_283; obj* x_284; obj* x_285; 
lean::dec(x_214);
lean::dec(x_13);
lean::dec(x_9);
lean::dec(x_1);
x_282 = lean::cnstr_get(x_215, 0);
lean::inc(x_282);
x_283 = lean::cnstr_get(x_215, 1);
lean::inc(x_283);
if (lean::is_exclusive(x_215)) {
 lean::cnstr_release(x_215, 0);
 lean::cnstr_release(x_215, 1);
 x_284 = x_215;
} else {
 lean::dec_ref(x_215);
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
}
else
{
uint8 x_286; 
lean::dec(x_13);
lean::dec(x_9);
lean::dec(x_1);
x_286 = !lean::is_exclusive(x_15);
if (x_286 == 0)
{
return x_15;
}
else
{
obj* x_287; obj* x_288; obj* x_289; 
x_287 = lean::cnstr_get(x_15, 0);
x_288 = lean::cnstr_get(x_15, 1);
lean::inc(x_288);
lean::inc(x_287);
lean::dec(x_15);
x_289 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_289, 0, x_287);
lean::cnstr_set(x_289, 1, x_288);
return x_289;
}
}
}
else
{
obj* x_290; obj* x_291; obj* x_292; obj* x_293; obj* x_294; obj* x_295; obj* x_296; obj* x_297; obj* x_298; obj* x_299; obj* x_300; 
x_290 = lean::cnstr_get(x_5, 0);
x_291 = lean::cnstr_get(x_5, 1);
lean::inc(x_291);
lean::inc(x_290);
lean::dec(x_5);
x_292 = lean::box(0);
x_293 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_293, 0, x_292);
lean::cnstr_set(x_293, 1, x_291);
x_294 = lean::cnstr_get(x_290, 1);
lean::inc(x_294);
lean::dec(x_290);
x_295 = l_Lean_SMap_insert___main___at_Lean_Environment_add___spec__1___closed__2;
x_296 = lean::mk_nat_obj(0u);
x_297 = l_HashMap_Inhabited___closed__1;
x_298 = l_Array_miterateAux___main___at_Lean_importModules___spec__8(x_294, x_295, x_294, x_296, x_297);
x_299 = l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2;
x_300 = l_Array_miterateAux___main___at_Lean_importModules___spec__10(x_294, x_295, x_294, x_296, x_299, x_293);
if (lean::obj_tag(x_300) == 0)
{
obj* x_301; obj* x_302; obj* x_303; obj* x_304; obj* x_305; obj* x_306; 
x_301 = lean::cnstr_get(x_300, 0);
lean::inc(x_301);
x_302 = lean::cnstr_get(x_300, 1);
lean::inc(x_302);
if (lean::is_exclusive(x_300)) {
 lean::cnstr_release(x_300, 0);
 lean::cnstr_release(x_300, 1);
 x_303 = x_300;
} else {
 lean::dec_ref(x_300);
 x_303 = lean::box(0);
}
if (lean::is_scalar(x_303)) {
 x_304 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_304 = x_303;
}
lean::cnstr_set(x_304, 0, x_292);
lean::cnstr_set(x_304, 1, x_302);
x_305 = l_Lean_SMap_switch___at___private_init_lean_environment_1__switch___spec__1(x_301);
x_306 = l___private_init_lean_environment_7__mkInitialExtensionStates(x_304);
if (lean::obj_tag(x_306) == 0)
{
obj* x_307; obj* x_308; obj* x_309; obj* x_310; uint8 x_311; obj* x_312; obj* x_313; obj* x_314; 
x_307 = lean::cnstr_get(x_306, 0);
lean::inc(x_307);
x_308 = lean::cnstr_get(x_306, 1);
lean::inc(x_308);
if (lean::is_exclusive(x_306)) {
 lean::cnstr_release(x_306, 0);
 lean::cnstr_release(x_306, 1);
 x_309 = x_306;
} else {
 lean::dec_ref(x_306);
 x_309 = lean::box(0);
}
if (lean::is_scalar(x_309)) {
 x_310 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_310 = x_309;
}
lean::cnstr_set(x_310, 0, x_292);
lean::cnstr_set(x_310, 1, x_308);
x_311 = l_List_isEmpty___main___rarg(x_1);
x_312 = l_List_redLength___main___rarg(x_1);
x_313 = lean::mk_empty_array(x_312);
lean::dec(x_312);
x_314 = l_List_toArrayAux___main___rarg(x_1, x_313);
if (x_311 == 0)
{
uint8 x_315; obj* x_316; obj* x_317; 
x_315 = 1;
x_316 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_316, 0, x_298);
lean::cnstr_set(x_316, 1, x_305);
lean::cnstr_set(x_316, 2, x_307);
lean::cnstr_set(x_316, 3, x_314);
lean::cnstr_set_scalar(x_316, sizeof(void*)*4, x_2);
lean::cnstr_set_scalar(x_316, sizeof(void*)*4 + 4, x_315);
x_317 = l___private_init_lean_environment_11__setImportedEntries(x_316, x_294, x_310);
if (lean::obj_tag(x_317) == 0)
{
obj* x_318; obj* x_319; obj* x_320; obj* x_321; obj* x_322; 
x_318 = lean::cnstr_get(x_317, 0);
lean::inc(x_318);
x_319 = lean::cnstr_get(x_317, 1);
lean::inc(x_319);
if (lean::is_exclusive(x_317)) {
 lean::cnstr_release(x_317, 0);
 lean::cnstr_release(x_317, 1);
 x_320 = x_317;
} else {
 lean::dec_ref(x_317);
 x_320 = lean::box(0);
}
if (lean::is_scalar(x_320)) {
 x_321 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_321 = x_320;
}
lean::cnstr_set(x_321, 0, x_292);
lean::cnstr_set(x_321, 1, x_319);
x_322 = l___private_init_lean_environment_13__finalizePersistentExtensions(x_318, x_321);
if (lean::obj_tag(x_322) == 0)
{
obj* x_323; obj* x_324; obj* x_325; obj* x_326; obj* x_327; 
x_323 = lean::cnstr_get(x_322, 0);
lean::inc(x_323);
x_324 = lean::cnstr_get(x_322, 1);
lean::inc(x_324);
if (lean::is_exclusive(x_322)) {
 lean::cnstr_release(x_322, 0);
 lean::cnstr_release(x_322, 1);
 x_325 = x_322;
} else {
 lean::dec_ref(x_322);
 x_325 = lean::box(0);
}
if (lean::is_scalar(x_325)) {
 x_326 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_326 = x_325;
}
lean::cnstr_set(x_326, 0, x_292);
lean::cnstr_set(x_326, 1, x_324);
x_327 = l_Array_miterateAux___main___at_Lean_importModules___spec__11(x_294, x_294, x_296, x_323, x_326);
lean::dec(x_294);
if (lean::obj_tag(x_327) == 0)
{
obj* x_328; obj* x_329; obj* x_330; obj* x_331; 
x_328 = lean::cnstr_get(x_327, 0);
lean::inc(x_328);
x_329 = lean::cnstr_get(x_327, 1);
lean::inc(x_329);
if (lean::is_exclusive(x_327)) {
 lean::cnstr_release(x_327, 0);
 lean::cnstr_release(x_327, 1);
 x_330 = x_327;
} else {
 lean::dec_ref(x_327);
 x_330 = lean::box(0);
}
if (lean::is_scalar(x_330)) {
 x_331 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_331 = x_330;
}
lean::cnstr_set(x_331, 0, x_328);
lean::cnstr_set(x_331, 1, x_329);
return x_331;
}
else
{
obj* x_332; obj* x_333; obj* x_334; obj* x_335; 
x_332 = lean::cnstr_get(x_327, 0);
lean::inc(x_332);
x_333 = lean::cnstr_get(x_327, 1);
lean::inc(x_333);
if (lean::is_exclusive(x_327)) {
 lean::cnstr_release(x_327, 0);
 lean::cnstr_release(x_327, 1);
 x_334 = x_327;
} else {
 lean::dec_ref(x_327);
 x_334 = lean::box(0);
}
if (lean::is_scalar(x_334)) {
 x_335 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_335 = x_334;
}
lean::cnstr_set(x_335, 0, x_332);
lean::cnstr_set(x_335, 1, x_333);
return x_335;
}
}
else
{
obj* x_336; obj* x_337; obj* x_338; obj* x_339; 
lean::dec(x_294);
x_336 = lean::cnstr_get(x_322, 0);
lean::inc(x_336);
x_337 = lean::cnstr_get(x_322, 1);
lean::inc(x_337);
if (lean::is_exclusive(x_322)) {
 lean::cnstr_release(x_322, 0);
 lean::cnstr_release(x_322, 1);
 x_338 = x_322;
} else {
 lean::dec_ref(x_322);
 x_338 = lean::box(0);
}
if (lean::is_scalar(x_338)) {
 x_339 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_339 = x_338;
}
lean::cnstr_set(x_339, 0, x_336);
lean::cnstr_set(x_339, 1, x_337);
return x_339;
}
}
else
{
obj* x_340; obj* x_341; obj* x_342; obj* x_343; 
lean::dec(x_294);
x_340 = lean::cnstr_get(x_317, 0);
lean::inc(x_340);
x_341 = lean::cnstr_get(x_317, 1);
lean::inc(x_341);
if (lean::is_exclusive(x_317)) {
 lean::cnstr_release(x_317, 0);
 lean::cnstr_release(x_317, 1);
 x_342 = x_317;
} else {
 lean::dec_ref(x_317);
 x_342 = lean::box(0);
}
if (lean::is_scalar(x_342)) {
 x_343 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_343 = x_342;
}
lean::cnstr_set(x_343, 0, x_340);
lean::cnstr_set(x_343, 1, x_341);
return x_343;
}
}
else
{
uint8 x_344; obj* x_345; obj* x_346; 
x_344 = 0;
x_345 = lean::alloc_cnstr(0, 4, 5);
lean::cnstr_set(x_345, 0, x_298);
lean::cnstr_set(x_345, 1, x_305);
lean::cnstr_set(x_345, 2, x_307);
lean::cnstr_set(x_345, 3, x_314);
lean::cnstr_set_scalar(x_345, sizeof(void*)*4, x_2);
lean::cnstr_set_scalar(x_345, sizeof(void*)*4 + 4, x_344);
x_346 = l___private_init_lean_environment_11__setImportedEntries(x_345, x_294, x_310);
if (lean::obj_tag(x_346) == 0)
{
obj* x_347; obj* x_348; obj* x_349; obj* x_350; obj* x_351; 
x_347 = lean::cnstr_get(x_346, 0);
lean::inc(x_347);
x_348 = lean::cnstr_get(x_346, 1);
lean::inc(x_348);
if (lean::is_exclusive(x_346)) {
 lean::cnstr_release(x_346, 0);
 lean::cnstr_release(x_346, 1);
 x_349 = x_346;
} else {
 lean::dec_ref(x_346);
 x_349 = lean::box(0);
}
if (lean::is_scalar(x_349)) {
 x_350 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_350 = x_349;
}
lean::cnstr_set(x_350, 0, x_292);
lean::cnstr_set(x_350, 1, x_348);
x_351 = l___private_init_lean_environment_13__finalizePersistentExtensions(x_347, x_350);
if (lean::obj_tag(x_351) == 0)
{
obj* x_352; obj* x_353; obj* x_354; obj* x_355; obj* x_356; 
x_352 = lean::cnstr_get(x_351, 0);
lean::inc(x_352);
x_353 = lean::cnstr_get(x_351, 1);
lean::inc(x_353);
if (lean::is_exclusive(x_351)) {
 lean::cnstr_release(x_351, 0);
 lean::cnstr_release(x_351, 1);
 x_354 = x_351;
} else {
 lean::dec_ref(x_351);
 x_354 = lean::box(0);
}
if (lean::is_scalar(x_354)) {
 x_355 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_355 = x_354;
}
lean::cnstr_set(x_355, 0, x_292);
lean::cnstr_set(x_355, 1, x_353);
x_356 = l_Array_miterateAux___main___at_Lean_importModules___spec__12(x_294, x_294, x_296, x_352, x_355);
lean::dec(x_294);
if (lean::obj_tag(x_356) == 0)
{
obj* x_357; obj* x_358; obj* x_359; obj* x_360; 
x_357 = lean::cnstr_get(x_356, 0);
lean::inc(x_357);
x_358 = lean::cnstr_get(x_356, 1);
lean::inc(x_358);
if (lean::is_exclusive(x_356)) {
 lean::cnstr_release(x_356, 0);
 lean::cnstr_release(x_356, 1);
 x_359 = x_356;
} else {
 lean::dec_ref(x_356);
 x_359 = lean::box(0);
}
if (lean::is_scalar(x_359)) {
 x_360 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_360 = x_359;
}
lean::cnstr_set(x_360, 0, x_357);
lean::cnstr_set(x_360, 1, x_358);
return x_360;
}
else
{
obj* x_361; obj* x_362; obj* x_363; obj* x_364; 
x_361 = lean::cnstr_get(x_356, 0);
lean::inc(x_361);
x_362 = lean::cnstr_get(x_356, 1);
lean::inc(x_362);
if (lean::is_exclusive(x_356)) {
 lean::cnstr_release(x_356, 0);
 lean::cnstr_release(x_356, 1);
 x_363 = x_356;
} else {
 lean::dec_ref(x_356);
 x_363 = lean::box(0);
}
if (lean::is_scalar(x_363)) {
 x_364 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_364 = x_363;
}
lean::cnstr_set(x_364, 0, x_361);
lean::cnstr_set(x_364, 1, x_362);
return x_364;
}
}
else
{
obj* x_365; obj* x_366; obj* x_367; obj* x_368; 
lean::dec(x_294);
x_365 = lean::cnstr_get(x_351, 0);
lean::inc(x_365);
x_366 = lean::cnstr_get(x_351, 1);
lean::inc(x_366);
if (lean::is_exclusive(x_351)) {
 lean::cnstr_release(x_351, 0);
 lean::cnstr_release(x_351, 1);
 x_367 = x_351;
} else {
 lean::dec_ref(x_351);
 x_367 = lean::box(0);
}
if (lean::is_scalar(x_367)) {
 x_368 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_368 = x_367;
}
lean::cnstr_set(x_368, 0, x_365);
lean::cnstr_set(x_368, 1, x_366);
return x_368;
}
}
else
{
obj* x_369; obj* x_370; obj* x_371; obj* x_372; 
lean::dec(x_294);
x_369 = lean::cnstr_get(x_346, 0);
lean::inc(x_369);
x_370 = lean::cnstr_get(x_346, 1);
lean::inc(x_370);
if (lean::is_exclusive(x_346)) {
 lean::cnstr_release(x_346, 0);
 lean::cnstr_release(x_346, 1);
 x_371 = x_346;
} else {
 lean::dec_ref(x_346);
 x_371 = lean::box(0);
}
if (lean::is_scalar(x_371)) {
 x_372 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_372 = x_371;
}
lean::cnstr_set(x_372, 0, x_369);
lean::cnstr_set(x_372, 1, x_370);
return x_372;
}
}
}
else
{
obj* x_373; obj* x_374; obj* x_375; obj* x_376; 
lean::dec(x_305);
lean::dec(x_298);
lean::dec(x_294);
lean::dec(x_1);
x_373 = lean::cnstr_get(x_306, 0);
lean::inc(x_373);
x_374 = lean::cnstr_get(x_306, 1);
lean::inc(x_374);
if (lean::is_exclusive(x_306)) {
 lean::cnstr_release(x_306, 0);
 lean::cnstr_release(x_306, 1);
 x_375 = x_306;
} else {
 lean::dec_ref(x_306);
 x_375 = lean::box(0);
}
if (lean::is_scalar(x_375)) {
 x_376 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_376 = x_375;
}
lean::cnstr_set(x_376, 0, x_373);
lean::cnstr_set(x_376, 1, x_374);
return x_376;
}
}
else
{
obj* x_377; obj* x_378; obj* x_379; obj* x_380; 
lean::dec(x_298);
lean::dec(x_294);
lean::dec(x_1);
x_377 = lean::cnstr_get(x_300, 0);
lean::inc(x_377);
x_378 = lean::cnstr_get(x_300, 1);
lean::inc(x_378);
if (lean::is_exclusive(x_300)) {
 lean::cnstr_release(x_300, 0);
 lean::cnstr_release(x_300, 1);
 x_379 = x_300;
} else {
 lean::dec_ref(x_300);
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
}
else
{
uint8 x_381; 
lean::dec(x_1);
x_381 = !lean::is_exclusive(x_5);
if (x_381 == 0)
{
return x_5;
}
else
{
obj* x_382; obj* x_383; obj* x_384; 
x_382 = lean::cnstr_get(x_5, 0);
x_383 = lean::cnstr_get(x_5, 1);
lean::inc(x_383);
lean::inc(x_382);
lean::dec(x_5);
x_384 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_384, 0, x_382);
lean::cnstr_set(x_384, 1, x_383);
return x_384;
}
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
obj* l_Array_miterateAux___main___at_Lean_importModules___spec__11___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_importModules___spec__11(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
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
obj* l_Lean_importModules___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_5 = lean::import_modules_core(x_1, x_4, x_3);
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
lean::dec(x_2);
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
x_9 = lean::string_append(x_8, x_7);
lean::dec(x_7);
x_10 = l_List_toStringAux___main___at_Lean_Environment_displayStats___spec__2(x_1, x_5);
x_11 = lean::string_append(x_9, x_10);
lean::dec(x_10);
return x_11;
}
}
else
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_12; 
lean::dec(x_2);
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
x_19 = lean::string_append(x_16, x_18);
lean::dec(x_18);
return x_19;
}
}
}
}
obj* l_List_toString___main___at_Lean_Environment_displayStats___spec__1(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
lean::dec(x_1);
x_2 = l_List_repr___main___rarg___closed__1;
return x_2;
}
else
{
uint8 x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = 1;
x_4 = l_List_toStringAux___main___at_Lean_Environment_displayStats___spec__2(x_3, x_1);
x_5 = l_List_repr___main___rarg___closed__2;
x_6 = lean::string_append(x_5, x_4);
lean::dec(x_4);
x_7 = l_List_repr___main___rarg___closed__3;
x_8 = lean::string_append(x_6, x_7);
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
x_7 = lean::nat_add(x_6, x_5);
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
x_3 = lean::array_get_size(x_2);
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
x_6 = lean::array_get_size(x_3);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
return x_5;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_8 = lean::array_fget(x_3, x_4);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
x_10 = lean::nat_add(x_5, x_9);
lean::dec(x_9);
lean::dec(x_5);
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_add(x_4, x_11);
lean::dec(x_4);
x_4 = x_12;
x_5 = x_10;
goto _start;
}
}
}
obj* _init_l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("extension '");
return x_1;
}
}
obj* _init_l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("  lazy:                       ");
return x_1;
}
}
obj* _init_l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("  number of imported entries: ");
return x_1;
}
}
obj* _init_l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("  number of local entries:    ");
return x_1;
}
}
obj* _init_l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_string("  forced state:               ");
x_2 = lean::mk_string("false");
x_3 = lean::string_append(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_string("  forced state:               ");
x_2 = lean::mk_string("true");
x_3 = lean::string_append(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_3, x_5);
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
x_13 = lean::array_fget(x_2, x_3);
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_3, x_14);
lean::dec(x_3);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
x_17 = l_Lean_Name_toString___closed__1;
x_18 = l_Lean_Name_toStringWithSep___main(x_17, x_16);
x_19 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__1;
x_20 = lean::string_append(x_19, x_18);
lean::dec(x_18);
x_21 = l_Char_HasRepr___closed__1;
x_22 = lean::string_append(x_20, x_21);
x_23 = l_IO_println___at_HasRepr_HasEval___spec__1(x_22, x_4);
lean::dec(x_22);
if (lean::obj_tag(x_23) == 0)
{
uint8 x_24; 
x_24 = !lean::is_exclusive(x_23);
if (x_24 == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; uint8 x_199; 
x_25 = lean::cnstr_get(x_23, 0);
lean::dec(x_25);
x_26 = lean::box(0);
lean::cnstr_set(x_23, 0, x_26);
x_27 = lean::cnstr_get(x_13, 0);
lean::inc(x_27);
x_28 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_27, x_1);
x_199 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*5);
if (x_199 == 0)
{
obj* x_200; 
x_200 = l_Bool_HasRepr___closed__1;
x_29 = x_200;
goto block_198;
}
else
{
obj* x_201; 
x_201 = l_Bool_HasRepr___closed__2;
x_29 = x_201;
goto block_198;
}
block_198:
{
obj* x_30; obj* x_31; obj* x_32; 
x_30 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__2;
x_31 = lean::string_append(x_30, x_29);
lean::dec(x_29);
x_32 = l_IO_println___at_HasRepr_HasEval___spec__1(x_31, x_23);
lean::dec(x_31);
if (lean::obj_tag(x_32) == 0)
{
uint8 x_33; 
x_33 = !lean::is_exclusive(x_32);
if (x_33 == 0)
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_34 = lean::cnstr_get(x_32, 0);
lean::dec(x_34);
lean::cnstr_set(x_32, 0, x_26);
x_35 = lean::cnstr_get(x_28, 0);
lean::inc(x_35);
x_36 = lean::mk_nat_obj(0u);
x_37 = l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__8(x_1, x_13, x_35, x_36, x_36);
lean::dec(x_35);
lean::dec(x_13);
x_38 = l_Nat_repr(x_37);
x_39 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__3;
x_40 = lean::string_append(x_39, x_38);
lean::dec(x_38);
x_41 = l_IO_println___at_HasRepr_HasEval___spec__1(x_40, x_32);
lean::dec(x_40);
if (lean::obj_tag(x_41) == 0)
{
uint8 x_42; 
x_42 = !lean::is_exclusive(x_41);
if (x_42 == 0)
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_43 = lean::cnstr_get(x_41, 0);
lean::dec(x_43);
lean::cnstr_set(x_41, 0, x_26);
x_44 = lean::cnstr_get(x_28, 2);
lean::inc(x_44);
x_45 = l_List_lengthAux___main___rarg(x_44, x_36);
lean::dec(x_44);
x_46 = l_Nat_repr(x_45);
x_47 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__4;
x_48 = lean::string_append(x_47, x_46);
lean::dec(x_46);
x_49 = l_IO_println___at_HasRepr_HasEval___spec__1(x_48, x_41);
lean::dec(x_48);
if (lean::obj_tag(x_49) == 0)
{
uint8 x_50; 
x_50 = !lean::is_exclusive(x_49);
if (x_50 == 0)
{
obj* x_51; obj* x_52; 
x_51 = lean::cnstr_get(x_49, 0);
lean::dec(x_51);
lean::cnstr_set(x_49, 0, x_26);
x_52 = lean::cnstr_get(x_28, 3);
lean::inc(x_52);
lean::dec(x_28);
if (lean::obj_tag(x_52) == 0)
{
obj* x_53; obj* x_54; 
lean::dec(x_52);
x_53 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__5;
x_54 = l_IO_println___at_HasRepr_HasEval___spec__1(x_53, x_49);
if (lean::obj_tag(x_54) == 0)
{
uint8 x_55; 
x_55 = !lean::is_exclusive(x_54);
if (x_55 == 0)
{
obj* x_56; obj* x_57; 
x_56 = lean::cnstr_get(x_54, 0);
lean::dec(x_56);
lean::cnstr_set(x_54, 0, x_26);
x_3 = x_15;
x_4 = x_54;
goto _start;
}
else
{
obj* x_58; obj* x_59; obj* x_60; 
x_58 = lean::cnstr_get(x_54, 1);
lean::inc(x_58);
lean::dec(x_54);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_26);
lean::cnstr_set(x_59, 1, x_58);
x_3 = x_15;
x_4 = x_59;
goto _start;
}
}
else
{
uint8 x_61; 
lean::dec(x_15);
x_61 = !lean::is_exclusive(x_54);
if (x_61 == 0)
{
return x_54;
}
else
{
obj* x_62; obj* x_63; obj* x_64; 
x_62 = lean::cnstr_get(x_54, 0);
x_63 = lean::cnstr_get(x_54, 1);
lean::inc(x_63);
lean::inc(x_62);
lean::dec(x_54);
x_64 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_64, 0, x_62);
lean::cnstr_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
obj* x_65; obj* x_66; 
lean::dec(x_52);
x_65 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__6;
x_66 = l_IO_println___at_HasRepr_HasEval___spec__1(x_65, x_49);
if (lean::obj_tag(x_66) == 0)
{
uint8 x_67; 
x_67 = !lean::is_exclusive(x_66);
if (x_67 == 0)
{
obj* x_68; obj* x_69; 
x_68 = lean::cnstr_get(x_66, 0);
lean::dec(x_68);
lean::cnstr_set(x_66, 0, x_26);
x_3 = x_15;
x_4 = x_66;
goto _start;
}
else
{
obj* x_70; obj* x_71; obj* x_72; 
x_70 = lean::cnstr_get(x_66, 1);
lean::inc(x_70);
lean::dec(x_66);
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_26);
lean::cnstr_set(x_71, 1, x_70);
x_3 = x_15;
x_4 = x_71;
goto _start;
}
}
else
{
uint8 x_73; 
lean::dec(x_15);
x_73 = !lean::is_exclusive(x_66);
if (x_73 == 0)
{
return x_66;
}
else
{
obj* x_74; obj* x_75; obj* x_76; 
x_74 = lean::cnstr_get(x_66, 0);
x_75 = lean::cnstr_get(x_66, 1);
lean::inc(x_75);
lean::inc(x_74);
lean::dec(x_66);
x_76 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_76, 0, x_74);
lean::cnstr_set(x_76, 1, x_75);
return x_76;
}
}
}
}
else
{
obj* x_77; obj* x_78; obj* x_79; 
x_77 = lean::cnstr_get(x_49, 1);
lean::inc(x_77);
lean::dec(x_49);
x_78 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_78, 0, x_26);
lean::cnstr_set(x_78, 1, x_77);
x_79 = lean::cnstr_get(x_28, 3);
lean::inc(x_79);
lean::dec(x_28);
if (lean::obj_tag(x_79) == 0)
{
obj* x_80; obj* x_81; 
lean::dec(x_79);
x_80 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__5;
x_81 = l_IO_println___at_HasRepr_HasEval___spec__1(x_80, x_78);
if (lean::obj_tag(x_81) == 0)
{
obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_82 = lean::cnstr_get(x_81, 1);
lean::inc(x_82);
if (lean::is_exclusive(x_81)) {
 lean::cnstr_release(x_81, 0);
 lean::cnstr_release(x_81, 1);
 x_83 = x_81;
} else {
 lean::dec_ref(x_81);
 x_83 = lean::box(0);
}
if (lean::is_scalar(x_83)) {
 x_84 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_84 = x_83;
}
lean::cnstr_set(x_84, 0, x_26);
lean::cnstr_set(x_84, 1, x_82);
x_3 = x_15;
x_4 = x_84;
goto _start;
}
else
{
obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
lean::dec(x_15);
x_86 = lean::cnstr_get(x_81, 0);
lean::inc(x_86);
x_87 = lean::cnstr_get(x_81, 1);
lean::inc(x_87);
if (lean::is_exclusive(x_81)) {
 lean::cnstr_release(x_81, 0);
 lean::cnstr_release(x_81, 1);
 x_88 = x_81;
} else {
 lean::dec_ref(x_81);
 x_88 = lean::box(0);
}
if (lean::is_scalar(x_88)) {
 x_89 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_89 = x_88;
}
lean::cnstr_set(x_89, 0, x_86);
lean::cnstr_set(x_89, 1, x_87);
return x_89;
}
}
else
{
obj* x_90; obj* x_91; 
lean::dec(x_79);
x_90 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__6;
x_91 = l_IO_println___at_HasRepr_HasEval___spec__1(x_90, x_78);
if (lean::obj_tag(x_91) == 0)
{
obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_92 = lean::cnstr_get(x_91, 1);
lean::inc(x_92);
if (lean::is_exclusive(x_91)) {
 lean::cnstr_release(x_91, 0);
 lean::cnstr_release(x_91, 1);
 x_93 = x_91;
} else {
 lean::dec_ref(x_91);
 x_93 = lean::box(0);
}
if (lean::is_scalar(x_93)) {
 x_94 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_94 = x_93;
}
lean::cnstr_set(x_94, 0, x_26);
lean::cnstr_set(x_94, 1, x_92);
x_3 = x_15;
x_4 = x_94;
goto _start;
}
else
{
obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
lean::dec(x_15);
x_96 = lean::cnstr_get(x_91, 0);
lean::inc(x_96);
x_97 = lean::cnstr_get(x_91, 1);
lean::inc(x_97);
if (lean::is_exclusive(x_91)) {
 lean::cnstr_release(x_91, 0);
 lean::cnstr_release(x_91, 1);
 x_98 = x_91;
} else {
 lean::dec_ref(x_91);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_98)) {
 x_99 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_99 = x_98;
}
lean::cnstr_set(x_99, 0, x_96);
lean::cnstr_set(x_99, 1, x_97);
return x_99;
}
}
}
}
else
{
uint8 x_100; 
lean::dec(x_28);
lean::dec(x_15);
x_100 = !lean::is_exclusive(x_49);
if (x_100 == 0)
{
return x_49;
}
else
{
obj* x_101; obj* x_102; obj* x_103; 
x_101 = lean::cnstr_get(x_49, 0);
x_102 = lean::cnstr_get(x_49, 1);
lean::inc(x_102);
lean::inc(x_101);
lean::dec(x_49);
x_103 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_103, 0, x_101);
lean::cnstr_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
x_104 = lean::cnstr_get(x_41, 1);
lean::inc(x_104);
lean::dec(x_41);
x_105 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_105, 0, x_26);
lean::cnstr_set(x_105, 1, x_104);
x_106 = lean::cnstr_get(x_28, 2);
lean::inc(x_106);
x_107 = l_List_lengthAux___main___rarg(x_106, x_36);
lean::dec(x_106);
x_108 = l_Nat_repr(x_107);
x_109 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__4;
x_110 = lean::string_append(x_109, x_108);
lean::dec(x_108);
x_111 = l_IO_println___at_HasRepr_HasEval___spec__1(x_110, x_105);
lean::dec(x_110);
if (lean::obj_tag(x_111) == 0)
{
obj* x_112; obj* x_113; obj* x_114; obj* x_115; 
x_112 = lean::cnstr_get(x_111, 1);
lean::inc(x_112);
if (lean::is_exclusive(x_111)) {
 lean::cnstr_release(x_111, 0);
 lean::cnstr_release(x_111, 1);
 x_113 = x_111;
} else {
 lean::dec_ref(x_111);
 x_113 = lean::box(0);
}
if (lean::is_scalar(x_113)) {
 x_114 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_114 = x_113;
}
lean::cnstr_set(x_114, 0, x_26);
lean::cnstr_set(x_114, 1, x_112);
x_115 = lean::cnstr_get(x_28, 3);
lean::inc(x_115);
lean::dec(x_28);
if (lean::obj_tag(x_115) == 0)
{
obj* x_116; obj* x_117; 
lean::dec(x_115);
x_116 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__5;
x_117 = l_IO_println___at_HasRepr_HasEval___spec__1(x_116, x_114);
if (lean::obj_tag(x_117) == 0)
{
obj* x_118; obj* x_119; obj* x_120; obj* x_121; 
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
lean::cnstr_set(x_120, 0, x_26);
lean::cnstr_set(x_120, 1, x_118);
x_3 = x_15;
x_4 = x_120;
goto _start;
}
else
{
obj* x_122; obj* x_123; obj* x_124; obj* x_125; 
lean::dec(x_15);
x_122 = lean::cnstr_get(x_117, 0);
lean::inc(x_122);
x_123 = lean::cnstr_get(x_117, 1);
lean::inc(x_123);
if (lean::is_exclusive(x_117)) {
 lean::cnstr_release(x_117, 0);
 lean::cnstr_release(x_117, 1);
 x_124 = x_117;
} else {
 lean::dec_ref(x_117);
 x_124 = lean::box(0);
}
if (lean::is_scalar(x_124)) {
 x_125 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_125 = x_124;
}
lean::cnstr_set(x_125, 0, x_122);
lean::cnstr_set(x_125, 1, x_123);
return x_125;
}
}
else
{
obj* x_126; obj* x_127; 
lean::dec(x_115);
x_126 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__6;
x_127 = l_IO_println___at_HasRepr_HasEval___spec__1(x_126, x_114);
if (lean::obj_tag(x_127) == 0)
{
obj* x_128; obj* x_129; obj* x_130; obj* x_131; 
x_128 = lean::cnstr_get(x_127, 1);
lean::inc(x_128);
if (lean::is_exclusive(x_127)) {
 lean::cnstr_release(x_127, 0);
 lean::cnstr_release(x_127, 1);
 x_129 = x_127;
} else {
 lean::dec_ref(x_127);
 x_129 = lean::box(0);
}
if (lean::is_scalar(x_129)) {
 x_130 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_130 = x_129;
}
lean::cnstr_set(x_130, 0, x_26);
lean::cnstr_set(x_130, 1, x_128);
x_3 = x_15;
x_4 = x_130;
goto _start;
}
else
{
obj* x_132; obj* x_133; obj* x_134; obj* x_135; 
lean::dec(x_15);
x_132 = lean::cnstr_get(x_127, 0);
lean::inc(x_132);
x_133 = lean::cnstr_get(x_127, 1);
lean::inc(x_133);
if (lean::is_exclusive(x_127)) {
 lean::cnstr_release(x_127, 0);
 lean::cnstr_release(x_127, 1);
 x_134 = x_127;
} else {
 lean::dec_ref(x_127);
 x_134 = lean::box(0);
}
if (lean::is_scalar(x_134)) {
 x_135 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_135 = x_134;
}
lean::cnstr_set(x_135, 0, x_132);
lean::cnstr_set(x_135, 1, x_133);
return x_135;
}
}
}
else
{
obj* x_136; obj* x_137; obj* x_138; obj* x_139; 
lean::dec(x_28);
lean::dec(x_15);
x_136 = lean::cnstr_get(x_111, 0);
lean::inc(x_136);
x_137 = lean::cnstr_get(x_111, 1);
lean::inc(x_137);
if (lean::is_exclusive(x_111)) {
 lean::cnstr_release(x_111, 0);
 lean::cnstr_release(x_111, 1);
 x_138 = x_111;
} else {
 lean::dec_ref(x_111);
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
}
else
{
uint8 x_140; 
lean::dec(x_28);
lean::dec(x_15);
x_140 = !lean::is_exclusive(x_41);
if (x_140 == 0)
{
return x_41;
}
else
{
obj* x_141; obj* x_142; obj* x_143; 
x_141 = lean::cnstr_get(x_41, 0);
x_142 = lean::cnstr_get(x_41, 1);
lean::inc(x_142);
lean::inc(x_141);
lean::dec(x_41);
x_143 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_143, 0, x_141);
lean::cnstr_set(x_143, 1, x_142);
return x_143;
}
}
}
else
{
obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
x_144 = lean::cnstr_get(x_32, 1);
lean::inc(x_144);
lean::dec(x_32);
x_145 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_145, 0, x_26);
lean::cnstr_set(x_145, 1, x_144);
x_146 = lean::cnstr_get(x_28, 0);
lean::inc(x_146);
x_147 = lean::mk_nat_obj(0u);
x_148 = l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__8(x_1, x_13, x_146, x_147, x_147);
lean::dec(x_146);
lean::dec(x_13);
x_149 = l_Nat_repr(x_148);
x_150 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__3;
x_151 = lean::string_append(x_150, x_149);
lean::dec(x_149);
x_152 = l_IO_println___at_HasRepr_HasEval___spec__1(x_151, x_145);
lean::dec(x_151);
if (lean::obj_tag(x_152) == 0)
{
obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; 
x_153 = lean::cnstr_get(x_152, 1);
lean::inc(x_153);
if (lean::is_exclusive(x_152)) {
 lean::cnstr_release(x_152, 0);
 lean::cnstr_release(x_152, 1);
 x_154 = x_152;
} else {
 lean::dec_ref(x_152);
 x_154 = lean::box(0);
}
if (lean::is_scalar(x_154)) {
 x_155 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_155 = x_154;
}
lean::cnstr_set(x_155, 0, x_26);
lean::cnstr_set(x_155, 1, x_153);
x_156 = lean::cnstr_get(x_28, 2);
lean::inc(x_156);
x_157 = l_List_lengthAux___main___rarg(x_156, x_147);
lean::dec(x_156);
x_158 = l_Nat_repr(x_157);
x_159 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__4;
x_160 = lean::string_append(x_159, x_158);
lean::dec(x_158);
x_161 = l_IO_println___at_HasRepr_HasEval___spec__1(x_160, x_155);
lean::dec(x_160);
if (lean::obj_tag(x_161) == 0)
{
obj* x_162; obj* x_163; obj* x_164; obj* x_165; 
x_162 = lean::cnstr_get(x_161, 1);
lean::inc(x_162);
if (lean::is_exclusive(x_161)) {
 lean::cnstr_release(x_161, 0);
 lean::cnstr_release(x_161, 1);
 x_163 = x_161;
} else {
 lean::dec_ref(x_161);
 x_163 = lean::box(0);
}
if (lean::is_scalar(x_163)) {
 x_164 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_164 = x_163;
}
lean::cnstr_set(x_164, 0, x_26);
lean::cnstr_set(x_164, 1, x_162);
x_165 = lean::cnstr_get(x_28, 3);
lean::inc(x_165);
lean::dec(x_28);
if (lean::obj_tag(x_165) == 0)
{
obj* x_166; obj* x_167; 
lean::dec(x_165);
x_166 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__5;
x_167 = l_IO_println___at_HasRepr_HasEval___spec__1(x_166, x_164);
if (lean::obj_tag(x_167) == 0)
{
obj* x_168; obj* x_169; obj* x_170; obj* x_171; 
x_168 = lean::cnstr_get(x_167, 1);
lean::inc(x_168);
if (lean::is_exclusive(x_167)) {
 lean::cnstr_release(x_167, 0);
 lean::cnstr_release(x_167, 1);
 x_169 = x_167;
} else {
 lean::dec_ref(x_167);
 x_169 = lean::box(0);
}
if (lean::is_scalar(x_169)) {
 x_170 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_170 = x_169;
}
lean::cnstr_set(x_170, 0, x_26);
lean::cnstr_set(x_170, 1, x_168);
x_3 = x_15;
x_4 = x_170;
goto _start;
}
else
{
obj* x_172; obj* x_173; obj* x_174; obj* x_175; 
lean::dec(x_15);
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
obj* x_176; obj* x_177; 
lean::dec(x_165);
x_176 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__6;
x_177 = l_IO_println___at_HasRepr_HasEval___spec__1(x_176, x_164);
if (lean::obj_tag(x_177) == 0)
{
obj* x_178; obj* x_179; obj* x_180; obj* x_181; 
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
lean::cnstr_set(x_180, 0, x_26);
lean::cnstr_set(x_180, 1, x_178);
x_3 = x_15;
x_4 = x_180;
goto _start;
}
else
{
obj* x_182; obj* x_183; obj* x_184; obj* x_185; 
lean::dec(x_15);
x_182 = lean::cnstr_get(x_177, 0);
lean::inc(x_182);
x_183 = lean::cnstr_get(x_177, 1);
lean::inc(x_183);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 x_184 = x_177;
} else {
 lean::dec_ref(x_177);
 x_184 = lean::box(0);
}
if (lean::is_scalar(x_184)) {
 x_185 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_185 = x_184;
}
lean::cnstr_set(x_185, 0, x_182);
lean::cnstr_set(x_185, 1, x_183);
return x_185;
}
}
}
else
{
obj* x_186; obj* x_187; obj* x_188; obj* x_189; 
lean::dec(x_28);
lean::dec(x_15);
x_186 = lean::cnstr_get(x_161, 0);
lean::inc(x_186);
x_187 = lean::cnstr_get(x_161, 1);
lean::inc(x_187);
if (lean::is_exclusive(x_161)) {
 lean::cnstr_release(x_161, 0);
 lean::cnstr_release(x_161, 1);
 x_188 = x_161;
} else {
 lean::dec_ref(x_161);
 x_188 = lean::box(0);
}
if (lean::is_scalar(x_188)) {
 x_189 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_189 = x_188;
}
lean::cnstr_set(x_189, 0, x_186);
lean::cnstr_set(x_189, 1, x_187);
return x_189;
}
}
else
{
obj* x_190; obj* x_191; obj* x_192; obj* x_193; 
lean::dec(x_28);
lean::dec(x_15);
x_190 = lean::cnstr_get(x_152, 0);
lean::inc(x_190);
x_191 = lean::cnstr_get(x_152, 1);
lean::inc(x_191);
if (lean::is_exclusive(x_152)) {
 lean::cnstr_release(x_152, 0);
 lean::cnstr_release(x_152, 1);
 x_192 = x_152;
} else {
 lean::dec_ref(x_152);
 x_192 = lean::box(0);
}
if (lean::is_scalar(x_192)) {
 x_193 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_193 = x_192;
}
lean::cnstr_set(x_193, 0, x_190);
lean::cnstr_set(x_193, 1, x_191);
return x_193;
}
}
}
else
{
uint8 x_194; 
lean::dec(x_28);
lean::dec(x_15);
lean::dec(x_13);
x_194 = !lean::is_exclusive(x_32);
if (x_194 == 0)
{
return x_32;
}
else
{
obj* x_195; obj* x_196; obj* x_197; 
x_195 = lean::cnstr_get(x_32, 0);
x_196 = lean::cnstr_get(x_32, 1);
lean::inc(x_196);
lean::inc(x_195);
lean::dec(x_32);
x_197 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_197, 0, x_195);
lean::cnstr_set(x_197, 1, x_196);
return x_197;
}
}
}
}
else
{
obj* x_202; obj* x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_207; uint8 x_267; 
x_202 = lean::cnstr_get(x_23, 1);
lean::inc(x_202);
lean::dec(x_23);
x_203 = lean::box(0);
x_204 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_204, 0, x_203);
lean::cnstr_set(x_204, 1, x_202);
x_205 = lean::cnstr_get(x_13, 0);
lean::inc(x_205);
x_206 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_205, x_1);
x_267 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*5);
if (x_267 == 0)
{
obj* x_268; 
x_268 = l_Bool_HasRepr___closed__1;
x_207 = x_268;
goto block_266;
}
else
{
obj* x_269; 
x_269 = l_Bool_HasRepr___closed__2;
x_207 = x_269;
goto block_266;
}
block_266:
{
obj* x_208; obj* x_209; obj* x_210; 
x_208 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__2;
x_209 = lean::string_append(x_208, x_207);
lean::dec(x_207);
x_210 = l_IO_println___at_HasRepr_HasEval___spec__1(x_209, x_204);
lean::dec(x_209);
if (lean::obj_tag(x_210) == 0)
{
obj* x_211; obj* x_212; obj* x_213; obj* x_214; obj* x_215; obj* x_216; obj* x_217; obj* x_218; obj* x_219; obj* x_220; 
x_211 = lean::cnstr_get(x_210, 1);
lean::inc(x_211);
if (lean::is_exclusive(x_210)) {
 lean::cnstr_release(x_210, 0);
 lean::cnstr_release(x_210, 1);
 x_212 = x_210;
} else {
 lean::dec_ref(x_210);
 x_212 = lean::box(0);
}
if (lean::is_scalar(x_212)) {
 x_213 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_213 = x_212;
}
lean::cnstr_set(x_213, 0, x_203);
lean::cnstr_set(x_213, 1, x_211);
x_214 = lean::cnstr_get(x_206, 0);
lean::inc(x_214);
x_215 = lean::mk_nat_obj(0u);
x_216 = l_Array_miterateAux___main___at_Lean_Environment_displayStats___spec__8(x_1, x_13, x_214, x_215, x_215);
lean::dec(x_214);
lean::dec(x_13);
x_217 = l_Nat_repr(x_216);
x_218 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__3;
x_219 = lean::string_append(x_218, x_217);
lean::dec(x_217);
x_220 = l_IO_println___at_HasRepr_HasEval___spec__1(x_219, x_213);
lean::dec(x_219);
if (lean::obj_tag(x_220) == 0)
{
obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; obj* x_229; 
x_221 = lean::cnstr_get(x_220, 1);
lean::inc(x_221);
if (lean::is_exclusive(x_220)) {
 lean::cnstr_release(x_220, 0);
 lean::cnstr_release(x_220, 1);
 x_222 = x_220;
} else {
 lean::dec_ref(x_220);
 x_222 = lean::box(0);
}
if (lean::is_scalar(x_222)) {
 x_223 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_223 = x_222;
}
lean::cnstr_set(x_223, 0, x_203);
lean::cnstr_set(x_223, 1, x_221);
x_224 = lean::cnstr_get(x_206, 2);
lean::inc(x_224);
x_225 = l_List_lengthAux___main___rarg(x_224, x_215);
lean::dec(x_224);
x_226 = l_Nat_repr(x_225);
x_227 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__4;
x_228 = lean::string_append(x_227, x_226);
lean::dec(x_226);
x_229 = l_IO_println___at_HasRepr_HasEval___spec__1(x_228, x_223);
lean::dec(x_228);
if (lean::obj_tag(x_229) == 0)
{
obj* x_230; obj* x_231; obj* x_232; obj* x_233; 
x_230 = lean::cnstr_get(x_229, 1);
lean::inc(x_230);
if (lean::is_exclusive(x_229)) {
 lean::cnstr_release(x_229, 0);
 lean::cnstr_release(x_229, 1);
 x_231 = x_229;
} else {
 lean::dec_ref(x_229);
 x_231 = lean::box(0);
}
if (lean::is_scalar(x_231)) {
 x_232 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_232 = x_231;
}
lean::cnstr_set(x_232, 0, x_203);
lean::cnstr_set(x_232, 1, x_230);
x_233 = lean::cnstr_get(x_206, 3);
lean::inc(x_233);
lean::dec(x_206);
if (lean::obj_tag(x_233) == 0)
{
obj* x_234; obj* x_235; 
lean::dec(x_233);
x_234 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__5;
x_235 = l_IO_println___at_HasRepr_HasEval___spec__1(x_234, x_232);
if (lean::obj_tag(x_235) == 0)
{
obj* x_236; obj* x_237; obj* x_238; obj* x_239; 
x_236 = lean::cnstr_get(x_235, 1);
lean::inc(x_236);
if (lean::is_exclusive(x_235)) {
 lean::cnstr_release(x_235, 0);
 lean::cnstr_release(x_235, 1);
 x_237 = x_235;
} else {
 lean::dec_ref(x_235);
 x_237 = lean::box(0);
}
if (lean::is_scalar(x_237)) {
 x_238 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_238 = x_237;
}
lean::cnstr_set(x_238, 0, x_203);
lean::cnstr_set(x_238, 1, x_236);
x_3 = x_15;
x_4 = x_238;
goto _start;
}
else
{
obj* x_240; obj* x_241; obj* x_242; obj* x_243; 
lean::dec(x_15);
x_240 = lean::cnstr_get(x_235, 0);
lean::inc(x_240);
x_241 = lean::cnstr_get(x_235, 1);
lean::inc(x_241);
if (lean::is_exclusive(x_235)) {
 lean::cnstr_release(x_235, 0);
 lean::cnstr_release(x_235, 1);
 x_242 = x_235;
} else {
 lean::dec_ref(x_235);
 x_242 = lean::box(0);
}
if (lean::is_scalar(x_242)) {
 x_243 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_243 = x_242;
}
lean::cnstr_set(x_243, 0, x_240);
lean::cnstr_set(x_243, 1, x_241);
return x_243;
}
}
else
{
obj* x_244; obj* x_245; 
lean::dec(x_233);
x_244 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__6;
x_245 = l_IO_println___at_HasRepr_HasEval___spec__1(x_244, x_232);
if (lean::obj_tag(x_245) == 0)
{
obj* x_246; obj* x_247; obj* x_248; obj* x_249; 
x_246 = lean::cnstr_get(x_245, 1);
lean::inc(x_246);
if (lean::is_exclusive(x_245)) {
 lean::cnstr_release(x_245, 0);
 lean::cnstr_release(x_245, 1);
 x_247 = x_245;
} else {
 lean::dec_ref(x_245);
 x_247 = lean::box(0);
}
if (lean::is_scalar(x_247)) {
 x_248 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_248 = x_247;
}
lean::cnstr_set(x_248, 0, x_203);
lean::cnstr_set(x_248, 1, x_246);
x_3 = x_15;
x_4 = x_248;
goto _start;
}
else
{
obj* x_250; obj* x_251; obj* x_252; obj* x_253; 
lean::dec(x_15);
x_250 = lean::cnstr_get(x_245, 0);
lean::inc(x_250);
x_251 = lean::cnstr_get(x_245, 1);
lean::inc(x_251);
if (lean::is_exclusive(x_245)) {
 lean::cnstr_release(x_245, 0);
 lean::cnstr_release(x_245, 1);
 x_252 = x_245;
} else {
 lean::dec_ref(x_245);
 x_252 = lean::box(0);
}
if (lean::is_scalar(x_252)) {
 x_253 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_253 = x_252;
}
lean::cnstr_set(x_253, 0, x_250);
lean::cnstr_set(x_253, 1, x_251);
return x_253;
}
}
}
else
{
obj* x_254; obj* x_255; obj* x_256; obj* x_257; 
lean::dec(x_206);
lean::dec(x_15);
x_254 = lean::cnstr_get(x_229, 0);
lean::inc(x_254);
x_255 = lean::cnstr_get(x_229, 1);
lean::inc(x_255);
if (lean::is_exclusive(x_229)) {
 lean::cnstr_release(x_229, 0);
 lean::cnstr_release(x_229, 1);
 x_256 = x_229;
} else {
 lean::dec_ref(x_229);
 x_256 = lean::box(0);
}
if (lean::is_scalar(x_256)) {
 x_257 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_257 = x_256;
}
lean::cnstr_set(x_257, 0, x_254);
lean::cnstr_set(x_257, 1, x_255);
return x_257;
}
}
else
{
obj* x_258; obj* x_259; obj* x_260; obj* x_261; 
lean::dec(x_206);
lean::dec(x_15);
x_258 = lean::cnstr_get(x_220, 0);
lean::inc(x_258);
x_259 = lean::cnstr_get(x_220, 1);
lean::inc(x_259);
if (lean::is_exclusive(x_220)) {
 lean::cnstr_release(x_220, 0);
 lean::cnstr_release(x_220, 1);
 x_260 = x_220;
} else {
 lean::dec_ref(x_220);
 x_260 = lean::box(0);
}
if (lean::is_scalar(x_260)) {
 x_261 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_261 = x_260;
}
lean::cnstr_set(x_261, 0, x_258);
lean::cnstr_set(x_261, 1, x_259);
return x_261;
}
}
else
{
obj* x_262; obj* x_263; obj* x_264; obj* x_265; 
lean::dec(x_206);
lean::dec(x_15);
lean::dec(x_13);
x_262 = lean::cnstr_get(x_210, 0);
lean::inc(x_262);
x_263 = lean::cnstr_get(x_210, 1);
lean::inc(x_263);
if (lean::is_exclusive(x_210)) {
 lean::cnstr_release(x_210, 0);
 lean::cnstr_release(x_210, 1);
 x_264 = x_210;
} else {
 lean::dec_ref(x_210);
 x_264 = lean::box(0);
}
if (lean::is_scalar(x_264)) {
 x_265 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_265 = x_264;
}
lean::cnstr_set(x_265, 0, x_262);
lean::cnstr_set(x_265, 1, x_263);
return x_265;
}
}
}
}
else
{
uint8 x_270; 
lean::dec(x_15);
lean::dec(x_13);
x_270 = !lean::is_exclusive(x_23);
if (x_270 == 0)
{
return x_23;
}
else
{
obj* x_271; obj* x_272; obj* x_273; 
x_271 = lean::cnstr_get(x_23, 0);
x_272 = lean::cnstr_get(x_23, 1);
lean::inc(x_272);
lean::inc(x_271);
lean::dec(x_23);
x_273 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_273, 0, x_271);
lean::cnstr_set(x_273, 1, x_272);
return x_273;
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
namespace lean {
obj* display_stats_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l___private_init_lean_environment_9__persistentEnvExtensionsRef;
x_4 = lean::io_ref_get(x_3, x_2);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_6 = lean::cnstr_get(x_4, 0);
x_7 = lean::box(0);
lean::cnstr_set(x_4, 0, x_7);
x_8 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_9 = lean::mk_nat_obj(0u);
x_10 = lean::array_get(x_8, x_6, x_9);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
lean::dec(x_10);
x_12 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_11, x_1);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
lean::dec(x_12);
x_14 = lean::array_get_size(x_13);
lean::dec(x_13);
x_15 = lean::cnstr_get(x_1, 3);
lean::inc(x_15);
x_16 = l_Array_toList___rarg(x_15);
lean::dec(x_15);
x_17 = l_List_toString___main___at_Lean_Environment_displayStats___spec__1(x_16);
x_18 = l_Lean_Environment_displayStats___closed__1;
x_19 = lean::string_append(x_18, x_17);
lean::dec(x_17);
x_20 = l_IO_println___at_HasRepr_HasEval___spec__1(x_19, x_4);
lean::dec(x_19);
if (lean::obj_tag(x_20) == 0)
{
uint8 x_21; 
x_21 = !lean::is_exclusive(x_20);
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_22 = lean::cnstr_get(x_20, 0);
lean::dec(x_22);
lean::cnstr_set(x_20, 0, x_7);
x_23 = l_Nat_repr(x_14);
x_24 = l_Lean_Environment_displayStats___closed__2;
x_25 = lean::string_append(x_24, x_23);
lean::dec(x_23);
x_26 = l_IO_println___at_HasRepr_HasEval___spec__1(x_25, x_20);
lean::dec(x_25);
if (lean::obj_tag(x_26) == 0)
{
uint8 x_27; 
x_27 = !lean::is_exclusive(x_26);
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_28 = lean::cnstr_get(x_26, 0);
lean::dec(x_28);
lean::cnstr_set(x_26, 0, x_7);
x_29 = lean::cnstr_get(x_1, 1);
lean::inc(x_29);
x_30 = l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3(x_29);
x_31 = l_Nat_repr(x_30);
x_32 = l_Lean_Environment_displayStats___closed__3;
x_33 = lean::string_append(x_32, x_31);
lean::dec(x_31);
x_34 = l_IO_println___at_HasRepr_HasEval___spec__1(x_33, x_26);
lean::dec(x_33);
if (lean::obj_tag(x_34) == 0)
{
uint8 x_35; 
x_35 = !lean::is_exclusive(x_34);
if (x_35 == 0)
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_36 = lean::cnstr_get(x_34, 0);
lean::dec(x_36);
lean::cnstr_set(x_34, 0, x_7);
x_37 = l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4(x_29);
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
x_39 = l_Nat_repr(x_38);
x_40 = l_Lean_Environment_displayStats___closed__4;
x_41 = lean::string_append(x_40, x_39);
lean::dec(x_39);
x_42 = l_IO_println___at_HasRepr_HasEval___spec__1(x_41, x_34);
lean::dec(x_41);
if (lean::obj_tag(x_42) == 0)
{
uint8 x_43; 
x_43 = !lean::is_exclusive(x_42);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_44 = lean::cnstr_get(x_42, 0);
lean::dec(x_44);
lean::cnstr_set(x_42, 0, x_7);
x_45 = lean::cnstr_get(x_37, 1);
lean::inc(x_45);
lean::dec(x_37);
x_46 = l_Nat_repr(x_45);
x_47 = l_Lean_Environment_displayStats___closed__5;
x_48 = lean::string_append(x_47, x_46);
lean::dec(x_46);
x_49 = l_IO_println___at_HasRepr_HasEval___spec__1(x_48, x_42);
lean::dec(x_48);
if (lean::obj_tag(x_49) == 0)
{
uint8 x_50; 
x_50 = !lean::is_exclusive(x_49);
if (x_50 == 0)
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_51 = lean::cnstr_get(x_49, 0);
lean::dec(x_51);
lean::cnstr_set(x_49, 0, x_7);
x_52 = l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(x_29);
x_53 = l_Nat_repr(x_52);
x_54 = l_Lean_Environment_displayStats___closed__6;
x_55 = lean::string_append(x_54, x_53);
lean::dec(x_53);
x_56 = l_IO_println___at_HasRepr_HasEval___spec__1(x_55, x_49);
lean::dec(x_55);
if (lean::obj_tag(x_56) == 0)
{
uint8 x_57; 
x_57 = !lean::is_exclusive(x_56);
if (x_57 == 0)
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_58 = lean::cnstr_get(x_56, 0);
lean::dec(x_58);
lean::cnstr_set(x_56, 0, x_7);
x_59 = l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(x_29);
lean::dec(x_29);
x_60 = l_Nat_repr(x_59);
x_61 = l_Lean_Environment_displayStats___closed__7;
x_62 = lean::string_append(x_61, x_60);
lean::dec(x_60);
x_63 = l_IO_println___at_HasRepr_HasEval___spec__1(x_62, x_56);
lean::dec(x_62);
if (lean::obj_tag(x_63) == 0)
{
uint8 x_64; 
x_64 = !lean::is_exclusive(x_63);
if (x_64 == 0)
{
obj* x_65; uint32 x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_65 = lean::cnstr_get(x_63, 0);
lean::dec(x_65);
lean::cnstr_set(x_63, 0, x_7);
x_66 = lean::cnstr_get_scalar<uint32>(x_1, sizeof(void*)*4);
x_67 = lean::uint32_to_nat(x_66);
x_68 = l_Nat_repr(x_67);
x_69 = l_Lean_Environment_displayStats___closed__8;
x_70 = lean::string_append(x_69, x_68);
lean::dec(x_68);
x_71 = l_IO_println___at_HasRepr_HasEval___spec__1(x_70, x_63);
lean::dec(x_70);
if (lean::obj_tag(x_71) == 0)
{
uint8 x_72; 
x_72 = !lean::is_exclusive(x_71);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
x_73 = lean::cnstr_get(x_71, 0);
lean::dec(x_73);
lean::cnstr_set(x_71, 0, x_7);
x_74 = lean::cnstr_get(x_1, 2);
lean::inc(x_74);
x_75 = lean::array_get_size(x_74);
lean::dec(x_74);
x_76 = l_Nat_repr(x_75);
x_77 = l_Lean_Environment_displayStats___closed__9;
x_78 = lean::string_append(x_77, x_76);
lean::dec(x_76);
x_79 = l_IO_println___at_HasRepr_HasEval___spec__1(x_78, x_71);
lean::dec(x_78);
if (lean::obj_tag(x_79) == 0)
{
uint8 x_80; 
x_80 = !lean::is_exclusive(x_79);
if (x_80 == 0)
{
obj* x_81; obj* x_82; 
x_81 = lean::cnstr_get(x_79, 0);
lean::dec(x_81);
lean::cnstr_set(x_79, 0, x_7);
x_82 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9(x_1, x_6, x_9, x_79);
lean::dec(x_6);
lean::dec(x_1);
if (lean::obj_tag(x_82) == 0)
{
uint8 x_83; 
x_83 = !lean::is_exclusive(x_82);
if (x_83 == 0)
{
obj* x_84; 
x_84 = lean::cnstr_get(x_82, 0);
lean::dec(x_84);
lean::cnstr_set(x_82, 0, x_7);
return x_82;
}
else
{
obj* x_85; obj* x_86; 
x_85 = lean::cnstr_get(x_82, 1);
lean::inc(x_85);
lean::dec(x_82);
x_86 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_86, 0, x_7);
lean::cnstr_set(x_86, 1, x_85);
return x_86;
}
}
else
{
uint8 x_87; 
x_87 = !lean::is_exclusive(x_82);
if (x_87 == 0)
{
return x_82;
}
else
{
obj* x_88; obj* x_89; obj* x_90; 
x_88 = lean::cnstr_get(x_82, 0);
x_89 = lean::cnstr_get(x_82, 1);
lean::inc(x_89);
lean::inc(x_88);
lean::dec(x_82);
x_90 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_90, 0, x_88);
lean::cnstr_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
obj* x_91; obj* x_92; obj* x_93; 
x_91 = lean::cnstr_get(x_79, 1);
lean::inc(x_91);
lean::dec(x_79);
x_92 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_92, 0, x_7);
lean::cnstr_set(x_92, 1, x_91);
x_93 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9(x_1, x_6, x_9, x_92);
lean::dec(x_6);
lean::dec(x_1);
if (lean::obj_tag(x_93) == 0)
{
obj* x_94; obj* x_95; obj* x_96; 
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
lean::cnstr_set(x_96, 0, x_7);
lean::cnstr_set(x_96, 1, x_94);
return x_96;
}
else
{
obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
x_97 = lean::cnstr_get(x_93, 0);
lean::inc(x_97);
x_98 = lean::cnstr_get(x_93, 1);
lean::inc(x_98);
if (lean::is_exclusive(x_93)) {
 lean::cnstr_release(x_93, 0);
 lean::cnstr_release(x_93, 1);
 x_99 = x_93;
} else {
 lean::dec_ref(x_93);
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
}
else
{
uint8 x_101; 
lean::dec(x_6);
lean::dec(x_1);
x_101 = !lean::is_exclusive(x_79);
if (x_101 == 0)
{
return x_79;
}
else
{
obj* x_102; obj* x_103; obj* x_104; 
x_102 = lean::cnstr_get(x_79, 0);
x_103 = lean::cnstr_get(x_79, 1);
lean::inc(x_103);
lean::inc(x_102);
lean::dec(x_79);
x_104 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_104, 0, x_102);
lean::cnstr_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
x_105 = lean::cnstr_get(x_71, 1);
lean::inc(x_105);
lean::dec(x_71);
x_106 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_106, 0, x_7);
lean::cnstr_set(x_106, 1, x_105);
x_107 = lean::cnstr_get(x_1, 2);
lean::inc(x_107);
x_108 = lean::array_get_size(x_107);
lean::dec(x_107);
x_109 = l_Nat_repr(x_108);
x_110 = l_Lean_Environment_displayStats___closed__9;
x_111 = lean::string_append(x_110, x_109);
lean::dec(x_109);
x_112 = l_IO_println___at_HasRepr_HasEval___spec__1(x_111, x_106);
lean::dec(x_111);
if (lean::obj_tag(x_112) == 0)
{
obj* x_113; obj* x_114; obj* x_115; obj* x_116; 
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
lean::cnstr_set(x_115, 0, x_7);
lean::cnstr_set(x_115, 1, x_113);
x_116 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9(x_1, x_6, x_9, x_115);
lean::dec(x_6);
lean::dec(x_1);
if (lean::obj_tag(x_116) == 0)
{
obj* x_117; obj* x_118; obj* x_119; 
x_117 = lean::cnstr_get(x_116, 1);
lean::inc(x_117);
if (lean::is_exclusive(x_116)) {
 lean::cnstr_release(x_116, 0);
 lean::cnstr_release(x_116, 1);
 x_118 = x_116;
} else {
 lean::dec_ref(x_116);
 x_118 = lean::box(0);
}
if (lean::is_scalar(x_118)) {
 x_119 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_119 = x_118;
}
lean::cnstr_set(x_119, 0, x_7);
lean::cnstr_set(x_119, 1, x_117);
return x_119;
}
else
{
obj* x_120; obj* x_121; obj* x_122; obj* x_123; 
x_120 = lean::cnstr_get(x_116, 0);
lean::inc(x_120);
x_121 = lean::cnstr_get(x_116, 1);
lean::inc(x_121);
if (lean::is_exclusive(x_116)) {
 lean::cnstr_release(x_116, 0);
 lean::cnstr_release(x_116, 1);
 x_122 = x_116;
} else {
 lean::dec_ref(x_116);
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
else
{
obj* x_124; obj* x_125; obj* x_126; obj* x_127; 
lean::dec(x_6);
lean::dec(x_1);
x_124 = lean::cnstr_get(x_112, 0);
lean::inc(x_124);
x_125 = lean::cnstr_get(x_112, 1);
lean::inc(x_125);
if (lean::is_exclusive(x_112)) {
 lean::cnstr_release(x_112, 0);
 lean::cnstr_release(x_112, 1);
 x_126 = x_112;
} else {
 lean::dec_ref(x_112);
 x_126 = lean::box(0);
}
if (lean::is_scalar(x_126)) {
 x_127 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_127 = x_126;
}
lean::cnstr_set(x_127, 0, x_124);
lean::cnstr_set(x_127, 1, x_125);
return x_127;
}
}
}
else
{
uint8 x_128; 
lean::dec(x_6);
lean::dec(x_1);
x_128 = !lean::is_exclusive(x_71);
if (x_128 == 0)
{
return x_71;
}
else
{
obj* x_129; obj* x_130; obj* x_131; 
x_129 = lean::cnstr_get(x_71, 0);
x_130 = lean::cnstr_get(x_71, 1);
lean::inc(x_130);
lean::inc(x_129);
lean::dec(x_71);
x_131 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_131, 0, x_129);
lean::cnstr_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
obj* x_132; obj* x_133; uint32 x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; 
x_132 = lean::cnstr_get(x_63, 1);
lean::inc(x_132);
lean::dec(x_63);
x_133 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_133, 0, x_7);
lean::cnstr_set(x_133, 1, x_132);
x_134 = lean::cnstr_get_scalar<uint32>(x_1, sizeof(void*)*4);
x_135 = lean::uint32_to_nat(x_134);
x_136 = l_Nat_repr(x_135);
x_137 = l_Lean_Environment_displayStats___closed__8;
x_138 = lean::string_append(x_137, x_136);
lean::dec(x_136);
x_139 = l_IO_println___at_HasRepr_HasEval___spec__1(x_138, x_133);
lean::dec(x_138);
if (lean::obj_tag(x_139) == 0)
{
obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; 
x_140 = lean::cnstr_get(x_139, 1);
lean::inc(x_140);
if (lean::is_exclusive(x_139)) {
 lean::cnstr_release(x_139, 0);
 lean::cnstr_release(x_139, 1);
 x_141 = x_139;
} else {
 lean::dec_ref(x_139);
 x_141 = lean::box(0);
}
if (lean::is_scalar(x_141)) {
 x_142 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_142 = x_141;
}
lean::cnstr_set(x_142, 0, x_7);
lean::cnstr_set(x_142, 1, x_140);
x_143 = lean::cnstr_get(x_1, 2);
lean::inc(x_143);
x_144 = lean::array_get_size(x_143);
lean::dec(x_143);
x_145 = l_Nat_repr(x_144);
x_146 = l_Lean_Environment_displayStats___closed__9;
x_147 = lean::string_append(x_146, x_145);
lean::dec(x_145);
x_148 = l_IO_println___at_HasRepr_HasEval___spec__1(x_147, x_142);
lean::dec(x_147);
if (lean::obj_tag(x_148) == 0)
{
obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
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
lean::cnstr_set(x_151, 0, x_7);
lean::cnstr_set(x_151, 1, x_149);
x_152 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9(x_1, x_6, x_9, x_151);
lean::dec(x_6);
lean::dec(x_1);
if (lean::obj_tag(x_152) == 0)
{
obj* x_153; obj* x_154; obj* x_155; 
x_153 = lean::cnstr_get(x_152, 1);
lean::inc(x_153);
if (lean::is_exclusive(x_152)) {
 lean::cnstr_release(x_152, 0);
 lean::cnstr_release(x_152, 1);
 x_154 = x_152;
} else {
 lean::dec_ref(x_152);
 x_154 = lean::box(0);
}
if (lean::is_scalar(x_154)) {
 x_155 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_155 = x_154;
}
lean::cnstr_set(x_155, 0, x_7);
lean::cnstr_set(x_155, 1, x_153);
return x_155;
}
else
{
obj* x_156; obj* x_157; obj* x_158; obj* x_159; 
x_156 = lean::cnstr_get(x_152, 0);
lean::inc(x_156);
x_157 = lean::cnstr_get(x_152, 1);
lean::inc(x_157);
if (lean::is_exclusive(x_152)) {
 lean::cnstr_release(x_152, 0);
 lean::cnstr_release(x_152, 1);
 x_158 = x_152;
} else {
 lean::dec_ref(x_152);
 x_158 = lean::box(0);
}
if (lean::is_scalar(x_158)) {
 x_159 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_159 = x_158;
}
lean::cnstr_set(x_159, 0, x_156);
lean::cnstr_set(x_159, 1, x_157);
return x_159;
}
}
else
{
obj* x_160; obj* x_161; obj* x_162; obj* x_163; 
lean::dec(x_6);
lean::dec(x_1);
x_160 = lean::cnstr_get(x_148, 0);
lean::inc(x_160);
x_161 = lean::cnstr_get(x_148, 1);
lean::inc(x_161);
if (lean::is_exclusive(x_148)) {
 lean::cnstr_release(x_148, 0);
 lean::cnstr_release(x_148, 1);
 x_162 = x_148;
} else {
 lean::dec_ref(x_148);
 x_162 = lean::box(0);
}
if (lean::is_scalar(x_162)) {
 x_163 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_163 = x_162;
}
lean::cnstr_set(x_163, 0, x_160);
lean::cnstr_set(x_163, 1, x_161);
return x_163;
}
}
else
{
obj* x_164; obj* x_165; obj* x_166; obj* x_167; 
lean::dec(x_6);
lean::dec(x_1);
x_164 = lean::cnstr_get(x_139, 0);
lean::inc(x_164);
x_165 = lean::cnstr_get(x_139, 1);
lean::inc(x_165);
if (lean::is_exclusive(x_139)) {
 lean::cnstr_release(x_139, 0);
 lean::cnstr_release(x_139, 1);
 x_166 = x_139;
} else {
 lean::dec_ref(x_139);
 x_166 = lean::box(0);
}
if (lean::is_scalar(x_166)) {
 x_167 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_167 = x_166;
}
lean::cnstr_set(x_167, 0, x_164);
lean::cnstr_set(x_167, 1, x_165);
return x_167;
}
}
}
else
{
uint8 x_168; 
lean::dec(x_6);
lean::dec(x_1);
x_168 = !lean::is_exclusive(x_63);
if (x_168 == 0)
{
return x_63;
}
else
{
obj* x_169; obj* x_170; obj* x_171; 
x_169 = lean::cnstr_get(x_63, 0);
x_170 = lean::cnstr_get(x_63, 1);
lean::inc(x_170);
lean::inc(x_169);
lean::dec(x_63);
x_171 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_171, 0, x_169);
lean::cnstr_set(x_171, 1, x_170);
return x_171;
}
}
}
else
{
obj* x_172; obj* x_173; obj* x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; 
x_172 = lean::cnstr_get(x_56, 1);
lean::inc(x_172);
lean::dec(x_56);
x_173 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_173, 0, x_7);
lean::cnstr_set(x_173, 1, x_172);
x_174 = l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(x_29);
lean::dec(x_29);
x_175 = l_Nat_repr(x_174);
x_176 = l_Lean_Environment_displayStats___closed__7;
x_177 = lean::string_append(x_176, x_175);
lean::dec(x_175);
x_178 = l_IO_println___at_HasRepr_HasEval___spec__1(x_177, x_173);
lean::dec(x_177);
if (lean::obj_tag(x_178) == 0)
{
obj* x_179; obj* x_180; obj* x_181; uint32 x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; 
x_179 = lean::cnstr_get(x_178, 1);
lean::inc(x_179);
if (lean::is_exclusive(x_178)) {
 lean::cnstr_release(x_178, 0);
 lean::cnstr_release(x_178, 1);
 x_180 = x_178;
} else {
 lean::dec_ref(x_178);
 x_180 = lean::box(0);
}
if (lean::is_scalar(x_180)) {
 x_181 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_181 = x_180;
}
lean::cnstr_set(x_181, 0, x_7);
lean::cnstr_set(x_181, 1, x_179);
x_182 = lean::cnstr_get_scalar<uint32>(x_1, sizeof(void*)*4);
x_183 = lean::uint32_to_nat(x_182);
x_184 = l_Nat_repr(x_183);
x_185 = l_Lean_Environment_displayStats___closed__8;
x_186 = lean::string_append(x_185, x_184);
lean::dec(x_184);
x_187 = l_IO_println___at_HasRepr_HasEval___spec__1(x_186, x_181);
lean::dec(x_186);
if (lean::obj_tag(x_187) == 0)
{
obj* x_188; obj* x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; obj* x_196; 
x_188 = lean::cnstr_get(x_187, 1);
lean::inc(x_188);
if (lean::is_exclusive(x_187)) {
 lean::cnstr_release(x_187, 0);
 lean::cnstr_release(x_187, 1);
 x_189 = x_187;
} else {
 lean::dec_ref(x_187);
 x_189 = lean::box(0);
}
if (lean::is_scalar(x_189)) {
 x_190 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_190 = x_189;
}
lean::cnstr_set(x_190, 0, x_7);
lean::cnstr_set(x_190, 1, x_188);
x_191 = lean::cnstr_get(x_1, 2);
lean::inc(x_191);
x_192 = lean::array_get_size(x_191);
lean::dec(x_191);
x_193 = l_Nat_repr(x_192);
x_194 = l_Lean_Environment_displayStats___closed__9;
x_195 = lean::string_append(x_194, x_193);
lean::dec(x_193);
x_196 = l_IO_println___at_HasRepr_HasEval___spec__1(x_195, x_190);
lean::dec(x_195);
if (lean::obj_tag(x_196) == 0)
{
obj* x_197; obj* x_198; obj* x_199; obj* x_200; 
x_197 = lean::cnstr_get(x_196, 1);
lean::inc(x_197);
if (lean::is_exclusive(x_196)) {
 lean::cnstr_release(x_196, 0);
 lean::cnstr_release(x_196, 1);
 x_198 = x_196;
} else {
 lean::dec_ref(x_196);
 x_198 = lean::box(0);
}
if (lean::is_scalar(x_198)) {
 x_199 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_199 = x_198;
}
lean::cnstr_set(x_199, 0, x_7);
lean::cnstr_set(x_199, 1, x_197);
x_200 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9(x_1, x_6, x_9, x_199);
lean::dec(x_6);
lean::dec(x_1);
if (lean::obj_tag(x_200) == 0)
{
obj* x_201; obj* x_202; obj* x_203; 
x_201 = lean::cnstr_get(x_200, 1);
lean::inc(x_201);
if (lean::is_exclusive(x_200)) {
 lean::cnstr_release(x_200, 0);
 lean::cnstr_release(x_200, 1);
 x_202 = x_200;
} else {
 lean::dec_ref(x_200);
 x_202 = lean::box(0);
}
if (lean::is_scalar(x_202)) {
 x_203 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_203 = x_202;
}
lean::cnstr_set(x_203, 0, x_7);
lean::cnstr_set(x_203, 1, x_201);
return x_203;
}
else
{
obj* x_204; obj* x_205; obj* x_206; obj* x_207; 
x_204 = lean::cnstr_get(x_200, 0);
lean::inc(x_204);
x_205 = lean::cnstr_get(x_200, 1);
lean::inc(x_205);
if (lean::is_exclusive(x_200)) {
 lean::cnstr_release(x_200, 0);
 lean::cnstr_release(x_200, 1);
 x_206 = x_200;
} else {
 lean::dec_ref(x_200);
 x_206 = lean::box(0);
}
if (lean::is_scalar(x_206)) {
 x_207 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_207 = x_206;
}
lean::cnstr_set(x_207, 0, x_204);
lean::cnstr_set(x_207, 1, x_205);
return x_207;
}
}
else
{
obj* x_208; obj* x_209; obj* x_210; obj* x_211; 
lean::dec(x_6);
lean::dec(x_1);
x_208 = lean::cnstr_get(x_196, 0);
lean::inc(x_208);
x_209 = lean::cnstr_get(x_196, 1);
lean::inc(x_209);
if (lean::is_exclusive(x_196)) {
 lean::cnstr_release(x_196, 0);
 lean::cnstr_release(x_196, 1);
 x_210 = x_196;
} else {
 lean::dec_ref(x_196);
 x_210 = lean::box(0);
}
if (lean::is_scalar(x_210)) {
 x_211 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_211 = x_210;
}
lean::cnstr_set(x_211, 0, x_208);
lean::cnstr_set(x_211, 1, x_209);
return x_211;
}
}
else
{
obj* x_212; obj* x_213; obj* x_214; obj* x_215; 
lean::dec(x_6);
lean::dec(x_1);
x_212 = lean::cnstr_get(x_187, 0);
lean::inc(x_212);
x_213 = lean::cnstr_get(x_187, 1);
lean::inc(x_213);
if (lean::is_exclusive(x_187)) {
 lean::cnstr_release(x_187, 0);
 lean::cnstr_release(x_187, 1);
 x_214 = x_187;
} else {
 lean::dec_ref(x_187);
 x_214 = lean::box(0);
}
if (lean::is_scalar(x_214)) {
 x_215 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_215 = x_214;
}
lean::cnstr_set(x_215, 0, x_212);
lean::cnstr_set(x_215, 1, x_213);
return x_215;
}
}
else
{
obj* x_216; obj* x_217; obj* x_218; obj* x_219; 
lean::dec(x_6);
lean::dec(x_1);
x_216 = lean::cnstr_get(x_178, 0);
lean::inc(x_216);
x_217 = lean::cnstr_get(x_178, 1);
lean::inc(x_217);
if (lean::is_exclusive(x_178)) {
 lean::cnstr_release(x_178, 0);
 lean::cnstr_release(x_178, 1);
 x_218 = x_178;
} else {
 lean::dec_ref(x_178);
 x_218 = lean::box(0);
}
if (lean::is_scalar(x_218)) {
 x_219 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_219 = x_218;
}
lean::cnstr_set(x_219, 0, x_216);
lean::cnstr_set(x_219, 1, x_217);
return x_219;
}
}
}
else
{
uint8 x_220; 
lean::dec(x_29);
lean::dec(x_6);
lean::dec(x_1);
x_220 = !lean::is_exclusive(x_56);
if (x_220 == 0)
{
return x_56;
}
else
{
obj* x_221; obj* x_222; obj* x_223; 
x_221 = lean::cnstr_get(x_56, 0);
x_222 = lean::cnstr_get(x_56, 1);
lean::inc(x_222);
lean::inc(x_221);
lean::dec(x_56);
x_223 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_223, 0, x_221);
lean::cnstr_set(x_223, 1, x_222);
return x_223;
}
}
}
else
{
obj* x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; obj* x_229; obj* x_230; 
x_224 = lean::cnstr_get(x_49, 1);
lean::inc(x_224);
lean::dec(x_49);
x_225 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_225, 0, x_7);
lean::cnstr_set(x_225, 1, x_224);
x_226 = l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(x_29);
x_227 = l_Nat_repr(x_226);
x_228 = l_Lean_Environment_displayStats___closed__6;
x_229 = lean::string_append(x_228, x_227);
lean::dec(x_227);
x_230 = l_IO_println___at_HasRepr_HasEval___spec__1(x_229, x_225);
lean::dec(x_229);
if (lean::obj_tag(x_230) == 0)
{
obj* x_231; obj* x_232; obj* x_233; obj* x_234; obj* x_235; obj* x_236; obj* x_237; obj* x_238; 
x_231 = lean::cnstr_get(x_230, 1);
lean::inc(x_231);
if (lean::is_exclusive(x_230)) {
 lean::cnstr_release(x_230, 0);
 lean::cnstr_release(x_230, 1);
 x_232 = x_230;
} else {
 lean::dec_ref(x_230);
 x_232 = lean::box(0);
}
if (lean::is_scalar(x_232)) {
 x_233 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_233 = x_232;
}
lean::cnstr_set(x_233, 0, x_7);
lean::cnstr_set(x_233, 1, x_231);
x_234 = l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(x_29);
lean::dec(x_29);
x_235 = l_Nat_repr(x_234);
x_236 = l_Lean_Environment_displayStats___closed__7;
x_237 = lean::string_append(x_236, x_235);
lean::dec(x_235);
x_238 = l_IO_println___at_HasRepr_HasEval___spec__1(x_237, x_233);
lean::dec(x_237);
if (lean::obj_tag(x_238) == 0)
{
obj* x_239; obj* x_240; obj* x_241; uint32 x_242; obj* x_243; obj* x_244; obj* x_245; obj* x_246; obj* x_247; 
x_239 = lean::cnstr_get(x_238, 1);
lean::inc(x_239);
if (lean::is_exclusive(x_238)) {
 lean::cnstr_release(x_238, 0);
 lean::cnstr_release(x_238, 1);
 x_240 = x_238;
} else {
 lean::dec_ref(x_238);
 x_240 = lean::box(0);
}
if (lean::is_scalar(x_240)) {
 x_241 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_241 = x_240;
}
lean::cnstr_set(x_241, 0, x_7);
lean::cnstr_set(x_241, 1, x_239);
x_242 = lean::cnstr_get_scalar<uint32>(x_1, sizeof(void*)*4);
x_243 = lean::uint32_to_nat(x_242);
x_244 = l_Nat_repr(x_243);
x_245 = l_Lean_Environment_displayStats___closed__8;
x_246 = lean::string_append(x_245, x_244);
lean::dec(x_244);
x_247 = l_IO_println___at_HasRepr_HasEval___spec__1(x_246, x_241);
lean::dec(x_246);
if (lean::obj_tag(x_247) == 0)
{
obj* x_248; obj* x_249; obj* x_250; obj* x_251; obj* x_252; obj* x_253; obj* x_254; obj* x_255; obj* x_256; 
x_248 = lean::cnstr_get(x_247, 1);
lean::inc(x_248);
if (lean::is_exclusive(x_247)) {
 lean::cnstr_release(x_247, 0);
 lean::cnstr_release(x_247, 1);
 x_249 = x_247;
} else {
 lean::dec_ref(x_247);
 x_249 = lean::box(0);
}
if (lean::is_scalar(x_249)) {
 x_250 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_250 = x_249;
}
lean::cnstr_set(x_250, 0, x_7);
lean::cnstr_set(x_250, 1, x_248);
x_251 = lean::cnstr_get(x_1, 2);
lean::inc(x_251);
x_252 = lean::array_get_size(x_251);
lean::dec(x_251);
x_253 = l_Nat_repr(x_252);
x_254 = l_Lean_Environment_displayStats___closed__9;
x_255 = lean::string_append(x_254, x_253);
lean::dec(x_253);
x_256 = l_IO_println___at_HasRepr_HasEval___spec__1(x_255, x_250);
lean::dec(x_255);
if (lean::obj_tag(x_256) == 0)
{
obj* x_257; obj* x_258; obj* x_259; obj* x_260; 
x_257 = lean::cnstr_get(x_256, 1);
lean::inc(x_257);
if (lean::is_exclusive(x_256)) {
 lean::cnstr_release(x_256, 0);
 lean::cnstr_release(x_256, 1);
 x_258 = x_256;
} else {
 lean::dec_ref(x_256);
 x_258 = lean::box(0);
}
if (lean::is_scalar(x_258)) {
 x_259 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_259 = x_258;
}
lean::cnstr_set(x_259, 0, x_7);
lean::cnstr_set(x_259, 1, x_257);
x_260 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9(x_1, x_6, x_9, x_259);
lean::dec(x_6);
lean::dec(x_1);
if (lean::obj_tag(x_260) == 0)
{
obj* x_261; obj* x_262; obj* x_263; 
x_261 = lean::cnstr_get(x_260, 1);
lean::inc(x_261);
if (lean::is_exclusive(x_260)) {
 lean::cnstr_release(x_260, 0);
 lean::cnstr_release(x_260, 1);
 x_262 = x_260;
} else {
 lean::dec_ref(x_260);
 x_262 = lean::box(0);
}
if (lean::is_scalar(x_262)) {
 x_263 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_263 = x_262;
}
lean::cnstr_set(x_263, 0, x_7);
lean::cnstr_set(x_263, 1, x_261);
return x_263;
}
else
{
obj* x_264; obj* x_265; obj* x_266; obj* x_267; 
x_264 = lean::cnstr_get(x_260, 0);
lean::inc(x_264);
x_265 = lean::cnstr_get(x_260, 1);
lean::inc(x_265);
if (lean::is_exclusive(x_260)) {
 lean::cnstr_release(x_260, 0);
 lean::cnstr_release(x_260, 1);
 x_266 = x_260;
} else {
 lean::dec_ref(x_260);
 x_266 = lean::box(0);
}
if (lean::is_scalar(x_266)) {
 x_267 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_267 = x_266;
}
lean::cnstr_set(x_267, 0, x_264);
lean::cnstr_set(x_267, 1, x_265);
return x_267;
}
}
else
{
obj* x_268; obj* x_269; obj* x_270; obj* x_271; 
lean::dec(x_6);
lean::dec(x_1);
x_268 = lean::cnstr_get(x_256, 0);
lean::inc(x_268);
x_269 = lean::cnstr_get(x_256, 1);
lean::inc(x_269);
if (lean::is_exclusive(x_256)) {
 lean::cnstr_release(x_256, 0);
 lean::cnstr_release(x_256, 1);
 x_270 = x_256;
} else {
 lean::dec_ref(x_256);
 x_270 = lean::box(0);
}
if (lean::is_scalar(x_270)) {
 x_271 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_271 = x_270;
}
lean::cnstr_set(x_271, 0, x_268);
lean::cnstr_set(x_271, 1, x_269);
return x_271;
}
}
else
{
obj* x_272; obj* x_273; obj* x_274; obj* x_275; 
lean::dec(x_6);
lean::dec(x_1);
x_272 = lean::cnstr_get(x_247, 0);
lean::inc(x_272);
x_273 = lean::cnstr_get(x_247, 1);
lean::inc(x_273);
if (lean::is_exclusive(x_247)) {
 lean::cnstr_release(x_247, 0);
 lean::cnstr_release(x_247, 1);
 x_274 = x_247;
} else {
 lean::dec_ref(x_247);
 x_274 = lean::box(0);
}
if (lean::is_scalar(x_274)) {
 x_275 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_275 = x_274;
}
lean::cnstr_set(x_275, 0, x_272);
lean::cnstr_set(x_275, 1, x_273);
return x_275;
}
}
else
{
obj* x_276; obj* x_277; obj* x_278; obj* x_279; 
lean::dec(x_6);
lean::dec(x_1);
x_276 = lean::cnstr_get(x_238, 0);
lean::inc(x_276);
x_277 = lean::cnstr_get(x_238, 1);
lean::inc(x_277);
if (lean::is_exclusive(x_238)) {
 lean::cnstr_release(x_238, 0);
 lean::cnstr_release(x_238, 1);
 x_278 = x_238;
} else {
 lean::dec_ref(x_238);
 x_278 = lean::box(0);
}
if (lean::is_scalar(x_278)) {
 x_279 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_279 = x_278;
}
lean::cnstr_set(x_279, 0, x_276);
lean::cnstr_set(x_279, 1, x_277);
return x_279;
}
}
else
{
obj* x_280; obj* x_281; obj* x_282; obj* x_283; 
lean::dec(x_29);
lean::dec(x_6);
lean::dec(x_1);
x_280 = lean::cnstr_get(x_230, 0);
lean::inc(x_280);
x_281 = lean::cnstr_get(x_230, 1);
lean::inc(x_281);
if (lean::is_exclusive(x_230)) {
 lean::cnstr_release(x_230, 0);
 lean::cnstr_release(x_230, 1);
 x_282 = x_230;
} else {
 lean::dec_ref(x_230);
 x_282 = lean::box(0);
}
if (lean::is_scalar(x_282)) {
 x_283 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_283 = x_282;
}
lean::cnstr_set(x_283, 0, x_280);
lean::cnstr_set(x_283, 1, x_281);
return x_283;
}
}
}
else
{
uint8 x_284; 
lean::dec(x_29);
lean::dec(x_6);
lean::dec(x_1);
x_284 = !lean::is_exclusive(x_49);
if (x_284 == 0)
{
return x_49;
}
else
{
obj* x_285; obj* x_286; obj* x_287; 
x_285 = lean::cnstr_get(x_49, 0);
x_286 = lean::cnstr_get(x_49, 1);
lean::inc(x_286);
lean::inc(x_285);
lean::dec(x_49);
x_287 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_287, 0, x_285);
lean::cnstr_set(x_287, 1, x_286);
return x_287;
}
}
}
else
{
obj* x_288; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; obj* x_294; 
x_288 = lean::cnstr_get(x_42, 1);
lean::inc(x_288);
lean::dec(x_42);
x_289 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_289, 0, x_7);
lean::cnstr_set(x_289, 1, x_288);
x_290 = lean::cnstr_get(x_37, 1);
lean::inc(x_290);
lean::dec(x_37);
x_291 = l_Nat_repr(x_290);
x_292 = l_Lean_Environment_displayStats___closed__5;
x_293 = lean::string_append(x_292, x_291);
lean::dec(x_291);
x_294 = l_IO_println___at_HasRepr_HasEval___spec__1(x_293, x_289);
lean::dec(x_293);
if (lean::obj_tag(x_294) == 0)
{
obj* x_295; obj* x_296; obj* x_297; obj* x_298; obj* x_299; obj* x_300; obj* x_301; obj* x_302; 
x_295 = lean::cnstr_get(x_294, 1);
lean::inc(x_295);
if (lean::is_exclusive(x_294)) {
 lean::cnstr_release(x_294, 0);
 lean::cnstr_release(x_294, 1);
 x_296 = x_294;
} else {
 lean::dec_ref(x_294);
 x_296 = lean::box(0);
}
if (lean::is_scalar(x_296)) {
 x_297 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_297 = x_296;
}
lean::cnstr_set(x_297, 0, x_7);
lean::cnstr_set(x_297, 1, x_295);
x_298 = l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(x_29);
x_299 = l_Nat_repr(x_298);
x_300 = l_Lean_Environment_displayStats___closed__6;
x_301 = lean::string_append(x_300, x_299);
lean::dec(x_299);
x_302 = l_IO_println___at_HasRepr_HasEval___spec__1(x_301, x_297);
lean::dec(x_301);
if (lean::obj_tag(x_302) == 0)
{
obj* x_303; obj* x_304; obj* x_305; obj* x_306; obj* x_307; obj* x_308; obj* x_309; obj* x_310; 
x_303 = lean::cnstr_get(x_302, 1);
lean::inc(x_303);
if (lean::is_exclusive(x_302)) {
 lean::cnstr_release(x_302, 0);
 lean::cnstr_release(x_302, 1);
 x_304 = x_302;
} else {
 lean::dec_ref(x_302);
 x_304 = lean::box(0);
}
if (lean::is_scalar(x_304)) {
 x_305 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_305 = x_304;
}
lean::cnstr_set(x_305, 0, x_7);
lean::cnstr_set(x_305, 1, x_303);
x_306 = l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(x_29);
lean::dec(x_29);
x_307 = l_Nat_repr(x_306);
x_308 = l_Lean_Environment_displayStats___closed__7;
x_309 = lean::string_append(x_308, x_307);
lean::dec(x_307);
x_310 = l_IO_println___at_HasRepr_HasEval___spec__1(x_309, x_305);
lean::dec(x_309);
if (lean::obj_tag(x_310) == 0)
{
obj* x_311; obj* x_312; obj* x_313; uint32 x_314; obj* x_315; obj* x_316; obj* x_317; obj* x_318; obj* x_319; 
x_311 = lean::cnstr_get(x_310, 1);
lean::inc(x_311);
if (lean::is_exclusive(x_310)) {
 lean::cnstr_release(x_310, 0);
 lean::cnstr_release(x_310, 1);
 x_312 = x_310;
} else {
 lean::dec_ref(x_310);
 x_312 = lean::box(0);
}
if (lean::is_scalar(x_312)) {
 x_313 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_313 = x_312;
}
lean::cnstr_set(x_313, 0, x_7);
lean::cnstr_set(x_313, 1, x_311);
x_314 = lean::cnstr_get_scalar<uint32>(x_1, sizeof(void*)*4);
x_315 = lean::uint32_to_nat(x_314);
x_316 = l_Nat_repr(x_315);
x_317 = l_Lean_Environment_displayStats___closed__8;
x_318 = lean::string_append(x_317, x_316);
lean::dec(x_316);
x_319 = l_IO_println___at_HasRepr_HasEval___spec__1(x_318, x_313);
lean::dec(x_318);
if (lean::obj_tag(x_319) == 0)
{
obj* x_320; obj* x_321; obj* x_322; obj* x_323; obj* x_324; obj* x_325; obj* x_326; obj* x_327; obj* x_328; 
x_320 = lean::cnstr_get(x_319, 1);
lean::inc(x_320);
if (lean::is_exclusive(x_319)) {
 lean::cnstr_release(x_319, 0);
 lean::cnstr_release(x_319, 1);
 x_321 = x_319;
} else {
 lean::dec_ref(x_319);
 x_321 = lean::box(0);
}
if (lean::is_scalar(x_321)) {
 x_322 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_322 = x_321;
}
lean::cnstr_set(x_322, 0, x_7);
lean::cnstr_set(x_322, 1, x_320);
x_323 = lean::cnstr_get(x_1, 2);
lean::inc(x_323);
x_324 = lean::array_get_size(x_323);
lean::dec(x_323);
x_325 = l_Nat_repr(x_324);
x_326 = l_Lean_Environment_displayStats___closed__9;
x_327 = lean::string_append(x_326, x_325);
lean::dec(x_325);
x_328 = l_IO_println___at_HasRepr_HasEval___spec__1(x_327, x_322);
lean::dec(x_327);
if (lean::obj_tag(x_328) == 0)
{
obj* x_329; obj* x_330; obj* x_331; obj* x_332; 
x_329 = lean::cnstr_get(x_328, 1);
lean::inc(x_329);
if (lean::is_exclusive(x_328)) {
 lean::cnstr_release(x_328, 0);
 lean::cnstr_release(x_328, 1);
 x_330 = x_328;
} else {
 lean::dec_ref(x_328);
 x_330 = lean::box(0);
}
if (lean::is_scalar(x_330)) {
 x_331 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_331 = x_330;
}
lean::cnstr_set(x_331, 0, x_7);
lean::cnstr_set(x_331, 1, x_329);
x_332 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9(x_1, x_6, x_9, x_331);
lean::dec(x_6);
lean::dec(x_1);
if (lean::obj_tag(x_332) == 0)
{
obj* x_333; obj* x_334; obj* x_335; 
x_333 = lean::cnstr_get(x_332, 1);
lean::inc(x_333);
if (lean::is_exclusive(x_332)) {
 lean::cnstr_release(x_332, 0);
 lean::cnstr_release(x_332, 1);
 x_334 = x_332;
} else {
 lean::dec_ref(x_332);
 x_334 = lean::box(0);
}
if (lean::is_scalar(x_334)) {
 x_335 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_335 = x_334;
}
lean::cnstr_set(x_335, 0, x_7);
lean::cnstr_set(x_335, 1, x_333);
return x_335;
}
else
{
obj* x_336; obj* x_337; obj* x_338; obj* x_339; 
x_336 = lean::cnstr_get(x_332, 0);
lean::inc(x_336);
x_337 = lean::cnstr_get(x_332, 1);
lean::inc(x_337);
if (lean::is_exclusive(x_332)) {
 lean::cnstr_release(x_332, 0);
 lean::cnstr_release(x_332, 1);
 x_338 = x_332;
} else {
 lean::dec_ref(x_332);
 x_338 = lean::box(0);
}
if (lean::is_scalar(x_338)) {
 x_339 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_339 = x_338;
}
lean::cnstr_set(x_339, 0, x_336);
lean::cnstr_set(x_339, 1, x_337);
return x_339;
}
}
else
{
obj* x_340; obj* x_341; obj* x_342; obj* x_343; 
lean::dec(x_6);
lean::dec(x_1);
x_340 = lean::cnstr_get(x_328, 0);
lean::inc(x_340);
x_341 = lean::cnstr_get(x_328, 1);
lean::inc(x_341);
if (lean::is_exclusive(x_328)) {
 lean::cnstr_release(x_328, 0);
 lean::cnstr_release(x_328, 1);
 x_342 = x_328;
} else {
 lean::dec_ref(x_328);
 x_342 = lean::box(0);
}
if (lean::is_scalar(x_342)) {
 x_343 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_343 = x_342;
}
lean::cnstr_set(x_343, 0, x_340);
lean::cnstr_set(x_343, 1, x_341);
return x_343;
}
}
else
{
obj* x_344; obj* x_345; obj* x_346; obj* x_347; 
lean::dec(x_6);
lean::dec(x_1);
x_344 = lean::cnstr_get(x_319, 0);
lean::inc(x_344);
x_345 = lean::cnstr_get(x_319, 1);
lean::inc(x_345);
if (lean::is_exclusive(x_319)) {
 lean::cnstr_release(x_319, 0);
 lean::cnstr_release(x_319, 1);
 x_346 = x_319;
} else {
 lean::dec_ref(x_319);
 x_346 = lean::box(0);
}
if (lean::is_scalar(x_346)) {
 x_347 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_347 = x_346;
}
lean::cnstr_set(x_347, 0, x_344);
lean::cnstr_set(x_347, 1, x_345);
return x_347;
}
}
else
{
obj* x_348; obj* x_349; obj* x_350; obj* x_351; 
lean::dec(x_6);
lean::dec(x_1);
x_348 = lean::cnstr_get(x_310, 0);
lean::inc(x_348);
x_349 = lean::cnstr_get(x_310, 1);
lean::inc(x_349);
if (lean::is_exclusive(x_310)) {
 lean::cnstr_release(x_310, 0);
 lean::cnstr_release(x_310, 1);
 x_350 = x_310;
} else {
 lean::dec_ref(x_310);
 x_350 = lean::box(0);
}
if (lean::is_scalar(x_350)) {
 x_351 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_351 = x_350;
}
lean::cnstr_set(x_351, 0, x_348);
lean::cnstr_set(x_351, 1, x_349);
return x_351;
}
}
else
{
obj* x_352; obj* x_353; obj* x_354; obj* x_355; 
lean::dec(x_29);
lean::dec(x_6);
lean::dec(x_1);
x_352 = lean::cnstr_get(x_302, 0);
lean::inc(x_352);
x_353 = lean::cnstr_get(x_302, 1);
lean::inc(x_353);
if (lean::is_exclusive(x_302)) {
 lean::cnstr_release(x_302, 0);
 lean::cnstr_release(x_302, 1);
 x_354 = x_302;
} else {
 lean::dec_ref(x_302);
 x_354 = lean::box(0);
}
if (lean::is_scalar(x_354)) {
 x_355 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_355 = x_354;
}
lean::cnstr_set(x_355, 0, x_352);
lean::cnstr_set(x_355, 1, x_353);
return x_355;
}
}
else
{
obj* x_356; obj* x_357; obj* x_358; obj* x_359; 
lean::dec(x_29);
lean::dec(x_6);
lean::dec(x_1);
x_356 = lean::cnstr_get(x_294, 0);
lean::inc(x_356);
x_357 = lean::cnstr_get(x_294, 1);
lean::inc(x_357);
if (lean::is_exclusive(x_294)) {
 lean::cnstr_release(x_294, 0);
 lean::cnstr_release(x_294, 1);
 x_358 = x_294;
} else {
 lean::dec_ref(x_294);
 x_358 = lean::box(0);
}
if (lean::is_scalar(x_358)) {
 x_359 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_359 = x_358;
}
lean::cnstr_set(x_359, 0, x_356);
lean::cnstr_set(x_359, 1, x_357);
return x_359;
}
}
}
else
{
uint8 x_360; 
lean::dec(x_37);
lean::dec(x_29);
lean::dec(x_6);
lean::dec(x_1);
x_360 = !lean::is_exclusive(x_42);
if (x_360 == 0)
{
return x_42;
}
else
{
obj* x_361; obj* x_362; obj* x_363; 
x_361 = lean::cnstr_get(x_42, 0);
x_362 = lean::cnstr_get(x_42, 1);
lean::inc(x_362);
lean::inc(x_361);
lean::dec(x_42);
x_363 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_363, 0, x_361);
lean::cnstr_set(x_363, 1, x_362);
return x_363;
}
}
}
else
{
obj* x_364; obj* x_365; obj* x_366; obj* x_367; obj* x_368; obj* x_369; obj* x_370; obj* x_371; 
x_364 = lean::cnstr_get(x_34, 1);
lean::inc(x_364);
lean::dec(x_34);
x_365 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_365, 0, x_7);
lean::cnstr_set(x_365, 1, x_364);
x_366 = l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4(x_29);
x_367 = lean::cnstr_get(x_366, 0);
lean::inc(x_367);
x_368 = l_Nat_repr(x_367);
x_369 = l_Lean_Environment_displayStats___closed__4;
x_370 = lean::string_append(x_369, x_368);
lean::dec(x_368);
x_371 = l_IO_println___at_HasRepr_HasEval___spec__1(x_370, x_365);
lean::dec(x_370);
if (lean::obj_tag(x_371) == 0)
{
obj* x_372; obj* x_373; obj* x_374; obj* x_375; obj* x_376; obj* x_377; obj* x_378; obj* x_379; 
x_372 = lean::cnstr_get(x_371, 1);
lean::inc(x_372);
if (lean::is_exclusive(x_371)) {
 lean::cnstr_release(x_371, 0);
 lean::cnstr_release(x_371, 1);
 x_373 = x_371;
} else {
 lean::dec_ref(x_371);
 x_373 = lean::box(0);
}
if (lean::is_scalar(x_373)) {
 x_374 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_374 = x_373;
}
lean::cnstr_set(x_374, 0, x_7);
lean::cnstr_set(x_374, 1, x_372);
x_375 = lean::cnstr_get(x_366, 1);
lean::inc(x_375);
lean::dec(x_366);
x_376 = l_Nat_repr(x_375);
x_377 = l_Lean_Environment_displayStats___closed__5;
x_378 = lean::string_append(x_377, x_376);
lean::dec(x_376);
x_379 = l_IO_println___at_HasRepr_HasEval___spec__1(x_378, x_374);
lean::dec(x_378);
if (lean::obj_tag(x_379) == 0)
{
obj* x_380; obj* x_381; obj* x_382; obj* x_383; obj* x_384; obj* x_385; obj* x_386; obj* x_387; 
x_380 = lean::cnstr_get(x_379, 1);
lean::inc(x_380);
if (lean::is_exclusive(x_379)) {
 lean::cnstr_release(x_379, 0);
 lean::cnstr_release(x_379, 1);
 x_381 = x_379;
} else {
 lean::dec_ref(x_379);
 x_381 = lean::box(0);
}
if (lean::is_scalar(x_381)) {
 x_382 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_382 = x_381;
}
lean::cnstr_set(x_382, 0, x_7);
lean::cnstr_set(x_382, 1, x_380);
x_383 = l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(x_29);
x_384 = l_Nat_repr(x_383);
x_385 = l_Lean_Environment_displayStats___closed__6;
x_386 = lean::string_append(x_385, x_384);
lean::dec(x_384);
x_387 = l_IO_println___at_HasRepr_HasEval___spec__1(x_386, x_382);
lean::dec(x_386);
if (lean::obj_tag(x_387) == 0)
{
obj* x_388; obj* x_389; obj* x_390; obj* x_391; obj* x_392; obj* x_393; obj* x_394; obj* x_395; 
x_388 = lean::cnstr_get(x_387, 1);
lean::inc(x_388);
if (lean::is_exclusive(x_387)) {
 lean::cnstr_release(x_387, 0);
 lean::cnstr_release(x_387, 1);
 x_389 = x_387;
} else {
 lean::dec_ref(x_387);
 x_389 = lean::box(0);
}
if (lean::is_scalar(x_389)) {
 x_390 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_390 = x_389;
}
lean::cnstr_set(x_390, 0, x_7);
lean::cnstr_set(x_390, 1, x_388);
x_391 = l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(x_29);
lean::dec(x_29);
x_392 = l_Nat_repr(x_391);
x_393 = l_Lean_Environment_displayStats___closed__7;
x_394 = lean::string_append(x_393, x_392);
lean::dec(x_392);
x_395 = l_IO_println___at_HasRepr_HasEval___spec__1(x_394, x_390);
lean::dec(x_394);
if (lean::obj_tag(x_395) == 0)
{
obj* x_396; obj* x_397; obj* x_398; uint32 x_399; obj* x_400; obj* x_401; obj* x_402; obj* x_403; obj* x_404; 
x_396 = lean::cnstr_get(x_395, 1);
lean::inc(x_396);
if (lean::is_exclusive(x_395)) {
 lean::cnstr_release(x_395, 0);
 lean::cnstr_release(x_395, 1);
 x_397 = x_395;
} else {
 lean::dec_ref(x_395);
 x_397 = lean::box(0);
}
if (lean::is_scalar(x_397)) {
 x_398 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_398 = x_397;
}
lean::cnstr_set(x_398, 0, x_7);
lean::cnstr_set(x_398, 1, x_396);
x_399 = lean::cnstr_get_scalar<uint32>(x_1, sizeof(void*)*4);
x_400 = lean::uint32_to_nat(x_399);
x_401 = l_Nat_repr(x_400);
x_402 = l_Lean_Environment_displayStats___closed__8;
x_403 = lean::string_append(x_402, x_401);
lean::dec(x_401);
x_404 = l_IO_println___at_HasRepr_HasEval___spec__1(x_403, x_398);
lean::dec(x_403);
if (lean::obj_tag(x_404) == 0)
{
obj* x_405; obj* x_406; obj* x_407; obj* x_408; obj* x_409; obj* x_410; obj* x_411; obj* x_412; obj* x_413; 
x_405 = lean::cnstr_get(x_404, 1);
lean::inc(x_405);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 x_406 = x_404;
} else {
 lean::dec_ref(x_404);
 x_406 = lean::box(0);
}
if (lean::is_scalar(x_406)) {
 x_407 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_407 = x_406;
}
lean::cnstr_set(x_407, 0, x_7);
lean::cnstr_set(x_407, 1, x_405);
x_408 = lean::cnstr_get(x_1, 2);
lean::inc(x_408);
x_409 = lean::array_get_size(x_408);
lean::dec(x_408);
x_410 = l_Nat_repr(x_409);
x_411 = l_Lean_Environment_displayStats___closed__9;
x_412 = lean::string_append(x_411, x_410);
lean::dec(x_410);
x_413 = l_IO_println___at_HasRepr_HasEval___spec__1(x_412, x_407);
lean::dec(x_412);
if (lean::obj_tag(x_413) == 0)
{
obj* x_414; obj* x_415; obj* x_416; obj* x_417; 
x_414 = lean::cnstr_get(x_413, 1);
lean::inc(x_414);
if (lean::is_exclusive(x_413)) {
 lean::cnstr_release(x_413, 0);
 lean::cnstr_release(x_413, 1);
 x_415 = x_413;
} else {
 lean::dec_ref(x_413);
 x_415 = lean::box(0);
}
if (lean::is_scalar(x_415)) {
 x_416 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_416 = x_415;
}
lean::cnstr_set(x_416, 0, x_7);
lean::cnstr_set(x_416, 1, x_414);
x_417 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9(x_1, x_6, x_9, x_416);
lean::dec(x_6);
lean::dec(x_1);
if (lean::obj_tag(x_417) == 0)
{
obj* x_418; obj* x_419; obj* x_420; 
x_418 = lean::cnstr_get(x_417, 1);
lean::inc(x_418);
if (lean::is_exclusive(x_417)) {
 lean::cnstr_release(x_417, 0);
 lean::cnstr_release(x_417, 1);
 x_419 = x_417;
} else {
 lean::dec_ref(x_417);
 x_419 = lean::box(0);
}
if (lean::is_scalar(x_419)) {
 x_420 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_420 = x_419;
}
lean::cnstr_set(x_420, 0, x_7);
lean::cnstr_set(x_420, 1, x_418);
return x_420;
}
else
{
obj* x_421; obj* x_422; obj* x_423; obj* x_424; 
x_421 = lean::cnstr_get(x_417, 0);
lean::inc(x_421);
x_422 = lean::cnstr_get(x_417, 1);
lean::inc(x_422);
if (lean::is_exclusive(x_417)) {
 lean::cnstr_release(x_417, 0);
 lean::cnstr_release(x_417, 1);
 x_423 = x_417;
} else {
 lean::dec_ref(x_417);
 x_423 = lean::box(0);
}
if (lean::is_scalar(x_423)) {
 x_424 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_424 = x_423;
}
lean::cnstr_set(x_424, 0, x_421);
lean::cnstr_set(x_424, 1, x_422);
return x_424;
}
}
else
{
obj* x_425; obj* x_426; obj* x_427; obj* x_428; 
lean::dec(x_6);
lean::dec(x_1);
x_425 = lean::cnstr_get(x_413, 0);
lean::inc(x_425);
x_426 = lean::cnstr_get(x_413, 1);
lean::inc(x_426);
if (lean::is_exclusive(x_413)) {
 lean::cnstr_release(x_413, 0);
 lean::cnstr_release(x_413, 1);
 x_427 = x_413;
} else {
 lean::dec_ref(x_413);
 x_427 = lean::box(0);
}
if (lean::is_scalar(x_427)) {
 x_428 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_428 = x_427;
}
lean::cnstr_set(x_428, 0, x_425);
lean::cnstr_set(x_428, 1, x_426);
return x_428;
}
}
else
{
obj* x_429; obj* x_430; obj* x_431; obj* x_432; 
lean::dec(x_6);
lean::dec(x_1);
x_429 = lean::cnstr_get(x_404, 0);
lean::inc(x_429);
x_430 = lean::cnstr_get(x_404, 1);
lean::inc(x_430);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 x_431 = x_404;
} else {
 lean::dec_ref(x_404);
 x_431 = lean::box(0);
}
if (lean::is_scalar(x_431)) {
 x_432 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_432 = x_431;
}
lean::cnstr_set(x_432, 0, x_429);
lean::cnstr_set(x_432, 1, x_430);
return x_432;
}
}
else
{
obj* x_433; obj* x_434; obj* x_435; obj* x_436; 
lean::dec(x_6);
lean::dec(x_1);
x_433 = lean::cnstr_get(x_395, 0);
lean::inc(x_433);
x_434 = lean::cnstr_get(x_395, 1);
lean::inc(x_434);
if (lean::is_exclusive(x_395)) {
 lean::cnstr_release(x_395, 0);
 lean::cnstr_release(x_395, 1);
 x_435 = x_395;
} else {
 lean::dec_ref(x_395);
 x_435 = lean::box(0);
}
if (lean::is_scalar(x_435)) {
 x_436 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_436 = x_435;
}
lean::cnstr_set(x_436, 0, x_433);
lean::cnstr_set(x_436, 1, x_434);
return x_436;
}
}
else
{
obj* x_437; obj* x_438; obj* x_439; obj* x_440; 
lean::dec(x_29);
lean::dec(x_6);
lean::dec(x_1);
x_437 = lean::cnstr_get(x_387, 0);
lean::inc(x_437);
x_438 = lean::cnstr_get(x_387, 1);
lean::inc(x_438);
if (lean::is_exclusive(x_387)) {
 lean::cnstr_release(x_387, 0);
 lean::cnstr_release(x_387, 1);
 x_439 = x_387;
} else {
 lean::dec_ref(x_387);
 x_439 = lean::box(0);
}
if (lean::is_scalar(x_439)) {
 x_440 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_440 = x_439;
}
lean::cnstr_set(x_440, 0, x_437);
lean::cnstr_set(x_440, 1, x_438);
return x_440;
}
}
else
{
obj* x_441; obj* x_442; obj* x_443; obj* x_444; 
lean::dec(x_29);
lean::dec(x_6);
lean::dec(x_1);
x_441 = lean::cnstr_get(x_379, 0);
lean::inc(x_441);
x_442 = lean::cnstr_get(x_379, 1);
lean::inc(x_442);
if (lean::is_exclusive(x_379)) {
 lean::cnstr_release(x_379, 0);
 lean::cnstr_release(x_379, 1);
 x_443 = x_379;
} else {
 lean::dec_ref(x_379);
 x_443 = lean::box(0);
}
if (lean::is_scalar(x_443)) {
 x_444 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_444 = x_443;
}
lean::cnstr_set(x_444, 0, x_441);
lean::cnstr_set(x_444, 1, x_442);
return x_444;
}
}
else
{
obj* x_445; obj* x_446; obj* x_447; obj* x_448; 
lean::dec(x_366);
lean::dec(x_29);
lean::dec(x_6);
lean::dec(x_1);
x_445 = lean::cnstr_get(x_371, 0);
lean::inc(x_445);
x_446 = lean::cnstr_get(x_371, 1);
lean::inc(x_446);
if (lean::is_exclusive(x_371)) {
 lean::cnstr_release(x_371, 0);
 lean::cnstr_release(x_371, 1);
 x_447 = x_371;
} else {
 lean::dec_ref(x_371);
 x_447 = lean::box(0);
}
if (lean::is_scalar(x_447)) {
 x_448 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_448 = x_447;
}
lean::cnstr_set(x_448, 0, x_445);
lean::cnstr_set(x_448, 1, x_446);
return x_448;
}
}
}
else
{
uint8 x_449; 
lean::dec(x_29);
lean::dec(x_6);
lean::dec(x_1);
x_449 = !lean::is_exclusive(x_34);
if (x_449 == 0)
{
return x_34;
}
else
{
obj* x_450; obj* x_451; obj* x_452; 
x_450 = lean::cnstr_get(x_34, 0);
x_451 = lean::cnstr_get(x_34, 1);
lean::inc(x_451);
lean::inc(x_450);
lean::dec(x_34);
x_452 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_452, 0, x_450);
lean::cnstr_set(x_452, 1, x_451);
return x_452;
}
}
}
else
{
obj* x_453; obj* x_454; obj* x_455; obj* x_456; obj* x_457; obj* x_458; obj* x_459; obj* x_460; 
x_453 = lean::cnstr_get(x_26, 1);
lean::inc(x_453);
lean::dec(x_26);
x_454 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_454, 0, x_7);
lean::cnstr_set(x_454, 1, x_453);
x_455 = lean::cnstr_get(x_1, 1);
lean::inc(x_455);
x_456 = l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3(x_455);
x_457 = l_Nat_repr(x_456);
x_458 = l_Lean_Environment_displayStats___closed__3;
x_459 = lean::string_append(x_458, x_457);
lean::dec(x_457);
x_460 = l_IO_println___at_HasRepr_HasEval___spec__1(x_459, x_454);
lean::dec(x_459);
if (lean::obj_tag(x_460) == 0)
{
obj* x_461; obj* x_462; obj* x_463; obj* x_464; obj* x_465; obj* x_466; obj* x_467; obj* x_468; obj* x_469; 
x_461 = lean::cnstr_get(x_460, 1);
lean::inc(x_461);
if (lean::is_exclusive(x_460)) {
 lean::cnstr_release(x_460, 0);
 lean::cnstr_release(x_460, 1);
 x_462 = x_460;
} else {
 lean::dec_ref(x_460);
 x_462 = lean::box(0);
}
if (lean::is_scalar(x_462)) {
 x_463 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_463 = x_462;
}
lean::cnstr_set(x_463, 0, x_7);
lean::cnstr_set(x_463, 1, x_461);
x_464 = l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4(x_455);
x_465 = lean::cnstr_get(x_464, 0);
lean::inc(x_465);
x_466 = l_Nat_repr(x_465);
x_467 = l_Lean_Environment_displayStats___closed__4;
x_468 = lean::string_append(x_467, x_466);
lean::dec(x_466);
x_469 = l_IO_println___at_HasRepr_HasEval___spec__1(x_468, x_463);
lean::dec(x_468);
if (lean::obj_tag(x_469) == 0)
{
obj* x_470; obj* x_471; obj* x_472; obj* x_473; obj* x_474; obj* x_475; obj* x_476; obj* x_477; 
x_470 = lean::cnstr_get(x_469, 1);
lean::inc(x_470);
if (lean::is_exclusive(x_469)) {
 lean::cnstr_release(x_469, 0);
 lean::cnstr_release(x_469, 1);
 x_471 = x_469;
} else {
 lean::dec_ref(x_469);
 x_471 = lean::box(0);
}
if (lean::is_scalar(x_471)) {
 x_472 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_472 = x_471;
}
lean::cnstr_set(x_472, 0, x_7);
lean::cnstr_set(x_472, 1, x_470);
x_473 = lean::cnstr_get(x_464, 1);
lean::inc(x_473);
lean::dec(x_464);
x_474 = l_Nat_repr(x_473);
x_475 = l_Lean_Environment_displayStats___closed__5;
x_476 = lean::string_append(x_475, x_474);
lean::dec(x_474);
x_477 = l_IO_println___at_HasRepr_HasEval___spec__1(x_476, x_472);
lean::dec(x_476);
if (lean::obj_tag(x_477) == 0)
{
obj* x_478; obj* x_479; obj* x_480; obj* x_481; obj* x_482; obj* x_483; obj* x_484; obj* x_485; 
x_478 = lean::cnstr_get(x_477, 1);
lean::inc(x_478);
if (lean::is_exclusive(x_477)) {
 lean::cnstr_release(x_477, 0);
 lean::cnstr_release(x_477, 1);
 x_479 = x_477;
} else {
 lean::dec_ref(x_477);
 x_479 = lean::box(0);
}
if (lean::is_scalar(x_479)) {
 x_480 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_480 = x_479;
}
lean::cnstr_set(x_480, 0, x_7);
lean::cnstr_set(x_480, 1, x_478);
x_481 = l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(x_455);
x_482 = l_Nat_repr(x_481);
x_483 = l_Lean_Environment_displayStats___closed__6;
x_484 = lean::string_append(x_483, x_482);
lean::dec(x_482);
x_485 = l_IO_println___at_HasRepr_HasEval___spec__1(x_484, x_480);
lean::dec(x_484);
if (lean::obj_tag(x_485) == 0)
{
obj* x_486; obj* x_487; obj* x_488; obj* x_489; obj* x_490; obj* x_491; obj* x_492; obj* x_493; 
x_486 = lean::cnstr_get(x_485, 1);
lean::inc(x_486);
if (lean::is_exclusive(x_485)) {
 lean::cnstr_release(x_485, 0);
 lean::cnstr_release(x_485, 1);
 x_487 = x_485;
} else {
 lean::dec_ref(x_485);
 x_487 = lean::box(0);
}
if (lean::is_scalar(x_487)) {
 x_488 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_488 = x_487;
}
lean::cnstr_set(x_488, 0, x_7);
lean::cnstr_set(x_488, 1, x_486);
x_489 = l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(x_455);
lean::dec(x_455);
x_490 = l_Nat_repr(x_489);
x_491 = l_Lean_Environment_displayStats___closed__7;
x_492 = lean::string_append(x_491, x_490);
lean::dec(x_490);
x_493 = l_IO_println___at_HasRepr_HasEval___spec__1(x_492, x_488);
lean::dec(x_492);
if (lean::obj_tag(x_493) == 0)
{
obj* x_494; obj* x_495; obj* x_496; uint32 x_497; obj* x_498; obj* x_499; obj* x_500; obj* x_501; obj* x_502; 
x_494 = lean::cnstr_get(x_493, 1);
lean::inc(x_494);
if (lean::is_exclusive(x_493)) {
 lean::cnstr_release(x_493, 0);
 lean::cnstr_release(x_493, 1);
 x_495 = x_493;
} else {
 lean::dec_ref(x_493);
 x_495 = lean::box(0);
}
if (lean::is_scalar(x_495)) {
 x_496 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_496 = x_495;
}
lean::cnstr_set(x_496, 0, x_7);
lean::cnstr_set(x_496, 1, x_494);
x_497 = lean::cnstr_get_scalar<uint32>(x_1, sizeof(void*)*4);
x_498 = lean::uint32_to_nat(x_497);
x_499 = l_Nat_repr(x_498);
x_500 = l_Lean_Environment_displayStats___closed__8;
x_501 = lean::string_append(x_500, x_499);
lean::dec(x_499);
x_502 = l_IO_println___at_HasRepr_HasEval___spec__1(x_501, x_496);
lean::dec(x_501);
if (lean::obj_tag(x_502) == 0)
{
obj* x_503; obj* x_504; obj* x_505; obj* x_506; obj* x_507; obj* x_508; obj* x_509; obj* x_510; obj* x_511; 
x_503 = lean::cnstr_get(x_502, 1);
lean::inc(x_503);
if (lean::is_exclusive(x_502)) {
 lean::cnstr_release(x_502, 0);
 lean::cnstr_release(x_502, 1);
 x_504 = x_502;
} else {
 lean::dec_ref(x_502);
 x_504 = lean::box(0);
}
if (lean::is_scalar(x_504)) {
 x_505 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_505 = x_504;
}
lean::cnstr_set(x_505, 0, x_7);
lean::cnstr_set(x_505, 1, x_503);
x_506 = lean::cnstr_get(x_1, 2);
lean::inc(x_506);
x_507 = lean::array_get_size(x_506);
lean::dec(x_506);
x_508 = l_Nat_repr(x_507);
x_509 = l_Lean_Environment_displayStats___closed__9;
x_510 = lean::string_append(x_509, x_508);
lean::dec(x_508);
x_511 = l_IO_println___at_HasRepr_HasEval___spec__1(x_510, x_505);
lean::dec(x_510);
if (lean::obj_tag(x_511) == 0)
{
obj* x_512; obj* x_513; obj* x_514; obj* x_515; 
x_512 = lean::cnstr_get(x_511, 1);
lean::inc(x_512);
if (lean::is_exclusive(x_511)) {
 lean::cnstr_release(x_511, 0);
 lean::cnstr_release(x_511, 1);
 x_513 = x_511;
} else {
 lean::dec_ref(x_511);
 x_513 = lean::box(0);
}
if (lean::is_scalar(x_513)) {
 x_514 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_514 = x_513;
}
lean::cnstr_set(x_514, 0, x_7);
lean::cnstr_set(x_514, 1, x_512);
x_515 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9(x_1, x_6, x_9, x_514);
lean::dec(x_6);
lean::dec(x_1);
if (lean::obj_tag(x_515) == 0)
{
obj* x_516; obj* x_517; obj* x_518; 
x_516 = lean::cnstr_get(x_515, 1);
lean::inc(x_516);
if (lean::is_exclusive(x_515)) {
 lean::cnstr_release(x_515, 0);
 lean::cnstr_release(x_515, 1);
 x_517 = x_515;
} else {
 lean::dec_ref(x_515);
 x_517 = lean::box(0);
}
if (lean::is_scalar(x_517)) {
 x_518 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_518 = x_517;
}
lean::cnstr_set(x_518, 0, x_7);
lean::cnstr_set(x_518, 1, x_516);
return x_518;
}
else
{
obj* x_519; obj* x_520; obj* x_521; obj* x_522; 
x_519 = lean::cnstr_get(x_515, 0);
lean::inc(x_519);
x_520 = lean::cnstr_get(x_515, 1);
lean::inc(x_520);
if (lean::is_exclusive(x_515)) {
 lean::cnstr_release(x_515, 0);
 lean::cnstr_release(x_515, 1);
 x_521 = x_515;
} else {
 lean::dec_ref(x_515);
 x_521 = lean::box(0);
}
if (lean::is_scalar(x_521)) {
 x_522 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_522 = x_521;
}
lean::cnstr_set(x_522, 0, x_519);
lean::cnstr_set(x_522, 1, x_520);
return x_522;
}
}
else
{
obj* x_523; obj* x_524; obj* x_525; obj* x_526; 
lean::dec(x_6);
lean::dec(x_1);
x_523 = lean::cnstr_get(x_511, 0);
lean::inc(x_523);
x_524 = lean::cnstr_get(x_511, 1);
lean::inc(x_524);
if (lean::is_exclusive(x_511)) {
 lean::cnstr_release(x_511, 0);
 lean::cnstr_release(x_511, 1);
 x_525 = x_511;
} else {
 lean::dec_ref(x_511);
 x_525 = lean::box(0);
}
if (lean::is_scalar(x_525)) {
 x_526 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_526 = x_525;
}
lean::cnstr_set(x_526, 0, x_523);
lean::cnstr_set(x_526, 1, x_524);
return x_526;
}
}
else
{
obj* x_527; obj* x_528; obj* x_529; obj* x_530; 
lean::dec(x_6);
lean::dec(x_1);
x_527 = lean::cnstr_get(x_502, 0);
lean::inc(x_527);
x_528 = lean::cnstr_get(x_502, 1);
lean::inc(x_528);
if (lean::is_exclusive(x_502)) {
 lean::cnstr_release(x_502, 0);
 lean::cnstr_release(x_502, 1);
 x_529 = x_502;
} else {
 lean::dec_ref(x_502);
 x_529 = lean::box(0);
}
if (lean::is_scalar(x_529)) {
 x_530 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_530 = x_529;
}
lean::cnstr_set(x_530, 0, x_527);
lean::cnstr_set(x_530, 1, x_528);
return x_530;
}
}
else
{
obj* x_531; obj* x_532; obj* x_533; obj* x_534; 
lean::dec(x_6);
lean::dec(x_1);
x_531 = lean::cnstr_get(x_493, 0);
lean::inc(x_531);
x_532 = lean::cnstr_get(x_493, 1);
lean::inc(x_532);
if (lean::is_exclusive(x_493)) {
 lean::cnstr_release(x_493, 0);
 lean::cnstr_release(x_493, 1);
 x_533 = x_493;
} else {
 lean::dec_ref(x_493);
 x_533 = lean::box(0);
}
if (lean::is_scalar(x_533)) {
 x_534 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_534 = x_533;
}
lean::cnstr_set(x_534, 0, x_531);
lean::cnstr_set(x_534, 1, x_532);
return x_534;
}
}
else
{
obj* x_535; obj* x_536; obj* x_537; obj* x_538; 
lean::dec(x_455);
lean::dec(x_6);
lean::dec(x_1);
x_535 = lean::cnstr_get(x_485, 0);
lean::inc(x_535);
x_536 = lean::cnstr_get(x_485, 1);
lean::inc(x_536);
if (lean::is_exclusive(x_485)) {
 lean::cnstr_release(x_485, 0);
 lean::cnstr_release(x_485, 1);
 x_537 = x_485;
} else {
 lean::dec_ref(x_485);
 x_537 = lean::box(0);
}
if (lean::is_scalar(x_537)) {
 x_538 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_538 = x_537;
}
lean::cnstr_set(x_538, 0, x_535);
lean::cnstr_set(x_538, 1, x_536);
return x_538;
}
}
else
{
obj* x_539; obj* x_540; obj* x_541; obj* x_542; 
lean::dec(x_455);
lean::dec(x_6);
lean::dec(x_1);
x_539 = lean::cnstr_get(x_477, 0);
lean::inc(x_539);
x_540 = lean::cnstr_get(x_477, 1);
lean::inc(x_540);
if (lean::is_exclusive(x_477)) {
 lean::cnstr_release(x_477, 0);
 lean::cnstr_release(x_477, 1);
 x_541 = x_477;
} else {
 lean::dec_ref(x_477);
 x_541 = lean::box(0);
}
if (lean::is_scalar(x_541)) {
 x_542 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_542 = x_541;
}
lean::cnstr_set(x_542, 0, x_539);
lean::cnstr_set(x_542, 1, x_540);
return x_542;
}
}
else
{
obj* x_543; obj* x_544; obj* x_545; obj* x_546; 
lean::dec(x_464);
lean::dec(x_455);
lean::dec(x_6);
lean::dec(x_1);
x_543 = lean::cnstr_get(x_469, 0);
lean::inc(x_543);
x_544 = lean::cnstr_get(x_469, 1);
lean::inc(x_544);
if (lean::is_exclusive(x_469)) {
 lean::cnstr_release(x_469, 0);
 lean::cnstr_release(x_469, 1);
 x_545 = x_469;
} else {
 lean::dec_ref(x_469);
 x_545 = lean::box(0);
}
if (lean::is_scalar(x_545)) {
 x_546 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_546 = x_545;
}
lean::cnstr_set(x_546, 0, x_543);
lean::cnstr_set(x_546, 1, x_544);
return x_546;
}
}
else
{
obj* x_547; obj* x_548; obj* x_549; obj* x_550; 
lean::dec(x_455);
lean::dec(x_6);
lean::dec(x_1);
x_547 = lean::cnstr_get(x_460, 0);
lean::inc(x_547);
x_548 = lean::cnstr_get(x_460, 1);
lean::inc(x_548);
if (lean::is_exclusive(x_460)) {
 lean::cnstr_release(x_460, 0);
 lean::cnstr_release(x_460, 1);
 x_549 = x_460;
} else {
 lean::dec_ref(x_460);
 x_549 = lean::box(0);
}
if (lean::is_scalar(x_549)) {
 x_550 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_550 = x_549;
}
lean::cnstr_set(x_550, 0, x_547);
lean::cnstr_set(x_550, 1, x_548);
return x_550;
}
}
}
else
{
uint8 x_551; 
lean::dec(x_6);
lean::dec(x_1);
x_551 = !lean::is_exclusive(x_26);
if (x_551 == 0)
{
return x_26;
}
else
{
obj* x_552; obj* x_553; obj* x_554; 
x_552 = lean::cnstr_get(x_26, 0);
x_553 = lean::cnstr_get(x_26, 1);
lean::inc(x_553);
lean::inc(x_552);
lean::dec(x_26);
x_554 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_554, 0, x_552);
lean::cnstr_set(x_554, 1, x_553);
return x_554;
}
}
}
else
{
obj* x_555; obj* x_556; obj* x_557; obj* x_558; obj* x_559; obj* x_560; 
x_555 = lean::cnstr_get(x_20, 1);
lean::inc(x_555);
lean::dec(x_20);
x_556 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_556, 0, x_7);
lean::cnstr_set(x_556, 1, x_555);
x_557 = l_Nat_repr(x_14);
x_558 = l_Lean_Environment_displayStats___closed__2;
x_559 = lean::string_append(x_558, x_557);
lean::dec(x_557);
x_560 = l_IO_println___at_HasRepr_HasEval___spec__1(x_559, x_556);
lean::dec(x_559);
if (lean::obj_tag(x_560) == 0)
{
obj* x_561; obj* x_562; obj* x_563; obj* x_564; obj* x_565; obj* x_566; obj* x_567; obj* x_568; obj* x_569; 
x_561 = lean::cnstr_get(x_560, 1);
lean::inc(x_561);
if (lean::is_exclusive(x_560)) {
 lean::cnstr_release(x_560, 0);
 lean::cnstr_release(x_560, 1);
 x_562 = x_560;
} else {
 lean::dec_ref(x_560);
 x_562 = lean::box(0);
}
if (lean::is_scalar(x_562)) {
 x_563 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_563 = x_562;
}
lean::cnstr_set(x_563, 0, x_7);
lean::cnstr_set(x_563, 1, x_561);
x_564 = lean::cnstr_get(x_1, 1);
lean::inc(x_564);
x_565 = l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3(x_564);
x_566 = l_Nat_repr(x_565);
x_567 = l_Lean_Environment_displayStats___closed__3;
x_568 = lean::string_append(x_567, x_566);
lean::dec(x_566);
x_569 = l_IO_println___at_HasRepr_HasEval___spec__1(x_568, x_563);
lean::dec(x_568);
if (lean::obj_tag(x_569) == 0)
{
obj* x_570; obj* x_571; obj* x_572; obj* x_573; obj* x_574; obj* x_575; obj* x_576; obj* x_577; obj* x_578; 
x_570 = lean::cnstr_get(x_569, 1);
lean::inc(x_570);
if (lean::is_exclusive(x_569)) {
 lean::cnstr_release(x_569, 0);
 lean::cnstr_release(x_569, 1);
 x_571 = x_569;
} else {
 lean::dec_ref(x_569);
 x_571 = lean::box(0);
}
if (lean::is_scalar(x_571)) {
 x_572 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_572 = x_571;
}
lean::cnstr_set(x_572, 0, x_7);
lean::cnstr_set(x_572, 1, x_570);
x_573 = l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4(x_564);
x_574 = lean::cnstr_get(x_573, 0);
lean::inc(x_574);
x_575 = l_Nat_repr(x_574);
x_576 = l_Lean_Environment_displayStats___closed__4;
x_577 = lean::string_append(x_576, x_575);
lean::dec(x_575);
x_578 = l_IO_println___at_HasRepr_HasEval___spec__1(x_577, x_572);
lean::dec(x_577);
if (lean::obj_tag(x_578) == 0)
{
obj* x_579; obj* x_580; obj* x_581; obj* x_582; obj* x_583; obj* x_584; obj* x_585; obj* x_586; 
x_579 = lean::cnstr_get(x_578, 1);
lean::inc(x_579);
if (lean::is_exclusive(x_578)) {
 lean::cnstr_release(x_578, 0);
 lean::cnstr_release(x_578, 1);
 x_580 = x_578;
} else {
 lean::dec_ref(x_578);
 x_580 = lean::box(0);
}
if (lean::is_scalar(x_580)) {
 x_581 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_581 = x_580;
}
lean::cnstr_set(x_581, 0, x_7);
lean::cnstr_set(x_581, 1, x_579);
x_582 = lean::cnstr_get(x_573, 1);
lean::inc(x_582);
lean::dec(x_573);
x_583 = l_Nat_repr(x_582);
x_584 = l_Lean_Environment_displayStats___closed__5;
x_585 = lean::string_append(x_584, x_583);
lean::dec(x_583);
x_586 = l_IO_println___at_HasRepr_HasEval___spec__1(x_585, x_581);
lean::dec(x_585);
if (lean::obj_tag(x_586) == 0)
{
obj* x_587; obj* x_588; obj* x_589; obj* x_590; obj* x_591; obj* x_592; obj* x_593; obj* x_594; 
x_587 = lean::cnstr_get(x_586, 1);
lean::inc(x_587);
if (lean::is_exclusive(x_586)) {
 lean::cnstr_release(x_586, 0);
 lean::cnstr_release(x_586, 1);
 x_588 = x_586;
} else {
 lean::dec_ref(x_586);
 x_588 = lean::box(0);
}
if (lean::is_scalar(x_588)) {
 x_589 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_589 = x_588;
}
lean::cnstr_set(x_589, 0, x_7);
lean::cnstr_set(x_589, 1, x_587);
x_590 = l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(x_564);
x_591 = l_Nat_repr(x_590);
x_592 = l_Lean_Environment_displayStats___closed__6;
x_593 = lean::string_append(x_592, x_591);
lean::dec(x_591);
x_594 = l_IO_println___at_HasRepr_HasEval___spec__1(x_593, x_589);
lean::dec(x_593);
if (lean::obj_tag(x_594) == 0)
{
obj* x_595; obj* x_596; obj* x_597; obj* x_598; obj* x_599; obj* x_600; obj* x_601; obj* x_602; 
x_595 = lean::cnstr_get(x_594, 1);
lean::inc(x_595);
if (lean::is_exclusive(x_594)) {
 lean::cnstr_release(x_594, 0);
 lean::cnstr_release(x_594, 1);
 x_596 = x_594;
} else {
 lean::dec_ref(x_594);
 x_596 = lean::box(0);
}
if (lean::is_scalar(x_596)) {
 x_597 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_597 = x_596;
}
lean::cnstr_set(x_597, 0, x_7);
lean::cnstr_set(x_597, 1, x_595);
x_598 = l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(x_564);
lean::dec(x_564);
x_599 = l_Nat_repr(x_598);
x_600 = l_Lean_Environment_displayStats___closed__7;
x_601 = lean::string_append(x_600, x_599);
lean::dec(x_599);
x_602 = l_IO_println___at_HasRepr_HasEval___spec__1(x_601, x_597);
lean::dec(x_601);
if (lean::obj_tag(x_602) == 0)
{
obj* x_603; obj* x_604; obj* x_605; uint32 x_606; obj* x_607; obj* x_608; obj* x_609; obj* x_610; obj* x_611; 
x_603 = lean::cnstr_get(x_602, 1);
lean::inc(x_603);
if (lean::is_exclusive(x_602)) {
 lean::cnstr_release(x_602, 0);
 lean::cnstr_release(x_602, 1);
 x_604 = x_602;
} else {
 lean::dec_ref(x_602);
 x_604 = lean::box(0);
}
if (lean::is_scalar(x_604)) {
 x_605 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_605 = x_604;
}
lean::cnstr_set(x_605, 0, x_7);
lean::cnstr_set(x_605, 1, x_603);
x_606 = lean::cnstr_get_scalar<uint32>(x_1, sizeof(void*)*4);
x_607 = lean::uint32_to_nat(x_606);
x_608 = l_Nat_repr(x_607);
x_609 = l_Lean_Environment_displayStats___closed__8;
x_610 = lean::string_append(x_609, x_608);
lean::dec(x_608);
x_611 = l_IO_println___at_HasRepr_HasEval___spec__1(x_610, x_605);
lean::dec(x_610);
if (lean::obj_tag(x_611) == 0)
{
obj* x_612; obj* x_613; obj* x_614; obj* x_615; obj* x_616; obj* x_617; obj* x_618; obj* x_619; obj* x_620; 
x_612 = lean::cnstr_get(x_611, 1);
lean::inc(x_612);
if (lean::is_exclusive(x_611)) {
 lean::cnstr_release(x_611, 0);
 lean::cnstr_release(x_611, 1);
 x_613 = x_611;
} else {
 lean::dec_ref(x_611);
 x_613 = lean::box(0);
}
if (lean::is_scalar(x_613)) {
 x_614 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_614 = x_613;
}
lean::cnstr_set(x_614, 0, x_7);
lean::cnstr_set(x_614, 1, x_612);
x_615 = lean::cnstr_get(x_1, 2);
lean::inc(x_615);
x_616 = lean::array_get_size(x_615);
lean::dec(x_615);
x_617 = l_Nat_repr(x_616);
x_618 = l_Lean_Environment_displayStats___closed__9;
x_619 = lean::string_append(x_618, x_617);
lean::dec(x_617);
x_620 = l_IO_println___at_HasRepr_HasEval___spec__1(x_619, x_614);
lean::dec(x_619);
if (lean::obj_tag(x_620) == 0)
{
obj* x_621; obj* x_622; obj* x_623; obj* x_624; 
x_621 = lean::cnstr_get(x_620, 1);
lean::inc(x_621);
if (lean::is_exclusive(x_620)) {
 lean::cnstr_release(x_620, 0);
 lean::cnstr_release(x_620, 1);
 x_622 = x_620;
} else {
 lean::dec_ref(x_620);
 x_622 = lean::box(0);
}
if (lean::is_scalar(x_622)) {
 x_623 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_623 = x_622;
}
lean::cnstr_set(x_623, 0, x_7);
lean::cnstr_set(x_623, 1, x_621);
x_624 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9(x_1, x_6, x_9, x_623);
lean::dec(x_6);
lean::dec(x_1);
if (lean::obj_tag(x_624) == 0)
{
obj* x_625; obj* x_626; obj* x_627; 
x_625 = lean::cnstr_get(x_624, 1);
lean::inc(x_625);
if (lean::is_exclusive(x_624)) {
 lean::cnstr_release(x_624, 0);
 lean::cnstr_release(x_624, 1);
 x_626 = x_624;
} else {
 lean::dec_ref(x_624);
 x_626 = lean::box(0);
}
if (lean::is_scalar(x_626)) {
 x_627 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_627 = x_626;
}
lean::cnstr_set(x_627, 0, x_7);
lean::cnstr_set(x_627, 1, x_625);
return x_627;
}
else
{
obj* x_628; obj* x_629; obj* x_630; obj* x_631; 
x_628 = lean::cnstr_get(x_624, 0);
lean::inc(x_628);
x_629 = lean::cnstr_get(x_624, 1);
lean::inc(x_629);
if (lean::is_exclusive(x_624)) {
 lean::cnstr_release(x_624, 0);
 lean::cnstr_release(x_624, 1);
 x_630 = x_624;
} else {
 lean::dec_ref(x_624);
 x_630 = lean::box(0);
}
if (lean::is_scalar(x_630)) {
 x_631 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_631 = x_630;
}
lean::cnstr_set(x_631, 0, x_628);
lean::cnstr_set(x_631, 1, x_629);
return x_631;
}
}
else
{
obj* x_632; obj* x_633; obj* x_634; obj* x_635; 
lean::dec(x_6);
lean::dec(x_1);
x_632 = lean::cnstr_get(x_620, 0);
lean::inc(x_632);
x_633 = lean::cnstr_get(x_620, 1);
lean::inc(x_633);
if (lean::is_exclusive(x_620)) {
 lean::cnstr_release(x_620, 0);
 lean::cnstr_release(x_620, 1);
 x_634 = x_620;
} else {
 lean::dec_ref(x_620);
 x_634 = lean::box(0);
}
if (lean::is_scalar(x_634)) {
 x_635 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_635 = x_634;
}
lean::cnstr_set(x_635, 0, x_632);
lean::cnstr_set(x_635, 1, x_633);
return x_635;
}
}
else
{
obj* x_636; obj* x_637; obj* x_638; obj* x_639; 
lean::dec(x_6);
lean::dec(x_1);
x_636 = lean::cnstr_get(x_611, 0);
lean::inc(x_636);
x_637 = lean::cnstr_get(x_611, 1);
lean::inc(x_637);
if (lean::is_exclusive(x_611)) {
 lean::cnstr_release(x_611, 0);
 lean::cnstr_release(x_611, 1);
 x_638 = x_611;
} else {
 lean::dec_ref(x_611);
 x_638 = lean::box(0);
}
if (lean::is_scalar(x_638)) {
 x_639 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_639 = x_638;
}
lean::cnstr_set(x_639, 0, x_636);
lean::cnstr_set(x_639, 1, x_637);
return x_639;
}
}
else
{
obj* x_640; obj* x_641; obj* x_642; obj* x_643; 
lean::dec(x_6);
lean::dec(x_1);
x_640 = lean::cnstr_get(x_602, 0);
lean::inc(x_640);
x_641 = lean::cnstr_get(x_602, 1);
lean::inc(x_641);
if (lean::is_exclusive(x_602)) {
 lean::cnstr_release(x_602, 0);
 lean::cnstr_release(x_602, 1);
 x_642 = x_602;
} else {
 lean::dec_ref(x_602);
 x_642 = lean::box(0);
}
if (lean::is_scalar(x_642)) {
 x_643 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_643 = x_642;
}
lean::cnstr_set(x_643, 0, x_640);
lean::cnstr_set(x_643, 1, x_641);
return x_643;
}
}
else
{
obj* x_644; obj* x_645; obj* x_646; obj* x_647; 
lean::dec(x_564);
lean::dec(x_6);
lean::dec(x_1);
x_644 = lean::cnstr_get(x_594, 0);
lean::inc(x_644);
x_645 = lean::cnstr_get(x_594, 1);
lean::inc(x_645);
if (lean::is_exclusive(x_594)) {
 lean::cnstr_release(x_594, 0);
 lean::cnstr_release(x_594, 1);
 x_646 = x_594;
} else {
 lean::dec_ref(x_594);
 x_646 = lean::box(0);
}
if (lean::is_scalar(x_646)) {
 x_647 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_647 = x_646;
}
lean::cnstr_set(x_647, 0, x_644);
lean::cnstr_set(x_647, 1, x_645);
return x_647;
}
}
else
{
obj* x_648; obj* x_649; obj* x_650; obj* x_651; 
lean::dec(x_564);
lean::dec(x_6);
lean::dec(x_1);
x_648 = lean::cnstr_get(x_586, 0);
lean::inc(x_648);
x_649 = lean::cnstr_get(x_586, 1);
lean::inc(x_649);
if (lean::is_exclusive(x_586)) {
 lean::cnstr_release(x_586, 0);
 lean::cnstr_release(x_586, 1);
 x_650 = x_586;
} else {
 lean::dec_ref(x_586);
 x_650 = lean::box(0);
}
if (lean::is_scalar(x_650)) {
 x_651 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_651 = x_650;
}
lean::cnstr_set(x_651, 0, x_648);
lean::cnstr_set(x_651, 1, x_649);
return x_651;
}
}
else
{
obj* x_652; obj* x_653; obj* x_654; obj* x_655; 
lean::dec(x_573);
lean::dec(x_564);
lean::dec(x_6);
lean::dec(x_1);
x_652 = lean::cnstr_get(x_578, 0);
lean::inc(x_652);
x_653 = lean::cnstr_get(x_578, 1);
lean::inc(x_653);
if (lean::is_exclusive(x_578)) {
 lean::cnstr_release(x_578, 0);
 lean::cnstr_release(x_578, 1);
 x_654 = x_578;
} else {
 lean::dec_ref(x_578);
 x_654 = lean::box(0);
}
if (lean::is_scalar(x_654)) {
 x_655 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_655 = x_654;
}
lean::cnstr_set(x_655, 0, x_652);
lean::cnstr_set(x_655, 1, x_653);
return x_655;
}
}
else
{
obj* x_656; obj* x_657; obj* x_658; obj* x_659; 
lean::dec(x_564);
lean::dec(x_6);
lean::dec(x_1);
x_656 = lean::cnstr_get(x_569, 0);
lean::inc(x_656);
x_657 = lean::cnstr_get(x_569, 1);
lean::inc(x_657);
if (lean::is_exclusive(x_569)) {
 lean::cnstr_release(x_569, 0);
 lean::cnstr_release(x_569, 1);
 x_658 = x_569;
} else {
 lean::dec_ref(x_569);
 x_658 = lean::box(0);
}
if (lean::is_scalar(x_658)) {
 x_659 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_659 = x_658;
}
lean::cnstr_set(x_659, 0, x_656);
lean::cnstr_set(x_659, 1, x_657);
return x_659;
}
}
else
{
obj* x_660; obj* x_661; obj* x_662; obj* x_663; 
lean::dec(x_6);
lean::dec(x_1);
x_660 = lean::cnstr_get(x_560, 0);
lean::inc(x_660);
x_661 = lean::cnstr_get(x_560, 1);
lean::inc(x_661);
if (lean::is_exclusive(x_560)) {
 lean::cnstr_release(x_560, 0);
 lean::cnstr_release(x_560, 1);
 x_662 = x_560;
} else {
 lean::dec_ref(x_560);
 x_662 = lean::box(0);
}
if (lean::is_scalar(x_662)) {
 x_663 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_663 = x_662;
}
lean::cnstr_set(x_663, 0, x_660);
lean::cnstr_set(x_663, 1, x_661);
return x_663;
}
}
}
else
{
uint8 x_664; 
lean::dec(x_14);
lean::dec(x_6);
lean::dec(x_1);
x_664 = !lean::is_exclusive(x_20);
if (x_664 == 0)
{
return x_20;
}
else
{
obj* x_665; obj* x_666; obj* x_667; 
x_665 = lean::cnstr_get(x_20, 0);
x_666 = lean::cnstr_get(x_20, 1);
lean::inc(x_666);
lean::inc(x_665);
lean::dec(x_20);
x_667 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_667, 0, x_665);
lean::cnstr_set(x_667, 1, x_666);
return x_667;
}
}
}
else
{
obj* x_668; obj* x_669; obj* x_670; obj* x_671; obj* x_672; obj* x_673; obj* x_674; obj* x_675; obj* x_676; obj* x_677; obj* x_678; obj* x_679; obj* x_680; obj* x_681; obj* x_682; obj* x_683; obj* x_684; 
x_668 = lean::cnstr_get(x_4, 0);
x_669 = lean::cnstr_get(x_4, 1);
lean::inc(x_669);
lean::inc(x_668);
lean::dec(x_4);
x_670 = lean::box(0);
x_671 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_671, 0, x_670);
lean::cnstr_set(x_671, 1, x_669);
x_672 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_673 = lean::mk_nat_obj(0u);
x_674 = lean::array_get(x_672, x_668, x_673);
x_675 = lean::cnstr_get(x_674, 0);
lean::inc(x_675);
lean::dec(x_674);
x_676 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_675, x_1);
x_677 = lean::cnstr_get(x_676, 0);
lean::inc(x_677);
lean::dec(x_676);
x_678 = lean::array_get_size(x_677);
lean::dec(x_677);
x_679 = lean::cnstr_get(x_1, 3);
lean::inc(x_679);
x_680 = l_Array_toList___rarg(x_679);
lean::dec(x_679);
x_681 = l_List_toString___main___at_Lean_Environment_displayStats___spec__1(x_680);
x_682 = l_Lean_Environment_displayStats___closed__1;
x_683 = lean::string_append(x_682, x_681);
lean::dec(x_681);
x_684 = l_IO_println___at_HasRepr_HasEval___spec__1(x_683, x_671);
lean::dec(x_683);
if (lean::obj_tag(x_684) == 0)
{
obj* x_685; obj* x_686; obj* x_687; obj* x_688; obj* x_689; obj* x_690; obj* x_691; 
x_685 = lean::cnstr_get(x_684, 1);
lean::inc(x_685);
if (lean::is_exclusive(x_684)) {
 lean::cnstr_release(x_684, 0);
 lean::cnstr_release(x_684, 1);
 x_686 = x_684;
} else {
 lean::dec_ref(x_684);
 x_686 = lean::box(0);
}
if (lean::is_scalar(x_686)) {
 x_687 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_687 = x_686;
}
lean::cnstr_set(x_687, 0, x_670);
lean::cnstr_set(x_687, 1, x_685);
x_688 = l_Nat_repr(x_678);
x_689 = l_Lean_Environment_displayStats___closed__2;
x_690 = lean::string_append(x_689, x_688);
lean::dec(x_688);
x_691 = l_IO_println___at_HasRepr_HasEval___spec__1(x_690, x_687);
lean::dec(x_690);
if (lean::obj_tag(x_691) == 0)
{
obj* x_692; obj* x_693; obj* x_694; obj* x_695; obj* x_696; obj* x_697; obj* x_698; obj* x_699; obj* x_700; 
x_692 = lean::cnstr_get(x_691, 1);
lean::inc(x_692);
if (lean::is_exclusive(x_691)) {
 lean::cnstr_release(x_691, 0);
 lean::cnstr_release(x_691, 1);
 x_693 = x_691;
} else {
 lean::dec_ref(x_691);
 x_693 = lean::box(0);
}
if (lean::is_scalar(x_693)) {
 x_694 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_694 = x_693;
}
lean::cnstr_set(x_694, 0, x_670);
lean::cnstr_set(x_694, 1, x_692);
x_695 = lean::cnstr_get(x_1, 1);
lean::inc(x_695);
x_696 = l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3(x_695);
x_697 = l_Nat_repr(x_696);
x_698 = l_Lean_Environment_displayStats___closed__3;
x_699 = lean::string_append(x_698, x_697);
lean::dec(x_697);
x_700 = l_IO_println___at_HasRepr_HasEval___spec__1(x_699, x_694);
lean::dec(x_699);
if (lean::obj_tag(x_700) == 0)
{
obj* x_701; obj* x_702; obj* x_703; obj* x_704; obj* x_705; obj* x_706; obj* x_707; obj* x_708; obj* x_709; 
x_701 = lean::cnstr_get(x_700, 1);
lean::inc(x_701);
if (lean::is_exclusive(x_700)) {
 lean::cnstr_release(x_700, 0);
 lean::cnstr_release(x_700, 1);
 x_702 = x_700;
} else {
 lean::dec_ref(x_700);
 x_702 = lean::box(0);
}
if (lean::is_scalar(x_702)) {
 x_703 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_703 = x_702;
}
lean::cnstr_set(x_703, 0, x_670);
lean::cnstr_set(x_703, 1, x_701);
x_704 = l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4(x_695);
x_705 = lean::cnstr_get(x_704, 0);
lean::inc(x_705);
x_706 = l_Nat_repr(x_705);
x_707 = l_Lean_Environment_displayStats___closed__4;
x_708 = lean::string_append(x_707, x_706);
lean::dec(x_706);
x_709 = l_IO_println___at_HasRepr_HasEval___spec__1(x_708, x_703);
lean::dec(x_708);
if (lean::obj_tag(x_709) == 0)
{
obj* x_710; obj* x_711; obj* x_712; obj* x_713; obj* x_714; obj* x_715; obj* x_716; obj* x_717; 
x_710 = lean::cnstr_get(x_709, 1);
lean::inc(x_710);
if (lean::is_exclusive(x_709)) {
 lean::cnstr_release(x_709, 0);
 lean::cnstr_release(x_709, 1);
 x_711 = x_709;
} else {
 lean::dec_ref(x_709);
 x_711 = lean::box(0);
}
if (lean::is_scalar(x_711)) {
 x_712 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_712 = x_711;
}
lean::cnstr_set(x_712, 0, x_670);
lean::cnstr_set(x_712, 1, x_710);
x_713 = lean::cnstr_get(x_704, 1);
lean::inc(x_713);
lean::dec(x_704);
x_714 = l_Nat_repr(x_713);
x_715 = l_Lean_Environment_displayStats___closed__5;
x_716 = lean::string_append(x_715, x_714);
lean::dec(x_714);
x_717 = l_IO_println___at_HasRepr_HasEval___spec__1(x_716, x_712);
lean::dec(x_716);
if (lean::obj_tag(x_717) == 0)
{
obj* x_718; obj* x_719; obj* x_720; obj* x_721; obj* x_722; obj* x_723; obj* x_724; obj* x_725; 
x_718 = lean::cnstr_get(x_717, 1);
lean::inc(x_718);
if (lean::is_exclusive(x_717)) {
 lean::cnstr_release(x_717, 0);
 lean::cnstr_release(x_717, 1);
 x_719 = x_717;
} else {
 lean::dec_ref(x_717);
 x_719 = lean::box(0);
}
if (lean::is_scalar(x_719)) {
 x_720 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_720 = x_719;
}
lean::cnstr_set(x_720, 0, x_670);
lean::cnstr_set(x_720, 1, x_718);
x_721 = l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(x_695);
x_722 = l_Nat_repr(x_721);
x_723 = l_Lean_Environment_displayStats___closed__6;
x_724 = lean::string_append(x_723, x_722);
lean::dec(x_722);
x_725 = l_IO_println___at_HasRepr_HasEval___spec__1(x_724, x_720);
lean::dec(x_724);
if (lean::obj_tag(x_725) == 0)
{
obj* x_726; obj* x_727; obj* x_728; obj* x_729; obj* x_730; obj* x_731; obj* x_732; obj* x_733; 
x_726 = lean::cnstr_get(x_725, 1);
lean::inc(x_726);
if (lean::is_exclusive(x_725)) {
 lean::cnstr_release(x_725, 0);
 lean::cnstr_release(x_725, 1);
 x_727 = x_725;
} else {
 lean::dec_ref(x_725);
 x_727 = lean::box(0);
}
if (lean::is_scalar(x_727)) {
 x_728 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_728 = x_727;
}
lean::cnstr_set(x_728, 0, x_670);
lean::cnstr_set(x_728, 1, x_726);
x_729 = l_Lean_SMap_maxDepth___at_Lean_Environment_displayStats___spec__7(x_695);
lean::dec(x_695);
x_730 = l_Nat_repr(x_729);
x_731 = l_Lean_Environment_displayStats___closed__7;
x_732 = lean::string_append(x_731, x_730);
lean::dec(x_730);
x_733 = l_IO_println___at_HasRepr_HasEval___spec__1(x_732, x_728);
lean::dec(x_732);
if (lean::obj_tag(x_733) == 0)
{
obj* x_734; obj* x_735; obj* x_736; uint32 x_737; obj* x_738; obj* x_739; obj* x_740; obj* x_741; obj* x_742; 
x_734 = lean::cnstr_get(x_733, 1);
lean::inc(x_734);
if (lean::is_exclusive(x_733)) {
 lean::cnstr_release(x_733, 0);
 lean::cnstr_release(x_733, 1);
 x_735 = x_733;
} else {
 lean::dec_ref(x_733);
 x_735 = lean::box(0);
}
if (lean::is_scalar(x_735)) {
 x_736 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_736 = x_735;
}
lean::cnstr_set(x_736, 0, x_670);
lean::cnstr_set(x_736, 1, x_734);
x_737 = lean::cnstr_get_scalar<uint32>(x_1, sizeof(void*)*4);
x_738 = lean::uint32_to_nat(x_737);
x_739 = l_Nat_repr(x_738);
x_740 = l_Lean_Environment_displayStats___closed__8;
x_741 = lean::string_append(x_740, x_739);
lean::dec(x_739);
x_742 = l_IO_println___at_HasRepr_HasEval___spec__1(x_741, x_736);
lean::dec(x_741);
if (lean::obj_tag(x_742) == 0)
{
obj* x_743; obj* x_744; obj* x_745; obj* x_746; obj* x_747; obj* x_748; obj* x_749; obj* x_750; obj* x_751; 
x_743 = lean::cnstr_get(x_742, 1);
lean::inc(x_743);
if (lean::is_exclusive(x_742)) {
 lean::cnstr_release(x_742, 0);
 lean::cnstr_release(x_742, 1);
 x_744 = x_742;
} else {
 lean::dec_ref(x_742);
 x_744 = lean::box(0);
}
if (lean::is_scalar(x_744)) {
 x_745 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_745 = x_744;
}
lean::cnstr_set(x_745, 0, x_670);
lean::cnstr_set(x_745, 1, x_743);
x_746 = lean::cnstr_get(x_1, 2);
lean::inc(x_746);
x_747 = lean::array_get_size(x_746);
lean::dec(x_746);
x_748 = l_Nat_repr(x_747);
x_749 = l_Lean_Environment_displayStats___closed__9;
x_750 = lean::string_append(x_749, x_748);
lean::dec(x_748);
x_751 = l_IO_println___at_HasRepr_HasEval___spec__1(x_750, x_745);
lean::dec(x_750);
if (lean::obj_tag(x_751) == 0)
{
obj* x_752; obj* x_753; obj* x_754; obj* x_755; 
x_752 = lean::cnstr_get(x_751, 1);
lean::inc(x_752);
if (lean::is_exclusive(x_751)) {
 lean::cnstr_release(x_751, 0);
 lean::cnstr_release(x_751, 1);
 x_753 = x_751;
} else {
 lean::dec_ref(x_751);
 x_753 = lean::box(0);
}
if (lean::is_scalar(x_753)) {
 x_754 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_754 = x_753;
}
lean::cnstr_set(x_754, 0, x_670);
lean::cnstr_set(x_754, 1, x_752);
x_755 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9(x_1, x_668, x_673, x_754);
lean::dec(x_668);
lean::dec(x_1);
if (lean::obj_tag(x_755) == 0)
{
obj* x_756; obj* x_757; obj* x_758; 
x_756 = lean::cnstr_get(x_755, 1);
lean::inc(x_756);
if (lean::is_exclusive(x_755)) {
 lean::cnstr_release(x_755, 0);
 lean::cnstr_release(x_755, 1);
 x_757 = x_755;
} else {
 lean::dec_ref(x_755);
 x_757 = lean::box(0);
}
if (lean::is_scalar(x_757)) {
 x_758 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_758 = x_757;
}
lean::cnstr_set(x_758, 0, x_670);
lean::cnstr_set(x_758, 1, x_756);
return x_758;
}
else
{
obj* x_759; obj* x_760; obj* x_761; obj* x_762; 
x_759 = lean::cnstr_get(x_755, 0);
lean::inc(x_759);
x_760 = lean::cnstr_get(x_755, 1);
lean::inc(x_760);
if (lean::is_exclusive(x_755)) {
 lean::cnstr_release(x_755, 0);
 lean::cnstr_release(x_755, 1);
 x_761 = x_755;
} else {
 lean::dec_ref(x_755);
 x_761 = lean::box(0);
}
if (lean::is_scalar(x_761)) {
 x_762 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_762 = x_761;
}
lean::cnstr_set(x_762, 0, x_759);
lean::cnstr_set(x_762, 1, x_760);
return x_762;
}
}
else
{
obj* x_763; obj* x_764; obj* x_765; obj* x_766; 
lean::dec(x_668);
lean::dec(x_1);
x_763 = lean::cnstr_get(x_751, 0);
lean::inc(x_763);
x_764 = lean::cnstr_get(x_751, 1);
lean::inc(x_764);
if (lean::is_exclusive(x_751)) {
 lean::cnstr_release(x_751, 0);
 lean::cnstr_release(x_751, 1);
 x_765 = x_751;
} else {
 lean::dec_ref(x_751);
 x_765 = lean::box(0);
}
if (lean::is_scalar(x_765)) {
 x_766 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_766 = x_765;
}
lean::cnstr_set(x_766, 0, x_763);
lean::cnstr_set(x_766, 1, x_764);
return x_766;
}
}
else
{
obj* x_767; obj* x_768; obj* x_769; obj* x_770; 
lean::dec(x_668);
lean::dec(x_1);
x_767 = lean::cnstr_get(x_742, 0);
lean::inc(x_767);
x_768 = lean::cnstr_get(x_742, 1);
lean::inc(x_768);
if (lean::is_exclusive(x_742)) {
 lean::cnstr_release(x_742, 0);
 lean::cnstr_release(x_742, 1);
 x_769 = x_742;
} else {
 lean::dec_ref(x_742);
 x_769 = lean::box(0);
}
if (lean::is_scalar(x_769)) {
 x_770 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_770 = x_769;
}
lean::cnstr_set(x_770, 0, x_767);
lean::cnstr_set(x_770, 1, x_768);
return x_770;
}
}
else
{
obj* x_771; obj* x_772; obj* x_773; obj* x_774; 
lean::dec(x_668);
lean::dec(x_1);
x_771 = lean::cnstr_get(x_733, 0);
lean::inc(x_771);
x_772 = lean::cnstr_get(x_733, 1);
lean::inc(x_772);
if (lean::is_exclusive(x_733)) {
 lean::cnstr_release(x_733, 0);
 lean::cnstr_release(x_733, 1);
 x_773 = x_733;
} else {
 lean::dec_ref(x_733);
 x_773 = lean::box(0);
}
if (lean::is_scalar(x_773)) {
 x_774 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_774 = x_773;
}
lean::cnstr_set(x_774, 0, x_771);
lean::cnstr_set(x_774, 1, x_772);
return x_774;
}
}
else
{
obj* x_775; obj* x_776; obj* x_777; obj* x_778; 
lean::dec(x_695);
lean::dec(x_668);
lean::dec(x_1);
x_775 = lean::cnstr_get(x_725, 0);
lean::inc(x_775);
x_776 = lean::cnstr_get(x_725, 1);
lean::inc(x_776);
if (lean::is_exclusive(x_725)) {
 lean::cnstr_release(x_725, 0);
 lean::cnstr_release(x_725, 1);
 x_777 = x_725;
} else {
 lean::dec_ref(x_725);
 x_777 = lean::box(0);
}
if (lean::is_scalar(x_777)) {
 x_778 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_778 = x_777;
}
lean::cnstr_set(x_778, 0, x_775);
lean::cnstr_set(x_778, 1, x_776);
return x_778;
}
}
else
{
obj* x_779; obj* x_780; obj* x_781; obj* x_782; 
lean::dec(x_695);
lean::dec(x_668);
lean::dec(x_1);
x_779 = lean::cnstr_get(x_717, 0);
lean::inc(x_779);
x_780 = lean::cnstr_get(x_717, 1);
lean::inc(x_780);
if (lean::is_exclusive(x_717)) {
 lean::cnstr_release(x_717, 0);
 lean::cnstr_release(x_717, 1);
 x_781 = x_717;
} else {
 lean::dec_ref(x_717);
 x_781 = lean::box(0);
}
if (lean::is_scalar(x_781)) {
 x_782 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_782 = x_781;
}
lean::cnstr_set(x_782, 0, x_779);
lean::cnstr_set(x_782, 1, x_780);
return x_782;
}
}
else
{
obj* x_783; obj* x_784; obj* x_785; obj* x_786; 
lean::dec(x_704);
lean::dec(x_695);
lean::dec(x_668);
lean::dec(x_1);
x_783 = lean::cnstr_get(x_709, 0);
lean::inc(x_783);
x_784 = lean::cnstr_get(x_709, 1);
lean::inc(x_784);
if (lean::is_exclusive(x_709)) {
 lean::cnstr_release(x_709, 0);
 lean::cnstr_release(x_709, 1);
 x_785 = x_709;
} else {
 lean::dec_ref(x_709);
 x_785 = lean::box(0);
}
if (lean::is_scalar(x_785)) {
 x_786 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_786 = x_785;
}
lean::cnstr_set(x_786, 0, x_783);
lean::cnstr_set(x_786, 1, x_784);
return x_786;
}
}
else
{
obj* x_787; obj* x_788; obj* x_789; obj* x_790; 
lean::dec(x_695);
lean::dec(x_668);
lean::dec(x_1);
x_787 = lean::cnstr_get(x_700, 0);
lean::inc(x_787);
x_788 = lean::cnstr_get(x_700, 1);
lean::inc(x_788);
if (lean::is_exclusive(x_700)) {
 lean::cnstr_release(x_700, 0);
 lean::cnstr_release(x_700, 1);
 x_789 = x_700;
} else {
 lean::dec_ref(x_700);
 x_789 = lean::box(0);
}
if (lean::is_scalar(x_789)) {
 x_790 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_790 = x_789;
}
lean::cnstr_set(x_790, 0, x_787);
lean::cnstr_set(x_790, 1, x_788);
return x_790;
}
}
else
{
obj* x_791; obj* x_792; obj* x_793; obj* x_794; 
lean::dec(x_668);
lean::dec(x_1);
x_791 = lean::cnstr_get(x_691, 0);
lean::inc(x_791);
x_792 = lean::cnstr_get(x_691, 1);
lean::inc(x_792);
if (lean::is_exclusive(x_691)) {
 lean::cnstr_release(x_691, 0);
 lean::cnstr_release(x_691, 1);
 x_793 = x_691;
} else {
 lean::dec_ref(x_691);
 x_793 = lean::box(0);
}
if (lean::is_scalar(x_793)) {
 x_794 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_794 = x_793;
}
lean::cnstr_set(x_794, 0, x_791);
lean::cnstr_set(x_794, 1, x_792);
return x_794;
}
}
else
{
obj* x_795; obj* x_796; obj* x_797; obj* x_798; 
lean::dec(x_678);
lean::dec(x_668);
lean::dec(x_1);
x_795 = lean::cnstr_get(x_684, 0);
lean::inc(x_795);
x_796 = lean::cnstr_get(x_684, 1);
lean::inc(x_796);
if (lean::is_exclusive(x_684)) {
 lean::cnstr_release(x_684, 0);
 lean::cnstr_release(x_684, 1);
 x_797 = x_684;
} else {
 lean::dec_ref(x_684);
 x_797 = lean::box(0);
}
if (lean::is_scalar(x_797)) {
 x_798 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_798 = x_797;
}
lean::cnstr_set(x_798, 0, x_795);
lean::cnstr_set(x_798, 1, x_796);
return x_798;
}
}
}
else
{
uint8 x_799; 
lean::dec(x_1);
x_799 = !lean::is_exclusive(x_4);
if (x_799 == 0)
{
return x_4;
}
else
{
obj* x_800; obj* x_801; obj* x_802; 
x_800 = lean::cnstr_get(x_4, 0);
x_801 = lean::cnstr_get(x_4, 1);
lean::inc(x_801);
lean::inc(x_800);
lean::dec(x_4);
x_802 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_802, 0, x_800);
lean::cnstr_set(x_802, 1, x_801);
return x_802;
}
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
obj* l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* initialize_init_io(obj*);
obj* initialize_init_util(obj*);
obj* initialize_init_data_bytearray_default(obj*);
obj* initialize_init_lean_declaration(obj*);
obj* initialize_init_lean_smap(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_environment(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_io(w);
if (io_result_is_error(w)) return w;
w = initialize_init_util(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_bytearray_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_declaration(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_smap(w);
if (io_result_is_error(w)) return w;
l_Lean_EnvExtensionState_Inhabited = _init_l_Lean_EnvExtensionState_Inhabited();
lean::mark_persistent(l_Lean_EnvExtensionState_Inhabited);
l_Lean_ModuleIdx_Inhabited = _init_l_Lean_ModuleIdx_Inhabited();
lean::mark_persistent(l_Lean_ModuleIdx_Inhabited);
l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2 = _init_l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2();
lean::mark_persistent(l_Lean_SMap_empty___at_Lean_Environment_Inhabited___spec__2);
l_Lean_Environment_Inhabited = _init_l_Lean_Environment_Inhabited();
lean::mark_persistent(l_Lean_Environment_Inhabited);
l_Lean_SMap_insert___main___at_Lean_Environment_add___spec__1___closed__1 = _init_l_Lean_SMap_insert___main___at_Lean_Environment_add___spec__1___closed__1();
lean::mark_persistent(l_Lean_SMap_insert___main___at_Lean_Environment_add___spec__1___closed__1);
l_Lean_SMap_insert___main___at_Lean_Environment_add___spec__1___closed__2 = _init_l_Lean_SMap_insert___main___at_Lean_Environment_add___spec__1___closed__2();
lean::mark_persistent(l_Lean_SMap_insert___main___at_Lean_Environment_add___spec__1___closed__2);
l_Lean_EnvExtension_setState___closed__1 = _init_l_Lean_EnvExtension_setState___closed__1();
lean::mark_persistent(l_Lean_EnvExtension_setState___closed__1);
w = l___private_init_lean_environment_5__mkEnvExtensionsRef(w);
if (io_result_is_error(w)) return w;
l___private_init_lean_environment_6__envExtensionsRef = io_result_get_value(w);
lean::mark_persistent(l___private_init_lean_environment_6__envExtensionsRef);
l_Lean_registerEnvExtensionUnsafe___rarg___closed__1 = _init_l_Lean_registerEnvExtensionUnsafe___rarg___closed__1();
lean::mark_persistent(l_Lean_registerEnvExtensionUnsafe___rarg___closed__1);
l_Lean_registerEnvExtensionUnsafe___rarg___closed__2 = _init_l_Lean_registerEnvExtensionUnsafe___rarg___closed__2();
lean::mark_persistent(l_Lean_registerEnvExtensionUnsafe___rarg___closed__2);
l_Lean_mkEmptyEnvironment___closed__1 = _init_l_Lean_mkEmptyEnvironment___closed__1();
lean::mark_persistent(l_Lean_mkEmptyEnvironment___closed__1);
l_Lean_EnvExtensionEntry_Inhabited = _init_l_Lean_EnvExtensionEntry_Inhabited();
lean::mark_persistent(l_Lean_EnvExtensionEntry_Inhabited);
l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1 = _init_l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1();
lean::mark_persistent(l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1);
l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2 = _init_l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2();
lean::mark_persistent(l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2);
w = l___private_init_lean_environment_8__mkPersistentEnvExtensionsRef(w);
if (io_result_is_error(w)) return w;
l___private_init_lean_environment_9__persistentEnvExtensionsRef = io_result_get_value(w);
lean::mark_persistent(l___private_init_lean_environment_9__persistentEnvExtensionsRef);
l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1 = _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1();
lean::mark_persistent(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1);
l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2 = _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2();
lean::mark_persistent(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2);
l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3 = _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3();
lean::mark_persistent(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3);
l_Lean_CPPExtensionState_Inhabited = _init_l_Lean_CPPExtensionState_Inhabited();
lean::mark_persistent(l_Lean_CPPExtensionState_Inhabited);
l_Lean_Modification_Inhabited = _init_l_Lean_Modification_Inhabited();
lean::mark_persistent(l_Lean_Modification_Inhabited);
w = l_Lean_regModListExtension(w);
if (io_result_is_error(w)) return w;
l_Lean_modListExtension = io_result_get_value(w);
lean::mark_persistent(l_Lean_modListExtension);
l_Lean_addModification___closed__1 = _init_l_Lean_addModification___closed__1();
lean::mark_persistent(l_Lean_addModification___closed__1);
l_Lean_addModification___closed__2 = _init_l_Lean_addModification___closed__2();
lean::mark_persistent(l_Lean_addModification___closed__2);
l_Lean_ModuleData_inhabited = _init_l_Lean_ModuleData_inhabited();
lean::mark_persistent(l_Lean_ModuleData_inhabited);
l___private_init_lean_environment_10__getEntriesFor___main___closed__1 = _init_l___private_init_lean_environment_10__getEntriesFor___main___closed__1();
lean::mark_persistent(l___private_init_lean_environment_10__getEntriesFor___main___closed__1);
l_Array_miterateAux___main___at_Lean_importModules___spec__9___closed__1 = _init_l_Array_miterateAux___main___at_Lean_importModules___spec__9___closed__1();
lean::mark_persistent(l_Array_miterateAux___main___at_Lean_importModules___spec__9___closed__1);
l_Lean_importModules___closed__1 = _init_l_Lean_importModules___closed__1();
lean::mark_persistent(l_Lean_importModules___closed__1);
l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__1 = _init_l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__1();
lean::mark_persistent(l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__1);
l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__2 = _init_l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__2();
lean::mark_persistent(l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__2);
l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__3 = _init_l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__3();
lean::mark_persistent(l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__3);
l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__4 = _init_l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__4();
lean::mark_persistent(l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__4);
l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__5 = _init_l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__5();
lean::mark_persistent(l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__5);
l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__6 = _init_l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__6();
lean::mark_persistent(l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__6);
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

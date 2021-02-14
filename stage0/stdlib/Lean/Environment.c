// Lean compiler output
// Module: Lean.Environment
// Imports: Init Std.Data.HashMap Lean.Data.SMap Lean.Declaration Lean.LocalContext Lean.Util.Path Lean.Util.FindExpr Lean.Util.Profile
#include <lean/lean.h>
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
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_mkModuleData___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_contains_match__1(lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkTagDeclarationExtension___spec__5(lean_object*, lean_object*);
lean_object* l_List_toStringAux___at_Lean_Environment_displayStats___spec__2(uint8_t, lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg___closed__2;
lean_object* l_Lean_Environment_hasUnsafe___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Environment_displayStats___lambda__1(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__8;
lean_object* l_Lean_mkMapDeclarationExtension___rarg___closed__1;
lean_object* l_Lean_MapDeclarationExtension_insert(lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtension___lambda__2(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_Environment_isNamespaceName___boxed(lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_importModules___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_isNamespace___boxed(lean_object*, lean_object*);
lean_object* l_Array_binSearchContains___at_Lean_MapDeclarationExtension_contains___spec__1(lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_importModules___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__6___rarg(lean_object*);
lean_object* l_Lean_Environment_displayStats___closed__2;
lean_object* l_Lean_instInhabitedEnvExtensionInterface___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsort___at_Lean_mkTagDeclarationExtension___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg___closed__1;
lean_object* l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_setState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___rarg___closed__2;
lean_object* l_Lean_mkMapDeclarationExtension___rarg___lambda__2___boxed(lean_object*);
lean_object* l_Lean_Environment_displayStats___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_instInhabitedEnvExtensionInterface___closed__2;
uint8_t l_Lean_EnvironmentHeader_quotInit___default;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__5___boxed(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Environment_displayStats___closed__6;
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Environment_find_x3f___spec__6___boxed(lean_object*, lean_object*);
lean_object* lean_display_stats(lean_object*, lean_object*);
lean_object* l_Lean_importModules___lambda__4(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_isConstructor_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withImportModules(lean_object*);
uint8_t l_Lean_Environment_isNamespace(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedEnvironmentHeader;
extern lean_object* l_Lean_NameSet_instInhabitedNameSet;
extern lean_object* l_term_x5b___x5d___closed__9;
lean_object* l_Lean_namespacesExt___elambda__3(lean_object*, lean_object*);
extern lean_object* l_Char_quote___closed__1;
lean_object* lean_environment_free_regions(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_setState(lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___lambda__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_setImportedEntries(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_displayStats___closed__1;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_mkMapDeclarationExtension___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension_match__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Environment_displayStats___closed__4;
lean_object* l_Lean_SimplePersistentEnvExtension_setState(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_setState(lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__4___rarg___boxed(lean_object*, lean_object*);
uint8_t l_Std_PersistentHashMap_containsAtAux___at_Lean_Environment_contains___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header___default;
lean_object* l_Lean_Environment_imports(lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt(lean_object*);
extern lean_object* l_Std_Format_defWidth;
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
lean_object* l_Lean_Environment_displayStats___closed__8;
lean_object* l_Lean_Environment_displayStats___lambda__3___closed__1;
lean_object* l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5___boxed(lean_object*);
lean_object* l_Lean_Environment_hasUnsafe_match__2___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentHashMap_containsAux___at_Lean_Environment_contains___spec__4(lean_object*, size_t, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Environment_getModuleIdxFor_x3f___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_mkModuleData___spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_instInhabitedSimplePersistentEnvExtension(lean_object*, lean_object*);
lean_object* l_Lean_Environment_displayStats___lambda__3___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension___closed__1;
uint8_t l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__3(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_mkModuleData___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType(lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_MapDeclarationExtension_contains___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_set_main_module(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___boxed__const__2;
lean_object* l___private_Lean_Environment_0__Lean_Environment_isQuotInit___boxed(lean_object*);
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_Environment___hyg_2919____spec__1___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedModuleIdx;
lean_object* l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__4(lean_object*);
size_t l_USize_sub(size_t, size_t);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_registerSimplePersistentEnvExtension_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_Environment___hyg_2919____spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe___at_Array_any___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkStateFromImportedEntries___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_fileExists___at_Lean_importModules_importMods___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck_match__1(lean_object*);
lean_object* l_Lean_instInhabitedEnvironment___closed__4;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Monad_seqRight___default___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_Environment_displayStats___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_read_module_data(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__3___rarg___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
lean_object* l_Array_qsort___at_Lean_mkMapDeclarationExtension___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forM___at_Lean_Environment_freeRegions___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_finalizePersistentExtensions(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_freeRegions___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension___closed__2;
lean_object* l_Lean_PersistentEnvExtension_setState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_allImportedModuleNames___boxed(lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_MapDeclarationExtension_find_x3f___spec__4(lean_object*);
extern lean_object* l_instInhabitedNat;
lean_object* l_Lean_EnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_hasUnsafe_match__2(lean_object*);
extern lean_object* l_Lean_instHashableName___closed__1;
lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_mkMapDeclarationExtension___spec__7___rarg(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_displayStats___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_getEntriesFor(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__6(lean_object*);
lean_object* l_Lean_EnvExtension_getState(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_modifyState_match__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_2919____closed__4;
lean_object* l_Lean_importModules_match__2(lean_object*);
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_Environment___hyg_2919____spec__1___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__4___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___at_Lean_Environment_addAux___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_namespacesExt___elambda__4___rarg(lean_object*);
lean_object* l_Array_forM___at_Lean_Environment_displayStats___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__3___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedEnvironment___closed__1;
lean_object* l_Array_qsort___at_Lean_mkMapDeclarationExtension___spec__1(lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtension___rarg(lean_object*);
lean_object* l_Std_RBNode_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_setState___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__4___rarg(lean_object*, lean_object*);
uint8_t l_Lean_mkMapDeclarationExtension___rarg___lambda__3(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_modifyState(lean_object*);
lean_object* l_Lean_importModules___lambda__3(lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f_match__2(lean_object*);
lean_object* l_Lean_readModuleData___boxed(lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Lean_Environment_compileDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Environment_find_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___at_Lean_mkModuleData___spec__1___closed__1;
lean_object* l_Lean_namespacesExt___closed__2;
lean_object* l_Lean_namespacesExt___elambda__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instMonadEnv(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4(lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Environment_find_x3f___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
uint8_t l_Lean_NameMap_contains___rarg(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_MapDeclarationExtension_find_x3f___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_modifyState(lean_object*, lean_object*);
lean_object* l_Std_AssocList_contains___at_Lean_importModules___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_reinsertAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___at_Lean_mkModuleData___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_findOLean(lean_object*, lean_object*);
lean_object* l_Lean_namespacesExt___elambda__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_TagDeclarationExtension_instInhabitedTagDeclarationExtension;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck_match__2(lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_importModules_importMods_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_2919____closed__5;
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___closed__1;
lean_object* l_Array_foldlMUnsafe___at_Lean_Environment_displayStats___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_contains___boxed(lean_object*, lean_object*);
lean_object* l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__3(lean_object*);
lean_object* l_Lean_mkStateFromImportedEntries___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_MapDeclarationExtension_find_x3f___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TagDeclarationExtension_isTagged_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_importModules_importMods_match__1(lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___closed__4;
lean_object* l_Lean_PersistentEnvExtension_setState(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_containsAux___at_Lean_Environment_contains___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp;
lean_object* l_Lean_mkEmptyEnvironment___lambda__1(uint32_t, lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtensionDescr_toArrayFn___default___rarg(lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f_match__1(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedEnvExtensionInterface___closed__1;
lean_object* l_Lean_instInhabitedEnvironment___closed__3;
lean_object* l_Lean_EnvironmentHeader_moduleNames___default;
lean_object* l_Lean_ImportState_moduleNameSet___default;
lean_object* l_Array_foldlMUnsafe___at_Array_foldl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_isConstructor(lean_object*, lean_object*);
lean_object* l_Lean_Environment_displayStats___closed__7;
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_Environment___hyg_2919____spec__1___closed__1;
lean_object* l_Lean_importModules_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_displayStats___closed__5;
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_mkModuleData___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_Environment_registerNamePrefixes_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Environment_find_x3f___spec__2(lean_object*, lean_object*);
lean_object* lean_write_module(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchContains___at_Lean_TagDeclarationExtension_isTagged___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getEntries(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__3___rarg(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_moveEntries___at_Lean_importModules___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_2919____closed__1;
lean_object* l_Lean_Environment_hasUnsafe___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_modify___at_Lean_EnvExtensionInterfaceUnsafe_modifyState___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_insert___closed__1;
lean_object* l_Lean_SimplePersistentEnvExtension_modifyState_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_setState_match__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___at_Lean_mkModuleData___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_MapDeclarationExtension_find_x3f___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentHashMap_insertAux___rarg___closed__3;
lean_object* l_Array_binSearch___at_Lean_MapDeclarationExtension_find_x3f___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f___boxed(lean_object*, lean_object*);
lean_object* l_EStateM_bind___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Declaration_0__Lean_reprDefinitionSafety____x40_Lean_Declaration___hyg_192____closed__3;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__3(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_2919____closed__2;
uint8_t lean_environment_quot_init(lean_object*);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtension___lambda__2___boxed(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_Environment_isNamespaceName_match__1(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_finalizePersistentExtensions___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_MapDeclarationExtension_contains___spec__3(lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__3___boxed(lean_object*, lean_object*);
lean_object* l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_getEntriesFor___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_instReprList___rarg___closed__1;
lean_object* l_Lean_instInhabitedEnvironment___closed__5;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkEmptyEnvironment___closed__1;
lean_object* l_Lean_EnvironmentHeader_mainModule___default;
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__3(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_forM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtension___closed__2;
lean_object* l_Array_binSearchContains___at_Lean_MapDeclarationExtension_contains___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_mkInitialExtensionStates(lean_object*);
lean_object* l_Lean_importModules_importMods___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_binSearchAux___at_Lean_TagDeclarationExtension_isTagged___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_instInhabitedEnvironment___spec__1(lean_object*);
lean_object* l_Lean_Environment_isConstructor_match__1(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtension___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3___boxed(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtension___closed__4;
lean_object* l_Lean_PersistentEnvExtension_addEntry(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_Environment_freeRegions___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_importModules_match__2___rarg(lean_object*, lean_object*);
lean_object* l_List_toStringAux___at_Lean_Environment_displayStats___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_setImportedEntries___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_namespacesExt___elambda__1(lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_IO_fileExists___at_Lean_importModules_importMods___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TagDeclarationExtension_isTagged_match__1(lean_object*);
uint8_t l___private_Lean_Environment_0__Lean_Environment_isNamespaceName(lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___rarg___lambda__2(lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtension___closed__1;
lean_object* l_Lean_instInhabitedPersistentEnvExtension___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_2919____closed__3;
lean_object* l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__1___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_MapDeclarationExtension_contains___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedModuleData___closed__1;
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg(lean_object*, lean_object*);
uint8_t l_Lean_SMap_contains___at_Lean_Environment_contains___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_modifyState(lean_object*);
extern lean_object* l_IO_instInhabitedError___closed__1;
lean_object* l_Array_qsort___at_Lean_mkMapDeclarationExtension___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__1(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtension(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_displayStats___closed__3;
lean_object* l_Array_modifyM___at_Lean_Environment_addAux___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_importModules_importMods___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkEmptyEnvironment___closed__2;
lean_object* l_Lean_importModules_importMods___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___rarg___boxed(lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_importModules_importMods___closed__1;
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_expand___at_Lean_importModules___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension___lambda__2(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_Environment_getTrustLevel___boxed(lean_object*);
lean_object* l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_importModules___closed__3;
lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadEnv___rarg(lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___rarg___lambda__3___boxed(lean_object*, lean_object*);
lean_object* l_Array_modifyM___at_Lean_EnvExtensionInterfaceUnsafe_modifyState___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_instInhabitedEnvExtension(lean_object*, lean_object*);
lean_object* l_Lean_importModules_importMods___closed__2;
lean_object* l_Array_binSearch___at_Lean_MapDeclarationExtension_find_x3f___spec__2(lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
lean_object* lean_eval_const(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_contains___at_Lean_Environment_contains___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Lean_SMap_switch___at_Lean_importModules___spec__10(lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtension___lambda__3___boxed(lean_object*);
uint32_t lean_environment_trust_level(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_setState___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___rarg___closed__1;
extern lean_object* l_instMonadControlReaderT___closed__2;
lean_object* l_Lean_persistentEnvExtensionsRef;
lean_object* l_Lean_mkMapDeclarationExtension(lean_object*);
lean_object* l_Lean_ImportState_regions___default;
lean_object* lean_environment_add(lean_object*, lean_object*);
lean_object* lean_save_module_data(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withImportModules___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ImportState_moduleNames___default;
lean_object* l_Lean_EnvExtension_getState___rarg___boxed(lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_saveModuleData___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkModuleData(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_instInhabitedMapDeclarationExtension(lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_namespacesExt___elambda__1___boxed(lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_Environment_addAux___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkEmptyEnvironment___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkEmptyEnvironment___lambda__1___closed__1;
lean_object* l_Lean_PersistentEnvExtension_modifyState(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentHashMap_contains___at_Lean_Environment_contains___spec__3(lean_object*, lean_object*);
lean_object* l_Array_binSearch___at_Lean_MapDeclarationExtension_find_x3f___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtensionDescr_statsFn___default___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedEnvironmentHeader___closed__1;
lean_object* l_Lean_PersistentEnvExtension_getState___rarg___boxed(lean_object*, lean_object*);
size_t l_USize_mul(size_t, size_t);
lean_object* l_Lean_registerEnvExtension(lean_object*);
lean_object* l_Lean_importModules___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___rarg___lambda__4(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_mkRef___at_Lean_initFn____x40_Lean_Environment___hyg_1088____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionEntrySpec;
lean_object* l_Std_AssocList_contains___at_Lean_Environment_addAux___spec__9___boxed(lean_object*, lean_object*);
lean_object* l_Lean_importModules___closed__1;
uint8_t l_Array_binSearchContains___at_Lean_MapDeclarationExtension_contains___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_addDecl___boxed(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__6(lean_object*);
uint8_t lean_kernel_is_def_eq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CompactedRegion_free___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedEnvExtensionInterface;
extern uint32_t l_instInhabitedUInt32___closed__1;
lean_object* l_Lean_EnvExtensionInterfaceImp___closed__6;
lean_object* l_Lean_TagDeclarationExtension_instInhabitedTagDeclarationExtension___closed__1;
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Environment_addAux___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_importModules_importMods_match__2___rarg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_instInhabitedModuleData;
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Environment_find_x3f___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f_x27___at_Lean_Environment_find_x3f___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__1;
lean_object* l_Array_forM___at_Lean_Environment_freeRegions___spec__1___lambda__1(lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_instInhabitedMapDeclarationExtension___closed__1;
lean_object* l_Std_AssocList_replace___at_Lean_importModules___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__2;
lean_object* l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_mkEnvExtensionsRef(lean_object*);
lean_object* l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4(lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__6___rarg___boxed(lean_object*);
lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Environment_addAux___spec__11(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__3___boxed(lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_Environment_evalConstCheck___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvironmentHeader_regions___default;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_mkStateFromImportedEntries___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkEmptyEnvironment___boxed(lean_object*, lean_object*);
lean_object* lean_kernel_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_MapDeclarationExtension_find_x3f___spec__1(lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___closed__2;
lean_object* l_Lean_instInhabitedEnvironment___closed__2;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp;
lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8___closed__1;
lean_object* l_Array_forM___at_Lean_Environment_freeRegions___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_namespacesExt___elambda__2___boxed(lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Environment_addAux___spec__4(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1(lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2___closed__1;
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_setState___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Array_modify___at_Lean_EnvExtensionInterfaceUnsafe_modifyState___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_namespacesExt___elambda__2(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_modifyState___rarg___lambda__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_FindImpl_initCache;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_file_exists(lean_object*, lean_object*);
lean_object* lean_mk_empty_environment(uint32_t, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_import_modules(lean_object*, lean_object*, uint32_t, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Environment_getModuleIdxFor_x3f___spec__1(lean_object*, lean_object*);
lean_object* l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__6(lean_object*);
lean_object* l_Lean_instInhabitedEnvironment;
extern lean_object* l_term_x5b___x5d___closed__5;
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___closed__1;
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instToStringImport___closed__1;
lean_object* l_Lean_importModules_match__3(lean_object*);
lean_object* l_Std_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__6(lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__4;
lean_object* l_Lean_instInhabitedPersistentEnvExtension___lambda__3(lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkMapDeclarationExtension___spec__8___rarg(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__3(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_modify___at_Lean_Environment_addAux___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_importModules_importMods(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_modify___at_Lean_Environment_addAux___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_freeRegions___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtensionDescr_toArrayFn___default(lean_object*);
lean_object* l_Lean_Environment_evalConstCheck_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_list_to_array(lean_object*, lean_object*);
lean_object* l_IO_mkRef___at___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_mkEnvExtensionsRef___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__2;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__4(lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l_Lean_MapDeclarationExtension_find_x3f(lean_object*);
lean_object* l_Lean_importModules_importMods___closed__3;
lean_object* l_Lean_importModules_match__3___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_MapDeclarationExtension_find_x3f___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_modifyState___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withImportModules___rarg(lean_object*, lean_object*, uint32_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_Environment_registerNamePrefixes(lean_object*, lean_object*);
lean_object* l_Lean_mkStateFromImportedEntries(lean_object*, lean_object*);
lean_object* l_Lean_Environment_addAndCompile(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasUnsafe___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_namespacesExt___closed__5;
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_registerNamespace(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedEnvExtensionInterface___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getNamespaceSet(lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1;
lean_object* l_Lean_EnvExtensionInterfaceImp___closed__2;
extern lean_object* l_Array_instToStringArray___rarg___closed__1;
lean_object* l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg___closed__3;
lean_object* l_Lean_namespacesExt___closed__3;
lean_object* l_Lean_instInhabitedPersistentEnvExtension___closed__3;
lean_object* l_Std_PersistentHashMap_containsAtAux___at_Lean_Environment_contains___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_whnf___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__1;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_MapDeclarationExtension_contains___spec__2(lean_object*);
uint8_t l_Array_binSearchAux___at_Lean_MapDeclarationExtension_contains___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__2;
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__4(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Environment_find_x3f___spec__3(lean_object*, size_t, lean_object*);
lean_object* l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_instInhabitedEnvExtension___boxed(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates___boxed__const__1;
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Environment_find_x3f___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Std_AssocList_foldlM___at_Lean_Environment_addAux___spec__12(lean_object*, lean_object*);
uint8_t l_Std_AssocList_contains___at_Lean_Environment_addAux___spec__9(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedEnvExtensionInterface___closed__3;
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__2___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_instInhabitedEnvironment___spec__2(lean_object*);
lean_object* l_Lean_importModules___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtension___closed__5;
lean_object* l_Lean_SimplePersistentEnvExtension_setState_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___boxed(lean_object*);
lean_object* l_Lean_instMonadEnv___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_mkModuleData___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Environment_hasUnsafe_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__3;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__5(lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Environment_displayStats___spec__1(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_setState___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header___default___closed__1;
lean_object* l_Lean_Environment_displayStats___lambda__2___closed__1;
lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_mkMapDeclarationExtension___spec__7(lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtensionDescr_statsFn___default(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_2919_(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_1088_(lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___rarg(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_getEntriesFor___closed__1;
uint8_t l_Array_binSearchContains___at_Lean_TagDeclarationExtension_isTagged___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedEnvExtensionEntry;
extern lean_object* l_Lean_instInhabitedName;
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Environment_getModuleIdxFor_x3f___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_contains_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f_x27___at_Lean_Environment_find_x3f___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_AssocList_contains___at_Lean_importModules___spec__3(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___boxed__const__1;
lean_object* l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4___boxed(lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*);
lean_object* l_Std_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__6___boxed(lean_object*);
uint8_t l_Lean_Import_runtimeOnly___default;
lean_object* l_Array_qpartition_loop___at_Lean_mkTagDeclarationExtension___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_foldlM___at_Lean_importModules___spec__6(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_MapDeclarationExtension_find_x3f___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_MapDeclarationExtension_find_x3f___spec__3(lean_object*);
lean_object* l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__7;
uint8_t l_Array_binSearchAux___at_Lean_MapDeclarationExtension_contains___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
lean_object* l_Lean_Environment_hasUnsafe_match__1(lean_object*);
lean_object* l_Lean_Environment_addAux(lean_object*, lean_object*);
uint8_t l_Lean_MapDeclarationExtension_contains___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__5___rarg(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__2(lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___rarg___lambda__4___closed__1;
lean_object* l_Lean_profileitIOUnsafe___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_instInhabitedSimplePersistentEnvExtension___rarg(lean_object*);
lean_object* l_Lean_Environment_displayStats___lambda__2___closed__2;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__5;
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_namespacesExt___closed__1;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__1;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___closed__7;
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState(lean_object*, lean_object*);
extern size_t l_Std_PersistentHashMap_insertAux___rarg___closed__2;
lean_object* l_Lean_Environment_getNamespaceSet___boxed(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qpartition_loop___at_Lean_mkTagDeclarationExtension___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Environment_getModuleIdxFor_x3f___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashMap_instInhabitedHashMap___closed__1;
lean_object* l_Lean_SMap_empty___at_Lean_importModules___spec__1;
lean_object* l_Lean_namespacesExt___elambda__4(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_Environment_isNamespaceName_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_initializing(lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_object* l_Lean_MapDeclarationExtension_find_x3f___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates(lean_object*);
lean_object* l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__2(lean_object*);
lean_object* l_Lean_mkStateFromImportedEntries___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instToStringImport(lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtension(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_modifyM___at_Lean_EnvExtensionInterfaceUnsafe_modifyState___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_TagDeclarationExtension_isTagged___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__1(lean_object*);
lean_object* l_Lean_Environment_displayStats___lambda__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TagDeclarationExtension_isTagged___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findM_x3f_visit(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_IO_println___at_Lean_instEval___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Environment_isConstructor___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck_match__2___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension(lean_object*, lean_object*);
lean_object* l_Lean_Environment_imports___boxed(lean_object*);
lean_object* l_Lean_EnvExtension_setState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_namespacesExt;
lean_object* l_Lean_Environment_displayStats___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates___spec__1(size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_importModules_match__1(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_finalizePersistentExtensions___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_importModules___lambda__4___closed__1;
lean_object* l_Lean_namespacesExt___closed__4;
lean_object* l_Array_binSearchAux___at_Lean_MapDeclarationExtension_find_x3f___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_importModules_importMods_match__2(lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_MapDeclarationExtension_contains___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_compile_decl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ImportState_moduleData___default;
lean_object* l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__5(lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___closed__3;
lean_object* l_Array_modifyM___at_Lean_Environment_addAux___spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_importModules___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__5(lean_object*);
lean_object* l_Array_forM___at_Lean_Environment_displayStats___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvironmentHeader_imports___default;
lean_object* l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_envExtensionsRef;
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_importModules___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Environment_addAux___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_HashMapImp_contains___at_Lean_Environment_contains___spec__2(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___lambda__1(lean_object*, lean_object*, size_t, size_t, size_t, size_t, lean_object*);
lean_object* l_Std_HashMapImp_expand___at_Lean_Environment_addAux___spec__10(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_mkModuleData___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___closed__1;
lean_object* l_Lean_SMap_insert___at_Lean_Environment_addAux___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___rarg(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_addAndCompile___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_pure___rarg(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkMapDeclarationExtension___spec__8(lean_object*);
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___closed__5;
lean_object* l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_freeRegions___closed__1;
lean_object* l_Std_PersistentHashMap_contains___at_Lean_Environment_contains___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_Environment_freeRegions___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Environment_find_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension___lambda__3(lean_object*);
lean_object* l_Lean_registerPersistentEnvExtension___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__6;
lean_object* l_Array_binSearchAux___at_Lean_TagDeclarationExtension_isTagged___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Id_instMonadId___closed__4;
lean_object* lean_uint32_to_nat(uint32_t);
uint32_t l_Lean_EnvironmentHeader_trustLevel___default;
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___closed__2;
lean_object* l_Lean_importModules___lambda__4___closed__2;
lean_object* l_Lean_mkTagDeclarationExtension___closed__3;
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_Environment___hyg_2919____spec__1(lean_object*, lean_object*);
uint8_t l_Array_binSearchAux___at_Lean_TagDeclarationExtension_isTagged___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsort___at_Lean_mkTagDeclarationExtension___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_importModules___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_importModules___closed__2;
lean_object* l_Lean_Kernel_isDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_compacted_region_free(size_t, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_contains(lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension___lambda__2___boxed(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_setState___rarg___lambda__1(lean_object*, lean_object*);
uint8_t l_Std_Format_isNil(lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtension___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkModuleData___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedEnvExtensionState;
lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_mkTagDeclarationExtension___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionStateSpec;
lean_object* lean_environment_mark_quot_init(lean_object*);
extern lean_object* l_term_x5b___x5d___closed__3;
lean_object* l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_displayStats___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forM___at_Lean_Environment_freeRegions___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_Environment_registerNamePrefixes_match__1(lean_object*);
lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_add_decl(lean_object*, lean_object*);
lean_object* l_Std_AssocList_replace___at_Lean_Environment_addAux___spec__13(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_contains___at_Lean_Environment_contains___spec__2___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Lean_EnvExtensionStateSpec() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedEnvExtensionState() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedModuleIdx() {
_start:
{
lean_object* x_1; 
x_1 = l_instInhabitedNat;
return x_1;
}
}
static uint8_t _init_l_Lean_Import_runtimeOnly___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lean_instToStringImport___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" (runtime)");
return x_1;
}
}
lean_object* l_Lean_instToStringImport(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Name_toString___closed__1;
x_4 = l_Lean_Name_toStringWithSep(x_3, x_2);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_dec(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_instInhabitedParserDescr___closed__1;
x_7 = lean_string_append(x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_instToStringImport___closed__1;
x_9 = lean_string_append(x_4, x_8);
return x_9;
}
}
}
lean_object* l_Lean_CompactedRegion_free___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_compacted_region_free(x_3, x_2);
return x_4;
}
}
static uint32_t _init_l_Lean_EnvironmentHeader_trustLevel___default() {
_start:
{
uint32_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lean_EnvironmentHeader_quotInit___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lean_EnvironmentHeader_mainModule___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_EnvironmentHeader_imports___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_EnvironmentHeader_regions___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_EnvironmentHeader_moduleNames___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedEnvironmentHeader___closed__1() {
_start:
{
uint32_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_instInhabitedUInt32___closed__1;
x_2 = 0;
x_3 = lean_box(0);
x_4 = l_Array_empty___closed__1;
x_5 = lean_alloc_ctor(0, 4, 5);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_uint32(x_5, sizeof(void*)*4, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*4 + 4, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_instInhabitedEnvironmentHeader() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedEnvironmentHeader___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_header___default___closed__1() {
_start:
{
uint32_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 0;
x_3 = lean_box(0);
x_4 = l_Array_empty___closed__1;
x_5 = lean_alloc_ctor(0, 4, 5);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_uint32(x_5, sizeof(void*)*4, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*4 + 4, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Environment_header___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Environment_header___default___closed__1;
return x_1;
}
}
lean_object* l_Std_mkHashMap___at_Lean_instInhabitedEnvironment___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_Std_mkHashMap___at_Lean_instInhabitedEnvironment___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedEnvironment___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedEnvironment___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedEnvironment___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_instInhabitedEnvironment___closed__2;
x_3 = l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_instInhabitedEnvironment___closed__4() {
_start:
{
uint32_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_instInhabitedUInt32___closed__1;
x_2 = 0;
x_3 = lean_box(0);
x_4 = l_Array_empty___closed__1;
x_5 = lean_alloc_ctor(0, 4, 5);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_uint32(x_5, sizeof(void*)*4, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*4 + 4, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_instInhabitedEnvironment___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_instInhabitedEnvironment___closed__1;
x_2 = l_Lean_instInhabitedEnvironment___closed__3;
x_3 = l_Array_empty___closed__1;
x_4 = l_Lean_instInhabitedEnvironment___closed__4;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_instInhabitedEnvironment() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedEnvironment___closed__5;
return x_1;
}
}
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Environment_addAux___spec__4(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Name_hash(x_9);
x_12 = 1;
x_13 = x_1 - x_12;
x_14 = 5;
x_15 = x_14 * x_13;
x_16 = x_11 >> x_15;
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
x_19 = l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3(x_6, x_16, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_18;
x_6 = x_19;
goto _start;
}
}
}
lean_object* l_Array_modifyM___at_Lean_Environment_addAux___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_array_fget(x_1, x_2);
x_7 = lean_box(2);
x_8 = lean_array_fset(x_1, x_2, x_7);
x_9 = lean_apply_1(x_3, x_6);
x_10 = lean_array_fset(x_8, x_2, x_9);
return x_10;
}
}
}
lean_object* l_Array_modify___at_Lean_Environment_addAux___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_modifyM___at_Lean_Environment_addAux___spec__6(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Environment_addAux___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_name_eq(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_7)) {
case 0:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_name_eq(x_1, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_7);
x_12 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_9, x_10, x_1, x_2);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 0, x_1);
return x_7;
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = lean_name_eq(x_1, x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_14, x_15, x_1, x_2);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_14);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_2);
return x_19;
}
}
}
case 1:
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = x_3 >> x_4;
x_23 = x_5 + x_6;
x_24 = l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3(x_21, x_22, x_23, x_1, x_2);
lean_ctor_set(x_7, 0, x_24);
return x_7;
}
else
{
lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_7, 0);
lean_inc(x_25);
lean_dec(x_7);
x_26 = x_3 >> x_4;
x_27 = x_5 + x_6;
x_28 = l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3(x_25, x_26, x_27, x_1, x_2);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
default: 
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_2);
return x_30;
}
}
}
}
static lean_object* _init_l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 5;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___boxed__const__2() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_9 = x_2 & x_8;
x_10 = lean_usize_to_nat(x_9);
x_11 = lean_box_usize(x_2);
x_12 = l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___boxed__const__1;
x_13 = lean_box_usize(x_3);
x_14 = l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___boxed__const__2;
x_15 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___lambda__1___boxed), 7, 6);
lean_closure_set(x_15, 0, x_4);
lean_closure_set(x_15, 1, x_5);
lean_closure_set(x_15, 2, x_11);
lean_closure_set(x_15, 3, x_12);
lean_closure_set(x_15, 4, x_13);
lean_closure_set(x_15, 5, x_14);
x_16 = l_Array_modifyM___at_Lean_Environment_addAux___spec__6(x_7, x_10, x_15);
lean_dec(x_10);
lean_ctor_set(x_1, 0, x_16);
return x_1;
}
else
{
lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_19 = x_2 & x_18;
x_20 = lean_usize_to_nat(x_19);
x_21 = lean_box_usize(x_2);
x_22 = l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___boxed__const__1;
x_23 = lean_box_usize(x_3);
x_24 = l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___boxed__const__2;
x_25 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___lambda__1___boxed), 7, 6);
lean_closure_set(x_25, 0, x_4);
lean_closure_set(x_25, 1, x_5);
lean_closure_set(x_25, 2, x_21);
lean_closure_set(x_25, 3, x_22);
lean_closure_set(x_25, 4, x_23);
lean_closure_set(x_25, 5, x_24);
x_26 = l_Array_modifyM___at_Lean_Environment_addAux___spec__6(x_17, x_20, x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_1);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; size_t x_31; uint8_t x_32; 
x_29 = lean_unsigned_to_nat(0u);
x_30 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Environment_addAux___spec__7(x_1, x_29, x_4, x_5);
x_31 = 7;
x_32 = x_31 <= x_3;
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_30);
x_34 = lean_unsigned_to_nat(4u);
x_35 = lean_nat_dec_lt(x_33, x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_dec(x_30);
x_38 = l_Std_PersistentHashMap_insertAux___rarg___closed__3;
x_39 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Environment_addAux___spec__4(x_3, x_36, x_37, lean_box(0), x_29, x_38);
lean_dec(x_37);
lean_dec(x_36);
return x_39;
}
else
{
return x_30;
}
}
else
{
return x_30;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; uint8_t x_46; 
x_40 = lean_ctor_get(x_1, 0);
x_41 = lean_ctor_get(x_1, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_1);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_unsigned_to_nat(0u);
x_44 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Environment_addAux___spec__7(x_42, x_43, x_4, x_5);
x_45 = 7;
x_46 = x_45 <= x_3;
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_44);
x_48 = lean_unsigned_to_nat(4u);
x_49 = lean_nat_dec_lt(x_47, x_48);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_44, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
lean_dec(x_44);
x_52 = l_Std_PersistentHashMap_insertAux___rarg___closed__3;
x_53 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Environment_addAux___spec__4(x_3, x_50, x_51, lean_box(0), x_43, x_52);
lean_dec(x_51);
lean_dec(x_50);
return x_53;
}
else
{
return x_44;
}
}
else
{
return x_44;
}
}
}
}
}
lean_object* l_Std_PersistentHashMap_insert___at_Lean_Environment_addAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Name_hash(x_2);
x_8 = 1;
x_9 = l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3(x_5, x_7, x_8, x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = l_Lean_Name_hash(x_2);
x_15 = 1;
x_16 = l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3(x_12, x_14, x_15, x_2, x_3);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_13, x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
uint8_t l_Std_AssocList_contains___at_Lean_Environment_addAux___spec__9(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_name_eq(x_4, x_1);
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
lean_object* l_Std_AssocList_foldlM___at_Lean_Environment_addAux___spec__12(lean_object* x_1, lean_object* x_2) {
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
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_instHashableName___closed__1;
x_7 = l_Std_HashMapImp_reinsertAux___rarg(x_6, x_1, x_3, x_4);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Environment_addAux___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_foldlM___at_Lean_Environment_addAux___spec__12(x_3, x_6);
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
lean_object* l_Std_HashMapImp_expand___at_Lean_Environment_addAux___spec__10(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_HashMapImp_moveEntries___at_Lean_Environment_addAux___spec__11(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_Std_AssocList_replace___at_Lean_Environment_addAux___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_name_eq(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_AssocList_replace___at_Lean_Environment_addAux___spec__13(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_name_eq(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_AssocList_replace___at_Lean_Environment_addAux___spec__13(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
lean_object* l_Std_HashMapImp_insert___at_Lean_Environment_addAux___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_Std_AssocList_contains___at_Lean_Environment_addAux___spec__9(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = lean_nat_dec_le(x_13, x_7);
lean_dec(x_7);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_1);
x_17 = l_Std_HashMapImp_expand___at_Lean_Environment_addAux___spec__10(x_13, x_15);
return x_17;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = l_Std_AssocList_replace___at_Lean_Environment_addAux___spec__13(x_2, x_3, x_10);
x_19 = lean_array_uset(x_6, x_9, x_18);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_array_get_size(x_21);
x_23 = l_Lean_Name_hash(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_Std_AssocList_contains___at_Lean_Environment_addAux___spec__9(x_2, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_20, x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_array_uset(x_21, x_24, x_29);
x_31 = lean_nat_dec_le(x_28, x_22);
lean_dec(x_22);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Std_HashMapImp_expand___at_Lean_Environment_addAux___spec__10(x_28, x_30);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
x_34 = l_Std_AssocList_replace___at_Lean_Environment_addAux___spec__13(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
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
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Std_PersistentHashMap_insert___at_Lean_Environment_addAux___spec__2(x_6, x_2, x_3);
x_8 = 0;
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_8);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Std_PersistentHashMap_insert___at_Lean_Environment_addAux___spec__2(x_10, x_2, x_3);
x_12 = 0;
x_13 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = l_Std_HashMapImp_insert___at_Lean_Environment_addAux___spec__8(x_15, x_2, x_3);
x_17 = 1;
lean_ctor_set(x_1, 0, x_16);
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_17);
return x_1;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_20 = l_Std_HashMapImp_insert___at_Lean_Environment_addAux___spec__8(x_18, x_2, x_3);
x_21 = 1;
x_22 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_21);
return x_22;
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
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Environment_addAux___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Environment_addAux___spec__4(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_modifyM___at_Lean_Environment_addAux___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_modifyM___at_Lean_Environment_addAux___spec__6(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_modify___at_Lean_Environment_addAux___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_modify___at_Lean_Environment_addAux___spec__5(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___lambda__1(x_1, x_2, x_8, x_9, x_10, x_11, x_7);
return x_12;
}
}
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l_Std_AssocList_contains___at_Lean_Environment_addAux___spec__9___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___at_Lean_Environment_addAux___spec__9(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Environment_find_x3f___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_name_eq(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Environment_find_x3f___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = x_2 >> x_5;
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Std_PersistentHashMap_findAtAux___at_Lean_Environment_find_x3f___spec__4(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Environment_find_x3f___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Environment_find_x3f___spec__3(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_Environment_find_x3f___spec__6(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_name_eq(x_4, x_1);
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
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Std_AssocList_find_x3f___at_Lean_Environment_find_x3f___spec__6(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_SMap_find_x3f_x27___at_Lean_Environment_find_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Std_PersistentHashMap_find_x3f___at_Lean_Environment_find_x3f___spec__2(x_5, x_2);
x_7 = l_Std_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(x_4, x_2);
lean_dec(x_4);
if (lean_obj_tag(x_7) == 0)
{
return x_6;
}
else
{
uint8_t x_8; 
lean_dec(x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Std_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(x_11, x_2);
lean_dec(x_11);
return x_12;
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
x_4 = l_Lean_SMap_find_x3f_x27___at_Lean_Environment_find_x3f___spec__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Environment_find_x3f___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_Environment_find_x3f___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Environment_find_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Environment_find_x3f___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Environment_find_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_find_x3f___at_Lean_Environment_find_x3f___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_Environment_find_x3f___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_Environment_find_x3f___spec__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SMap_find_x3f_x27___at_Lean_Environment_find_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find_x3f_x27___at_Lean_Environment_find_x3f___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
uint8_t l_Std_HashMapImp_contains___at_Lean_Environment_contains___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Std_AssocList_contains___at_Lean_Environment_addAux___spec__9(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
uint8_t l_Std_PersistentHashMap_containsAtAux___at_Lean_Environment_contains___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_name_eq(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_4);
x_14 = 1;
return x_14;
}
}
}
}
uint8_t l_Std_PersistentHashMap_containsAux___at_Lean_Environment_contains___spec__4(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = x_2 >> x_5;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Std_PersistentHashMap_containsAtAux___at_Lean_Environment_contains___spec__5(x_17, x_18, lean_box(0), x_19, x_3);
lean_dec(x_18);
lean_dec(x_17);
return x_20;
}
}
}
uint8_t l_Std_PersistentHashMap_contains___at_Lean_Environment_contains___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_Std_PersistentHashMap_containsAux___at_Lean_Environment_contains___spec__4(x_3, x_4, x_2);
return x_5;
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
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Std_HashMapImp_contains___at_Lean_Environment_contains___spec__2(x_4, x_2);
lean_dec(x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l_Std_PersistentHashMap_contains___at_Lean_Environment_contains___spec__3(x_5, x_2);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_5);
x_8 = 1;
return x_8;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Std_HashMapImp_contains___at_Lean_Environment_contains___spec__2(x_9, x_2);
lean_dec(x_9);
return x_10;
}
}
}
uint8_t l_Lean_Environment_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_SMap_contains___at_Lean_Environment_contains___spec__1(x_3, x_2);
return x_4;
}
}
lean_object* l_Std_HashMapImp_contains___at_Lean_Environment_contains___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_HashMapImp_contains___at_Lean_Environment_contains___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_containsAtAux___at_Lean_Environment_contains___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Std_PersistentHashMap_containsAtAux___at_Lean_Environment_contains___spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Std_PersistentHashMap_containsAux___at_Lean_Environment_contains___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_containsAux___at_Lean_Environment_contains___spec__4(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_contains___at_Lean_Environment_contains___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_PersistentHashMap_contains___at_Lean_Environment_contains___spec__3(x_1, x_2);
lean_dec(x_2);
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
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
return x_3;
}
}
lean_object* l_Lean_Environment_allImportedModuleNames___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Environment_allImportedModuleNames(x_1);
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
uint32_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get_uint32(x_4, sizeof(void*)*4);
x_8 = lean_ctor_get_uint8(x_4, sizeof(void*)*4 + 4);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_4, 2);
x_11 = lean_ctor_get(x_4, 3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 4, 5);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_10);
lean_ctor_set(x_12, 3, x_11);
lean_ctor_set_uint32(x_12, sizeof(void*)*4, x_7);
lean_ctor_set_uint8(x_12, sizeof(void*)*4 + 4, x_8);
lean_ctor_set(x_1, 3, x_12);
return x_1;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint32_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_13 = lean_ctor_get(x_1, 3);
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_17 = lean_ctor_get_uint32(x_13, sizeof(void*)*4);
x_18 = lean_ctor_get_uint8(x_13, sizeof(void*)*4 + 4);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_13, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_13, 3);
lean_inc(x_21);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 x_22 = x_13;
} else {
 lean_dec_ref(x_13);
 x_22 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(0, 4, 5);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_21);
lean_ctor_set_uint32(x_23, sizeof(void*)*4, x_17);
lean_ctor_set_uint8(x_23, sizeof(void*)*4 + 4, x_18);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_15);
lean_ctor_set(x_24, 2, x_16);
lean_ctor_set(x_24, 3, x_23);
return x_24;
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
lean_ctor_set_uint8(x_3, sizeof(void*)*4 + 4, x_5);
return x_1;
}
else
{
uint32_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_6 = lean_ctor_get_uint32(x_3, sizeof(void*)*4);
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_3, 2);
x_10 = lean_ctor_get(x_3, 3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_11 = 1;
x_12 = lean_alloc_ctor(0, 4, 5);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_9);
lean_ctor_set(x_12, 3, x_10);
lean_ctor_set_uint32(x_12, sizeof(void*)*4, x_6);
lean_ctor_set_uint8(x_12, sizeof(void*)*4 + 4, x_11);
lean_ctor_set(x_1, 3, x_12);
return x_1;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint32_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_13 = lean_ctor_get(x_1, 3);
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_17 = lean_ctor_get_uint32(x_13, sizeof(void*)*4);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_13, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_13, 3);
lean_inc(x_21);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 x_22 = x_13;
} else {
 lean_dec_ref(x_13);
 x_22 = lean_box(0);
}
x_23 = 1;
if (lean_is_scalar(x_22)) {
 x_24 = lean_alloc_ctor(0, 4, 5);
} else {
 x_24 = x_22;
}
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_19);
lean_ctor_set(x_24, 2, x_20);
lean_ctor_set(x_24, 3, x_21);
lean_ctor_set_uint32(x_24, sizeof(void*)*4, x_17);
lean_ctor_set_uint8(x_24, sizeof(void*)*4 + 4, x_23);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_15);
lean_ctor_set(x_25, 2, x_16);
lean_ctor_set(x_25, 3, x_24);
return x_25;
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
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 4);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Environment_0__Lean_Environment_isQuotInit___boxed(lean_object* x_1) {
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
x_3 = lean_ctor_get_uint32(x_2, sizeof(void*)*4);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Environment_0__Lean_Environment_getTrustLevel___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_environment_trust_level(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_Environment_getModuleIdxFor_x3f___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_name_eq(x_4, x_1);
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
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Environment_getModuleIdxFor_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Std_AssocList_find_x3f___at_Lean_Environment_getModuleIdxFor_x3f___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Std_HashMapImp_find_x3f___at_Lean_Environment_getModuleIdxFor_x3f___spec__1(x_3, x_2);
return x_4;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_Environment_getModuleIdxFor_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_Environment_getModuleIdxFor_x3f___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Environment_getModuleIdxFor_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_find_x3f___at_Lean_Environment_getModuleIdxFor_x3f___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Environment_getModuleIdxFor_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Environment_getModuleIdxFor_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Environment_isConstructor_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 6)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
}
lean_object* l_Lean_Environment_isConstructor_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Environment_isConstructor_match__1___rarg), 3, 0);
return x_2;
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
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Environment_compileDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_compile_decl(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* l_Lean_instInhabitedEnvExtensionInterface___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_3);
return x_3;
}
}
static lean_object* _init_l_Lean_instInhabitedEnvExtensionInterface___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_empty___closed__1;
x_2 = lean_alloc_closure((void*)(l_EStateM_pure___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedEnvExtensionInterface___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instInhabitedEnvExtensionInterface___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedEnvExtensionInterface___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Id_instMonadId___closed__4;
x_2 = l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__8;
x_3 = l_Lean_instInhabitedEnvExtensionInterface___closed__2;
x_4 = l_instMonadControlReaderT___closed__2;
x_5 = l_Lean_instInhabitedEnvExtensionInterface___closed__1;
x_6 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_3);
lean_ctor_set(x_6, 4, x_4);
lean_ctor_set(x_6, 5, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_instInhabitedEnvExtensionInterface() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedEnvExtensionInterface___closed__3;
return x_1;
}
}
lean_object* l_Lean_instInhabitedEnvExtensionInterface___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_instInhabitedEnvExtensionInterface___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_instInhabitedError___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__2;
return x_2;
}
}
lean_object* l_IO_mkRef___at___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_mkEnvExtensionsRef___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_mk_ref(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_mkEnvExtensionsRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Array_empty___closed__1;
x_3 = l_IO_mkRef___at___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_mkEnvExtensionsRef___spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_1, 0);
x_7 = x_3;
x_8 = lean_array_set(x_5, x_6, x_7);
lean_ctor_set(x_2, 2, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_2, 3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
x_14 = x_3;
x_15 = lean_array_set(x_11, x_13, x_14);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_15);
lean_ctor_set(x_16, 3, x_12);
return x_16;
}
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_setState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_modifyM___at_Lean_EnvExtensionInterfaceUnsafe_modifyState___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_array_fget(x_1, x_2);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_1, x_2, x_7);
x_9 = lean_apply_1(x_3, x_6);
x_10 = lean_array_fset(x_8, x_2, x_9);
return x_10;
}
}
}
lean_object* l_Array_modify___at_Lean_EnvExtensionInterfaceUnsafe_modifyState___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_modifyM___at_Lean_EnvExtensionInterfaceUnsafe_modifyState___spec__2(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = x_2;
x_4 = lean_apply_1(x_1, x_3);
x_5 = x_4;
return x_5;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg___lambda__1), 2, 1);
lean_closure_set(x_7, 0, x_3);
x_8 = l_Array_modifyM___at_Lean_EnvExtensionInterfaceUnsafe_modifyState___spec__2(x_5, x_6, x_7);
lean_ctor_set(x_2, 2, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_2, 3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg___lambda__1), 2, 1);
lean_closure_set(x_14, 0, x_3);
x_15 = l_Array_modifyM___at_Lean_EnvExtensionInterfaceUnsafe_modifyState___spec__2(x_11, x_13, x_14);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_15);
lean_ctor_set(x_16, 3, x_12);
return x_16;
}
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_modifyState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Array_modifyM___at_Lean_EnvExtensionInterfaceUnsafe_modifyState___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_modifyM___at_Lean_EnvExtensionInterfaceUnsafe_modifyState___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_modify___at_Lean_EnvExtensionInterfaceUnsafe_modifyState___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_modify___at_Lean_EnvExtensionInterfaceUnsafe_modifyState___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 2);
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_instInhabitedEnvExtensionState;
x_6 = lean_array_get(x_5, x_3, x_4);
x_7 = x_6;
return x_7;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_4 = l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_envExtensionsRef;
x_5 = lean_st_ref_get(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_array_get_size(x_6);
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_1);
x_10 = lean_st_ref_take(x_4, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_9);
x_13 = x_9;
x_14 = lean_array_push(x_11, x_13);
x_15 = lean_st_ref_set(x_4, x_14, x_12);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to register environment, extensions can only be registered during initialization");
return x_1;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___closed__2;
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
x_10 = l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___closed__2;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___lambda__1(x_1, x_13, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_1);
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
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 < x_1;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = x_3;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_array_uget(x_3, x_2);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_3, x_2, x_9);
x_11 = x_8;
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_apply_1(x_12, x_4);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = x_2 + x_16;
x_18 = x_14;
x_19 = lean_array_uset(x_10, x_2, x_18);
x_2 = x_17;
x_3 = x_19;
x_4 = x_15;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_10);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_envExtensionsRef;
x_3 = lean_st_ref_get(x_2, x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_array_get_size(x_4);
x_7 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_8 = x_4;
x_9 = lean_box_usize(x_7);
x_10 = l_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates___boxed__const__1;
x_11 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates___spec__1___boxed), 4, 3);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_8);
x_12 = x_11;
x_13 = lean_apply_1(x_12, x_5);
return x_13;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Array_mapMUnsafe_map___at_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates___spec__1(x_5, x_6, x_3, x_4);
return x_7;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__1___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__3___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__4___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__4___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__2;
return x_3;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__5___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__4), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__3), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__1;
x_2 = l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__2;
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__3;
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__4;
x_5 = l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__5;
x_6 = l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__6;
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
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_imp() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__7;
return x_1;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__1___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__3___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__5(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__1(lean_object* x_1) {
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
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceImp___elambda__2___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceImp___elambda__3___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__4___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceImp___elambda__4___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__5___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceImp___elambda__5___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__6___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceImp___elambda__6___rarg___boxed), 1, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceImp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceImp___elambda__6), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceImp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceImp___elambda__5), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceImp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceImp___elambda__4___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceImp___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceImp___elambda__3___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceImp___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceImp___elambda__2), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceImp___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceImp___elambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceImp___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_EnvExtensionInterfaceImp___closed__1;
x_2 = l_Lean_EnvExtensionInterfaceImp___closed__2;
x_3 = l_Lean_EnvExtensionInterfaceImp___closed__3;
x_4 = l_Lean_EnvExtensionInterfaceImp___closed__4;
x_5 = l_Lean_EnvExtensionInterfaceImp___closed__5;
x_6 = l_Lean_EnvExtensionInterfaceImp___closed__6;
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
static lean_object* _init_l_Lean_EnvExtensionInterfaceImp() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_EnvExtensionInterfaceImp___closed__7;
return x_1;
}
}
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EnvExtensionInterfaceImp___elambda__2___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__3___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EnvExtensionInterfaceImp___elambda__3___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EnvExtensionInterfaceImp___elambda__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__4___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EnvExtensionInterfaceImp___elambda__4___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EnvExtensionInterfaceImp___elambda__4(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__6___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_EnvExtensionInterfaceImp___elambda__6___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_EnvExtension_instInhabitedEnvExtension(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__2;
return x_3;
}
}
lean_object* l_Lean_EnvExtension_instInhabitedEnvExtension___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EnvExtension_instInhabitedEnvExtension(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_EnvExtension_setState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_EnvExtension_setState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_EnvExtension_setState___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_EnvExtension_setState___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnvExtension_setState___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_EnvExtension_modifyState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_EnvExtension_modifyState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_EnvExtension_modifyState___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_EnvExtension_modifyState___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnvExtension_modifyState___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_EnvExtension_getState___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_1, x_2);
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
lean_object* l_Lean_registerEnvExtension___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_registerEnvExtension(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_registerEnvExtension___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Environment_0__Lean_mkInitialExtensionStates(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkEmptyEnvironment___lambda__1___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Std_HashMap_instInhabitedHashMap___closed__1;
x_3 = l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* l_Lean_mkEmptyEnvironment___lambda__1(uint32_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates(x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = 0;
x_8 = lean_box(0);
x_9 = l_Array_empty___closed__1;
x_10 = lean_alloc_ctor(0, 4, 5);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_9);
lean_ctor_set(x_10, 3, x_9);
lean_ctor_set_uint32(x_10, sizeof(void*)*4, x_1);
lean_ctor_set_uint8(x_10, sizeof(void*)*4 + 4, x_7);
x_11 = l_Std_HashMap_instInhabitedHashMap___closed__1;
x_12 = l_Lean_mkEmptyEnvironment___lambda__1___closed__1;
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_6);
lean_ctor_set(x_13, 3, x_10);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_16 = 0;
x_17 = lean_box(0);
x_18 = l_Array_empty___closed__1;
x_19 = lean_alloc_ctor(0, 4, 5);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set(x_19, 3, x_18);
lean_ctor_set_uint32(x_19, sizeof(void*)*4, x_1);
lean_ctor_set_uint8(x_19, sizeof(void*)*4 + 4, x_16);
x_20 = l_Std_HashMap_instInhabitedHashMap___closed__1;
x_21 = l_Lean_mkEmptyEnvironment___lambda__1___closed__1;
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_14);
lean_ctor_set(x_22, 3, x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_15);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_4);
if (x_24 == 0)
{
return x_4;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_4, 0);
x_26 = lean_ctor_get(x_4, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_4);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
static lean_object* _init_l_Lean_mkEmptyEnvironment___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("environment objects cannot be created during initialization");
return x_1;
}
}
static lean_object* _init_l_Lean_mkEmptyEnvironment___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkEmptyEnvironment___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = l_Lean_mkEmptyEnvironment___lambda__1(x_1, x_7, x_6);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_3, 0);
lean_dec(x_10);
x_11 = l_Lean_mkEmptyEnvironment___closed__2;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l_Lean_mkEmptyEnvironment___closed__2;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
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
lean_object* l_Lean_mkEmptyEnvironment___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_5 = l_Lean_mkEmptyEnvironment___lambda__1(x_4, x_2, x_3);
lean_dec(x_2);
return x_5;
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
static lean_object* _init_l_Lean_EnvExtensionEntrySpec() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedEnvExtensionEntry() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___rarg(lean_object* x_1) {
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
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instInhabitedPersistentEnvExtensionState___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_instInhabitedPersistentEnvExtension___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_IO_instInhabitedError___closed__1;
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_instInhabitedPersistentEnvExtension___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_empty___closed__1;
return x_2;
}
}
lean_object* l_Lean_instInhabitedPersistentEnvExtension___lambda__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedPersistentEnvExtension___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instInhabitedPersistentEnvExtension___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedPersistentEnvExtension___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Monad_seqRight___default___rarg___lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedPersistentEnvExtension___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instInhabitedPersistentEnvExtension___lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedPersistentEnvExtension___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instInhabitedPersistentEnvExtension___lambda__3___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedPersistentEnvExtension___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__2;
x_2 = lean_box(0);
x_3 = l_Lean_instInhabitedPersistentEnvExtension___closed__1;
x_4 = l_Lean_instInhabitedPersistentEnvExtension___closed__2;
x_5 = l_Lean_instInhabitedPersistentEnvExtension___closed__3;
x_6 = l_Lean_instInhabitedPersistentEnvExtension___closed__4;
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
lean_object* l_Lean_instInhabitedPersistentEnvExtension(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_instInhabitedPersistentEnvExtension___closed__5;
return x_5;
}
}
lean_object* l_Lean_instInhabitedPersistentEnvExtension___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instInhabitedPersistentEnvExtension___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_instInhabitedPersistentEnvExtension___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instInhabitedPersistentEnvExtension___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_instInhabitedPersistentEnvExtension___lambda__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instInhabitedPersistentEnvExtension___lambda__3(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_instInhabitedPersistentEnvExtension___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_instInhabitedPersistentEnvExtension(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_4, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Array_empty___closed__1;
x_8 = lean_array_get(x_7, x_6, x_3);
lean_dec(x_6);
return x_8;
}
}
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentEnvExtension_getModuleEntries___rarg___boxed), 3, 0);
return x_4;
}
}
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentEnvExtension_getModuleEntries___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_apply_2(x_4, x_6, x_2);
lean_ctor_set(x_3, 1, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_apply_2(x_4, x_9, x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l_Lean_PersistentEnvExtension_addEntry___rarg___lambda__1), 3, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_3);
x_6 = l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg(x_4, x_2, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_PersistentEnvExtension_addEntry(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentEnvExtension_addEntry___rarg), 3, 0);
return x_4;
}
}
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_3, x_2);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Lean_PersistentEnvExtension_getState(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentEnvExtension_getState___rarg___boxed), 2, 0);
return x_4;
}
}
lean_object* l_Lean_PersistentEnvExtension_getState___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentEnvExtension_getState___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_PersistentEnvExtension_setState___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_PersistentEnvExtension_setState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_alloc_closure((void*)(l_Lean_PersistentEnvExtension_setState___rarg___lambda__1), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg(x_4, x_2, x_5);
return x_6;
}
}
lean_object* l_Lean_PersistentEnvExtension_setState(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentEnvExtension_setState___rarg___boxed), 3, 0);
return x_4;
}
}
lean_object* l_Lean_PersistentEnvExtension_setState___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentEnvExtension_setState___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_PersistentEnvExtension_modifyState___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_PersistentEnvExtension_modifyState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_alloc_closure((void*)(l_Lean_PersistentEnvExtension_modifyState___rarg___lambda__1), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg(x_4, x_2, x_5);
return x_6;
}
}
lean_object* l_Lean_PersistentEnvExtension_modifyState(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentEnvExtension_modifyState___rarg___boxed), 3, 0);
return x_4;
}
}
lean_object* l_Lean_PersistentEnvExtension_modifyState___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentEnvExtension_modifyState___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_IO_mkRef___at_Lean_initFn____x40_Lean_Environment___hyg_1088____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_mk_ref(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_1088_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Array_empty___closed__1;
x_3 = l_IO_mkRef___at_Lean_initFn____x40_Lean_Environment___hyg_1088____spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_PersistentEnvExtensionDescr_statsFn___default(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
lean_object* l_Lean_PersistentEnvExtensionDescr_statsFn___default___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentEnvExtensionDescr_statsFn___default(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Array_empty___closed__1;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__1), 2, 0);
return x_1;
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 5);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2___closed__1;
x_11 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_11, 0, x_5);
lean_closure_set(x_11, 1, x_10);
x_12 = l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(x_11, x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_4);
lean_ctor_set(x_15, 2, x_6);
lean_ctor_set(x_15, 3, x_7);
lean_ctor_set(x_15, 4, x_8);
lean_ctor_set(x_15, 5, x_9);
x_16 = l_Lean_persistentEnvExtensionsRef;
x_17 = lean_st_ref_take(x_16, x_14);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_15);
x_20 = x_15;
x_21 = lean_array_push(x_18, x_20);
x_22 = lean_st_ref_set(x_16, x_21, x_19);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_15);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_12);
if (x_27 == 0)
{
return x_12;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_12, 0);
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_12);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
uint8_t l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_name_eq(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid environment extension, '");
return x_1;
}
}
static lean_object* _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has already been used");
return x_1;
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_persistentEnvExtensionsRef;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__3___boxed), 2, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_array_get_size(x_6);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_anyMUnsafe___at_Array_any___spec__1___rarg(x_8, x_6, x_10, x_9);
lean_dec(x_9);
lean_dec(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_4);
x_12 = lean_box(0);
x_13 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_12, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_Name_toString___closed__1;
x_16 = l_Lean_Name_toStringWithSep(x_15, x_14);
x_17 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_21);
return x_4;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_4);
lean_inc(x_1);
x_24 = lean_alloc_closure((void*)(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__3___boxed), 2, 1);
lean_closure_set(x_24, 0, x_1);
x_25 = lean_array_get_size(x_22);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Array_anyMUnsafe___at_Array_any___spec__1___rarg(x_24, x_22, x_26, x_25);
lean_dec(x_25);
lean_dec(x_22);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_28, x_23);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
lean_dec(x_1);
x_31 = l_Lean_Name_toString___closed__1;
x_32 = l_Lean_Name_toStringWithSep(x_31, x_30);
x_33 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_34 = lean_string_append(x_33, x_32);
lean_dec(x_32);
x_35 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_23);
return x_38;
}
}
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_registerPersistentEnvExtensionUnsafe___rarg), 2, 0);
return x_5;
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_registerPersistentEnvExtensionUnsafe(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Lean_registerPersistentEnvExtension___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_instInhabitedError___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_registerPersistentEnvExtension(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_registerPersistentEnvExtension___rarg), 1, 0);
return x_6;
}
}
lean_object* l_Lean_registerPersistentEnvExtension___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_registerPersistentEnvExtension(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_mkStateFromImportedEntries___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_foldlMUnsafe___at_Array_foldl___spec__1___rarg(x_1, x_2, x_3, x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_mkStateFromImportedEntries___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_alloc_closure((void*)(l_Lean_mkStateFromImportedEntries___rarg___lambda__1___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_array_get_size(x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_foldlMUnsafe___at_Array_foldl___spec__1___rarg(x_4, x_2, x_3, x_6, x_5);
lean_dec(x_5);
return x_7;
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
lean_object* l_Lean_mkStateFromImportedEntries___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkStateFromImportedEntries___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
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
lean_object* l_Lean_SimplePersistentEnvExtensionDescr_toArrayFn___default___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_List_redLength___rarg(x_1);
x_3 = lean_mk_empty_array_with_capacity(x_2);
lean_dec(x_2);
x_4 = l_List_toArrayAux___rarg(x_1, x_3);
return x_4;
}
}
lean_object* l_Lean_SimplePersistentEnvExtensionDescr_toArrayFn___default(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtensionDescr_toArrayFn___default___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_registerSimplePersistentEnvExtension_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_registerSimplePersistentEnvExtension_match__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension_match__1___rarg), 2, 0);
return x_4;
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_persistentEnvExtensionsRef;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__3___boxed), 2, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_array_get_size(x_6);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_anyMUnsafe___at_Array_any___spec__1___rarg(x_8, x_6, x_10, x_9);
lean_dec(x_9);
lean_dec(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_4);
x_12 = lean_box(0);
x_13 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_12, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_Name_toString___closed__1;
x_16 = l_Lean_Name_toStringWithSep(x_15, x_14);
x_17 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_21);
return x_4;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_4);
lean_inc(x_1);
x_24 = lean_alloc_closure((void*)(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__3___boxed), 2, 1);
lean_closure_set(x_24, 0, x_1);
x_25 = lean_array_get_size(x_22);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Array_anyMUnsafe___at_Array_any___spec__1___rarg(x_24, x_22, x_26, x_25);
lean_dec(x_25);
lean_dec(x_22);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_28, x_23);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
lean_dec(x_1);
x_31 = l_Lean_Name_toString___closed__1;
x_32 = l_Lean_Name_toStringWithSep(x_31, x_30);
x_33 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_34 = lean_string_append(x_33, x_32);
lean_dec(x_32);
x_35 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_23);
return x_38;
}
}
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__1___rarg), 2, 0);
return x_4;
}
}
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_apply_1(x_1, x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
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
static lean_object* _init_l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("number of local entries: ");
return x_1;
}
}
static lean_object* _init_l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__2() {
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_lengthAux___rarg(x_2, x_3);
x_5 = l_Nat_repr(x_4);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__2;
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1() {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_box(0);
x_7 = l_Array_empty___closed__1;
lean_inc(x_5);
x_8 = lean_apply_1(x_5, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_closure((void*)(l_EStateM_pure___rarg), 2, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1___boxed), 5, 2);
lean_closure_set(x_11, 0, x_5);
lean_closure_set(x_11, 1, x_6);
lean_inc(x_2);
x_12 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__2), 3, 1);
lean_closure_set(x_12, 0, x_2);
x_13 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__3), 2, 1);
lean_closure_set(x_13, 0, x_2);
x_14 = l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1;
x_15 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_11);
lean_ctor_set(x_15, 3, x_12);
lean_ctor_set(x_15, 4, x_13);
lean_ctor_set(x_15, 5, x_14);
x_16 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__1___rarg(x_15, x_3);
return x_16;
}
}
lean_object* l_Lean_registerSimplePersistentEnvExtension(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
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
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_registerSimplePersistentEnvExtension___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_SimplePersistentEnvExtension_instInhabitedSimplePersistentEnvExtension___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
x_4 = l_Lean_instInhabitedPersistentEnvExtension(lean_box(0), lean_box(0), lean_box(0), x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_SimplePersistentEnvExtension_instInhabitedSimplePersistentEnvExtension(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_instInhabitedSimplePersistentEnvExtension___rarg), 1, 0);
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
lean_dec(x_1);
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
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SimplePersistentEnvExtension_setState_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_SimplePersistentEnvExtension_setState_match__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_setState_match__1___rarg), 2, 0);
return x_4;
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
x_3 = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_setState___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Lean_SimplePersistentEnvExtension_setState___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_SimplePersistentEnvExtension_setState___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_SimplePersistentEnvExtension_modifyState_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_SimplePersistentEnvExtension_modifyState_match__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_modifyState_match__1___rarg), 2, 0);
return x_4;
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
x_3 = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_modifyState___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_SimplePersistentEnvExtension_modifyState___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_qpartition_loop___at_Lean_mkTagDeclarationExtension___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_array_swap(x_4, x_5, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = l_Lean_instInhabitedName;
x_11 = lean_array_get(x_10, x_4, x_6);
lean_inc(x_1);
lean_inc(x_3);
x_12 = lean_apply_2(x_1, x_11, x_3);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_6 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_swap(x_4, x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
x_4 = x_17;
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
}
lean_object* l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_3, x_4);
if (x_14 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_15 = lean_nat_add(x_3, x_4);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_nat_div(x_15, x_16);
lean_dec(x_15);
x_41 = l_Lean_instInhabitedName;
x_42 = lean_array_get(x_41, x_2, x_17);
x_43 = lean_array_get(x_41, x_2, x_3);
lean_inc(x_1);
x_44 = lean_apply_2(x_1, x_42, x_43);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
x_18 = x_2;
goto block_40;
}
else
{
lean_object* x_46; 
x_46 = lean_array_swap(x_2, x_3, x_17);
x_18 = x_46;
goto block_40;
}
block_40:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = l_Lean_instInhabitedName;
x_20 = lean_array_get(x_19, x_18, x_4);
x_21 = lean_array_get(x_19, x_18, x_3);
lean_inc(x_1);
lean_inc(x_20);
x_22 = lean_apply_2(x_1, x_20, x_21);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_array_get(x_19, x_18, x_17);
lean_inc(x_1);
lean_inc(x_20);
x_25 = lean_apply_2(x_1, x_24, x_20);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_17);
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_27 = l_Array_qpartition_loop___at_Lean_mkTagDeclarationExtension___spec__3(x_1, x_4, x_20, x_18, x_3, x_3);
x_5 = x_27;
goto block_13;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_20);
x_28 = lean_array_swap(x_18, x_17, x_4);
lean_dec(x_17);
x_29 = lean_array_get(x_19, x_28, x_4);
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_30 = l_Array_qpartition_loop___at_Lean_mkTagDeclarationExtension___spec__3(x_1, x_4, x_29, x_28, x_3, x_3);
x_5 = x_30;
goto block_13;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_20);
x_31 = lean_array_swap(x_18, x_3, x_4);
x_32 = lean_array_get(x_19, x_31, x_17);
x_33 = lean_array_get(x_19, x_31, x_4);
lean_inc(x_1);
lean_inc(x_33);
x_34 = lean_apply_2(x_1, x_32, x_33);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_17);
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_36 = l_Array_qpartition_loop___at_Lean_mkTagDeclarationExtension___spec__3(x_1, x_4, x_33, x_31, x_3, x_3);
x_5 = x_36;
goto block_13;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_33);
x_37 = lean_array_swap(x_31, x_17, x_4);
lean_dec(x_17);
x_38 = lean_array_get(x_19, x_37, x_4);
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_39 = l_Array_qpartition_loop___at_Lean_mkTagDeclarationExtension___spec__3(x_1, x_4, x_38, x_37, x_3, x_3);
x_5 = x_39;
goto block_13;
}
}
}
}
block_13:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_nat_dec_le(x_4, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_9 = l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__2(x_1, x_7, x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
x_2 = x_9;
x_3 = x_11;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
}
}
lean_object* l_Array_qsort___at_Lean_mkTagDeclarationExtension___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__2(x_2, x_1, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkTagDeclarationExtension___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_persistentEnvExtensionsRef;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__3___boxed), 2, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_array_get_size(x_6);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_anyMUnsafe___at_Array_any___spec__1___rarg(x_8, x_6, x_10, x_9);
lean_dec(x_9);
lean_dec(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_4);
x_12 = lean_box(0);
x_13 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_12, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_Name_toString___closed__1;
x_16 = l_Lean_Name_toStringWithSep(x_15, x_14);
x_17 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_21);
return x_4;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_4);
lean_inc(x_1);
x_24 = lean_alloc_closure((void*)(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__3___boxed), 2, 1);
lean_closure_set(x_24, 0, x_1);
x_25 = lean_array_get_size(x_22);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Array_anyMUnsafe___at_Array_any___spec__1___rarg(x_24, x_22, x_26, x_25);
lean_dec(x_25);
lean_dec(x_22);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_28, x_23);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
lean_dec(x_1);
x_31 = l_Lean_Name_toString___closed__1;
x_32 = l_Lean_Name_toStringWithSep(x_31, x_30);
x_33 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_34 = lean_string_append(x_33, x_32);
lean_dec(x_32);
x_35 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_23);
return x_38;
}
}
}
}
lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_mkTagDeclarationExtension___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_box(0);
x_6 = l_Array_empty___closed__1;
lean_inc(x_4);
x_7 = lean_apply_1(x_4, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_closure((void*)(l_EStateM_pure___rarg), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1___boxed), 5, 2);
lean_closure_set(x_10, 0, x_4);
lean_closure_set(x_10, 1, x_5);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__2), 3, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__3), 2, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1;
x_14 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_10);
lean_ctor_set(x_14, 3, x_11);
lean_ctor_set(x_14, 4, x_12);
lean_ctor_set(x_14, 5, x_13);
x_15 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkTagDeclarationExtension___spec__5(x_14, x_2);
return x_15;
}
}
lean_object* l_Lean_mkTagDeclarationExtension___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_NameSet_insert___closed__1;
x_4 = lean_box(0);
x_5 = l_Std_RBNode_insert___rarg(x_3, x_1, x_2, x_4);
return x_5;
}
}
lean_object* l_Lean_mkTagDeclarationExtension___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_NameSet_empty;
return x_2;
}
}
lean_object* l_Lean_mkTagDeclarationExtension___lambda__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = l_List_redLength___rarg(x_1);
x_3 = lean_mk_empty_array_with_capacity(x_2);
lean_dec(x_2);
x_4 = l_List_toArrayAux___rarg(x_1, x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_5, x_6);
lean_dec(x_5);
x_8 = l_Lean_NameSet_insert___closed__1;
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__2(x_8, x_4, x_9, x_7);
lean_dec(x_7);
return x_10;
}
}
static lean_object* _init_l_Lean_mkTagDeclarationExtension___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_mkTagDeclarationExtension___lambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_mkTagDeclarationExtension___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_mkTagDeclarationExtension___lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_mkTagDeclarationExtension___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_mkTagDeclarationExtension___lambda__3), 1, 0);
return x_1;
}
}
lean_object* l_Lean_mkTagDeclarationExtension(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_mkTagDeclarationExtension___closed__1;
x_4 = l_Lean_mkTagDeclarationExtension___closed__2;
x_5 = l_Lean_mkTagDeclarationExtension___closed__3;
x_6 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_5);
x_7 = l_Lean_registerSimplePersistentEnvExtension___at_Lean_mkTagDeclarationExtension___spec__4(x_6, x_2);
return x_7;
}
}
lean_object* l_Array_qpartition_loop___at_Lean_mkTagDeclarationExtension___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qpartition_loop___at_Lean_mkTagDeclarationExtension___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Array_qsort___at_Lean_mkTagDeclarationExtension___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_qsort___at_Lean_mkTagDeclarationExtension___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Lean_mkTagDeclarationExtension___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkTagDeclarationExtension___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_instInhabitedTagDeclarationExtension___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_NameSet_instInhabitedNameSet;
x_2 = l_Lean_SimplePersistentEnvExtension_instInhabitedSimplePersistentEnvExtension___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_instInhabitedTagDeclarationExtension() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_TagDeclarationExtension_instInhabitedTagDeclarationExtension___closed__1;
return x_1;
}
}
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_TagDeclarationExtension_isTagged_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_TagDeclarationExtension_isTagged_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_TagDeclarationExtension_isTagged_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Array_binSearchAux___at_Lean_TagDeclarationExtension_isTagged___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_nat_add(x_4, x_5);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_nat_div(x_8, x_9);
lean_dec(x_8);
x_11 = l_Lean_instInhabitedName;
x_12 = lean_array_get(x_11, x_2, x_10);
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_12);
x_13 = lean_apply_2(x_1, x_12, x_3);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_5);
lean_inc(x_1);
lean_inc(x_3);
x_15 = lean_apply_2(x_1, x_3, x_12);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_17 = 1;
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_10, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_10, x_20);
lean_dec(x_10);
x_5 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = 0;
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
lean_dec(x_4);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_10, x_24);
lean_dec(x_10);
x_4 = x_25;
goto _start;
}
}
}
}
uint8_t l_Array_binSearchAux___at_Lean_TagDeclarationExtension_isTagged___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_nat_add(x_4, x_5);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_nat_div(x_8, x_9);
lean_dec(x_8);
x_11 = l_Lean_instInhabitedName;
x_12 = lean_array_get(x_11, x_2, x_10);
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_12);
x_13 = lean_apply_2(x_1, x_12, x_3);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_5);
lean_inc(x_1);
lean_inc(x_3);
x_15 = lean_apply_2(x_1, x_3, x_12);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_17 = 1;
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_10, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_10, x_20);
lean_dec(x_10);
x_5 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = 0;
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
lean_dec(x_4);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_10, x_24);
lean_dec(x_10);
x_4 = x_25;
goto _start;
}
}
}
}
uint8_t l_Array_binSearchContains___at_Lean_TagDeclarationExtension_isTagged___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_5, x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_5);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_6, x_10);
lean_dec(x_6);
x_12 = l_Array_binSearchAux___at_Lean_TagDeclarationExtension_isTagged___spec__2(x_3, x_1, x_2, x_4, x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = l_Array_binSearchAux___at_Lean_TagDeclarationExtension_isTagged___spec__3(x_3, x_1, x_2, x_4, x_5);
return x_13;
}
}
}
}
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_getModuleIdxFor_x3f(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_1, x_2);
x_6 = l_Lean_NameSet_contains(x_5, x_3);
lean_dec(x_3);
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = l_Lean_PersistentEnvExtension_getModuleEntries___rarg(x_1, x_2, x_7);
lean_dec(x_7);
x_9 = lean_array_get_size(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_9, x_10);
lean_dec(x_9);
x_12 = l_Lean_NameSet_insert___closed__1;
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_binSearchContains___at_Lean_TagDeclarationExtension_isTagged___spec__1(x_8, x_3, x_12, x_13, x_11);
lean_dec(x_8);
return x_14;
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_TagDeclarationExtension_isTagged___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_binSearchAux___at_Lean_TagDeclarationExtension_isTagged___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_binSearchAux___at_Lean_TagDeclarationExtension_isTagged___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_binSearchAux___at_Lean_TagDeclarationExtension_isTagged___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_binSearchContains___at_Lean_TagDeclarationExtension_isTagged___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_binSearchContains___at_Lean_TagDeclarationExtension_isTagged___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_TagDeclarationExtension_isTagged___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_TagDeclarationExtension_isTagged(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_instInhabitedName;
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_1);
x_10 = lean_nat_dec_lt(x_7, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_array_swap(x_5, x_6, x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_array_get(x_9, x_5, x_7);
lean_inc(x_2);
lean_inc(x_4);
x_14 = lean_apply_2(x_2, x_13, x_4);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_7, x_16);
lean_dec(x_7);
x_7 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_array_swap(x_5, x_6, x_7);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_6, x_20);
lean_dec(x_6);
x_22 = lean_nat_add(x_7, x_20);
lean_dec(x_7);
x_5 = x_19;
x_6 = x_21;
x_7 = x_22;
goto _start;
}
}
}
}
lean_object* l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__3___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_instInhabitedName;
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_1);
x_10 = lean_nat_dec_lt(x_7, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_array_swap(x_5, x_6, x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_array_get(x_9, x_5, x_7);
lean_inc(x_2);
lean_inc(x_4);
x_14 = lean_apply_2(x_2, x_13, x_4);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_7, x_16);
lean_dec(x_7);
x_7 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_array_swap(x_5, x_6, x_7);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_6, x_20);
lean_dec(x_6);
x_22 = lean_nat_add(x_7, x_20);
lean_dec(x_7);
x_5 = x_19;
x_6 = x_21;
x_7 = x_22;
goto _start;
}
}
}
}
lean_object* l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__4___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_instInhabitedName;
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_1);
x_10 = lean_nat_dec_lt(x_7, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_array_swap(x_5, x_6, x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_array_get(x_9, x_5, x_7);
lean_inc(x_2);
lean_inc(x_4);
x_14 = lean_apply_2(x_2, x_13, x_4);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_7, x_16);
lean_dec(x_7);
x_7 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_array_swap(x_5, x_6, x_7);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_6, x_20);
lean_dec(x_6);
x_22 = lean_nat_add(x_7, x_20);
lean_dec(x_7);
x_5 = x_19;
x_6 = x_21;
x_7 = x_22;
goto _start;
}
}
}
}
lean_object* l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__5___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_instInhabitedName;
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_1);
x_10 = lean_nat_dec_lt(x_7, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_array_swap(x_5, x_6, x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_array_get(x_9, x_5, x_7);
lean_inc(x_2);
lean_inc(x_4);
x_14 = lean_apply_2(x_2, x_13, x_4);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_7, x_16);
lean_dec(x_7);
x_7 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_array_swap(x_5, x_6, x_7);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_6, x_20);
lean_dec(x_6);
x_22 = lean_nat_add(x_7, x_20);
lean_dec(x_7);
x_5 = x_19;
x_6 = x_21;
x_7 = x_22;
goto _start;
}
}
}
}
lean_object* l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__6___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_17; 
x_6 = l_Lean_instInhabitedName;
lean_inc(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_1);
x_17 = lean_nat_dec_lt(x_4, x_5);
if (x_17 == 0)
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_18 = lean_nat_add(x_4, x_5);
x_19 = lean_unsigned_to_nat(2u);
x_20 = lean_nat_div(x_18, x_19);
lean_dec(x_18);
lean_inc(x_7);
x_43 = lean_array_get(x_7, x_3, x_20);
lean_inc(x_7);
x_44 = lean_array_get(x_7, x_3, x_4);
lean_inc(x_2);
x_45 = lean_apply_2(x_2, x_43, x_44);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
x_21 = x_3;
goto block_42;
}
else
{
lean_object* x_47; 
x_47 = lean_array_swap(x_3, x_4, x_20);
x_21 = x_47;
goto block_42;
}
block_42:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_inc(x_7);
x_22 = lean_array_get(x_7, x_21, x_5);
lean_inc(x_7);
x_23 = lean_array_get(x_7, x_21, x_4);
lean_inc(x_2);
lean_inc(x_22);
x_24 = lean_apply_2(x_2, x_22, x_23);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_inc(x_7);
x_26 = lean_array_get(x_7, x_21, x_20);
lean_inc(x_2);
lean_inc(x_22);
x_27 = lean_apply_2(x_2, x_26, x_22);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_20);
lean_dec(x_7);
lean_inc_n(x_4, 2);
lean_inc(x_2);
lean_inc(x_1);
x_29 = l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__3___rarg(x_1, x_2, x_5, x_22, x_21, x_4, x_4);
x_8 = x_29;
goto block_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_22);
x_30 = lean_array_swap(x_21, x_20, x_5);
lean_dec(x_20);
x_31 = lean_array_get(x_7, x_30, x_5);
lean_inc_n(x_4, 2);
lean_inc(x_2);
lean_inc(x_1);
x_32 = l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__4___rarg(x_1, x_2, x_5, x_31, x_30, x_4, x_4);
x_8 = x_32;
goto block_16;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_22);
x_33 = lean_array_swap(x_21, x_4, x_5);
lean_inc(x_7);
x_34 = lean_array_get(x_7, x_33, x_20);
lean_inc(x_7);
x_35 = lean_array_get(x_7, x_33, x_5);
lean_inc(x_2);
lean_inc(x_35);
x_36 = lean_apply_2(x_2, x_34, x_35);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_20);
lean_dec(x_7);
lean_inc_n(x_4, 2);
lean_inc(x_2);
lean_inc(x_1);
x_38 = l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__5___rarg(x_1, x_2, x_5, x_35, x_33, x_4, x_4);
x_8 = x_38;
goto block_16;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_35);
x_39 = lean_array_swap(x_33, x_20, x_5);
lean_dec(x_20);
x_40 = lean_array_get(x_7, x_39, x_5);
lean_inc_n(x_4, 2);
lean_inc(x_2);
lean_inc(x_1);
x_41 = l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__6___rarg(x_1, x_2, x_5, x_40, x_39, x_4, x_4);
x_8 = x_41;
goto block_16;
}
}
}
}
block_16:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_nat_dec_le(x_5, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__2___rarg(x_1, x_2, x_10, x_4, x_9);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_9, x_13);
lean_dec(x_9);
x_3 = x_12;
x_4 = x_14;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
}
}
lean_object* l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__2___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_qsort___at_Lean_mkMapDeclarationExtension___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__2___rarg(x_1, x_3, x_2, x_4, x_5);
return x_6;
}
}
lean_object* l_Array_qsort___at_Lean_mkMapDeclarationExtension___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_qsort___at_Lean_mkMapDeclarationExtension___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkMapDeclarationExtension___spec__8___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_persistentEnvExtensionsRef;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__3___boxed), 2, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_array_get_size(x_6);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_anyMUnsafe___at_Array_any___spec__1___rarg(x_8, x_6, x_10, x_9);
lean_dec(x_9);
lean_dec(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_4);
x_12 = lean_box(0);
x_13 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_12, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_Name_toString___closed__1;
x_16 = l_Lean_Name_toStringWithSep(x_15, x_14);
x_17 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_21);
return x_4;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_4);
lean_inc(x_1);
x_24 = lean_alloc_closure((void*)(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__3___boxed), 2, 1);
lean_closure_set(x_24, 0, x_1);
x_25 = lean_array_get_size(x_22);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Array_anyMUnsafe___at_Array_any___spec__1___rarg(x_24, x_22, x_26, x_25);
lean_dec(x_25);
lean_dec(x_22);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_28, x_23);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
lean_dec(x_1);
x_31 = l_Lean_Name_toString___closed__1;
x_32 = l_Lean_Name_toStringWithSep(x_31, x_30);
x_33 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_34 = lean_string_append(x_33, x_32);
lean_dec(x_32);
x_35 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_23);
return x_38;
}
}
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkMapDeclarationExtension___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkMapDeclarationExtension___spec__8___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_mkMapDeclarationExtension___spec__7___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_box(0);
x_6 = l_Array_empty___closed__1;
lean_inc(x_4);
x_7 = lean_apply_1(x_4, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_closure((void*)(l_EStateM_pure___rarg), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1___boxed), 5, 2);
lean_closure_set(x_10, 0, x_4);
lean_closure_set(x_10, 1, x_5);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__2), 3, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__3), 2, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1;
x_14 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_10);
lean_ctor_set(x_14, 3, x_11);
lean_ctor_set(x_14, 4, x_12);
lean_ctor_set(x_14, 5, x_13);
x_15 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkMapDeclarationExtension___spec__8___rarg(x_14, x_2);
return x_15;
}
}
lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_mkMapDeclarationExtension___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___at_Lean_mkMapDeclarationExtension___spec__7___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_mkMapDeclarationExtension___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_1, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_mkMapDeclarationExtension___rarg___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
uint8_t l_Lean_mkMapDeclarationExtension___rarg___lambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Name_quickLt(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_mkMapDeclarationExtension___rarg___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_mkMapDeclarationExtension___rarg___lambda__3___boxed), 2, 0);
return x_1;
}
}
lean_object* l_Lean_mkMapDeclarationExtension___rarg___lambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = l_List_redLength___rarg(x_2);
x_4 = lean_mk_empty_array_with_capacity(x_3);
lean_dec(x_3);
x_5 = l_List_toArrayAux___rarg(x_2, x_4);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_6, x_7);
lean_dec(x_6);
x_9 = l_Lean_mkMapDeclarationExtension___rarg___lambda__4___closed__1;
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__2___rarg(x_1, x_9, x_5, x_10, x_8);
lean_dec(x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_mkMapDeclarationExtension___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_mkMapDeclarationExtension___rarg___lambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_mkMapDeclarationExtension___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_mkMapDeclarationExtension___rarg___lambda__2___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_mkMapDeclarationExtension___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_alloc_closure((void*)(l_Lean_mkMapDeclarationExtension___rarg___lambda__4), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_mkMapDeclarationExtension___rarg___closed__1;
x_6 = l_Lean_mkMapDeclarationExtension___rarg___closed__2;
x_7 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
lean_ctor_set(x_7, 3, x_4);
x_8 = l_Lean_registerSimplePersistentEnvExtension___at_Lean_mkMapDeclarationExtension___spec__7___rarg(x_7, x_3);
return x_8;
}
}
lean_object* l_Lean_mkMapDeclarationExtension(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_mkMapDeclarationExtension___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_qpartition_loop___at_Lean_mkMapDeclarationExtension___spec__6___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__2___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Array_qsort___at_Lean_mkMapDeclarationExtension___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_qsort___at_Lean_mkMapDeclarationExtension___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Lean_mkMapDeclarationExtension___rarg___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkMapDeclarationExtension___rarg___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_mkMapDeclarationExtension___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_mkMapDeclarationExtension___rarg___lambda__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_MapDeclarationExtension_instInhabitedMapDeclarationExtension___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_SimplePersistentEnvExtension_instInhabitedSimplePersistentEnvExtension___rarg(x_1);
return x_2;
}
}
lean_object* l_Lean_MapDeclarationExtension_instInhabitedMapDeclarationExtension(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MapDeclarationExtension_instInhabitedMapDeclarationExtension___closed__1;
return x_2;
}
}
lean_object* l_Lean_MapDeclarationExtension_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_1, x_2, x_5);
return x_6;
}
}
lean_object* l_Lean_MapDeclarationExtension_insert(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MapDeclarationExtension_insert___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_MapDeclarationExtension_find_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_MapDeclarationExtension_find_x3f_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_MapDeclarationExtension_find_x3f_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_MapDeclarationExtension_find_x3f_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_MapDeclarationExtension_find_x3f_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MapDeclarationExtension_find_x3f_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_find___at_Lean_MapDeclarationExtension_find_x3f___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_RBNode_find___at_Lean_MapDeclarationExtension_find_x3f___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_find___at_Lean_MapDeclarationExtension_find_x3f___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_MapDeclarationExtension_find_x3f___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_instInhabitedName;
lean_inc(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
x_9 = lean_nat_dec_le(x_5, x_6);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_nat_add(x_5, x_6);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_div(x_11, x_12);
lean_dec(x_11);
x_14 = lean_array_get(x_8, x_3, x_13);
lean_inc(x_2);
lean_inc(x_4);
lean_inc(x_14);
x_15 = lean_apply_2(x_2, x_14, x_4);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_6);
lean_inc(x_2);
lean_inc(x_14);
lean_inc(x_4);
x_17 = lean_apply_2(x_2, x_4, x_14);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_14);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_14);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_13, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_13, x_22);
lean_dec(x_13);
x_6 = x_23;
goto _start;
}
else
{
lean_object* x_25; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_box(0);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_14);
lean_dec(x_5);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_13, x_26);
lean_dec(x_13);
x_5 = x_27;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_MapDeclarationExtension_find_x3f___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_MapDeclarationExtension_find_x3f___spec__3___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_MapDeclarationExtension_find_x3f___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_instInhabitedName;
lean_inc(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
x_9 = lean_nat_dec_le(x_5, x_6);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_nat_add(x_5, x_6);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_div(x_11, x_12);
lean_dec(x_11);
x_14 = lean_array_get(x_8, x_3, x_13);
lean_inc(x_2);
lean_inc(x_4);
lean_inc(x_14);
x_15 = lean_apply_2(x_2, x_14, x_4);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_6);
lean_inc(x_2);
lean_inc(x_14);
lean_inc(x_4);
x_17 = lean_apply_2(x_2, x_4, x_14);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_14);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_14);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_13, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_13, x_22);
lean_dec(x_13);
x_6 = x_23;
goto _start;
}
else
{
lean_object* x_25; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_box(0);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_14);
lean_dec(x_5);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_13, x_26);
lean_dec(x_13);
x_5 = x_27;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_MapDeclarationExtension_find_x3f___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_MapDeclarationExtension_find_x3f___spec__4___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Array_binSearch___at_Lean_MapDeclarationExtension_find_x3f___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(0);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_lt(x_6, x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_7, x_11);
lean_dec(x_7);
x_13 = l_Array_binSearchAux___at_Lean_MapDeclarationExtension_find_x3f___spec__3___rarg(x_1, x_4, x_2, x_3, x_5, x_12);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_7);
x_14 = l_Array_binSearchAux___at_Lean_MapDeclarationExtension_find_x3f___spec__4___rarg(x_1, x_4, x_2, x_3, x_5, x_6);
return x_14;
}
}
}
}
lean_object* l_Array_binSearch___at_Lean_MapDeclarationExtension_find_x3f___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearch___at_Lean_MapDeclarationExtension_find_x3f___spec__2___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_MapDeclarationExtension_find_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_getModuleIdxFor_x3f(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_2, x_3);
x_7 = l_Std_RBNode_find___at_Lean_MapDeclarationExtension_find_x3f___spec__1___rarg(x_6, x_4);
lean_dec(x_4);
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_Lean_PersistentEnvExtension_getModuleEntries___rarg(x_2, x_3, x_8);
lean_dec(x_8);
lean_inc(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_1);
x_11 = lean_array_get_size(x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_11, x_12);
lean_dec(x_11);
x_14 = l_Lean_mkMapDeclarationExtension___rarg___lambda__4___closed__1;
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_binSearch___at_Lean_MapDeclarationExtension_find_x3f___spec__2___rarg(x_1, x_9, x_10, x_14, x_15, x_13);
lean_dec(x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_box(0);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
}
}
lean_object* l_Lean_MapDeclarationExtension_find_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MapDeclarationExtension_find_x3f___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_find___at_Lean_MapDeclarationExtension_find_x3f___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_MapDeclarationExtension_find_x3f___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_binSearchAux___at_Lean_MapDeclarationExtension_find_x3f___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_binSearchAux___at_Lean_MapDeclarationExtension_find_x3f___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Array_binSearchAux___at_Lean_MapDeclarationExtension_find_x3f___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_binSearchAux___at_Lean_MapDeclarationExtension_find_x3f___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Array_binSearch___at_Lean_MapDeclarationExtension_find_x3f___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_binSearch___at_Lean_MapDeclarationExtension_find_x3f___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_MapDeclarationExtension_find_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_MapDeclarationExtension_contains_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_MapDeclarationExtension_contains_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MapDeclarationExtension_contains_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Array_binSearchAux___at_Lean_MapDeclarationExtension_contains___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_instInhabitedName;
lean_inc(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
x_9 = lean_nat_dec_le(x_5, x_6);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_10 = 0;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_nat_add(x_5, x_6);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_div(x_11, x_12);
lean_dec(x_11);
x_14 = lean_array_get(x_8, x_3, x_13);
lean_inc(x_2);
lean_inc(x_4);
lean_inc(x_14);
x_15 = lean_apply_2(x_2, x_14, x_4);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_6);
lean_inc(x_2);
lean_inc(x_4);
x_17 = lean_apply_2(x_2, x_4, x_14);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_19 = 1;
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_13, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_13, x_22);
lean_dec(x_13);
x_6 = x_23;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_25 = 0;
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_14);
lean_dec(x_5);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_13, x_26);
lean_dec(x_13);
x_5 = x_27;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_MapDeclarationExtension_contains___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_MapDeclarationExtension_contains___spec__2___rarg___boxed), 6, 0);
return x_2;
}
}
uint8_t l_Array_binSearchAux___at_Lean_MapDeclarationExtension_contains___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_instInhabitedName;
lean_inc(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
x_9 = lean_nat_dec_le(x_5, x_6);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_10 = 0;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_nat_add(x_5, x_6);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_div(x_11, x_12);
lean_dec(x_11);
x_14 = lean_array_get(x_8, x_3, x_13);
lean_inc(x_2);
lean_inc(x_4);
lean_inc(x_14);
x_15 = lean_apply_2(x_2, x_14, x_4);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_6);
lean_inc(x_2);
lean_inc(x_4);
x_17 = lean_apply_2(x_2, x_4, x_14);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_19 = 1;
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_13, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_13, x_22);
lean_dec(x_13);
x_6 = x_23;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_25 = 0;
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_14);
lean_dec(x_5);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_13, x_26);
lean_dec(x_13);
x_5 = x_27;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_MapDeclarationExtension_contains___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_MapDeclarationExtension_contains___spec__3___rarg___boxed), 6, 0);
return x_2;
}
}
uint8_t l_Array_binSearchContains___at_Lean_MapDeclarationExtension_contains___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_9 = 0;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_lt(x_6, x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_6);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_7, x_11);
lean_dec(x_7);
x_13 = l_Array_binSearchAux___at_Lean_MapDeclarationExtension_contains___spec__2___rarg(x_1, x_4, x_2, x_3, x_5, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
x_14 = l_Array_binSearchAux___at_Lean_MapDeclarationExtension_contains___spec__3___rarg(x_1, x_4, x_2, x_3, x_5, x_6);
return x_14;
}
}
}
}
lean_object* l_Array_binSearchContains___at_Lean_MapDeclarationExtension_contains___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchContains___at_Lean_MapDeclarationExtension_contains___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
uint8_t l_Lean_MapDeclarationExtension_contains___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_getModuleIdxFor_x3f(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_1);
x_6 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_2, x_3);
x_7 = l_Lean_NameMap_contains___rarg(x_6, x_4);
lean_dec(x_4);
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_Lean_PersistentEnvExtension_getModuleEntries___rarg(x_2, x_3, x_8);
lean_dec(x_8);
lean_inc(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_1);
x_11 = lean_array_get_size(x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_11, x_12);
lean_dec(x_11);
x_14 = l_Lean_mkMapDeclarationExtension___rarg___lambda__4___closed__1;
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_binSearchContains___at_Lean_MapDeclarationExtension_contains___spec__1___rarg(x_1, x_9, x_10, x_14, x_15, x_13);
lean_dec(x_9);
return x_16;
}
}
}
lean_object* l_Lean_MapDeclarationExtension_contains(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MapDeclarationExtension_contains___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_MapDeclarationExtension_contains___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_binSearchAux___at_Lean_MapDeclarationExtension_contains___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Array_binSearchAux___at_Lean_MapDeclarationExtension_contains___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_binSearchAux___at_Lean_MapDeclarationExtension_contains___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Array_binSearchContains___at_Lean_MapDeclarationExtension_contains___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_binSearchContains___at_Lean_MapDeclarationExtension_contains___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Lean_MapDeclarationExtension_contains___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_MapDeclarationExtension_contains___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_instInhabitedModuleData___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_empty___closed__1;
x_2 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedModuleData() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedModuleData___closed__1;
return x_1;
}
}
lean_object* l_Lean_saveModuleData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_save_module_data(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_readModuleData___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_read_module_data(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_freeRegions___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_3 == x_4;
if (x_7 == 0)
{
lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_uget(x_2, x_3);
x_9 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_10 = lean_box_usize(x_9);
lean_inc(x_1);
x_11 = lean_apply_3(x_1, x_5, x_10, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = x_3 + x_14;
x_3 = x_15;
x_5 = x_12;
x_6 = x_13;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; 
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_6);
return x_21;
}
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_Environment_freeRegions___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_le(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_usize_of_nat(x_4);
x_13 = lean_usize_of_nat(x_5);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_freeRegions___spec__3(x_1, x_3, x_12, x_13, x_2, x_6);
return x_14;
}
}
}
}
lean_object* l_Array_forM___at_Lean_Environment_freeRegions___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box_usize(x_3);
x_6 = lean_apply_2(x_1, x_5, x_4);
return x_6;
}
}
lean_object* l_Array_forM___at_Lean_Environment_freeRegions___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Array_forM___at_Lean_Environment_freeRegions___spec__1___lambda__1___boxed), 4, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_box(0);
x_8 = l_Array_foldlMUnsafe___at_Lean_Environment_freeRegions___spec__2(x_6, x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Environment_freeRegions___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_CompactedRegion_free___boxed), 2, 0);
return x_1;
}
}
lean_object* lean_environment_free_regions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = l_Lean_Environment_freeRegions___closed__1;
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_forM___at_Lean_Environment_freeRegions___spec__1(x_6, x_4, x_7, x_5, x_2);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_freeRegions___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_freeRegions___spec__3(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_Environment_freeRegions___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_foldlMUnsafe___at_Lean_Environment_freeRegions___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Array_forM___at_Lean_Environment_freeRegions___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_forM___at_Lean_Environment_freeRegions___spec__1___lambda__1(x_1, x_2, x_5, x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_forM___at_Lean_Environment_freeRegions___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forM___at_Lean_Environment_freeRegions___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_Nat_foldAux___at_Lean_mkModuleData___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedEnvExtensionState;
x_2 = l_Lean_instInhabitedPersistentEnvExtension(lean_box(0), lean_box(0), lean_box(0), x_1);
return x_2;
}
}
lean_object* l_Nat_foldAux___at_Lean_mkModuleData___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
lean_dec(x_4);
x_10 = lean_nat_add(x_9, x_8);
x_11 = lean_nat_sub(x_3, x_10);
lean_dec(x_10);
x_12 = l_Nat_foldAux___at_Lean_mkModuleData___spec__1___closed__1;
x_13 = lean_array_get(x_12, x_2, x_11);
lean_dec(x_11);
x_14 = l_Lean_PersistentEnvExtension_getState___rarg(x_13, x_1);
x_15 = lean_ctor_get(x_13, 4);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_apply_1(x_15, x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_array_push(x_5, x_18);
x_4 = x_9;
x_5 = x_19;
goto _start;
}
else
{
lean_dec(x_4);
return x_5;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_mkModuleData___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_5, x_7);
x_9 = 1;
x_10 = x_3 + x_9;
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_mkModuleData___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_le(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_4);
x_10 = lean_usize_of_nat(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_mkModuleData___spec__5(x_1, x_3, x_9, x_10, x_2);
return x_11;
}
}
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
lean_inc(x_1);
x_11 = lean_apply_3(x_1, x_6, x_9, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_13;
x_6 = x_11;
goto _start;
}
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__6___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_array_push(x_1, x_3);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3(x_5, x_1);
lean_dec(x_5);
return x_6;
}
default: 
{
return x_1;
}
}
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_array_push(x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___lambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___lambda__2___boxed), 3, 0);
return x_1;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_array_get_size(x_3);
x_5 = l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___closed__1;
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_foldlMUnsafe___at_Lean_mkModuleData___spec__4(x_5, x_2, x_3, x_6, x_4);
lean_dec(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___closed__2;
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__6___rarg(x_10, x_8, x_9, lean_box(0), x_11, x_2);
return x_12;
}
}
}
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_mkModuleData___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_mkModuleData(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_persistentEnvExtensionsRef;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_array_get_size(x_6);
x_8 = l_Array_empty___closed__1;
lean_inc(x_7);
x_9 = l_Nat_foldAux___at_Lean_mkModuleData___spec__1(x_1, x_6, x_7, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_10, 1);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_12, 1);
x_14 = l_Std_PersistentHashMap_foldlM___at_Lean_mkModuleData___spec__2(x_13, x_8);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_9);
lean_ctor_set(x_4, 0, x_15);
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_18 = lean_array_get_size(x_16);
x_19 = l_Array_empty___closed__1;
lean_inc(x_18);
x_20 = l_Nat_foldAux___at_Lean_mkModuleData___spec__1(x_1, x_16, x_18, x_18, x_19);
lean_dec(x_18);
lean_dec(x_16);
x_21 = lean_ctor_get(x_1, 3);
x_22 = lean_ctor_get(x_21, 1);
x_23 = lean_ctor_get(x_1, 1);
x_24 = lean_ctor_get(x_23, 1);
x_25 = l_Std_PersistentHashMap_foldlM___at_Lean_mkModuleData___spec__2(x_24, x_19);
lean_inc(x_22);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_20);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_17);
return x_27;
}
}
}
lean_object* l_Nat_foldAux___at_Lean_mkModuleData___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_foldAux___at_Lean_mkModuleData___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_mkModuleData___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_mkModuleData___spec__5(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_mkModuleData___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_foldlMUnsafe___at_Lean_mkModuleData___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__6___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_mkModuleData___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_foldlM___at_Lean_mkModuleData___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_mkModuleData___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkModuleData(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* lean_write_module(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_mkModuleData(x_1, x_3);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_save_module_data(x_2, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Environment_0__Lean_getEntriesFor___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedName;
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Environment_0__Lean_getEntriesFor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l___private_Lean_Environment_0__Lean_getEntriesFor___closed__1;
x_9 = lean_array_get(x_8, x_4, x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_name_eq(x_10, x_2);
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
lean_object* l___private_Lean_Environment_0__Lean_getEntriesFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Environment_0__Lean_getEntriesFor(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__1___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_array_push(x_4, x_1);
lean_ctor_set(x_2, 0, x_5);
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
x_8 = lean_array_push(x_6, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_4 < x_3;
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_9 = lean_array_uget(x_2, x_4);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Environment_0__Lean_getEntriesFor(x_1, x_10, x_11);
lean_dec(x_10);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__1___lambda__1), 2, 1);
lean_closure_set(x_14, 0, x_12);
x_15 = l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg(x_13, x_5, x_14);
lean_dec(x_13);
x_16 = 1;
x_17 = x_4 + x_16;
x_4 = x_17;
x_5 = x_15;
goto _start;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_4 < x_3;
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_9 = lean_array_uget(x_2, x_4);
x_10 = lean_array_get_size(x_1);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = 0;
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__1(x_9, x_1, x_11, x_12, x_5, x_6);
lean_dec(x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = x_4 + x_16;
x_4 = x_17;
x_5 = x_14;
x_6 = x_15;
goto _start;
}
}
}
lean_object* l___private_Lean_Environment_0__Lean_setImportedEntries(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; 
x_4 = l_Lean_persistentEnvExtensionsRef;
x_5 = lean_st_ref_get(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_array_get_size(x_2);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
x_11 = l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__2(x_6, x_2, x_9, x_10, x_1, x_7);
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__1(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__2(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Environment_0__Lean_setImportedEntries___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Environment_0__Lean_setImportedEntries(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_finalizePersistentExtensions___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_4 < x_3;
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_array_uget(x_2, x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_10, x_5);
x_12 = lean_ctor_get(x_9, 2);
lean_inc(x_12);
lean_dec(x_9);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
lean_dec(x_15);
lean_inc(x_1);
lean_inc(x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_1);
lean_inc(x_14);
x_17 = lean_apply_3(x_12, x_14, x_16, x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_ctor_set(x_11, 1, x_18);
x_20 = l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg(x_10, x_5, x_11);
lean_dec(x_10);
x_21 = 1;
x_22 = x_4 + x_21;
x_4 = x_22;
x_5 = x_20;
x_6 = x_19;
goto _start;
}
else
{
uint8_t x_24; 
lean_free_object(x_11);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_11, 0);
lean_inc(x_28);
lean_dec(x_11);
lean_inc(x_1);
lean_inc(x_5);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_5);
lean_ctor_set(x_29, 1, x_1);
lean_inc(x_28);
x_30 = lean_apply_3(x_12, x_28, x_29, x_6);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg(x_10, x_5, x_33);
lean_dec(x_10);
x_35 = 1;
x_36 = x_4 + x_35;
x_4 = x_36;
x_5 = x_34;
x_6 = x_32;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_1);
x_38 = lean_ctor_get(x_30, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_40 = x_30;
} else {
 lean_dec_ref(x_30);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
}
}
lean_object* l___private_Lean_Environment_0__Lean_finalizePersistentExtensions(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_4 = l_Lean_persistentEnvExtensionsRef;
x_5 = lean_st_ref_get(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_array_get_size(x_6);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
x_11 = l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_finalizePersistentExtensions___spec__1(x_2, x_6, x_9, x_10, x_1, x_7);
lean_dec(x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_finalizePersistentExtensions___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_finalizePersistentExtensions___spec__1(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_Lean_ImportState_moduleNameSet___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameSet_empty;
return x_1;
}
}
static lean_object* _init_l_Lean_ImportState_moduleNames___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_ImportState_moduleData___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_ImportState_regions___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
lean_object* l_Lean_importModules_importMods_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_importModules_importMods_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_importModules_importMods_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_importModules_importMods_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
lean_object* l_Lean_importModules_importMods_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_importModules_importMods_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_importModules_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_importModules_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_importModules_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_importModules_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_apply_3(x_2, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_importModules_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_importModules_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_importModules_match__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_importModules_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_importModules_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l_IO_fileExists___at_Lean_importModules_importMods___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_file_exists(x_1, x_3);
return x_4;
}
}
lean_object* l_Lean_importModules_importMods___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_read_module_data(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_array_to_list(lean_box(0), x_12);
x_14 = l_Lean_importModules_importMods(x_13, x_5, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_take(x_5, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_17, 2);
x_22 = lean_ctor_get(x_17, 3);
x_23 = lean_array_push(x_20, x_2);
x_24 = lean_array_push(x_21, x_10);
x_25 = lean_array_push(x_22, x_11);
lean_ctor_set(x_17, 3, x_25);
lean_ctor_set(x_17, 2, x_24);
lean_ctor_set(x_17, 1, x_23);
x_26 = lean_st_ref_set(x_5, x_17, x_18);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_importModules_importMods(x_3, x_5, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
x_31 = lean_ctor_get(x_17, 2);
x_32 = lean_ctor_get(x_17, 3);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
x_33 = lean_array_push(x_30, x_2);
x_34 = lean_array_push(x_31, x_10);
x_35 = lean_array_push(x_32, x_11);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_35);
x_37 = lean_st_ref_set(x_5, x_36, x_18);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_importModules_importMods(x_3, x_5, x_38);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_14);
if (x_40 == 0)
{
return x_14;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_14, 0);
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_14);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_3);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_7);
if (x_44 == 0)
{
return x_7;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_7, 0);
x_46 = lean_ctor_get(x_7, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_7);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
static lean_object* _init_l_Lean_importModules_importMods___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("object file '");
return x_1;
}
}
static lean_object* _init_l_Lean_importModules_importMods___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' of module ");
return x_1;
}
}
static lean_object* _init_l_Lean_importModules_importMods___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" does not exist");
return x_1;
}
}
lean_object* l_Lean_importModules_importMods(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_st_ref_get(x_2, x_3);
x_9 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
lean_dec(x_6);
x_14 = l_Lean_NameSet_contains(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_st_ref_take(x_2, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = l_Lean_NameSet_insert___closed__1;
x_21 = lean_box(0);
lean_inc(x_13);
x_22 = l_Std_RBNode_insert___rarg(x_20, x_19, x_13, x_21);
lean_ctor_set(x_16, 0, x_22);
x_23 = lean_st_ref_set(x_2, x_16, x_17);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
lean_inc(x_13);
x_25 = l_Lean_findOLean(x_13, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_io_file_exists(x_26, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
uint8_t x_31; 
lean_dec(x_7);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_32 = lean_ctor_get(x_28, 0);
lean_dec(x_32);
x_33 = l_Lean_importModules_importMods___closed__1;
x_34 = lean_string_append(x_33, x_26);
lean_dec(x_26);
x_35 = l_Lean_importModules_importMods___closed__2;
x_36 = lean_string_append(x_34, x_35);
x_37 = l_Lean_Name_toString___closed__1;
x_38 = l_Lean_Name_toStringWithSep(x_37, x_13);
x_39 = lean_string_append(x_36, x_38);
lean_dec(x_38);
x_40 = l_Lean_importModules_importMods___closed__3;
x_41 = lean_string_append(x_39, x_40);
x_42 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 0, x_42);
return x_28;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_43 = lean_ctor_get(x_28, 1);
lean_inc(x_43);
lean_dec(x_28);
x_44 = l_Lean_importModules_importMods___closed__1;
x_45 = lean_string_append(x_44, x_26);
lean_dec(x_26);
x_46 = l_Lean_importModules_importMods___closed__2;
x_47 = lean_string_append(x_45, x_46);
x_48 = l_Lean_Name_toString___closed__1;
x_49 = l_Lean_Name_toStringWithSep(x_48, x_13);
x_50 = lean_string_append(x_47, x_49);
lean_dec(x_49);
x_51 = l_Lean_importModules_importMods___closed__3;
x_52 = lean_string_append(x_50, x_51);
x_53 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_43);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_28, 1);
lean_inc(x_55);
lean_dec(x_28);
x_56 = l_Lean_importModules_importMods___lambda__1(x_26, x_13, x_7, x_21, x_2, x_55);
lean_dec(x_26);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_7);
x_57 = !lean_is_exclusive(x_28);
if (x_57 == 0)
{
return x_28;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_28, 0);
x_59 = lean_ctor_get(x_28, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_28);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_13);
lean_dec(x_7);
x_61 = !lean_is_exclusive(x_25);
if (x_61 == 0)
{
return x_25;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_25, 0);
x_63 = lean_ctor_get(x_25, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_25);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_65 = lean_ctor_get(x_16, 0);
x_66 = lean_ctor_get(x_16, 1);
x_67 = lean_ctor_get(x_16, 2);
x_68 = lean_ctor_get(x_16, 3);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_16);
x_69 = l_Lean_NameSet_insert___closed__1;
x_70 = lean_box(0);
lean_inc(x_13);
x_71 = l_Std_RBNode_insert___rarg(x_69, x_65, x_13, x_70);
x_72 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_66);
lean_ctor_set(x_72, 2, x_67);
lean_ctor_set(x_72, 3, x_68);
x_73 = lean_st_ref_set(x_2, x_72, x_17);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
lean_inc(x_13);
x_75 = l_Lean_findOLean(x_13, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_io_file_exists(x_76, x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_unbox(x_79);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_7);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_82 = x_78;
} else {
 lean_dec_ref(x_78);
 x_82 = lean_box(0);
}
x_83 = l_Lean_importModules_importMods___closed__1;
x_84 = lean_string_append(x_83, x_76);
lean_dec(x_76);
x_85 = l_Lean_importModules_importMods___closed__2;
x_86 = lean_string_append(x_84, x_85);
x_87 = l_Lean_Name_toString___closed__1;
x_88 = l_Lean_Name_toStringWithSep(x_87, x_13);
x_89 = lean_string_append(x_86, x_88);
lean_dec(x_88);
x_90 = l_Lean_importModules_importMods___closed__3;
x_91 = lean_string_append(x_89, x_90);
x_92 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_92, 0, x_91);
if (lean_is_scalar(x_82)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_82;
 lean_ctor_set_tag(x_93, 1);
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_81);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_78, 1);
lean_inc(x_94);
lean_dec(x_78);
x_95 = l_Lean_importModules_importMods___lambda__1(x_76, x_13, x_7, x_70, x_2, x_94);
lean_dec(x_76);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_76);
lean_dec(x_13);
lean_dec(x_7);
x_96 = lean_ctor_get(x_78, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_78, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_98 = x_78;
} else {
 lean_dec_ref(x_78);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_13);
lean_dec(x_7);
x_100 = lean_ctor_get(x_75, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_75, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_102 = x_75;
} else {
 lean_dec_ref(x_75);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
}
else
{
lean_dec(x_13);
x_1 = x_7;
x_3 = x_11;
goto _start;
}
}
else
{
lean_object* x_105; 
lean_dec(x_6);
x_105 = lean_ctor_get(x_8, 1);
lean_inc(x_105);
lean_dec(x_8);
x_1 = x_7;
x_3 = x_105;
goto _start;
}
}
}
}
lean_object* l_IO_fileExists___at_Lean_importModules_importMods___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_fileExists___at_Lean_importModules_importMods___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_importModules_importMods___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_importModules_importMods___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_importModules_importMods___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_importModules_importMods(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_SMap_empty___at_Lean_importModules___spec__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_mkEmptyEnvironment___lambda__1___closed__1;
return x_1;
}
}
uint8_t l_Std_AssocList_contains___at_Lean_importModules___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_name_eq(x_4, x_1);
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
lean_object* l_Std_AssocList_foldlM___at_Lean_importModules___spec__6(lean_object* x_1, lean_object* x_2) {
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
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_instHashableName___closed__1;
x_7 = l_Std_HashMapImp_reinsertAux___rarg(x_6, x_1, x_3, x_4);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
lean_object* l_Std_HashMapImp_moveEntries___at_Lean_importModules___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_foldlM___at_Lean_importModules___spec__6(x_3, x_6);
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
lean_object* l_Std_HashMapImp_expand___at_Lean_importModules___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_HashMapImp_moveEntries___at_Lean_importModules___spec__5(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_Std_AssocList_replace___at_Lean_importModules___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_name_eq(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_AssocList_replace___at_Lean_importModules___spec__7(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_name_eq(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_AssocList_replace___at_Lean_importModules___spec__7(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
lean_object* l_Std_HashMapImp_insert___at_Lean_importModules___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_Std_AssocList_contains___at_Lean_importModules___spec__3(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = lean_nat_dec_le(x_13, x_7);
lean_dec(x_7);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_1);
x_17 = l_Std_HashMapImp_expand___at_Lean_importModules___spec__4(x_13, x_15);
return x_17;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = l_Std_AssocList_replace___at_Lean_importModules___spec__7(x_2, x_3, x_10);
x_19 = lean_array_uset(x_6, x_9, x_18);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_array_get_size(x_21);
x_23 = l_Lean_Name_hash(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_Std_AssocList_contains___at_Lean_importModules___spec__3(x_2, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_20, x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_array_uset(x_21, x_24, x_29);
x_31 = lean_nat_dec_le(x_28, x_22);
lean_dec(x_22);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Std_HashMapImp_expand___at_Lean_importModules___spec__4(x_28, x_30);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
x_34 = l_Std_AssocList_replace___at_Lean_importModules___spec__7(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_SMap_insert___at_Lean_Environment_addAux___spec__1(x_4, x_1, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("import failed, environment already contains '");
return x_1;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_4 < x_3;
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_array_uget(x_2, x_4);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = l_Lean_ConstantInfo_name(x_9);
lean_inc(x_10);
x_13 = l_Lean_SMap_contains___at_Lean_Environment_contains___spec__1(x_10, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
lean_inc(x_1);
lean_inc(x_12);
x_14 = l_Std_HashMapImp_insert___at_Lean_importModules___spec__2(x_11, x_12, x_1);
x_15 = lean_box(0);
x_16 = l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8___lambda__1(x_12, x_9, x_14, x_10, x_15, x_6);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = x_4 + x_20;
x_4 = x_21;
x_5 = x_19;
x_6 = x_18;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_23 = l_Lean_Name_toString___closed__1;
x_24 = l_Lean_Name_toStringWithSep(x_23, x_12);
x_25 = l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8___closed__1;
x_26 = lean_string_append(x_25, x_24);
lean_dec(x_24);
x_27 = l_Char_quote___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_6);
return x_30;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_1, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 < x_2;
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_array_uget(x_1, x_3);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
lean_ctor_set(x_9, 0, x_10);
x_14 = lean_array_get_size(x_13);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
lean_inc(x_12);
x_17 = l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8(x_12, x_13, x_15, x_16, x_9, x_5);
lean_dec(x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9___lambda__1___boxed), 4, 1);
lean_closure_set(x_20, 0, x_12);
x_21 = l_Lean_importModules_match__1___rarg(x_18, x_20);
x_22 = lean_apply_1(x_21, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_ctor_get(x_23, 0);
lean_inc(x_31);
lean_dec(x_23);
x_32 = 1;
x_33 = x_3 + x_32;
x_3 = x_33;
x_4 = x_31;
x_5 = x_30;
goto _start;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_22);
if (x_35 == 0)
{
return x_22;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_22, 0);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_22);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_12);
x_39 = !lean_is_exclusive(x_17);
if (x_39 == 0)
{
return x_17;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_17, 0);
x_41 = lean_ctor_get(x_17, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_17);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; size_t x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_9, 0);
x_44 = lean_ctor_get(x_9, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_9);
x_45 = lean_ctor_get(x_8, 1);
lean_inc(x_45);
lean_dec(x_8);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_10);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_array_get_size(x_45);
x_48 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_49 = 0;
lean_inc(x_43);
x_50 = l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8(x_43, x_45, x_48, x_49, x_46, x_5);
lean_dec(x_45);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9___lambda__1___boxed), 4, 1);
lean_closure_set(x_53, 0, x_43);
x_54 = l_Lean_importModules_match__1___rarg(x_51, x_53);
x_55 = lean_apply_1(x_54, x_52);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_58 = x_55;
} else {
 lean_dec_ref(x_55);
 x_58 = lean_box(0);
}
x_59 = lean_ctor_get(x_56, 0);
lean_inc(x_59);
lean_dec(x_56);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; size_t x_63; size_t x_64; 
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_dec(x_55);
x_62 = lean_ctor_get(x_56, 0);
lean_inc(x_62);
lean_dec(x_56);
x_63 = 1;
x_64 = x_3 + x_63;
x_3 = x_64;
x_4 = x_62;
x_5 = x_61;
goto _start;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_55, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_55, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_68 = x_55;
} else {
 lean_dec_ref(x_55);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_43);
x_70 = lean_ctor_get(x_50, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_50, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_72 = x_50;
} else {
 lean_dec_ref(x_50);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
}
}
lean_object* l_Lean_SMap_switch___at_Lean_importModules___spec__10(lean_object* x_1) {
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
lean_object* l_Lean_importModules___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_mk_ref(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
lean_object* l_Lean_importModules___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_importModules_importMods(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_st_ref_get(x_2, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_importModules___lambda__3(lean_object* x_1, lean_object* x_2, uint32_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_SMap_switch___at_Lean_importModules___spec__10(x_6);
x_11 = l_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates(x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_List_isEmpty___rarg(x_1);
x_15 = l_List_redLength___rarg(x_1);
x_16 = lean_mk_empty_array_with_capacity(x_15);
lean_dec(x_15);
x_17 = l_List_toArrayAux___rarg(x_1, x_16);
if (x_14 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_2, 3);
x_19 = lean_ctor_get(x_2, 1);
x_20 = 1;
x_21 = lean_box(0);
lean_inc(x_19);
lean_inc(x_18);
x_22 = lean_alloc_ctor(0, 4, 5);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 2, x_18);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set_uint32(x_22, sizeof(void*)*4, x_3);
lean_ctor_set_uint8(x_22, sizeof(void*)*4 + 4, x_20);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_10);
lean_ctor_set(x_23, 2, x_12);
lean_ctor_set(x_23, 3, x_22);
x_24 = l___private_Lean_Environment_0__Lean_setImportedEntries(x_23, x_4, x_13);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l___private_Lean_Environment_0__Lean_finalizePersistentExtensions(x_25, x_5, x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_27);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_36 = lean_ctor_get(x_2, 3);
x_37 = lean_ctor_get(x_2, 1);
x_38 = 0;
x_39 = lean_box(0);
lean_inc(x_37);
lean_inc(x_36);
x_40 = lean_alloc_ctor(0, 4, 5);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_17);
lean_ctor_set(x_40, 2, x_36);
lean_ctor_set(x_40, 3, x_37);
lean_ctor_set_uint32(x_40, sizeof(void*)*4, x_3);
lean_ctor_set_uint8(x_40, sizeof(void*)*4 + 4, x_38);
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_8);
lean_ctor_set(x_41, 1, x_10);
lean_ctor_set(x_41, 2, x_12);
lean_ctor_set(x_41, 3, x_40);
x_42 = l___private_Lean_Environment_0__Lean_setImportedEntries(x_41, x_4, x_13);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l___private_Lean_Environment_0__Lean_finalizePersistentExtensions(x_43, x_5, x_44);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
return x_45;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_45);
if (x_50 == 0)
{
return x_45;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_45, 0);
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_45);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_11);
if (x_54 == 0)
{
return x_11;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_11, 0);
x_56 = lean_ctor_get(x_11, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_11);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
static lean_object* _init_l_Lean_importModules___lambda__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_HashMap_instInhabitedHashMap___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_importModules___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SMap_empty___at_Lean_importModules___spec__1;
x_2 = l_Lean_importModules___lambda__4___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_importModules___lambda__4(lean_object* x_1, uint32_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
x_8 = lean_array_get_size(x_7);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
x_11 = l_Lean_importModules___lambda__4___closed__2;
x_12 = l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9(x_7, x_9, x_10, x_11, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box_uint32(x_2);
x_16 = lean_alloc_closure((void*)(l_Lean_importModules___lambda__3___boxed), 9, 5);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_6);
lean_closure_set(x_16, 2, x_15);
lean_closure_set(x_16, 3, x_7);
lean_closure_set(x_16, 4, x_3);
x_17 = l_Lean_importModules_match__2___rarg(x_13, x_16);
x_18 = lean_apply_1(x_17, x_14);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
static lean_object* _init_l_Lean_importModules___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_NameSet_empty;
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_importModules___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_importModules___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_importModules___lambda__1), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_importModules___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("import");
return x_1;
}
}
lean_object* lean_import_modules(lean_object* x_1, lean_object* x_2, uint32_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_importModules___lambda__2___boxed), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Lean_importModules___closed__2;
x_7 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_box_uint32(x_3);
lean_inc(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_importModules___lambda__4___boxed), 5, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_2);
x_10 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lean_importModules___closed__3;
x_12 = l_Lean_profileitIOUnsafe___rarg(x_11, x_2, x_10, x_4);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Std_AssocList_contains___at_Lean_importModules___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___at_Lean_importModules___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_importModules___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_importModules___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_importModules___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint32_t x_10; lean_object* x_11; 
x_10 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_11 = l_Lean_importModules___lambda__3(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_importModules___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint32_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_7 = l_Lean_importModules___lambda__4(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_importModules___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_6 = lean_import_modules(x_1, x_2, x_5, x_4);
return x_6;
}
}
lean_object* l_Lean_withImportModules___rarg(lean_object* x_1, lean_object* x_2, uint32_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_import_modules(x_1, x_2, x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_7);
x_9 = lean_apply_2(x_4, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_environment_free_regions(x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_10);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_9, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_dec(x_9);
x_23 = lean_environment_free_regions(x_7, x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_21);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_21);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_6);
if (x_32 == 0)
{
return x_6;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_6, 0);
x_34 = lean_ctor_get(x_6, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_6);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
lean_object* l_Lean_withImportModules(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_withImportModules___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_withImportModules___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint32_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_7 = l_Lean_withImportModules___rarg(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_Environment___hyg_2919____spec__1___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_array_get_size(x_2);
x_4 = l_Lean_mkTagDeclarationExtension___closed__1;
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_foldlMUnsafe___at_Array_foldl___spec__1___rarg(x_4, x_1, x_2, x_5, x_3);
lean_dec(x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_Environment___hyg_2919____spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_Environment___hyg_2919____spec__1___lambda__1___boxed), 2, 0);
return x_1;
}
}
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_Environment___hyg_2919____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_array_get_size(x_2);
x_4 = l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_Environment___hyg_2919____spec__1___closed__1;
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_foldlMUnsafe___at_Array_foldl___spec__1___rarg(x_4, x_1, x_2, x_5, x_3);
lean_dec(x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Environment___hyg_2919____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("namespaces");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Environment___hyg_2919____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_Environment___hyg_2919____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Environment___hyg_2919____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_NameSet_empty;
x_2 = lean_alloc_closure((void*)(l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_Environment___hyg_2919____spec__1___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Environment___hyg_2919____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lean_list_to_array), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Environment___hyg_2919____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_Environment___hyg_2919____closed__2;
x_2 = l_Lean_mkTagDeclarationExtension___closed__1;
x_3 = l_Lean_initFn____x40_Lean_Environment___hyg_2919____closed__3;
x_4 = l_Lean_initFn____x40_Lean_Environment___hyg_2919____closed__4;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_2919_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_initFn____x40_Lean_Environment___hyg_2919____closed__5;
x_3 = l_Lean_registerSimplePersistentEnvExtension___at_Lean_mkTagDeclarationExtension___spec__4(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_Environment___hyg_2919____spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_Environment___hyg_2919____spec__1___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_Environment___hyg_2919____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_Environment___hyg_2919____spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
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
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_instInhabitedError___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_namespacesExt___elambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_namespacesExt___elambda__4___rarg), 1, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_namespacesExt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_namespacesExt___elambda__4___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_namespacesExt___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_namespacesExt___elambda__3___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_namespacesExt___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_namespacesExt___elambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_namespacesExt___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_namespacesExt___elambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_namespacesExt___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__2;
x_2 = lean_box(0);
x_3 = l_Lean_namespacesExt___closed__1;
x_4 = l_Lean_namespacesExt___closed__2;
x_5 = l_Lean_namespacesExt___closed__3;
x_6 = l_Lean_namespacesExt___closed__4;
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
lean_object* l_Lean_namespacesExt___elambda__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_namespacesExt___elambda__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Environment_registerNamespace(lean_object* x_1, lean_object* x_2) {
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
uint8_t l_Lean_Environment_isNamespace(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Environment_isNamespace___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Environment_isNamespace(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Environment_getNamespaceSet(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_namespacesExt;
x_3 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Environment_getNamespaceSet___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Environment_getNamespaceSet(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Environment_0__Lean_Environment_isNamespaceName_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_8 = lean_box_usize(x_7);
x_9 = lean_apply_2(x_2, x_6, x_8);
return x_9;
}
else
{
lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_12 = lean_box_usize(x_11);
x_13 = lean_apply_3(x_3, x_5, x_10, x_12);
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_apply_1(x_4, x_1);
return x_14;
}
}
}
lean_object* l___private_Lean_Environment_0__Lean_Environment_isNamespaceName_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_Environment_isNamespaceName_match__1___rarg), 4, 0);
return x_2;
}
}
uint8_t l___private_Lean_Environment_0__Lean_Environment_isNamespaceName(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
x_1 = x_2;
goto _start;
}
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
lean_object* l___private_Lean_Environment_0__Lean_Environment_isNamespaceName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Environment_0__Lean_Environment_isNamespaceName(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Environment_0__Lean_Environment_registerNamePrefixes_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get_usize(x_2, 2);
lean_dec(x_2);
x_8 = lean_box_usize(x_7);
x_9 = lean_apply_4(x_3, x_1, x_5, x_6, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_2(x_4, x_1, x_2);
return x_10;
}
}
}
lean_object* l___private_Lean_Environment_0__Lean_Environment_registerNamePrefixes_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_Environment_registerNamePrefixes_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Environment_0__Lean_Environment_registerNamePrefixes(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l___private_Lean_Environment_0__Lean_Environment_isNamespaceName(x_3);
if (x_4 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Environment_registerNamespace(x_1, x_3);
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
lean_object* lean_environment_add(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_ConstantInfo_name(x_2);
x_4 = l___private_Lean_Environment_0__Lean_Environment_registerNamePrefixes(x_1, x_3);
x_5 = l_Lean_Environment_addAux(x_4, x_2);
return x_5;
}
}
lean_object* l_List_toStringAux___at_Lean_Environment_displayStats___spec__2(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_Lean_instInhabitedParserDescr___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = l_Lean_Name_toString___closed__1;
x_8 = l_Lean_Name_toStringWithSep(x_7, x_6);
x_9 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_dec(x_4);
x_10 = 0;
x_11 = l_List_toStringAux___at_Lean_Environment_displayStats___spec__2(x_10, x_5);
if (x_9 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_instInhabitedParserDescr___closed__1;
x_13 = lean_string_append(x_8, x_12);
x_14 = l_term_x5b___x5d___closed__5;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = lean_string_append(x_15, x_11);
lean_dec(x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = l_Lean_instToStringImport___closed__1;
x_18 = lean_string_append(x_8, x_17);
x_19 = l_term_x5b___x5d___closed__5;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = lean_string_append(x_20, x_11);
lean_dec(x_11);
return x_21;
}
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_22; 
x_22 = l_Lean_instInhabitedParserDescr___closed__1;
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
lean_dec(x_2);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = l_Lean_Name_toString___closed__1;
x_27 = l_Lean_Name_toStringWithSep(x_26, x_25);
x_28 = lean_ctor_get_uint8(x_23, sizeof(void*)*1);
lean_dec(x_23);
x_29 = 0;
x_30 = l_List_toStringAux___at_Lean_Environment_displayStats___spec__2(x_29, x_24);
if (x_28 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Lean_instInhabitedParserDescr___closed__1;
x_32 = lean_string_append(x_27, x_31);
x_33 = lean_string_append(x_32, x_30);
lean_dec(x_30);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = l_Lean_instToStringImport___closed__1;
x_35 = lean_string_append(x_27, x_34);
x_36 = lean_string_append(x_35, x_30);
lean_dec(x_30);
return x_36;
}
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
x_2 = l_instReprList___rarg___closed__1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = 1;
x_5 = l_List_toStringAux___at_Lean_Environment_displayStats___spec__2(x_4, x_1);
x_6 = l_term_x5b___x5d___closed__3;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_term_x5b___x5d___closed__9;
x_9 = lean_string_append(x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = 1;
x_14 = l_List_toStringAux___at_Lean_Environment_displayStats___spec__2(x_13, x_12);
x_15 = l_term_x5b___x5d___closed__3;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_term_x5b___x5d___closed__9;
x_18 = lean_string_append(x_16, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_3, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_nat_add(x_5, x_4);
return x_6;
}
}
lean_object* l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
lean_object* l_Std_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__6(lean_object* x_1) {
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
x_3 = l_Std_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__6(x_2);
return x_3;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_3 == x_4;
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_9 = lean_apply_3(x_1, x_5, x_8, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 1;
x_13 = x_3 + x_12;
x_3 = x_13;
x_5 = x_10;
x_6 = x_11;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_6);
return x_19;
}
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_Environment_displayStats___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_le(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_usize_of_nat(x_4);
x_13 = lean_usize_of_nat(x_5);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__9(x_1, x_3, x_12, x_13, x_2, x_6);
return x_14;
}
}
}
}
lean_object* l_Array_forM___at_Lean_Environment_displayStats___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_forM___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_box(0);
x_8 = l_Array_foldlMUnsafe___at_Lean_Environment_displayStats___spec__8(x_6, x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
lean_object* l_Lean_Environment_displayStats___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_add(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Environment_displayStats___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Environment_displayStats___lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_displayStats___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  number of imported entries: ");
return x_1;
}
}
lean_object* l_Lean_Environment_displayStats___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_array_get_size(x_4);
x_6 = l_Lean_Environment_displayStats___lambda__2___closed__1;
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_foldlMUnsafe___at_Array_foldl___spec__1___rarg(x_6, x_7, x_4, x_7, x_5);
lean_dec(x_5);
x_9 = l_Nat_repr(x_8);
x_10 = l_Lean_Environment_displayStats___lambda__2___closed__2;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_IO_println___at_Lean_instEval___spec__1(x_11, x_3);
return x_12;
}
}
static lean_object* _init_l_Lean_Environment_displayStats___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("extension '");
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_displayStats___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  ");
return x_1;
}
}
lean_object* l_Lean_Environment_displayStats___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lean_Name_toString___closed__1;
x_6 = l_Lean_Name_toStringWithSep(x_5, x_4);
x_7 = l_Lean_Environment_displayStats___lambda__3___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Char_quote___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = l_IO_println___at_Lean_instEval___spec__1(x_10, x_3);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_13, x_1);
lean_dec(x_13);
x_15 = lean_ctor_get(x_2, 5);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_17 = lean_apply_1(x_15, x_16);
x_18 = l_Std_Format_isNil(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = l___private_Lean_Declaration_0__Lean_reprDefinitionSafety____x40_Lean_Declaration___hyg_192____closed__3;
x_20 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
x_21 = l_Std_Format_defWidth;
x_22 = lean_format_pretty(x_20, x_21);
x_23 = l_Lean_Environment_displayStats___lambda__3___closed__2;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = l_IO_println___at_Lean_instEval___spec__1(x_24, x_12);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Environment_displayStats___lambda__2(x_14, x_26, x_27);
lean_dec(x_26);
lean_dec(x_14);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_14);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_17);
x_33 = lean_box(0);
x_34 = l_Lean_Environment_displayStats___lambda__2(x_14, x_33, x_12);
lean_dec(x_14);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_11);
if (x_35 == 0)
{
return x_11;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_11, 0);
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_11);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
static lean_object* _init_l_Lean_Environment_displayStats___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("direct imports:                        ");
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_displayStats___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("number of imported modules:            ");
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_displayStats___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("number of consts:                      ");
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_displayStats___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("number of imported consts:             ");
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_displayStats___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("number of local consts:                ");
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_displayStats___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("number of buckets for imported consts: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_displayStats___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("trust level:                           ");
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_displayStats___closed__8() {
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_3 = l_Lean_persistentEnvExtensionsRef;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Nat_foldAux___at_Lean_mkModuleData___spec__1___closed__1;
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_get(x_7, x_5, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_10, x_1);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_array_get_size(x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_array_to_list(lean_box(0), x_15);
x_17 = l_List_toString___at_Lean_Environment_displayStats___spec__1(x_16);
x_18 = l_Array_instToStringArray___rarg___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = l_Lean_Environment_displayStats___closed__1;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = l_IO_println___at_Lean_instEval___spec__1(x_21, x_6);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Nat_repr(x_13);
x_25 = l_Lean_Environment_displayStats___closed__2;
x_26 = lean_string_append(x_25, x_24);
lean_dec(x_24);
x_27 = l_IO_println___at_Lean_instEval___spec__1(x_26, x_23);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
x_30 = l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3(x_29);
x_31 = l_Nat_repr(x_30);
x_32 = l_Lean_Environment_displayStats___closed__3;
x_33 = lean_string_append(x_32, x_31);
lean_dec(x_31);
x_34 = l_IO_println___at_Lean_instEval___spec__1(x_33, x_28);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4(x_29);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = l_Nat_repr(x_37);
x_39 = l_Lean_Environment_displayStats___closed__4;
x_40 = lean_string_append(x_39, x_38);
lean_dec(x_38);
x_41 = l_IO_println___at_Lean_instEval___spec__1(x_40, x_35);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_dec(x_36);
x_44 = l_Nat_repr(x_43);
x_45 = l_Lean_Environment_displayStats___closed__5;
x_46 = lean_string_append(x_45, x_44);
lean_dec(x_44);
x_47 = l_IO_println___at_Lean_instEval___spec__1(x_46, x_42);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(x_29);
lean_dec(x_29);
x_50 = l_Nat_repr(x_49);
x_51 = l_Lean_Environment_displayStats___closed__6;
x_52 = lean_string_append(x_51, x_50);
lean_dec(x_50);
x_53 = l_IO_println___at_Lean_instEval___spec__1(x_52, x_48);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint32_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_ctor_get_uint32(x_14, sizeof(void*)*4);
lean_dec(x_14);
x_56 = lean_uint32_to_nat(x_55);
x_57 = l_Nat_repr(x_56);
x_58 = l_Lean_Environment_displayStats___closed__7;
x_59 = lean_string_append(x_58, x_57);
lean_dec(x_57);
x_60 = l_IO_println___at_Lean_instEval___spec__1(x_59, x_54);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_ctor_get(x_1, 2);
lean_inc(x_62);
x_63 = lean_array_get_size(x_62);
lean_dec(x_62);
x_64 = l_Nat_repr(x_63);
x_65 = l_Lean_Environment_displayStats___closed__8;
x_66 = lean_string_append(x_65, x_64);
lean_dec(x_64);
x_67 = l_IO_println___at_Lean_instEval___spec__1(x_66, x_61);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_alloc_closure((void*)(l_Lean_Environment_displayStats___lambda__3___boxed), 3, 1);
lean_closure_set(x_69, 0, x_1);
x_70 = lean_array_get_size(x_5);
x_71 = l_Array_forM___at_Lean_Environment_displayStats___spec__7(x_69, x_5, x_8, x_70, x_68);
lean_dec(x_70);
lean_dec(x_5);
return x_71;
}
else
{
uint8_t x_72; 
lean_dec(x_5);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_67);
if (x_72 == 0)
{
return x_67;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_67, 0);
x_74 = lean_ctor_get(x_67, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_67);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_5);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_60);
if (x_76 == 0)
{
return x_60;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_60, 0);
x_78 = lean_ctor_get(x_60, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_60);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_53);
if (x_80 == 0)
{
return x_53;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_53, 0);
x_82 = lean_ctor_get(x_53, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_53);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_29);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_47);
if (x_84 == 0)
{
return x_47;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_47, 0);
x_86 = lean_ctor_get(x_47, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_47);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_36);
lean_dec(x_29);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_41);
if (x_88 == 0)
{
return x_41;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_41, 0);
x_90 = lean_ctor_get(x_41, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_41);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_29);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_34);
if (x_92 == 0)
{
return x_34;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_34, 0);
x_94 = lean_ctor_get(x_34, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_34);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_27);
if (x_96 == 0)
{
return x_27;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_27, 0);
x_98 = lean_ctor_get(x_27, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_27);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_22);
if (x_100 == 0)
{
return x_22;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_22, 0);
x_102 = lean_ctor_get(x_22, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_22);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
lean_object* l_List_toStringAux___at_Lean_Environment_displayStats___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_toStringAux___at_Lean_Environment_displayStats___spec__2(x_3, x_2);
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
lean_object* l_Std_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__6___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__6(x_1);
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
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__9(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_Environment_displayStats___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_foldlMUnsafe___at_Lean_Environment_displayStats___spec__8(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Array_forM___at_Lean_Environment_displayStats___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forM___at_Lean_Environment_displayStats___spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Environment_displayStats___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Environment_displayStats___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Environment_displayStats___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_displayStats___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Environment_displayStats___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_displayStats___lambda__3(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Environment_evalConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_eval_const(x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected type at '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', `");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("` expected");
return x_1;
}
}
lean_object* l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_3 = l_Lean_Name_toString___closed__1;
x_4 = l_Lean_Name_toStringWithSep(x_3, x_2);
x_5 = l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg___closed__2;
x_8 = lean_string_append(x_6, x_7);
x_9 = l_Lean_Name_toStringWithSep(x_3, x_1);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
x_11 = l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg___closed__3;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
lean_object* l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Environment_evalConstCheck_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_3(x_2, x_4, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l_Lean_Environment_evalConstCheck_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Environment_evalConstCheck_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Environment_evalConstCheck_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Environment_evalConstCheck_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Environment_evalConstCheck_match__2___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Environment_evalConstCheck___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknow constant '");
return x_1;
}
}
lean_object* l_Lean_Environment_evalConstCheck___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_4);
lean_inc(x_1);
x_5 = lean_environment_find(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = l_Lean_Name_toString___closed__1;
x_7 = l_Lean_Name_toStringWithSep(x_6, x_4);
x_8 = l_Lean_Environment_evalConstCheck___rarg___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Char_quote___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec(x_5);
x_14 = l_Lean_ConstantInfo_type(x_13);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_name_eq(x_15, x_3);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_1);
x_17 = l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg(x_3, x_4);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_3);
x_18 = lean_eval_const(x_1, x_2, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_18;
}
}
else
{
lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_1);
x_19 = l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg(x_3, x_4);
return x_19;
}
}
}
}
lean_object* l_Lean_Environment_evalConstCheck(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Environment_evalConstCheck___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Environment_evalConstCheck___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_evalConstCheck___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Environment_hasUnsafe_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Environment_hasUnsafe_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Environment_hasUnsafe_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Environment_hasUnsafe_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_3(x_2, x_4, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l_Lean_Environment_hasUnsafe_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Environment_hasUnsafe_match__2___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Environment_hasUnsafe___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_environment_find(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_ConstantInfo_isUnsafe(x_6);
lean_dec(x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = 0;
return x_8;
}
}
}
uint8_t l_Lean_Environment_hasUnsafe(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_alloc_closure((void*)(l_Lean_Environment_hasUnsafe___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = 8192;
x_5 = l_Lean_Expr_FindImpl_initCache;
x_6 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_3, x_4, x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
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
}
lean_object* l_Lean_Environment_hasUnsafe___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Environment_hasUnsafe___lambda__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Environment_hasUnsafe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Environment_hasUnsafe(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Kernel_isDefEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_kernel_is_def_eq(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Lean_Kernel_whnf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_kernel_whnf(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_instMonadEnv___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_4, x_3);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_instMonadEnv___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_inc(x_1);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_instMonadEnv___rarg___lambda__1), 3, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
lean_object* l_Lean_instMonadEnv(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instMonadEnv___rarg), 2, 0);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Std_Data_HashMap(lean_object*);
lean_object* initialize_Lean_Data_SMap(lean_object*);
lean_object* initialize_Lean_Declaration(lean_object*);
lean_object* initialize_Lean_LocalContext(lean_object*);
lean_object* initialize_Lean_Util_Path(lean_object*);
lean_object* initialize_Lean_Util_FindExpr(lean_object*);
lean_object* initialize_Lean_Util_Profile(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Environment(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_SMap(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Declaration(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LocalContext(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Path(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FindExpr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Profile(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_EnvExtensionStateSpec = _init_l_Lean_EnvExtensionStateSpec();
lean_mark_persistent(l_Lean_EnvExtensionStateSpec);
l_Lean_instInhabitedEnvExtensionState = _init_l_Lean_instInhabitedEnvExtensionState();
lean_mark_persistent(l_Lean_instInhabitedEnvExtensionState);
l_Lean_instInhabitedModuleIdx = _init_l_Lean_instInhabitedModuleIdx();
lean_mark_persistent(l_Lean_instInhabitedModuleIdx);
l_Lean_Import_runtimeOnly___default = _init_l_Lean_Import_runtimeOnly___default();
l_Lean_instToStringImport___closed__1 = _init_l_Lean_instToStringImport___closed__1();
lean_mark_persistent(l_Lean_instToStringImport___closed__1);
l_Lean_EnvironmentHeader_trustLevel___default = _init_l_Lean_EnvironmentHeader_trustLevel___default();
l_Lean_EnvironmentHeader_quotInit___default = _init_l_Lean_EnvironmentHeader_quotInit___default();
l_Lean_EnvironmentHeader_mainModule___default = _init_l_Lean_EnvironmentHeader_mainModule___default();
lean_mark_persistent(l_Lean_EnvironmentHeader_mainModule___default);
l_Lean_EnvironmentHeader_imports___default = _init_l_Lean_EnvironmentHeader_imports___default();
lean_mark_persistent(l_Lean_EnvironmentHeader_imports___default);
l_Lean_EnvironmentHeader_regions___default = _init_l_Lean_EnvironmentHeader_regions___default();
lean_mark_persistent(l_Lean_EnvironmentHeader_regions___default);
l_Lean_EnvironmentHeader_moduleNames___default = _init_l_Lean_EnvironmentHeader_moduleNames___default();
lean_mark_persistent(l_Lean_EnvironmentHeader_moduleNames___default);
l_Lean_instInhabitedEnvironmentHeader___closed__1 = _init_l_Lean_instInhabitedEnvironmentHeader___closed__1();
lean_mark_persistent(l_Lean_instInhabitedEnvironmentHeader___closed__1);
l_Lean_instInhabitedEnvironmentHeader = _init_l_Lean_instInhabitedEnvironmentHeader();
lean_mark_persistent(l_Lean_instInhabitedEnvironmentHeader);
l_Lean_Environment_header___default___closed__1 = _init_l_Lean_Environment_header___default___closed__1();
lean_mark_persistent(l_Lean_Environment_header___default___closed__1);
l_Lean_Environment_header___default = _init_l_Lean_Environment_header___default();
lean_mark_persistent(l_Lean_Environment_header___default);
l_Lean_instInhabitedEnvironment___closed__1 = _init_l_Lean_instInhabitedEnvironment___closed__1();
lean_mark_persistent(l_Lean_instInhabitedEnvironment___closed__1);
l_Lean_instInhabitedEnvironment___closed__2 = _init_l_Lean_instInhabitedEnvironment___closed__2();
lean_mark_persistent(l_Lean_instInhabitedEnvironment___closed__2);
l_Lean_instInhabitedEnvironment___closed__3 = _init_l_Lean_instInhabitedEnvironment___closed__3();
lean_mark_persistent(l_Lean_instInhabitedEnvironment___closed__3);
l_Lean_instInhabitedEnvironment___closed__4 = _init_l_Lean_instInhabitedEnvironment___closed__4();
lean_mark_persistent(l_Lean_instInhabitedEnvironment___closed__4);
l_Lean_instInhabitedEnvironment___closed__5 = _init_l_Lean_instInhabitedEnvironment___closed__5();
lean_mark_persistent(l_Lean_instInhabitedEnvironment___closed__5);
l_Lean_instInhabitedEnvironment = _init_l_Lean_instInhabitedEnvironment();
lean_mark_persistent(l_Lean_instInhabitedEnvironment);
l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___boxed__const__1 = _init_l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___boxed__const__1();
lean_mark_persistent(l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___boxed__const__1);
l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___boxed__const__2 = _init_l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___boxed__const__2();
lean_mark_persistent(l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___boxed__const__2);
l_Lean_instInhabitedEnvExtensionInterface___closed__1 = _init_l_Lean_instInhabitedEnvExtensionInterface___closed__1();
lean_mark_persistent(l_Lean_instInhabitedEnvExtensionInterface___closed__1);
l_Lean_instInhabitedEnvExtensionInterface___closed__2 = _init_l_Lean_instInhabitedEnvExtensionInterface___closed__2();
lean_mark_persistent(l_Lean_instInhabitedEnvExtensionInterface___closed__2);
l_Lean_instInhabitedEnvExtensionInterface___closed__3 = _init_l_Lean_instInhabitedEnvExtensionInterface___closed__3();
lean_mark_persistent(l_Lean_instInhabitedEnvExtensionInterface___closed__3);
l_Lean_instInhabitedEnvExtensionInterface = _init_l_Lean_instInhabitedEnvExtensionInterface();
lean_mark_persistent(l_Lean_instInhabitedEnvExtensionInterface);
l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__1 = _init_l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__1();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__1);
l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__2 = _init_l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__2();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__2);
res = l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_mkEnvExtensionsRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_envExtensionsRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_envExtensionsRef);
lean_dec_ref(res);
l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___closed__1 = _init_l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___closed__1();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___closed__1);
l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___closed__2 = _init_l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___closed__2();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___closed__2);
l_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates___boxed__const__1 = _init_l_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates___boxed__const__1();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates___boxed__const__1);
l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__1 = _init_l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__1();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__1);
l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__2 = _init_l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__2();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__2);
l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__3 = _init_l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__3();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__3);
l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__4 = _init_l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__4();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__4);
l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__5 = _init_l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__5();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__5);
l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__6 = _init_l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__6();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__6);
l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__7 = _init_l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__7();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__7);
l_Lean_EnvExtensionInterfaceUnsafe_imp = _init_l_Lean_EnvExtensionInterfaceUnsafe_imp();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_imp);
l_Lean_EnvExtensionInterfaceImp___closed__1 = _init_l_Lean_EnvExtensionInterfaceImp___closed__1();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceImp___closed__1);
l_Lean_EnvExtensionInterfaceImp___closed__2 = _init_l_Lean_EnvExtensionInterfaceImp___closed__2();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceImp___closed__2);
l_Lean_EnvExtensionInterfaceImp___closed__3 = _init_l_Lean_EnvExtensionInterfaceImp___closed__3();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceImp___closed__3);
l_Lean_EnvExtensionInterfaceImp___closed__4 = _init_l_Lean_EnvExtensionInterfaceImp___closed__4();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceImp___closed__4);
l_Lean_EnvExtensionInterfaceImp___closed__5 = _init_l_Lean_EnvExtensionInterfaceImp___closed__5();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceImp___closed__5);
l_Lean_EnvExtensionInterfaceImp___closed__6 = _init_l_Lean_EnvExtensionInterfaceImp___closed__6();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceImp___closed__6);
l_Lean_EnvExtensionInterfaceImp___closed__7 = _init_l_Lean_EnvExtensionInterfaceImp___closed__7();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceImp___closed__7);
l_Lean_EnvExtensionInterfaceImp = _init_l_Lean_EnvExtensionInterfaceImp();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceImp);
l_Lean_mkEmptyEnvironment___lambda__1___closed__1 = _init_l_Lean_mkEmptyEnvironment___lambda__1___closed__1();
lean_mark_persistent(l_Lean_mkEmptyEnvironment___lambda__1___closed__1);
l_Lean_mkEmptyEnvironment___closed__1 = _init_l_Lean_mkEmptyEnvironment___closed__1();
lean_mark_persistent(l_Lean_mkEmptyEnvironment___closed__1);
l_Lean_mkEmptyEnvironment___closed__2 = _init_l_Lean_mkEmptyEnvironment___closed__2();
lean_mark_persistent(l_Lean_mkEmptyEnvironment___closed__2);
l_Lean_EnvExtensionEntrySpec = _init_l_Lean_EnvExtensionEntrySpec();
lean_mark_persistent(l_Lean_EnvExtensionEntrySpec);
l_Lean_instInhabitedEnvExtensionEntry = _init_l_Lean_instInhabitedEnvExtensionEntry();
lean_mark_persistent(l_Lean_instInhabitedEnvExtensionEntry);
l_Lean_instInhabitedPersistentEnvExtension___closed__1 = _init_l_Lean_instInhabitedPersistentEnvExtension___closed__1();
lean_mark_persistent(l_Lean_instInhabitedPersistentEnvExtension___closed__1);
l_Lean_instInhabitedPersistentEnvExtension___closed__2 = _init_l_Lean_instInhabitedPersistentEnvExtension___closed__2();
lean_mark_persistent(l_Lean_instInhabitedPersistentEnvExtension___closed__2);
l_Lean_instInhabitedPersistentEnvExtension___closed__3 = _init_l_Lean_instInhabitedPersistentEnvExtension___closed__3();
lean_mark_persistent(l_Lean_instInhabitedPersistentEnvExtension___closed__3);
l_Lean_instInhabitedPersistentEnvExtension___closed__4 = _init_l_Lean_instInhabitedPersistentEnvExtension___closed__4();
lean_mark_persistent(l_Lean_instInhabitedPersistentEnvExtension___closed__4);
l_Lean_instInhabitedPersistentEnvExtension___closed__5 = _init_l_Lean_instInhabitedPersistentEnvExtension___closed__5();
lean_mark_persistent(l_Lean_instInhabitedPersistentEnvExtension___closed__5);
res = l_Lean_initFn____x40_Lean_Environment___hyg_1088_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_persistentEnvExtensionsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_persistentEnvExtensionsRef);
lean_dec_ref(res);
l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2___closed__1 = _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2___closed__1);
l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1 = _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1();
lean_mark_persistent(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1);
l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2 = _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2();
lean_mark_persistent(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2);
l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__1 = _init_l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__1();
lean_mark_persistent(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__1);
l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__2 = _init_l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__2();
lean_mark_persistent(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__2);
l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1 = _init_l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1();
lean_mark_persistent(l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1);
l_Lean_mkTagDeclarationExtension___closed__1 = _init_l_Lean_mkTagDeclarationExtension___closed__1();
lean_mark_persistent(l_Lean_mkTagDeclarationExtension___closed__1);
l_Lean_mkTagDeclarationExtension___closed__2 = _init_l_Lean_mkTagDeclarationExtension___closed__2();
lean_mark_persistent(l_Lean_mkTagDeclarationExtension___closed__2);
l_Lean_mkTagDeclarationExtension___closed__3 = _init_l_Lean_mkTagDeclarationExtension___closed__3();
lean_mark_persistent(l_Lean_mkTagDeclarationExtension___closed__3);
l_Lean_TagDeclarationExtension_instInhabitedTagDeclarationExtension___closed__1 = _init_l_Lean_TagDeclarationExtension_instInhabitedTagDeclarationExtension___closed__1();
lean_mark_persistent(l_Lean_TagDeclarationExtension_instInhabitedTagDeclarationExtension___closed__1);
l_Lean_TagDeclarationExtension_instInhabitedTagDeclarationExtension = _init_l_Lean_TagDeclarationExtension_instInhabitedTagDeclarationExtension();
lean_mark_persistent(l_Lean_TagDeclarationExtension_instInhabitedTagDeclarationExtension);
l_Lean_mkMapDeclarationExtension___rarg___lambda__4___closed__1 = _init_l_Lean_mkMapDeclarationExtension___rarg___lambda__4___closed__1();
lean_mark_persistent(l_Lean_mkMapDeclarationExtension___rarg___lambda__4___closed__1);
l_Lean_mkMapDeclarationExtension___rarg___closed__1 = _init_l_Lean_mkMapDeclarationExtension___rarg___closed__1();
lean_mark_persistent(l_Lean_mkMapDeclarationExtension___rarg___closed__1);
l_Lean_mkMapDeclarationExtension___rarg___closed__2 = _init_l_Lean_mkMapDeclarationExtension___rarg___closed__2();
lean_mark_persistent(l_Lean_mkMapDeclarationExtension___rarg___closed__2);
l_Lean_MapDeclarationExtension_instInhabitedMapDeclarationExtension___closed__1 = _init_l_Lean_MapDeclarationExtension_instInhabitedMapDeclarationExtension___closed__1();
lean_mark_persistent(l_Lean_MapDeclarationExtension_instInhabitedMapDeclarationExtension___closed__1);
l_Lean_instInhabitedModuleData___closed__1 = _init_l_Lean_instInhabitedModuleData___closed__1();
lean_mark_persistent(l_Lean_instInhabitedModuleData___closed__1);
l_Lean_instInhabitedModuleData = _init_l_Lean_instInhabitedModuleData();
lean_mark_persistent(l_Lean_instInhabitedModuleData);
l_Lean_Environment_freeRegions___closed__1 = _init_l_Lean_Environment_freeRegions___closed__1();
lean_mark_persistent(l_Lean_Environment_freeRegions___closed__1);
l_Nat_foldAux___at_Lean_mkModuleData___spec__1___closed__1 = _init_l_Nat_foldAux___at_Lean_mkModuleData___spec__1___closed__1();
lean_mark_persistent(l_Nat_foldAux___at_Lean_mkModuleData___spec__1___closed__1);
l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___closed__1 = _init_l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___closed__1();
lean_mark_persistent(l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___closed__1);
l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___closed__2 = _init_l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___closed__2();
lean_mark_persistent(l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___closed__2);
l___private_Lean_Environment_0__Lean_getEntriesFor___closed__1 = _init_l___private_Lean_Environment_0__Lean_getEntriesFor___closed__1();
lean_mark_persistent(l___private_Lean_Environment_0__Lean_getEntriesFor___closed__1);
l_Lean_ImportState_moduleNameSet___default = _init_l_Lean_ImportState_moduleNameSet___default();
lean_mark_persistent(l_Lean_ImportState_moduleNameSet___default);
l_Lean_ImportState_moduleNames___default = _init_l_Lean_ImportState_moduleNames___default();
lean_mark_persistent(l_Lean_ImportState_moduleNames___default);
l_Lean_ImportState_moduleData___default = _init_l_Lean_ImportState_moduleData___default();
lean_mark_persistent(l_Lean_ImportState_moduleData___default);
l_Lean_ImportState_regions___default = _init_l_Lean_ImportState_regions___default();
lean_mark_persistent(l_Lean_ImportState_regions___default);
l_Lean_importModules_importMods___closed__1 = _init_l_Lean_importModules_importMods___closed__1();
lean_mark_persistent(l_Lean_importModules_importMods___closed__1);
l_Lean_importModules_importMods___closed__2 = _init_l_Lean_importModules_importMods___closed__2();
lean_mark_persistent(l_Lean_importModules_importMods___closed__2);
l_Lean_importModules_importMods___closed__3 = _init_l_Lean_importModules_importMods___closed__3();
lean_mark_persistent(l_Lean_importModules_importMods___closed__3);
l_Lean_SMap_empty___at_Lean_importModules___spec__1 = _init_l_Lean_SMap_empty___at_Lean_importModules___spec__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_importModules___spec__1);
l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8___closed__1);
l_Lean_importModules___lambda__4___closed__1 = _init_l_Lean_importModules___lambda__4___closed__1();
lean_mark_persistent(l_Lean_importModules___lambda__4___closed__1);
l_Lean_importModules___lambda__4___closed__2 = _init_l_Lean_importModules___lambda__4___closed__2();
lean_mark_persistent(l_Lean_importModules___lambda__4___closed__2);
l_Lean_importModules___closed__1 = _init_l_Lean_importModules___closed__1();
lean_mark_persistent(l_Lean_importModules___closed__1);
l_Lean_importModules___closed__2 = _init_l_Lean_importModules___closed__2();
lean_mark_persistent(l_Lean_importModules___closed__2);
l_Lean_importModules___closed__3 = _init_l_Lean_importModules___closed__3();
lean_mark_persistent(l_Lean_importModules___closed__3);
l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_Environment___hyg_2919____spec__1___closed__1 = _init_l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_Environment___hyg_2919____spec__1___closed__1();
lean_mark_persistent(l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_Environment___hyg_2919____spec__1___closed__1);
l_Lean_initFn____x40_Lean_Environment___hyg_2919____closed__1 = _init_l_Lean_initFn____x40_Lean_Environment___hyg_2919____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Environment___hyg_2919____closed__1);
l_Lean_initFn____x40_Lean_Environment___hyg_2919____closed__2 = _init_l_Lean_initFn____x40_Lean_Environment___hyg_2919____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Environment___hyg_2919____closed__2);
l_Lean_initFn____x40_Lean_Environment___hyg_2919____closed__3 = _init_l_Lean_initFn____x40_Lean_Environment___hyg_2919____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Environment___hyg_2919____closed__3);
l_Lean_initFn____x40_Lean_Environment___hyg_2919____closed__4 = _init_l_Lean_initFn____x40_Lean_Environment___hyg_2919____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Environment___hyg_2919____closed__4);
l_Lean_initFn____x40_Lean_Environment___hyg_2919____closed__5 = _init_l_Lean_initFn____x40_Lean_Environment___hyg_2919____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Environment___hyg_2919____closed__5);
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
res = l_Lean_initFn____x40_Lean_Environment___hyg_2919_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_namespacesExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_namespacesExt);
lean_dec_ref(res);
l_Lean_Environment_displayStats___lambda__2___closed__1 = _init_l_Lean_Environment_displayStats___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Environment_displayStats___lambda__2___closed__1);
l_Lean_Environment_displayStats___lambda__2___closed__2 = _init_l_Lean_Environment_displayStats___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Environment_displayStats___lambda__2___closed__2);
l_Lean_Environment_displayStats___lambda__3___closed__1 = _init_l_Lean_Environment_displayStats___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Environment_displayStats___lambda__3___closed__1);
l_Lean_Environment_displayStats___lambda__3___closed__2 = _init_l_Lean_Environment_displayStats___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Environment_displayStats___lambda__3___closed__2);
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
l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg___closed__1 = _init_l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg___closed__1);
l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg___closed__2 = _init_l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg___closed__2);
l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg___closed__3 = _init_l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg___closed__3);
l_Lean_Environment_evalConstCheck___rarg___closed__1 = _init_l_Lean_Environment_evalConstCheck___rarg___closed__1();
lean_mark_persistent(l_Lean_Environment_evalConstCheck___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

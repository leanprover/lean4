// Lean compiler output
// Module: Lean.Environment
// Imports: Init Std.Data.HashMap Lean.Data.SMap Lean.Declaration Lean.LocalContext Lean.Util.Path Lean.Util.FindExpr
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
lean_object* l_Lean_Environment_Lean_Environment___instance__4___closed__5;
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Lean_Lean_Environment___instance__10___closed__5;
lean_object* l_List_toStringAux___at_Lean_Environment_displayStats___spec__2(uint8_t, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg___closed__2;
lean_object* l_Lean_Environment_hasUnsafe___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___at_Lean_initFn____x40_Lean_Environment___hyg_2730____spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_Environment_isNamespaceName___boxed(lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Lean_Environment___instance__5___closed__4;
lean_object* l_Lean_Environment_isNamespace___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_importModules___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__6___rarg(lean_object*);
lean_object* l_Lean_Environment_displayStats___closed__2;
lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg___closed__1;
lean_object* l_Lean_SimplePersistentEnvExtension_Lean_Environment___instance__11(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_setState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lean_Environment___instance__5___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Lean_Environment___instance__10___closed__3;
uint8_t l_Lean_EnvironmentHeader_quotInit___default;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__5___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Environment_displayStats___closed__6;
lean_object* l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Environment_find_x3f___spec__6___boxed(lean_object*, lean_object*);
lean_object* lean_display_stats(lean_object*, lean_object*);
lean_object* l_Lean_Environment_isConstructor_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withImportModules(lean_object*);
uint8_t l_Lean_Environment_isNamespace(lean_object*, lean_object*);
lean_object* l_Lean_importModulesAux___closed__1;
lean_object* l_Lean_namespacesExt___elambda__3(lean_object*, lean_object*);
lean_object* lean_environment_free_regions(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_setState(lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_importModulesAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_setImportedEntries(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_displayStats___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_Id_Init_Control_Id___instance__1___closed__5;
extern lean_object* l_List_repr___rarg___closed__1;
lean_object* l_Lean_registerSimplePersistentEnvExtension_match__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Environment_displayStats___closed__4;
lean_object* l_Lean_SimplePersistentEnvExtension_setState(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_setState(lean_object*);
lean_object* lean_serialize_modifications(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__4___rarg___boxed(lean_object*, lean_object*);
uint8_t l_Std_PersistentHashMap_containsAtAux___at_Lean_Environment_contains___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header___default;
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_importModulesAux___closed__2;
lean_object* l_Lean_Environment_imports(lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt(lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__5(lean_object*);
lean_object* l_Lean_Environment_displayStats___closed__8;
lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_2730____closed__4;
lean_object* l_Lean_Environment_hasUnsafe_match__2___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentHashMap_containsAux___at_Lean_Environment_contains___spec__4(lean_object*, size_t, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Environment_getModuleIdxFor_x3f___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__7___boxed(lean_object*);
extern lean_object* l_Std_HashMap_inhabited___closed__1;
lean_object* l_Lean_Lean_Environment___instance__10___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension___closed__1;
lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_mkTagDeclarationExtension___spec__3(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType(lean_object*);
lean_object* l_Lean_Lean_Environment___instance__3___closed__1;
lean_object* l_Lean_importModulesAux_match__3(lean_object*);
lean_object* l_Lean_importModulesAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_set_main_module(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_Lean_Environment___instance__11___rarg(lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_Environment_isQuotInit___boxed(lean_object*);
lean_object* lean_set_extension(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_Lean_Data_Name___instance__6;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg(lean_object*, lean_object*, lean_object*);
size_t l_USize_sub(size_t, size_t);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_registerSimplePersistentEnvExtension_match__1___rarg(lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Lean_Environment___instance__5___closed__2;
lean_object* l_Lean_Environment_evalConstCheck_match__1(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__8___boxed(lean_object*);
lean_object* lean_read_module_data(lean_object*, lean_object*);
lean_object* l_Lean_Name_quickLt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__3___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_importModules_match__5___rarg(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Lean_Environment___instance__5___closed__1;
lean_object* l___private_Lean_Environment_0__Lean_finalizePersistentExtensions(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension___closed__2;
lean_object* l_Lean_PersistentEnvExtension_setState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_allImportedModuleNames___boxed(lean_object*);
lean_object* l_Lean_importModulesAux___closed__3;
lean_object* l_Lean_EnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_TagDeclarationExtension_isTagged___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_hasUnsafe_match__2(lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_getEntriesFor(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* l_Lean_EnvExtension_getState(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_modifyState_match__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lean_Environment___instance__2;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Lean_Environment___instance__5;
lean_object* l_Lean_importModules_match__2(lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__4___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___at_Lean_Environment_addAux___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___at_Lean_registerSimplePersistentEnvExtension___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_namespacesExt___elambda__4___rarg(lean_object*);
lean_object* lean_register_extension(lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__3___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtension___rarg(lean_object*);
extern lean_object* l_List_repr___rarg___closed__3;
uint8_t l_Array_anyRangeMAux___at_Lean_mkTagDeclarationExtension___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_setState___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__4___rarg(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_modifyState(lean_object*);
lean_object* l_Lean_readModuleData___boxed(lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Lean_Environment_compileDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Environment_find_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg(lean_object*, lean_object*);
lean_object* l_Nat_foldAux___at_Lean_mkModuleData___spec__1___closed__1;
lean_object* l_Lean_namespacesExt___closed__2;
lean_object* l_Lean_namespacesExt___elambda__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4(lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Environment_find_x3f___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_importModules_match__4___rarg(lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___closed__3;
extern lean_object* l_Id_Init_Control_Id___instance__1___closed__4;
lean_object* l_Lean_SimplePersistentEnvExtension_modifyState(lean_object*, lean_object*);
lean_object* l_Std_AssocList_contains___at_Lean_importModules___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Nat_foldAux___at_Lean_mkModuleData___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_findOLean(lean_object*, lean_object*);
lean_object* l_Lean_namespacesExt___elambda__4___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_Lean_Environment___instance__7___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck_match__2(lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___closed__1;
lean_object* l_Lean_Name_toStringWithSep(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_contains___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkStateFromImportedEntries___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TagDeclarationExtension_isTagged_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_Environment_Lean_Environment___instance__4___spec__2(lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___closed__4;
lean_object* l_Lean_PersistentEnvExtension_setState(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_containsAux___at_Lean_Environment_contains___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp;
lean_object* l_Lean_mkEmptyEnvironment___lambda__1(uint32_t, lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtensionDescr_toArrayFn___default___rarg(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames___default;
uint8_t l_Lean_Environment_isConstructor(lean_object*, lean_object*);
lean_object* l_Lean_Environment_displayStats___closed__7;
lean_object* l_Lean_importModules_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_displayStats___closed__5;
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_mkModuleData___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lean_Environment___instance__3(lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_Environment_registerNamePrefixes_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Environment_find_x3f___spec__2(lean_object*, lean_object*);
lean_object* lean_write_module(lean_object*, lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
uint8_t l_Array_binSearchAux___at_Lean_TagDeclarationExtension_isTagged___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getEntries(lean_object*, lean_object*);
lean_object* l_Lean_Lean_Environment___instance__13;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__3___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Lean_Environment___instance__5___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_moveEntries___at_Lean_importModules___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_hasUnsafe___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_environment_add_modification(lean_object*, lean_object*);
lean_object* l_Lean_serializeModifications___boxed(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_modifyState_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_setState_match__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___at_Lean_mkModuleData___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
extern lean_object* l_Std_PersistentHashMap_insertAux___rarg___closed__3;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_Environment___hyg_2730____spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__3(lean_object*);
lean_object* l_Array_qpartition_loop___at_Lean_mkTagDeclarationExtension___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_environment_quot_init(lean_object*);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_Environment_isNamespaceName_match__1(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_finalizePersistentExtensions___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkTagDeclarationExtension___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_getEntriesFor___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lean_Environment___instance__15___rarg(lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_2730____closed__5;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkEmptyEnvironment___closed__1;
lean_object* l_Lean_EnvironmentHeader_mainModule___default;
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__3(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___at_Lean_mkModuleData___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_mkInitialExtensionStates(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_isConstructor_match__1(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_IO_getStdout___at_Lean_Environment_displayStats___spec__5(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_replace___at_Lean_Environment_addAux___spec__11(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_importModules_match__2___rarg(lean_object*, lean_object*);
lean_object* l_List_toStringAux___at_Lean_Environment_displayStats___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_Environment___hyg_2730____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_registerSimplePersistentEnvExtension___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_setImportedEntries___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_namespacesExt___elambda__1(lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_Lean_Environment___instance__5___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TagDeclarationExtension_isTagged_match__1(lean_object*);
uint8_t l___private_Lean_Environment_0__Lean_Environment_isNamespaceName(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_2730____closed__3;
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__1___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck(lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_Lean_Environment___instance__6(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__8(lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg(lean_object*, lean_object*);
uint8_t l_Lean_SMap_contains___at_Lean_Environment_contains___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_modifyState(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__7(lean_object*);
lean_object* l_IO_fileExists___at_Lean_importModulesAux___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__1(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtension(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_displayStats___closed__3;
lean_object* l_Lean_Lean_Environment___instance__1;
lean_object* l_Lean_mkEmptyEnvironment___closed__2;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_foldlM___at_Lean_Environment_addAux___spec__10(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_expand___at_Lean_importModules___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension___lambda__2(lean_object*);
extern lean_object* l_Init_Data_Repr___instance__15___closed__1;
lean_object* l___private_Lean_Environment_0__Lean_Environment_getTrustLevel___boxed(lean_object*);
lean_object* l_Lean_importModules___closed__3;
lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_eval_const(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_contains___at_Lean_Environment_contains___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Lean_SMap_switch___at_Lean_importModules___spec__10(lean_object*);
lean_object* l_Lean_performModifications___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lean_Environment___instance__14___closed__1;
uint32_t lean_environment_trust_level(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_setState___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___rarg___closed__1;
lean_object* l_Lean_importModulesAux_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_persistentEnvExtensionsRef;
lean_object* lean_environment_add(lean_object*, lean_object*);
lean_object* lean_save_module_data(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_importModulesAux_match__2(lean_object*);
lean_object* l_Lean_withImportModules___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_getState___rarg___boxed(lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_saveModuleData___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkModuleData(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_namespacesExt___elambda__1___boxed(lean_object*);
lean_object* l_Lean_mkEmptyEnvironment___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Init_LeanInit___instance__1;
lean_object* l_Lean_Environment_Lean_Environment___instance__4___closed__2;
lean_object* l_Lean_mkEmptyEnvironment___lambda__1___closed__1;
lean_object* l_Lean_PersistentEnvExtension_modifyState(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentHashMap_contains___at_Lean_Environment_contains___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtensionDescr_statsFn___default___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg___boxed(lean_object*, lean_object*);
size_t l_USize_mul(size_t, size_t);
lean_object* l_Lean_registerEnvExtension(lean_object*);
lean_object* l_Lean_importModules___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_Lean_Environment___instance__4;
lean_object* l_Lean_PersistentEnvExtension_getState(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionEntrySpec;
lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_1674____closed__1;
lean_object* l_Lean_importModules___closed__1;
lean_object* l_Array_qpartition_loop___at_Lean_mkTagDeclarationExtension___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_addDecl___boxed(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__6(lean_object*);
uint8_t lean_kernel_is_def_eq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CompactedRegion_free___boxed(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___closed__6;
extern lean_object* l_NonScalar_Inhabited;
lean_object* l_Array_anyRangeMAux___at_Lean_registerSimplePersistentEnvExtension___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__1(lean_object*, lean_object*);
uint8_t l_Lean_Format_isNil(lean_object*);
lean_object* l_Lean_Lean_Environment___instance__5___closed__3;
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Environment_find_x3f___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f_x27___at_Lean_Environment_find_x3f___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__1;
lean_object* l_Std_AssocList_replace___at_Lean_importModules___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__2;
lean_object* l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_mkEnvExtensionsRef(lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__6___rarg___boxed(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__3___boxed(lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_Environment_evalConstCheck___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvironmentHeader_regions___default;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_mkStateFromImportedEntries___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkEmptyEnvironment___boxed(lean_object*, lean_object*);
lean_object* lean_kernel_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___closed__2;
uint8_t l_Std_AssocList_contains___at_Lean_Environment_addAux___spec__7(lean_object*, lean_object*);
lean_object* l_fix1___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_importModules___closed__4;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp;
lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___at_Lean_mkModuleData___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8___closed__1;
lean_object* l_Lean_namespacesExt___elambda__2___boxed(lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Environment_addAux___spec__4(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_IO_Error_Init_System_IOError___instance__2___closed__1;
lean_object* l_Lean_Environment_Lean_Environment___instance__4___closed__3;
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1___closed__1;
lean_object* l_Lean_PersistentEnvExtension_setState___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_namespacesExt___elambda__2(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_modifyState___rarg___lambda__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_FindImpl_initCache;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_file_exists(lean_object*, lean_object*);
lean_object* lean_mk_empty_environment(uint32_t, lean_object*);
lean_object* l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Environment_addAux___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_import_modules(lean_object*, lean_object*, uint32_t, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Environment_getModuleIdxFor_x3f___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_TagDeclarationExtension_Lean_Environment___instance__12;
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_2730____lambda__1(lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___closed__1;
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* l_Lean_importModules_match__3(lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__4;
extern lean_object* l_String_splitAux___closed__1;
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__3(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtensionDescr_toArrayFn___default(lean_object*);
lean_object* l_Lean_Environment_evalConstCheck_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_mkRef___at___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_mkEnvExtensionsRef___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__2;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__4(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l_Lean_importModules_match__3___rarg(lean_object*, lean_object*);
lean_object* l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___lambda__1___closed__1;
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__6___boxed(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_modifyState___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withImportModules___rarg(lean_object*, lean_object*, uint32_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_Environment_registerNamePrefixes(lean_object*, lean_object*);
lean_object* l_Lean_mkStateFromImportedEntries(lean_object*, lean_object*);
lean_object* l_Lean_Environment_Lean_Environment___instance__4___closed__1;
lean_object* l_Lean_Environment_addAndCompile(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasUnsafe___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_namespacesExt___closed__5;
lean_object* l_Lean_EnvExtension_Lean_Environment___instance__7(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_importModulesAux_match__1___rarg(lean_object*, lean_object*);
lean_object* l_IO_fileExists___at_Lean_importModulesAux___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Environment_registerNamespace(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getNamespaceSet(lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1;
lean_object* l_Lean_EnvExtensionInterfaceImp___closed__2;
lean_object* l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg___closed__3;
lean_object* l_Lean_namespacesExt___closed__3;
lean_object* l_Std_PersistentHashMap_containsAtAux___at_Lean_Environment_contains___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_whnf___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lean_Environment___instance__10___lambda__3(lean_object*);
lean_object* l_Lean_Lean_Environment___instance__15(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__1;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_get_stdout(lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__4(lean_object*, lean_object*);
lean_object* l_Lean_Lean_Environment___instance__10(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Environment_find_x3f___spec__3(lean_object*, size_t, lean_object*);
lean_object* l_Array_forMAux___at_Lean_Environment_freeRegions___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Environment_find_x3f___spec__2___boxed(lean_object*, lean_object*);
extern lean_object* l_List_reprAux___rarg___closed__1;
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__2___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Environment_addAux___spec__9(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___at_Lean_initFn____x40_Lean_Environment___hyg_2730____spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_mkRef___at_Lean_initFn____x40_Lean_Environment___hyg_1102____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Environment_Lean_Environment___instance__4___closed__4;
lean_object* l_Lean_SimplePersistentEnvExtension_setState_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___boxed(lean_object*);
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_mkModuleData___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Environment_hasUnsafe_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__3;
lean_object* l_Array_iterateMAux___at_Lean_Environment_displayStats___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__5(lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Environment_displayStats___spec__1(lean_object*);
lean_object* l_Array_iterateMAux___at_Lean_initFn____x40_Lean_Environment___hyg_2730____spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_setState___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header___default___closed__1;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtensionDescr_statsFn___default(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_2730_(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_1102_(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_1674_(lean_object*);
lean_object* l_Lean_Lean_Environment___instance__9(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_getEntriesFor___closed__1;
lean_object* l_Lean_EnvExtension_modifyState___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lean_Environment___instance__10___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___closed__2;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_expand___at_Lean_Environment_addAux___spec__8(lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Environment_getModuleIdxFor_x3f___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
extern lean_object* l_Id_Init_Control_Id___instance__1;
lean_object* l_Lean_SMap_find_x3f_x27___at_Lean_Environment_find_x3f___spec__1___boxed(lean_object*, lean_object*);
uint8_t l_Std_AssocList_contains___at_Lean_importModules___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*);
lean_object* l_Std_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__9(lean_object*);
lean_object* lean_get_extension(lean_object*, lean_object*);
uint8_t l_Lean_Import_runtimeOnly___default;
lean_object* l_Std_AssocList_foldlM___at_Lean_importModules___spec__6(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__7;
extern lean_object* l_Array_Init_Data_Array_Basic___instance__3___rarg___closed__1;
lean_object* l_Array_forMAux___at_Lean_Environment_freeRegions___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___at_Lean_registerSimplePersistentEnvExtension___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
lean_object* l_Lean_Environment_hasUnsafe_match__1(lean_object*);
lean_object* l_Lean_Environment_addAux(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__5___rarg(lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__2(lean_object*);
lean_object* l_Array_forMAux___at_Lean_Environment_displayStats___spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__5;
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_namespacesExt___closed__1;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_Lean_Environment___instance__6___closed__2;
lean_object* l_Lean_Lean_Environment___instance__14;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___closed__7;
extern size_t l_Std_PersistentHashMap_insertAux___rarg___closed__2;
lean_object* l_Array_anyRangeMAux___at_Lean_mkTagDeclarationExtension___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getNamespaceSet___boxed(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Environment_getModuleIdxFor_x3f___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Lean_Environment___instance__10___lambda__2(lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__6(lean_object*);
lean_object* l_Lean_Lean_Environment___instance__10___lambda__2___boxed(lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_importModules___spec__1;
lean_object* l_Lean_namespacesExt___elambda__4(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_Environment_isNamespaceName_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_initializing(lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates(lean_object*);
lean_object* l_Lean_Lean_Environment___instance__15___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkStateFromImportedEntries___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_println___at_Lean_Environment_displayStats___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_modListExtension;
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__1(lean_object*);
lean_object* l_Array_iterateMAux___at_Lean_initFn____x40_Lean_Environment___hyg_2730____spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TagDeclarationExtension_isTagged___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findM_x3f_visit(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Environment_isConstructor___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck_match__2___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension(lean_object*, lean_object*);
lean_object* l_Lean_Environment_imports___boxed(lean_object*);
lean_object* l_Lean_EnvExtension_setState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lean_Environment___instance__8;
lean_object* l_Lean_namespacesExt;
lean_object* l_Array_iterateMAux___at_Lean_Environment_displayStats___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_importModules_match__1(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_finalizePersistentExtensions___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_namespacesExt___closed__4;
lean_object* l_IO_print___at_Lean_Environment_displayStats___spec__4(lean_object*, lean_object*);
lean_object* lean_compile_decl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_importModulesAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___closed__3;
lean_object* l_Lean_Lean_Environment___instance__5___lambda__3(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___elambda__5(lean_object*);
extern lean_object* l_Nat_Inhabited;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvironmentHeader_imports___default;
lean_object* l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_envExtensionsRef;
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_importModulesAux_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Environment_addAux___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_importModules_match__5(lean_object*);
uint8_t l_Std_HashMapImp_contains___at_Lean_Environment_contains___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___closed__1;
lean_object* l_Lean_SMap_insert___at_Lean_Environment_addAux___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_contains___at_Lean_Environment_addAux___spec__7___boxed(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___rarg(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_2730____closed__1;
lean_object* l_Lean_Environment_addAndCompile___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lean_Environment___instance__9___rarg(lean_object*);
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
lean_object* lean_perform_serialized_modifications(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_2730____closed__2;
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceImp___closed__5;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_contains___at_Lean_Environment_contains___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_importModules_match__4(lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Environment_find_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension___lambda__3(lean_object*);
lean_object* l_Lean_registerPersistentEnvExtension___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lean_Environment___instance__10___lambda__3___boxed(lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__6;
lean_object* l_Lean_Lean_Environment___instance__10___closed__4;
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Lean_Lean_Environment___instance__10___closed__1;
lean_object* l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___closed__1;
uint32_t l_Lean_EnvironmentHeader_trustLevel___default;
lean_object* l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension___closed__3;
lean_object* l_Std_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__9___boxed(lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_Environment_addAux___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lean_Environment___instance__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_Lean_Environment___instance__6___closed__1;
lean_object* l_Lean_importModules___closed__2;
lean_object* l_Lean_Kernel_isDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_compacted_region_free(size_t, lean_object*);
lean_object* l_Lean_Lean_Environment___instance__10___closed__2;
lean_object* l_Lean_mkTagDeclarationExtension___lambda__2___boxed(lean_object*);
lean_object* l_List_mapA___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_setState___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_mkModuleData___boxed(lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_Environment_Lean_Environment___instance__4___spec__1(lean_object*);
lean_object* l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionStateSpec;
lean_object* lean_environment_mark_quot_init(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_Environment_registerNamePrefixes_match__1(lean_object*);
lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_Lean_Environment___instance__6___lambda__1(lean_object*);
lean_object* l_Lean_TagDeclarationExtension_Lean_Environment___instance__12___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_importModulesAux_match__1(lean_object*);
lean_object* lean_add_decl(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_contains___at_Lean_Environment_contains___spec__2___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Lean_EnvExtensionStateSpec() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lean_Environment___instance__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lean_Environment___instance__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_Inhabited;
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
static lean_object* _init_l_Lean_Lean_Environment___instance__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" (runtime)");
return x_1;
}
}
lean_object* l_Lean_Lean_Environment___instance__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_System_FilePath_dirName___closed__1;
x_4 = l_Lean_Name_toStringWithSep(x_3, x_2);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_dec(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_String_splitAux___closed__1;
x_7 = lean_string_append(x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Lean_Environment___instance__3___closed__1;
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
x_1 = l_Lean_NameSet_empty;
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_header___default___closed__1() {
_start:
{
uint32_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 0;
x_2 = 0;
x_3 = lean_box(0);
x_4 = l_Array_empty___closed__1;
x_5 = l_Lean_NameSet_empty;
x_6 = lean_alloc_ctor(0, 4, 5);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_5);
lean_ctor_set_uint32(x_6, sizeof(void*)*4, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*4 + 4, x_2);
return x_6;
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
lean_object* l_Std_mkHashMap___at_Lean_Environment_Lean_Environment___instance__4___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_Std_mkHashMap___at_Lean_Environment_Lean_Environment___instance__4___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Environment_Lean_Environment___instance__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Environment_Lean_Environment___instance__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Environment_Lean_Environment___instance__4___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Environment_Lean_Environment___instance__4___closed__2;
x_3 = l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Environment_Lean_Environment___instance__4___closed__4() {
_start:
{
uint32_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 0;
x_2 = 0;
x_3 = lean_box(0);
x_4 = l_Array_empty___closed__1;
x_5 = l_Lean_NameSet_empty;
x_6 = lean_alloc_ctor(0, 4, 5);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_5);
lean_ctor_set_uint32(x_6, sizeof(void*)*4, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*4 + 4, x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_Environment_Lean_Environment___instance__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Environment_Lean_Environment___instance__4___closed__1;
x_2 = l_Lean_Environment_Lean_Environment___instance__4___closed__3;
x_3 = l_Array_empty___closed__1;
x_4 = l_Lean_Environment_Lean_Environment___instance__4___closed__4;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Environment_Lean_Environment___instance__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Environment_Lean_Environment___instance__4___closed__5;
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
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Environment_addAux___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_11 = x_2 & x_10;
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(2);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_name_eq(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_name_eq(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = x_2 >> x_9;
x_37 = x_3 + x_8;
x_38 = l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = x_2 >> x_9;
x_42 = x_3 + x_8;
x_43 = l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_52 = x_2 & x_51;
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(2);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = lean_name_eq(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = x_2 >> x_50;
x_74 = x_3 + x_49;
x_75 = l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_1);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; size_t x_85; uint8_t x_86; 
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Environment_addAux___spec__5(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = x_85 <= x_3;
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
x_88 = lean_unsigned_to_nat(4u);
x_89 = lean_nat_dec_lt(x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = l_Std_PersistentHashMap_insertAux___rarg___closed__3;
x_93 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Environment_addAux___spec__4(x_3, x_90, x_91, lean_box(0), x_83, x_92);
lean_dec(x_91);
lean_dec(x_90);
return x_93;
}
else
{
return x_84;
}
}
else
{
return x_84;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; uint8_t x_100; 
x_94 = lean_ctor_get(x_1, 0);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_1);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Environment_addAux___spec__5(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = x_99 <= x_3;
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
x_102 = lean_unsigned_to_nat(4u);
x_103 = lean_nat_dec_lt(x_101, x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_dec(x_98);
x_106 = l_Std_PersistentHashMap_insertAux___rarg___closed__3;
x_107 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Environment_addAux___spec__4(x_3, x_104, x_105, lean_box(0), x_97, x_106);
lean_dec(x_105);
lean_dec(x_104);
return x_107;
}
else
{
return x_98;
}
}
else
{
return x_98;
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
uint8_t l_Std_AssocList_contains___at_Lean_Environment_addAux___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_AssocList_foldlM___at_Lean_Environment_addAux___spec__10(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l_Lean_Name_hash(x_12);
x_17 = lean_usize_modn(x_16, x_15);
lean_dec(x_15);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Environment_addAux___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_foldlM___at_Lean_Environment_addAux___spec__10(x_3, x_6);
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
lean_object* l_Std_HashMapImp_expand___at_Lean_Environment_addAux___spec__8(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_HashMapImp_moveEntries___at_Lean_Environment_addAux___spec__9(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_Std_AssocList_replace___at_Lean_Environment_addAux___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_Std_AssocList_replace___at_Lean_Environment_addAux___spec__11(x_1, x_2, x_8);
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
x_15 = l_Std_AssocList_replace___at_Lean_Environment_addAux___spec__11(x_1, x_2, x_13);
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
lean_object* l_Std_HashMapImp_insert___at_Lean_Environment_addAux___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_11 = l_Std_AssocList_contains___at_Lean_Environment_addAux___spec__7(x_2, x_10);
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
x_17 = l_Std_HashMapImp_expand___at_Lean_Environment_addAux___spec__8(x_13, x_15);
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
x_18 = l_Std_AssocList_replace___at_Lean_Environment_addAux___spec__11(x_2, x_3, x_10);
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
x_26 = l_Std_AssocList_contains___at_Lean_Environment_addAux___spec__7(x_2, x_25);
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
x_32 = l_Std_HashMapImp_expand___at_Lean_Environment_addAux___spec__8(x_28, x_30);
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
x_34 = l_Std_AssocList_replace___at_Lean_Environment_addAux___spec__11(x_2, x_3, x_25);
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
x_16 = l_Std_HashMapImp_insert___at_Lean_Environment_addAux___spec__6(x_15, x_2, x_3);
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
x_20 = l_Std_HashMapImp_insert___at_Lean_Environment_addAux___spec__6(x_18, x_2, x_3);
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
lean_object* l_Std_AssocList_contains___at_Lean_Environment_addAux___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___at_Lean_Environment_addAux___spec__7(x_1, x_2);
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
x_8 = l_Std_AssocList_contains___at_Lean_Environment_addAux___spec__7(x_2, x_7);
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
lean_object* l_Lean_Lean_Environment___instance__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Lean_Environment___instance__5___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_3);
return x_3;
}
}
lean_object* l_Lean_Lean_Environment___instance__5___lambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lean_Environment___instance__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_empty___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Lean_Environment___instance__5___lambda__3), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lean_Environment___instance__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lean_Environment___instance__5___lambda__1), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lean_Environment___instance__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lean_Environment___instance__5___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lean_Environment___instance__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Id_Init_Control_Id___instance__1___closed__4;
x_2 = l_Lean_Lean_Environment___instance__5___closed__2;
x_3 = l_Lean_Lean_Environment___instance__5___closed__3;
x_4 = l_Id_Init_Control_Id___instance__1___closed__5;
x_5 = l_Lean_Lean_Environment___instance__5___closed__1;
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
static lean_object* _init_l_Lean_Lean_Environment___instance__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lean_Environment___instance__5___closed__4;
return x_1;
}
}
lean_object* l_Lean_Lean_Environment___instance__5___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Lean_Environment___instance__5___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_Lean_Environment___instance__6___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_Error_Init_System_IOError___instance__2___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_Lean_Environment___instance__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_Lean_Environment___instance__6___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_Lean_Environment___instance__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_EnvExtensionInterfaceUnsafe_Lean_Environment___instance__6___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_Lean_Environment___instance__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_EnvExtensionInterfaceUnsafe_Lean_Environment___instance__6___closed__2;
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
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_array_fget(x_5, x_6);
x_10 = lean_box(0);
x_11 = lean_array_fset(x_5, x_6, x_10);
x_12 = x_9;
x_13 = lean_apply_1(x_3, x_12);
x_14 = x_13;
x_15 = lean_array_fset(x_11, x_6, x_14);
lean_ctor_set(x_2, 2, x_15);
return x_2;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_ctor_get(x_2, 2);
x_19 = lean_ctor_get(x_2, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_array_get_size(x_18);
x_22 = lean_nat_dec_lt(x_20, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_3);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_18);
lean_ctor_set(x_23, 3, x_19);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_array_fget(x_18, x_20);
x_25 = lean_box(0);
x_26 = lean_array_fset(x_18, x_20, x_25);
x_27 = x_24;
x_28 = lean_apply_1(x_3, x_27);
x_29 = x_28;
x_30 = lean_array_fset(x_26, x_20, x_29);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_16);
lean_ctor_set(x_31, 1, x_17);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set(x_31, 3, x_19);
return x_31;
}
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
x_5 = l_Lean_Lean_Environment___instance__1;
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
lean_object* l_Array_umapMAux___at_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = x_2;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_array_fget(x_2, x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_fset(x_2, x_1, x_9);
x_11 = x_8;
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_apply_1(x_12, x_3);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_1, x_16);
x_18 = x_14;
x_19 = lean_array_fset(x_10, x_1, x_18);
lean_dec(x_1);
x_1 = x_17;
x_2 = x_19;
x_3 = x_15;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_10);
lean_dec(x_1);
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
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_envExtensionsRef;
x_3 = lean_st_ref_get(x_2, x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = x_4;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_closure((void*)(l_Array_umapMAux___at_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates___spec__1), 3, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_6);
x_9 = x_8;
x_10 = lean_apply_1(x_9, x_5);
return x_10;
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_array_fget(x_5, x_6);
x_10 = lean_box(0);
x_11 = lean_array_fset(x_5, x_6, x_10);
x_12 = x_9;
x_13 = lean_apply_1(x_3, x_12);
x_14 = x_13;
x_15 = lean_array_fset(x_11, x_6, x_14);
lean_ctor_set(x_2, 2, x_15);
return x_2;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_ctor_get(x_2, 2);
x_19 = lean_ctor_get(x_2, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_array_get_size(x_18);
x_22 = lean_nat_dec_lt(x_20, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_3);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_18);
lean_ctor_set(x_23, 3, x_19);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_array_fget(x_18, x_20);
x_25 = lean_box(0);
x_26 = lean_array_fset(x_18, x_20, x_25);
x_27 = x_24;
x_28 = lean_apply_1(x_3, x_27);
x_29 = x_28;
x_30 = lean_array_fset(x_26, x_20, x_29);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_16);
lean_ctor_set(x_31, 1, x_17);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set(x_31, 3, x_19);
return x_31;
}
}
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
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_Lean_Environment___instance__6___closed__2;
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
lean_object* lean_register_extension(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Lean_Environment___instance__5___lambda__3), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_box(0);
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
}
}
lean_object* lean_set_extension(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_envExtensionsRef;
x_5 = lean_box(0);
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_Lean_Environment___instance__6___lambda__1), 1, 0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_array_get(x_10, x_7, x_2);
lean_dec(x_2);
lean_dec(x_7);
x_12 = l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg(x_11, x_1, x_3);
lean_dec(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
lean_object* lean_get_extension(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_envExtensionsRef;
x_4 = lean_box(0);
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_Lean_Environment___instance__6___lambda__1), 1, 0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_array_get(x_9, x_6, x_2);
lean_dec(x_2);
lean_dec(x_6);
x_11 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_10, x_1);
lean_dec(x_1);
lean_dec(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
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
lean_object* l_Lean_EnvExtension_Lean_Environment___instance__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_Lean_Environment___instance__6___closed__2;
return x_3;
}
}
lean_object* l_Lean_EnvExtension_Lean_Environment___instance__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EnvExtension_Lean_Environment___instance__7(x_1, x_2);
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
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg(x_1, x_2, x_3);
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
x_2 = l_Std_HashMap_inhabited___closed__1;
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
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = 0;
x_8 = lean_box(0);
x_9 = l_Array_empty___closed__1;
x_10 = l_Lean_NameSet_empty;
x_11 = lean_alloc_ctor(0, 4, 5);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_9);
lean_ctor_set(x_11, 3, x_10);
lean_ctor_set_uint32(x_11, sizeof(void*)*4, x_1);
lean_ctor_set_uint8(x_11, sizeof(void*)*4 + 4, x_7);
x_12 = l_Std_HashMap_inhabited___closed__1;
x_13 = l_Lean_mkEmptyEnvironment___lambda__1___closed__1;
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_6);
lean_ctor_set(x_14, 3, x_11);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_17 = 0;
x_18 = lean_box(0);
x_19 = l_Array_empty___closed__1;
x_20 = l_Lean_NameSet_empty;
x_21 = lean_alloc_ctor(0, 4, 5);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_19);
lean_ctor_set(x_21, 3, x_20);
lean_ctor_set_uint32(x_21, sizeof(void*)*4, x_1);
lean_ctor_set_uint8(x_21, sizeof(void*)*4 + 4, x_17);
x_22 = l_Std_HashMap_inhabited___closed__1;
x_23 = l_Lean_mkEmptyEnvironment___lambda__1___closed__1;
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_15);
lean_ctor_set(x_24, 3, x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_16);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_4);
if (x_26 == 0)
{
return x_4;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_4, 0);
x_28 = lean_ctor_get(x_4, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_4);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
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
static lean_object* _init_l_Lean_Lean_Environment___instance__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* l_Lean_Lean_Environment___instance__9___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Lean_Environment___instance__9(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Lean_Environment___instance__9___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Lean_Environment___instance__10___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_IO_Error_Init_System_IOError___instance__2___closed__1;
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Lean_Environment___instance__10___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_empty___closed__1;
return x_2;
}
}
lean_object* l_Lean_Lean_Environment___instance__10___lambda__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lean_Lean_Environment___instance__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lean_Environment___instance__10___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lean_Environment___instance__10___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_fix1___rarg___lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lean_Environment___instance__10___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lean_Environment___instance__10___lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lean_Environment___instance__10___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lean_Environment___instance__10___lambda__3___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lean_Environment___instance__10___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_EnvExtensionInterfaceUnsafe_Lean_Environment___instance__6___closed__2;
x_2 = lean_box(0);
x_3 = l_Lean_Lean_Environment___instance__10___closed__1;
x_4 = l_Lean_Lean_Environment___instance__10___closed__2;
x_5 = l_Lean_Lean_Environment___instance__10___closed__3;
x_6 = l_Lean_Lean_Environment___instance__10___closed__4;
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
lean_object* l_Lean_Lean_Environment___instance__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Lean_Environment___instance__10___closed__5;
return x_5;
}
}
lean_object* l_Lean_Lean_Environment___instance__10___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Lean_Environment___instance__10___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Lean_Environment___instance__10___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lean_Environment___instance__10___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Lean_Environment___instance__10___lambda__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lean_Environment___instance__10___lambda__3(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Lean_Environment___instance__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Lean_Environment___instance__10(x_1, x_2, x_3, x_4);
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
x_6 = l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg(x_4, x_2, x_5);
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
x_6 = l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg(x_4, x_2, x_5);
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
x_6 = l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg(x_4, x_2, x_5);
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
lean_object* l_IO_mkRef___at_Lean_initFn____x40_Lean_Environment___hyg_1102____spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_1102_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Array_empty___closed__1;
x_3 = l_IO_mkRef___at_Lean_initFn____x40_Lean_Environment___hyg_1102____spec__1(x_2, x_1);
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
uint8_t l_Array_anyRangeMAux___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_name_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_5 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_5);
x_15 = 1;
return x_15;
}
}
}
}
lean_object* l_Array_anyRangeMAux___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_anyRangeMAux___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg___boxed), 5, 0);
return x_4;
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Array_empty___closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = l_Array_empty___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
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
x_10 = lean_alloc_closure((void*)(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__1), 2, 1);
lean_closure_set(x_10, 0, x_5);
x_11 = l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(x_10, x_3);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_6);
lean_ctor_set(x_14, 3, x_7);
lean_ctor_set(x_14, 4, x_8);
lean_ctor_set(x_14, 5, x_9);
x_15 = l_Lean_persistentEnvExtensionsRef;
x_16 = lean_st_ref_take(x_15, x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_14);
x_19 = x_14;
x_20 = lean_array_push(x_17, x_19);
x_21 = lean_st_ref_set(x_15, x_20, x_18);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_14);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_11);
if (x_26 == 0)
{
return x_11;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_11);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg(x_1, x_6, x_6, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_free_object(x_4);
x_11 = lean_box(0);
x_12 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_11, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_System_FilePath_dirName___closed__1;
x_15 = l_Lean_Name_toStringWithSep(x_14, x_13);
x_16 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_20);
return x_4;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
x_23 = lean_array_get_size(x_21);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Array_anyRangeMAux___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg(x_1, x_21, x_21, x_23, x_24);
lean_dec(x_23);
lean_dec(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_26, x_22);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = l_System_FilePath_dirName___closed__1;
x_30 = l_Lean_Name_toStringWithSep(x_29, x_28);
x_31 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_32 = lean_string_append(x_31, x_30);
lean_dec(x_30);
x_33 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_22);
return x_36;
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
lean_object* l_Array_anyRangeMAux___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
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
x_2 = l_IO_Error_Init_System_IOError___instance__2___closed__1;
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
lean_object* l_Lean_mkStateFromImportedEntries___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_alloc_closure((void*)(l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___rarg___lambda__2___boxed), 4, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Id_Init_Control_Id___instance__1;
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_iterateMAux___rarg(x_6, lean_box(0), x_3, x_5, x_7, x_4);
return x_8;
}
}
lean_object* l_Lean_mkStateFromImportedEntries___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_alloc_closure((void*)(l_Lean_mkStateFromImportedEntries___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Id_Init_Control_Id___instance__1;
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_iterateMAux___rarg(x_5, lean_box(0), x_3, x_4, x_6, x_2);
return x_7;
}
}
lean_object* l_Lean_mkStateFromImportedEntries(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_mkStateFromImportedEntries___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_mkStateFromImportedEntries___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkStateFromImportedEntries___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
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
uint8_t l_Array_anyRangeMAux___at_Lean_registerSimplePersistentEnvExtension___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_name_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_5 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_5);
x_15 = 1;
return x_15;
}
}
}
}
lean_object* l_Array_anyRangeMAux___at_Lean_registerSimplePersistentEnvExtension___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_anyRangeMAux___at_Lean_registerSimplePersistentEnvExtension___spec__2___rarg___boxed), 5, 0);
return x_3;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___at_Lean_registerSimplePersistentEnvExtension___spec__2___rarg(x_1, x_6, x_6, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_free_object(x_4);
x_11 = lean_box(0);
x_12 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_11, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_System_FilePath_dirName___closed__1;
x_15 = l_Lean_Name_toStringWithSep(x_14, x_13);
x_16 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_20);
return x_4;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
x_23 = lean_array_get_size(x_21);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Array_anyRangeMAux___at_Lean_registerSimplePersistentEnvExtension___spec__2___rarg(x_1, x_21, x_21, x_23, x_24);
lean_dec(x_23);
lean_dec(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_26, x_22);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = l_System_FilePath_dirName___closed__1;
x_30 = l_Lean_Name_toStringWithSep(x_29, x_28);
x_31 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_32 = lean_string_append(x_31, x_30);
lean_dec(x_30);
x_33 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_22);
return x_36;
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
x_4 = l_List_lengthAux___main___rarg(x_2, x_3);
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
x_10 = lean_alloc_closure((void*)(l_Lean_Lean_Environment___instance__5___lambda__3), 2, 1);
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
lean_object* l_Array_anyRangeMAux___at_Lean_registerSimplePersistentEnvExtension___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___at_Lean_registerSimplePersistentEnvExtension___spec__2___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
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
lean_object* l_Lean_SimplePersistentEnvExtension_Lean_Environment___instance__11___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
x_4 = l_Lean_Lean_Environment___instance__10(lean_box(0), lean_box(0), lean_box(0), x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_SimplePersistentEnvExtension_Lean_Environment___instance__11(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_Lean_Environment___instance__11___rarg), 1, 0);
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
lean_object* l_Array_qpartition_loop___at_Lean_mkTagDeclarationExtension___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_10 = l_Lean_Init_LeanInit___instance__1;
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
static lean_object* _init_l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickLt___boxed), 2, 0);
return x_1;
}
}
lean_object* l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_2, x_3);
if (x_13 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_14 = lean_nat_add(x_2, x_3);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_div(x_14, x_15);
lean_dec(x_14);
x_41 = l_Lean_Init_LeanInit___instance__1;
x_42 = lean_array_get(x_41, x_1, x_16);
x_43 = lean_array_get(x_41, x_1, x_2);
x_44 = l_Lean_Name_quickLt(x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
if (x_44 == 0)
{
x_17 = x_1;
goto block_40;
}
else
{
lean_object* x_45; 
x_45 = lean_array_swap(x_1, x_2, x_16);
x_17 = x_45;
goto block_40;
}
block_40:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = l_Lean_Init_LeanInit___instance__1;
x_19 = lean_array_get(x_18, x_17, x_3);
x_20 = lean_array_get(x_18, x_17, x_2);
x_21 = l_Lean_Name_quickLt(x_19, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_array_get(x_18, x_17, x_16);
x_23 = l_Lean_Name_quickLt(x_22, x_19);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
x_24 = l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1___closed__1;
lean_inc_n(x_2, 2);
x_25 = l_Array_qpartition_loop___at_Lean_mkTagDeclarationExtension___spec__2(x_24, x_3, x_19, x_17, x_2, x_2);
x_4 = x_25;
goto block_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_19);
x_26 = lean_array_swap(x_17, x_16, x_3);
lean_dec(x_16);
x_27 = lean_array_get(x_18, x_26, x_3);
x_28 = l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1___closed__1;
lean_inc_n(x_2, 2);
x_29 = l_Array_qpartition_loop___at_Lean_mkTagDeclarationExtension___spec__2(x_28, x_3, x_27, x_26, x_2, x_2);
x_4 = x_29;
goto block_12;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_19);
x_30 = lean_array_swap(x_17, x_2, x_3);
x_31 = lean_array_get(x_18, x_30, x_16);
x_32 = lean_array_get(x_18, x_30, x_3);
x_33 = l_Lean_Name_quickLt(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_16);
x_34 = l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1___closed__1;
lean_inc_n(x_2, 2);
x_35 = l_Array_qpartition_loop___at_Lean_mkTagDeclarationExtension___spec__2(x_34, x_3, x_32, x_30, x_2, x_2);
x_4 = x_35;
goto block_12;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_32);
x_36 = lean_array_swap(x_30, x_16, x_3);
lean_dec(x_16);
x_37 = lean_array_get(x_18, x_36, x_3);
x_38 = l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1___closed__1;
lean_inc_n(x_2, 2);
x_39 = l_Array_qpartition_loop___at_Lean_mkTagDeclarationExtension___spec__2(x_38, x_3, x_37, x_36, x_2, x_2);
x_4 = x_39;
goto block_12;
}
}
}
}
block_12:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_nat_dec_le(x_3, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1(x_6, x_2, x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_5, x_9);
lean_dec(x_5);
x_1 = x_8;
x_2 = x_10;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
}
}
uint8_t l_Array_anyRangeMAux___at_Lean_mkTagDeclarationExtension___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_name_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_5 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_5);
x_15 = 1;
return x_15;
}
}
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkTagDeclarationExtension___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_persistentEnvExtensionsRef;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___at_Lean_mkTagDeclarationExtension___spec__5(x_1, x_6, x_6, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_free_object(x_4);
x_11 = lean_box(0);
x_12 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_11, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_System_FilePath_dirName___closed__1;
x_15 = l_Lean_Name_toStringWithSep(x_14, x_13);
x_16 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_20);
return x_4;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
x_23 = lean_array_get_size(x_21);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Array_anyRangeMAux___at_Lean_mkTagDeclarationExtension___spec__5(x_1, x_21, x_21, x_23, x_24);
lean_dec(x_23);
lean_dec(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_26, x_22);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = l_System_FilePath_dirName___closed__1;
x_30 = l_Lean_Name_toStringWithSep(x_29, x_28);
x_31 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_32 = lean_string_append(x_31, x_30);
lean_dec(x_30);
x_33 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_22);
return x_36;
}
}
}
}
lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_mkTagDeclarationExtension___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_9 = lean_alloc_closure((void*)(l_Lean_Lean_Environment___instance__5___lambda__3), 2, 1);
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
x_15 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkTagDeclarationExtension___spec__4(x_14, x_2);
return x_15;
}
}
lean_object* l_Lean_mkTagDeclarationExtension___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_2, x_3);
return x_4;
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = l_List_redLength___rarg(x_1);
x_3 = lean_mk_empty_array_with_capacity(x_2);
lean_dec(x_2);
x_4 = l_List_toArrayAux___rarg(x_1, x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_5, x_6);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1(x_4, x_8, x_7);
lean_dec(x_7);
return x_9;
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
x_7 = l_Lean_registerSimplePersistentEnvExtension___at_Lean_mkTagDeclarationExtension___spec__3(x_6, x_2);
return x_7;
}
}
lean_object* l_Array_qpartition_loop___at_Lean_mkTagDeclarationExtension___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qpartition_loop___at_Lean_mkTagDeclarationExtension___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Array_anyRangeMAux___at_Lean_mkTagDeclarationExtension___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___at_Lean_mkTagDeclarationExtension___spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
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
static lean_object* _init_l_Lean_TagDeclarationExtension_Lean_Environment___instance__12___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_NameSet_Lean_Data_Name___instance__6;
x_2 = l_Lean_SimplePersistentEnvExtension_Lean_Environment___instance__11___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_Lean_Environment___instance__12() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_TagDeclarationExtension_Lean_Environment___instance__12___closed__1;
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
uint8_t l_Array_binSearchAux___at_Lean_TagDeclarationExtension_isTagged___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Lean_Init_LeanInit___instance__1;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = l_Lean_Name_quickLt(x_11, x_2);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_4);
x_13 = l_Lean_Name_quickLt(x_2, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_9);
lean_dec(x_3);
x_14 = 1;
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_9, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_9, x_17);
lean_dec(x_9);
x_4 = x_18;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_9);
lean_dec(x_3);
x_20 = 0;
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_3);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_9, x_21);
lean_dec(x_9);
x_3 = x_22;
goto _start;
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
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = l_Lean_PersistentEnvExtension_getModuleEntries___rarg(x_1, x_2, x_7);
lean_dec(x_7);
x_9 = lean_array_get_size(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_9, x_10);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_binSearchAux___at_Lean_TagDeclarationExtension_isTagged___spec__1(x_8, x_3, x_12, x_11);
lean_dec(x_8);
return x_13;
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_TagDeclarationExtension_isTagged___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_binSearchAux___at_Lean_TagDeclarationExtension_isTagged___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Lean_TagDeclarationExtension_isTagged___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_TagDeclarationExtension_isTagged(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Lean_Environment___instance__13() {
_start:
{
lean_object* x_1; 
x_1 = l_NonScalar_Inhabited;
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Environment___hyg_1674____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_Lean_Lean_Environment___instance__5___lambda__3), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_1674_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_initFn____x40_Lean_Environment___hyg_1674____closed__1;
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(x_2, x_1);
return x_3;
}
}
lean_object* lean_environment_add_modification(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_List_mapA___rarg___lambda__1), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_modListExtension;
x_5 = l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg(x_4, x_1, x_3);
return x_5;
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
static lean_object* _init_l_Lean_Lean_Environment___instance__14___closed__1() {
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
static lean_object* _init_l_Lean_Lean_Environment___instance__14() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lean_Environment___instance__14___closed__1;
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
lean_object* l_Array_forMAux___at_Lean_Environment_freeRegions___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_array_fget(x_1, x_2);
x_9 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_10 = lean_compacted_region_free(x_9, x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_11;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
}
lean_object* lean_environment_free_regions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_forMAux___at_Lean_Environment_freeRegions___spec__1(x_4, x_5, x_2);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Array_forMAux___at_Lean_Environment_freeRegions___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_forMAux___at_Lean_Environment_freeRegions___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Nat_foldAux___at_Lean_mkModuleData___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lean_Environment___instance__1;
x_2 = l_Lean_Lean_Environment___instance__10(lean_box(0), lean_box(0), lean_box(0), x_1);
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
lean_object* l_Array_iterateMAux___at_Lean_mkModuleData___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_3, x_8);
lean_dec(x_3);
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_array_push(x_4, x_10);
x_3 = x_9;
x_4 = x_11;
goto _start;
}
case 1:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec(x_7);
x_14 = l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3(x_13, x_4);
lean_dec(x_13);
x_3 = x_9;
x_4 = x_14;
goto _start;
}
default: 
{
x_3 = x_9;
goto _start;
}
}
}
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__5___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_1 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_iterateMAux___at_Lean_mkModuleData___spec__4(x_3, x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___closed__1;
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__5___rarg(x_8, x_6, x_7, lean_box(0), x_9, x_2);
return x_10;
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = l_Lean_persistentEnvExtensionsRef;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_array_get_size(x_5);
x_8 = l_Array_empty___closed__1;
lean_inc(x_7);
x_9 = l_Nat_foldAux___at_Lean_mkModuleData___spec__1(x_1, x_5, x_7, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
x_10 = l_Lean_modListExtension;
x_11 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_10, x_1);
x_12 = lean_serialize_modifications(x_11, x_6);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_1, 3);
x_16 = lean_ctor_get(x_15, 1);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_17, 1);
x_19 = l_Std_PersistentHashMap_foldlM___at_Lean_mkModuleData___spec__2(x_18, x_8);
lean_inc(x_16);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_9);
lean_ctor_set(x_20, 3, x_14);
lean_ctor_set(x_12, 0, x_20);
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_ctor_get(x_1, 3);
x_24 = lean_ctor_get(x_23, 1);
x_25 = lean_ctor_get(x_1, 1);
x_26 = lean_ctor_get(x_25, 1);
x_27 = l_Std_PersistentHashMap_foldlM___at_Lean_mkModuleData___spec__2(x_26, x_8);
lean_inc(x_24);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_9);
lean_ctor_set(x_28, 3, x_21);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_22);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_9);
x_30 = !lean_is_exclusive(x_12);
if (x_30 == 0)
{
return x_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_12, 0);
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_12);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
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
lean_object* l_Array_iterateMAux___at_Lean_mkModuleData___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___at_Lean_mkModuleData___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___lambda__1(x_1, x_2, x_3);
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
lean_object* x_4; 
x_4 = l_Lean_mkModuleData(x_1, x_3);
lean_dec(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_save_module_data(x_2, x_5, x_6);
lean_dec(x_2);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
lean_object* l_Lean_importModulesAux_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_importModulesAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_importModulesAux_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_importModulesAux_match__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_importModulesAux_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_importModulesAux_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_importModulesAux_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_apply_1(x_3, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_apply_5(x_4, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
}
lean_object* l_Lean_importModulesAux_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_importModulesAux_match__3___rarg), 4, 0);
return x_2;
}
}
lean_object* l_IO_fileExists___at_Lean_importModulesAux___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_file_exists(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_importModulesAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_read_module_data(x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = l_Array_toList___rarg(x_14);
lean_dec(x_14);
lean_ctor_set(x_9, 1, x_3);
lean_ctor_set(x_9, 0, x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_9);
x_17 = l_Lean_importModulesAux(x_15, x_16, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_18, 1);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
x_26 = lean_array_push(x_24, x_12);
x_27 = lean_array_push(x_25, x_13);
lean_ctor_set(x_19, 1, x_27);
lean_ctor_set(x_19, 0, x_26);
x_28 = l_Lean_importModulesAux(x_5, x_18, x_20);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_19, 0);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_19);
x_31 = lean_array_push(x_29, x_12);
x_32 = lean_array_push(x_30, x_13);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_18, 1, x_33);
x_34 = l_Lean_importModulesAux(x_5, x_18, x_20);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_18, 0);
lean_inc(x_35);
lean_dec(x_18);
x_36 = lean_ctor_get(x_19, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_19, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_38 = x_19;
} else {
 lean_dec_ref(x_19);
 x_38 = lean_box(0);
}
x_39 = lean_array_push(x_36, x_12);
x_40 = lean_array_push(x_37, x_13);
if (lean_is_scalar(x_38)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_38;
}
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_35);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_importModulesAux(x_5, x_42, x_20);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
x_44 = !lean_is_exclusive(x_17);
if (x_44 == 0)
{
return x_17;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_17, 0);
x_46 = lean_ctor_get(x_17, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_17);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_9, 0);
x_49 = lean_ctor_get(x_9, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_9);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
x_51 = l_Array_toList___rarg(x_50);
lean_dec(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_2);
lean_ctor_set(x_52, 1, x_3);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_4);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_importModulesAux(x_51, x_53, x_10);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_59 = x_55;
} else {
 lean_dec_ref(x_55);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_56, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_62 = x_56;
} else {
 lean_dec_ref(x_56);
 x_62 = lean_box(0);
}
x_63 = lean_array_push(x_60, x_48);
x_64 = lean_array_push(x_61, x_49);
if (lean_is_scalar(x_62)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_62;
}
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
if (lean_is_scalar(x_59)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_59;
}
lean_ctor_set(x_66, 0, x_58);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_importModulesAux(x_5, x_66, x_57);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_5);
x_68 = lean_ctor_get(x_54, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_54, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_70 = x_54;
} else {
 lean_dec_ref(x_54);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_8);
if (x_72 == 0)
{
return x_8;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_8, 0);
x_74 = lean_ctor_get(x_8, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_8);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
static lean_object* _init_l_Lean_importModulesAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("object file '");
return x_1;
}
}
static lean_object* _init_l_Lean_importModulesAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' of module ");
return x_1;
}
}
static lean_object* _init_l_Lean_importModulesAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" does not exist");
return x_1;
}
}
lean_object* l_Lean_importModulesAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
x_16 = l_Lean_NameSet_contains(x_10, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_free_object(x_5);
lean_free_object(x_2);
x_17 = lean_box(0);
lean_inc(x_15);
x_18 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_10, x_15, x_17);
x_19 = l_Lean_findOLean(x_15, x_3);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_io_file_exists(x_20, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
x_27 = l_Lean_importModulesAux___closed__1;
x_28 = lean_string_append(x_27, x_20);
lean_dec(x_20);
x_29 = l_Lean_importModulesAux___closed__2;
x_30 = lean_string_append(x_28, x_29);
x_31 = l_System_FilePath_dirName___closed__1;
x_32 = l_Lean_Name_toStringWithSep(x_31, x_15);
x_33 = lean_string_append(x_30, x_32);
lean_dec(x_32);
x_34 = l_Lean_importModulesAux___closed__3;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_36);
return x_22;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_dec(x_22);
x_38 = l_Lean_importModulesAux___closed__1;
x_39 = lean_string_append(x_38, x_20);
lean_dec(x_20);
x_40 = l_Lean_importModulesAux___closed__2;
x_41 = lean_string_append(x_39, x_40);
x_42 = l_System_FilePath_dirName___closed__1;
x_43 = l_Lean_Name_toStringWithSep(x_42, x_15);
x_44 = lean_string_append(x_41, x_43);
lean_dec(x_43);
x_45 = l_Lean_importModulesAux___closed__3;
x_46 = lean_string_append(x_44, x_45);
x_47 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_37);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_15);
x_49 = lean_ctor_get(x_22, 1);
lean_inc(x_49);
lean_dec(x_22);
x_50 = l_Lean_importModulesAux___lambda__1(x_20, x_13, x_14, x_18, x_8, x_17, x_49);
lean_dec(x_20);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
x_51 = !lean_is_exclusive(x_22);
if (x_51 == 0)
{
return x_22;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_22, 0);
x_53 = lean_ctor_get(x_22, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_22);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
x_55 = !lean_is_exclusive(x_19);
if (x_55 == 0)
{
return x_19;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_19, 0);
x_57 = lean_ctor_get(x_19, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_19);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_dec(x_15);
x_1 = x_8;
goto _start;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_5, 0);
x_61 = lean_ctor_get(x_5, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_5);
x_62 = lean_ctor_get(x_6, 0);
lean_inc(x_62);
lean_dec(x_6);
x_63 = l_Lean_NameSet_contains(x_10, x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_free_object(x_2);
x_64 = lean_box(0);
lean_inc(x_62);
x_65 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_10, x_62, x_64);
x_66 = l_Lean_findOLean(x_62, x_3);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_io_file_exists(x_67, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_unbox(x_70);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_65);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_8);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_73 = x_69;
} else {
 lean_dec_ref(x_69);
 x_73 = lean_box(0);
}
x_74 = l_Lean_importModulesAux___closed__1;
x_75 = lean_string_append(x_74, x_67);
lean_dec(x_67);
x_76 = l_Lean_importModulesAux___closed__2;
x_77 = lean_string_append(x_75, x_76);
x_78 = l_System_FilePath_dirName___closed__1;
x_79 = l_Lean_Name_toStringWithSep(x_78, x_62);
x_80 = lean_string_append(x_77, x_79);
lean_dec(x_79);
x_81 = l_Lean_importModulesAux___closed__3;
x_82 = lean_string_append(x_80, x_81);
x_83 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_83, 0, x_82);
if (lean_is_scalar(x_73)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_73;
 lean_ctor_set_tag(x_84, 1);
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_72);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_62);
x_85 = lean_ctor_get(x_69, 1);
lean_inc(x_85);
lean_dec(x_69);
x_86 = l_Lean_importModulesAux___lambda__1(x_67, x_60, x_61, x_65, x_8, x_64, x_85);
lean_dec(x_67);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_8);
x_87 = lean_ctor_get(x_69, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_69, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_89 = x_69;
} else {
 lean_dec_ref(x_69);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_65);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_8);
x_91 = lean_ctor_get(x_66, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_66, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_93 = x_66;
} else {
 lean_dec_ref(x_66);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
lean_object* x_95; 
lean_dec(x_62);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_60);
lean_ctor_set(x_95, 1, x_61);
lean_ctor_set(x_2, 1, x_95);
x_1 = x_8;
goto _start;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_97 = lean_ctor_get(x_2, 0);
lean_inc(x_97);
lean_dec(x_2);
x_98 = lean_ctor_get(x_5, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_5, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_100 = x_5;
} else {
 lean_dec_ref(x_5);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_6, 0);
lean_inc(x_101);
lean_dec(x_6);
x_102 = l_Lean_NameSet_contains(x_97, x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_100);
x_103 = lean_box(0);
lean_inc(x_101);
x_104 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_97, x_101, x_103);
x_105 = l_Lean_findOLean(x_101, x_3);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_io_file_exists(x_106, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_unbox(x_109);
lean_dec(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_104);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_8);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_112 = x_108;
} else {
 lean_dec_ref(x_108);
 x_112 = lean_box(0);
}
x_113 = l_Lean_importModulesAux___closed__1;
x_114 = lean_string_append(x_113, x_106);
lean_dec(x_106);
x_115 = l_Lean_importModulesAux___closed__2;
x_116 = lean_string_append(x_114, x_115);
x_117 = l_System_FilePath_dirName___closed__1;
x_118 = l_Lean_Name_toStringWithSep(x_117, x_101);
x_119 = lean_string_append(x_116, x_118);
lean_dec(x_118);
x_120 = l_Lean_importModulesAux___closed__3;
x_121 = lean_string_append(x_119, x_120);
x_122 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_122, 0, x_121);
if (lean_is_scalar(x_112)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_112;
 lean_ctor_set_tag(x_123, 1);
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_111);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_101);
x_124 = lean_ctor_get(x_108, 1);
lean_inc(x_124);
lean_dec(x_108);
x_125 = l_Lean_importModulesAux___lambda__1(x_106, x_98, x_99, x_104, x_8, x_103, x_124);
lean_dec(x_106);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_106);
lean_dec(x_104);
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_8);
x_126 = lean_ctor_get(x_108, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_108, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_128 = x_108;
} else {
 lean_dec_ref(x_108);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_104);
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_8);
x_130 = lean_ctor_get(x_105, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_105, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_132 = x_105;
} else {
 lean_dec_ref(x_105);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_101);
if (lean_is_scalar(x_100)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_100;
}
lean_ctor_set(x_134, 0, x_98);
lean_ctor_set(x_134, 1, x_99);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_97);
lean_ctor_set(x_135, 1, x_134);
x_1 = x_8;
x_2 = x_135;
goto _start;
}
}
}
else
{
lean_object* x_137; uint8_t x_138; 
lean_dec(x_6);
x_137 = lean_ctor_get(x_1, 1);
lean_inc(x_137);
lean_dec(x_1);
x_138 = !lean_is_exclusive(x_2);
if (x_138 == 0)
{
lean_object* x_139; uint8_t x_140; 
x_139 = lean_ctor_get(x_2, 1);
lean_dec(x_139);
x_140 = !lean_is_exclusive(x_5);
if (x_140 == 0)
{
x_1 = x_137;
goto _start;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_5, 0);
x_143 = lean_ctor_get(x_5, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_5);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set(x_2, 1, x_144);
x_1 = x_137;
goto _start;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_146 = lean_ctor_get(x_2, 0);
lean_inc(x_146);
lean_dec(x_2);
x_147 = lean_ctor_get(x_5, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_5, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_149 = x_5;
} else {
 lean_dec_ref(x_5);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_148);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_146);
lean_ctor_set(x_151, 1, x_150);
x_1 = x_137;
x_2 = x_151;
goto _start;
}
}
}
}
}
lean_object* l_IO_fileExists___at_Lean_importModulesAux___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_fileExists___at_Lean_importModulesAux___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_importModulesAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_importModulesAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Environment_0__Lean_getEntriesFor___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Init_LeanInit___instance__1;
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
x_15 = l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg(x_13, x_5, x_14);
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
lean_object* l_Lean_importModules_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_importModules_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_importModules_match__4___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_importModules_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_importModules_match__4___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_importModules_match__5___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_importModules_match__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_importModules_match__5___rarg), 2, 0);
return x_2;
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
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l_Lean_Name_hash(x_12);
x_17 = lean_usize_modn(x_16, x_15);
lean_dec(x_15);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
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
x_23 = l_System_FilePath_dirName___closed__1;
x_24 = l_Lean_Name_toStringWithSep(x_23, x_12);
x_25 = l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8___closed__1;
x_26 = lean_string_append(x_25, x_24);
lean_dec(x_24);
x_27 = l_Init_Data_Repr___instance__15___closed__1;
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
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_uget(x_1, x_3);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_4, 1);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
lean_ctor_set(x_10, 0, x_12);
x_15 = lean_array_get_size(x_14);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
lean_inc(x_13);
x_18 = l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8(x_13, x_14, x_16, x_17, x_10, x_5);
lean_dec(x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_13, x_23);
lean_dec(x_13);
lean_ctor_set(x_19, 0, x_24);
lean_ctor_set(x_4, 1, x_19);
lean_ctor_set(x_4, 0, x_22);
x_25 = 1;
x_26 = x_3 + x_25;
x_3 = x_26;
x_5 = x_20;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_13, x_30);
lean_dec(x_13);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_4, 1, x_32);
lean_ctor_set(x_4, 0, x_28);
x_33 = 1;
x_34 = x_3 + x_33;
x_3 = x_34;
x_5 = x_20;
goto _start;
}
}
else
{
uint8_t x_36; 
lean_dec(x_13);
lean_free_object(x_4);
x_36 = !lean_is_exclusive(x_18);
if (x_36 == 0)
{
return x_18;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_18, 0);
x_38 = lean_ctor_get(x_18, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_18);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_4, 0);
x_41 = lean_ctor_get(x_10, 0);
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_10);
x_43 = lean_ctor_get(x_8, 1);
lean_inc(x_43);
lean_dec(x_8);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_array_get_size(x_43);
x_46 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_47 = 0;
lean_inc(x_41);
x_48 = l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8(x_41, x_43, x_46, x_47, x_44, x_5);
lean_dec(x_43);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_53 = x_49;
} else {
 lean_dec_ref(x_49);
 x_53 = lean_box(0);
}
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_41, x_54);
lean_dec(x_41);
if (lean_is_scalar(x_53)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_53;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_52);
lean_ctor_set(x_4, 1, x_56);
lean_ctor_set(x_4, 0, x_51);
x_57 = 1;
x_58 = x_3 + x_57;
x_3 = x_58;
x_5 = x_50;
goto _start;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_41);
lean_free_object(x_4);
x_60 = lean_ctor_get(x_48, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_48, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_62 = x_48;
} else {
 lean_dec_ref(x_48);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; size_t x_72; size_t x_73; lean_object* x_74; 
x_64 = lean_ctor_get(x_4, 1);
x_65 = lean_ctor_get(x_4, 0);
lean_inc(x_64);
lean_inc(x_65);
lean_dec(x_4);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_68 = x_64;
} else {
 lean_dec_ref(x_64);
 x_68 = lean_box(0);
}
x_69 = lean_ctor_get(x_8, 1);
lean_inc(x_69);
lean_dec(x_8);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_65);
lean_ctor_set(x_70, 1, x_67);
x_71 = lean_array_get_size(x_69);
x_72 = lean_usize_of_nat(x_71);
lean_dec(x_71);
x_73 = 0;
lean_inc(x_66);
x_74 = l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8(x_66, x_69, x_72, x_73, x_70, x_5);
lean_dec(x_69);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; size_t x_84; size_t x_85; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_79 = x_75;
} else {
 lean_dec_ref(x_75);
 x_79 = lean_box(0);
}
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_add(x_66, x_80);
lean_dec(x_66);
if (lean_is_scalar(x_79)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_79;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_78);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_77);
lean_ctor_set(x_83, 1, x_82);
x_84 = 1;
x_85 = x_3 + x_84;
x_3 = x_85;
x_4 = x_83;
x_5 = x_76;
goto _start;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_66);
x_87 = lean_ctor_get(x_74, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_74, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_89 = x_74;
} else {
 lean_dec_ref(x_74);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
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
lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__11(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_array_uget(x_1, x_3);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_perform_serialized_modifications(x_4, x_9, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
x_14 = x_3 + x_13;
x_3 = x_14;
x_4 = x_11;
x_5 = x_12;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
static lean_object* _init_l_Lean_importModules___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_empty___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_importModules___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_NameSet_empty;
x_2 = l_Lean_importModules___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_importModules___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_HashMap_inhabited___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_importModules___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SMap_empty___at_Lean_importModules___spec__1;
x_2 = l_Lean_importModules___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* lean_import_modules(lean_object* x_1, lean_object* x_2, uint32_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_importModules___closed__2;
lean_inc(x_1);
x_6 = l_Lean_importModulesAux(x_1, x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_array_get_size(x_11);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = 0;
x_16 = l_Lean_importModules___closed__4;
x_17 = l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9(x_11, x_14, x_15, x_16, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l_Lean_SMap_switch___at_Lean_importModules___spec__10(x_21);
x_24 = l_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates(x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_List_isEmpty___rarg(x_1);
x_28 = l_List_redLength___rarg(x_1);
x_29 = lean_mk_empty_array_with_capacity(x_28);
lean_dec(x_28);
x_30 = l_List_toArrayAux___rarg(x_1, x_29);
if (x_27 == 0)
{
uint8_t x_55; 
x_55 = 1;
x_31 = x_55;
goto block_54;
}
else
{
uint8_t x_56; 
x_56 = 0;
x_31 = x_56;
goto block_54;
}
block_54:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 4, 5);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set(x_33, 2, x_12);
lean_ctor_set(x_33, 3, x_10);
lean_ctor_set_uint32(x_33, sizeof(void*)*4, x_3);
lean_ctor_set_uint8(x_33, sizeof(void*)*4 + 4, x_31);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_22);
lean_ctor_set(x_34, 1, x_23);
lean_ctor_set(x_34, 2, x_25);
lean_ctor_set(x_34, 3, x_33);
x_35 = l___private_Lean_Environment_0__Lean_setImportedEntries(x_34, x_11, x_26);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l___private_Lean_Environment_0__Lean_finalizePersistentExtensions(x_36, x_2, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Array_forInUnsafe_loop___at_Lean_importModules___spec__11(x_11, x_14, x_15, x_39, x_40);
lean_dec(x_11);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_41);
if (x_46 == 0)
{
return x_41;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_41, 0);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_41);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_11);
x_50 = !lean_is_exclusive(x_38);
if (x_50 == 0)
{
return x_38;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_38, 0);
x_52 = lean_ctor_get(x_38, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_38);
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
uint8_t x_57; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_24);
if (x_57 == 0)
{
return x_24;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_24, 0);
x_59 = lean_ctor_get(x_24, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_24);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_17);
if (x_61 == 0)
{
return x_17;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_17, 0);
x_63 = lean_ctor_get(x_17, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_17);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_6);
if (x_65 == 0)
{
return x_6;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_6, 0);
x_67 = lean_ctor_get(x_6, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_6);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
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
lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forInUnsafe_loop___at_Lean_importModules___spec__11(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
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
lean_object* l_Array_iterateMAux___at_Lean_initFn____x40_Lean_Environment___hyg_2730____spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_4, x_7, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
x_4 = x_9;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___at_Lean_initFn____x40_Lean_Environment___hyg_2730____spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = l_Array_iterateMAux___at_Lean_initFn____x40_Lean_Environment___hyg_2730____spec__2(x_7, x_7, x_8, x_4);
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
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_Environment___hyg_2730____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_iterateMAux___at_Lean_initFn____x40_Lean_Environment___hyg_2730____spec__3(x_2, x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_2730____lambda__1(lean_object* x_1) {
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
static lean_object* _init_l_Lean_initFn____x40_Lean_Environment___hyg_2730____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("namespaces");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Environment___hyg_2730____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_Environment___hyg_2730____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Environment___hyg_2730____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_NameSet_empty;
x_2 = lean_alloc_closure((void*)(l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_Environment___hyg_2730____spec__1___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Environment___hyg_2730____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_initFn____x40_Lean_Environment___hyg_2730____lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Environment___hyg_2730____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_Environment___hyg_2730____closed__2;
x_2 = l_Lean_mkTagDeclarationExtension___closed__1;
x_3 = l_Lean_initFn____x40_Lean_Environment___hyg_2730____closed__3;
x_4 = l_Lean_initFn____x40_Lean_Environment___hyg_2730____closed__4;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_2730_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_initFn____x40_Lean_Environment___hyg_2730____closed__5;
x_3 = l_Lean_registerSimplePersistentEnvExtension___at_Lean_mkTagDeclarationExtension___spec__3(x_2, x_1);
return x_3;
}
}
lean_object* l_Array_iterateMAux___at_Lean_initFn____x40_Lean_Environment___hyg_2730____spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___at_Lean_initFn____x40_Lean_Environment___hyg_2730____spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___at_Lean_initFn____x40_Lean_Environment___hyg_2730____spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___at_Lean_initFn____x40_Lean_Environment___hyg_2730____spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_Environment___hyg_2730____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_Environment___hyg_2730____spec__1(x_1, x_2);
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
x_2 = l_IO_Error_Init_System_IOError___instance__2___closed__1;
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
x_1 = l_Lean_EnvExtensionInterfaceUnsafe_Lean_Environment___instance__6___closed__2;
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
x_3 = l_String_splitAux___closed__1;
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
x_7 = l_System_FilePath_dirName___closed__1;
x_8 = l_Lean_Name_toStringWithSep(x_7, x_6);
x_9 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_dec(x_4);
x_10 = 0;
x_11 = l_List_toStringAux___at_Lean_Environment_displayStats___spec__2(x_10, x_5);
if (x_9 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_String_splitAux___closed__1;
x_13 = lean_string_append(x_8, x_12);
x_14 = l_List_reprAux___rarg___closed__1;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = lean_string_append(x_15, x_11);
lean_dec(x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = l_Lean_Lean_Environment___instance__3___closed__1;
x_18 = lean_string_append(x_8, x_17);
x_19 = l_List_reprAux___rarg___closed__1;
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
x_22 = l_String_splitAux___closed__1;
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
x_26 = l_System_FilePath_dirName___closed__1;
x_27 = l_Lean_Name_toStringWithSep(x_26, x_25);
x_28 = lean_ctor_get_uint8(x_23, sizeof(void*)*1);
lean_dec(x_23);
x_29 = 0;
x_30 = l_List_toStringAux___at_Lean_Environment_displayStats___spec__2(x_29, x_24);
if (x_28 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_String_splitAux___closed__1;
x_32 = lean_string_append(x_27, x_31);
x_33 = lean_string_append(x_32, x_30);
lean_dec(x_30);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = l_Lean_Lean_Environment___instance__3___closed__1;
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
x_2 = l_List_repr___rarg___closed__1;
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
x_6 = l_List_repr___rarg___closed__2;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_List_repr___rarg___closed__3;
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
x_15 = l_List_repr___rarg___closed__2;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_List_repr___rarg___closed__3;
x_18 = lean_string_append(x_16, x_17);
return x_18;
}
}
}
}
lean_object* l_IO_getStdout___at_Lean_Environment_displayStats___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_stdout(x_1);
return x_2;
}
}
lean_object* l_IO_print___at_Lean_Environment_displayStats___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_get_stdout(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 5);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_2(x_6, x_1, x_5);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
lean_object* l_IO_println___at_Lean_Environment_displayStats___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_print___at_Lean_Environment_displayStats___spec__4(x_4, x_2);
return x_5;
}
}
lean_object* l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__6(lean_object* x_1) {
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
lean_object* l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__7(lean_object* x_1) {
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
lean_object* l_Std_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_array_get_size(x_2);
return x_3;
}
}
lean_object* l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Std_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__9(x_2);
return x_3;
}
}
lean_object* l_Array_iterateMAux___at_Lean_Environment_displayStats___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
static lean_object* _init_l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  number of imported entries: ");
return x_1;
}
}
lean_object* l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_iterateMAux___at_Lean_Environment_displayStats___spec__10(x_2, x_3, x_6, x_7, x_7);
x_9 = l_Nat_repr(x_8);
x_10 = l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___lambda__1___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_11, x_5);
return x_12;
}
}
static lean_object* _init_l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("extension '");
return x_1;
}
}
static lean_object* _init_l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  ");
return x_1;
}
}
lean_object* l_Array_forMAux___at_Lean_Environment_displayStats___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_array_fget(x_2, x_3);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = l_System_FilePath_dirName___closed__1;
x_12 = l_Lean_Name_toStringWithSep(x_11, x_10);
x_13 = l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___closed__1;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_Init_Data_Repr___instance__15___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_16, x_4);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
x_20 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_19, x_1);
lean_dec(x_19);
x_21 = lean_ctor_get(x_9, 5);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
x_23 = lean_apply_1(x_21, x_22);
x_24 = l_Lean_Format_isNil(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___closed__2;
x_26 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
x_27 = lean_box(0);
x_28 = l_Lean_Format_pretty(x_26, x_27);
x_29 = l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___closed__3;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_30, x_18);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___lambda__1(x_20, x_1, x_9, x_32, x_33);
lean_dec(x_32);
lean_dec(x_9);
lean_dec(x_20);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_3, x_36);
lean_dec(x_3);
x_3 = x_37;
x_4 = x_35;
goto _start;
}
else
{
uint8_t x_39; 
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_34);
if (x_39 == 0)
{
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_34, 0);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_34);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_31);
if (x_43 == 0)
{
return x_31;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_31, 0);
x_45 = lean_ctor_get(x_31, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_31);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_23);
x_47 = lean_box(0);
x_48 = l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___lambda__1(x_20, x_1, x_9, x_47, x_18);
lean_dec(x_9);
lean_dec(x_20);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_3, x_50);
lean_dec(x_3);
x_3 = x_51;
x_4 = x_49;
goto _start;
}
else
{
uint8_t x_53; 
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_48);
if (x_53 == 0)
{
return x_48;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_48, 0);
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_48);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_9);
lean_dec(x_3);
x_57 = !lean_is_exclusive(x_17);
if (x_57 == 0)
{
return x_17;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_17, 0);
x_59 = lean_ctor_get(x_17, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_17);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
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
x_16 = l_Array_toList___rarg(x_15);
lean_dec(x_15);
x_17 = l_List_toString___at_Lean_Environment_displayStats___spec__1(x_16);
x_18 = l_Array_Init_Data_Array_Basic___instance__3___rarg___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = l_Lean_Environment_displayStats___closed__1;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_21, x_6);
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
x_27 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_26, x_23);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
x_30 = l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__6(x_29);
x_31 = l_Nat_repr(x_30);
x_32 = l_Lean_Environment_displayStats___closed__3;
x_33 = lean_string_append(x_32, x_31);
lean_dec(x_31);
x_34 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_33, x_28);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__7(x_29);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = l_Nat_repr(x_37);
x_39 = l_Lean_Environment_displayStats___closed__4;
x_40 = lean_string_append(x_39, x_38);
lean_dec(x_38);
x_41 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_40, x_35);
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
x_47 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_46, x_42);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__8(x_29);
lean_dec(x_29);
x_50 = l_Nat_repr(x_49);
x_51 = l_Lean_Environment_displayStats___closed__6;
x_52 = lean_string_append(x_51, x_50);
lean_dec(x_50);
x_53 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_52, x_48);
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
x_60 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_59, x_54);
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
x_67 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_66, x_61);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = l_Array_forMAux___at_Lean_Environment_displayStats___spec__11(x_1, x_5, x_8, x_68);
lean_dec(x_5);
lean_dec(x_1);
return x_69;
}
else
{
uint8_t x_70; 
lean_dec(x_5);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_67);
if (x_70 == 0)
{
return x_67;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_67, 0);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_67);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_5);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_60);
if (x_74 == 0)
{
return x_60;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_60, 0);
x_76 = lean_ctor_get(x_60, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_60);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_53);
if (x_78 == 0)
{
return x_53;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_53, 0);
x_80 = lean_ctor_get(x_53, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_29);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_47);
if (x_82 == 0)
{
return x_47;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_47, 0);
x_84 = lean_ctor_get(x_47, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_47);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_36);
lean_dec(x_29);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_41);
if (x_86 == 0)
{
return x_41;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_41, 0);
x_88 = lean_ctor_get(x_41, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_41);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_29);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_34);
if (x_90 == 0)
{
return x_34;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_34, 0);
x_92 = lean_ctor_get(x_34, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_34);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_27);
if (x_94 == 0)
{
return x_27;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_27, 0);
x_96 = lean_ctor_get(x_27, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_27);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_22);
if (x_98 == 0)
{
return x_22;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_22, 0);
x_100 = lean_ctor_get(x_22, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_22);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
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
lean_object* l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__6___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__6(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__7___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__7(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Std_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__9___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__9(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__8___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__8(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_iterateMAux___at_Lean_Environment_displayStats___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___at_Lean_Environment_displayStats___spec__10(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___at_Lean_Environment_displayStats___spec__11(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
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
x_3 = l_System_FilePath_dirName___closed__1;
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
x_6 = l_System_FilePath_dirName___closed__1;
x_7 = l_Lean_Name_toStringWithSep(x_6, x_4);
x_8 = l_Lean_Environment_evalConstCheck___rarg___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Init_Data_Repr___instance__15___closed__1;
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
lean_object* l_Lean_Lean_Environment___instance__15___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Lean_Environment___instance__15___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_apply_2(x_2, lean_box(0), x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Lean_Environment___instance__15___rarg___lambda__1), 3, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
lean_object* l_Lean_Lean_Environment___instance__15(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Lean_Environment___instance__15___rarg), 2, 0);
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
l_Lean_EnvExtensionStateSpec = _init_l_Lean_EnvExtensionStateSpec();
lean_mark_persistent(l_Lean_EnvExtensionStateSpec);
l_Lean_Lean_Environment___instance__1 = _init_l_Lean_Lean_Environment___instance__1();
lean_mark_persistent(l_Lean_Lean_Environment___instance__1);
l_Lean_Lean_Environment___instance__2 = _init_l_Lean_Lean_Environment___instance__2();
lean_mark_persistent(l_Lean_Lean_Environment___instance__2);
l_Lean_Import_runtimeOnly___default = _init_l_Lean_Import_runtimeOnly___default();
l_Lean_Lean_Environment___instance__3___closed__1 = _init_l_Lean_Lean_Environment___instance__3___closed__1();
lean_mark_persistent(l_Lean_Lean_Environment___instance__3___closed__1);
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
l_Lean_Environment_header___default___closed__1 = _init_l_Lean_Environment_header___default___closed__1();
lean_mark_persistent(l_Lean_Environment_header___default___closed__1);
l_Lean_Environment_header___default = _init_l_Lean_Environment_header___default();
lean_mark_persistent(l_Lean_Environment_header___default);
l_Lean_Environment_Lean_Environment___instance__4___closed__1 = _init_l_Lean_Environment_Lean_Environment___instance__4___closed__1();
lean_mark_persistent(l_Lean_Environment_Lean_Environment___instance__4___closed__1);
l_Lean_Environment_Lean_Environment___instance__4___closed__2 = _init_l_Lean_Environment_Lean_Environment___instance__4___closed__2();
lean_mark_persistent(l_Lean_Environment_Lean_Environment___instance__4___closed__2);
l_Lean_Environment_Lean_Environment___instance__4___closed__3 = _init_l_Lean_Environment_Lean_Environment___instance__4___closed__3();
lean_mark_persistent(l_Lean_Environment_Lean_Environment___instance__4___closed__3);
l_Lean_Environment_Lean_Environment___instance__4___closed__4 = _init_l_Lean_Environment_Lean_Environment___instance__4___closed__4();
lean_mark_persistent(l_Lean_Environment_Lean_Environment___instance__4___closed__4);
l_Lean_Environment_Lean_Environment___instance__4___closed__5 = _init_l_Lean_Environment_Lean_Environment___instance__4___closed__5();
lean_mark_persistent(l_Lean_Environment_Lean_Environment___instance__4___closed__5);
l_Lean_Environment_Lean_Environment___instance__4 = _init_l_Lean_Environment_Lean_Environment___instance__4();
lean_mark_persistent(l_Lean_Environment_Lean_Environment___instance__4);
l_Lean_Lean_Environment___instance__5___closed__1 = _init_l_Lean_Lean_Environment___instance__5___closed__1();
lean_mark_persistent(l_Lean_Lean_Environment___instance__5___closed__1);
l_Lean_Lean_Environment___instance__5___closed__2 = _init_l_Lean_Lean_Environment___instance__5___closed__2();
lean_mark_persistent(l_Lean_Lean_Environment___instance__5___closed__2);
l_Lean_Lean_Environment___instance__5___closed__3 = _init_l_Lean_Lean_Environment___instance__5___closed__3();
lean_mark_persistent(l_Lean_Lean_Environment___instance__5___closed__3);
l_Lean_Lean_Environment___instance__5___closed__4 = _init_l_Lean_Lean_Environment___instance__5___closed__4();
lean_mark_persistent(l_Lean_Lean_Environment___instance__5___closed__4);
l_Lean_Lean_Environment___instance__5 = _init_l_Lean_Lean_Environment___instance__5();
lean_mark_persistent(l_Lean_Lean_Environment___instance__5);
l_Lean_EnvExtensionInterfaceUnsafe_Lean_Environment___instance__6___closed__1 = _init_l_Lean_EnvExtensionInterfaceUnsafe_Lean_Environment___instance__6___closed__1();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_Lean_Environment___instance__6___closed__1);
l_Lean_EnvExtensionInterfaceUnsafe_Lean_Environment___instance__6___closed__2 = _init_l_Lean_EnvExtensionInterfaceUnsafe_Lean_Environment___instance__6___closed__2();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_Lean_Environment___instance__6___closed__2);
res = l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_mkEnvExtensionsRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_envExtensionsRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_envExtensionsRef);
lean_dec_ref(res);
l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___closed__1 = _init_l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___closed__1();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___closed__1);
l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___closed__2 = _init_l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___closed__2();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___closed__2);
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
l_Lean_Lean_Environment___instance__8 = _init_l_Lean_Lean_Environment___instance__8();
lean_mark_persistent(l_Lean_Lean_Environment___instance__8);
l_Lean_Lean_Environment___instance__10___closed__1 = _init_l_Lean_Lean_Environment___instance__10___closed__1();
lean_mark_persistent(l_Lean_Lean_Environment___instance__10___closed__1);
l_Lean_Lean_Environment___instance__10___closed__2 = _init_l_Lean_Lean_Environment___instance__10___closed__2();
lean_mark_persistent(l_Lean_Lean_Environment___instance__10___closed__2);
l_Lean_Lean_Environment___instance__10___closed__3 = _init_l_Lean_Lean_Environment___instance__10___closed__3();
lean_mark_persistent(l_Lean_Lean_Environment___instance__10___closed__3);
l_Lean_Lean_Environment___instance__10___closed__4 = _init_l_Lean_Lean_Environment___instance__10___closed__4();
lean_mark_persistent(l_Lean_Lean_Environment___instance__10___closed__4);
l_Lean_Lean_Environment___instance__10___closed__5 = _init_l_Lean_Lean_Environment___instance__10___closed__5();
lean_mark_persistent(l_Lean_Lean_Environment___instance__10___closed__5);
res = l_Lean_initFn____x40_Lean_Environment___hyg_1102_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_persistentEnvExtensionsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_persistentEnvExtensionsRef);
lean_dec_ref(res);
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
l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1___closed__1 = _init_l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1___closed__1();
lean_mark_persistent(l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1___closed__1);
l_Lean_mkTagDeclarationExtension___closed__1 = _init_l_Lean_mkTagDeclarationExtension___closed__1();
lean_mark_persistent(l_Lean_mkTagDeclarationExtension___closed__1);
l_Lean_mkTagDeclarationExtension___closed__2 = _init_l_Lean_mkTagDeclarationExtension___closed__2();
lean_mark_persistent(l_Lean_mkTagDeclarationExtension___closed__2);
l_Lean_mkTagDeclarationExtension___closed__3 = _init_l_Lean_mkTagDeclarationExtension___closed__3();
lean_mark_persistent(l_Lean_mkTagDeclarationExtension___closed__3);
l_Lean_TagDeclarationExtension_Lean_Environment___instance__12___closed__1 = _init_l_Lean_TagDeclarationExtension_Lean_Environment___instance__12___closed__1();
lean_mark_persistent(l_Lean_TagDeclarationExtension_Lean_Environment___instance__12___closed__1);
l_Lean_TagDeclarationExtension_Lean_Environment___instance__12 = _init_l_Lean_TagDeclarationExtension_Lean_Environment___instance__12();
lean_mark_persistent(l_Lean_TagDeclarationExtension_Lean_Environment___instance__12);
l_Lean_Lean_Environment___instance__13 = _init_l_Lean_Lean_Environment___instance__13();
lean_mark_persistent(l_Lean_Lean_Environment___instance__13);
l_Lean_initFn____x40_Lean_Environment___hyg_1674____closed__1 = _init_l_Lean_initFn____x40_Lean_Environment___hyg_1674____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Environment___hyg_1674____closed__1);
res = l_Lean_initFn____x40_Lean_Environment___hyg_1674_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_modListExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_modListExtension);
lean_dec_ref(res);
l_Lean_Lean_Environment___instance__14___closed__1 = _init_l_Lean_Lean_Environment___instance__14___closed__1();
lean_mark_persistent(l_Lean_Lean_Environment___instance__14___closed__1);
l_Lean_Lean_Environment___instance__14 = _init_l_Lean_Lean_Environment___instance__14();
lean_mark_persistent(l_Lean_Lean_Environment___instance__14);
l_Nat_foldAux___at_Lean_mkModuleData___spec__1___closed__1 = _init_l_Nat_foldAux___at_Lean_mkModuleData___spec__1___closed__1();
lean_mark_persistent(l_Nat_foldAux___at_Lean_mkModuleData___spec__1___closed__1);
l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___closed__1 = _init_l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___closed__1();
lean_mark_persistent(l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___closed__1);
l_Lean_importModulesAux___closed__1 = _init_l_Lean_importModulesAux___closed__1();
lean_mark_persistent(l_Lean_importModulesAux___closed__1);
l_Lean_importModulesAux___closed__2 = _init_l_Lean_importModulesAux___closed__2();
lean_mark_persistent(l_Lean_importModulesAux___closed__2);
l_Lean_importModulesAux___closed__3 = _init_l_Lean_importModulesAux___closed__3();
lean_mark_persistent(l_Lean_importModulesAux___closed__3);
l___private_Lean_Environment_0__Lean_getEntriesFor___closed__1 = _init_l___private_Lean_Environment_0__Lean_getEntriesFor___closed__1();
lean_mark_persistent(l___private_Lean_Environment_0__Lean_getEntriesFor___closed__1);
l_Lean_SMap_empty___at_Lean_importModules___spec__1 = _init_l_Lean_SMap_empty___at_Lean_importModules___spec__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_importModules___spec__1);
l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_importModules___spec__8___closed__1);
l_Lean_importModules___closed__1 = _init_l_Lean_importModules___closed__1();
lean_mark_persistent(l_Lean_importModules___closed__1);
l_Lean_importModules___closed__2 = _init_l_Lean_importModules___closed__2();
lean_mark_persistent(l_Lean_importModules___closed__2);
l_Lean_importModules___closed__3 = _init_l_Lean_importModules___closed__3();
lean_mark_persistent(l_Lean_importModules___closed__3);
l_Lean_importModules___closed__4 = _init_l_Lean_importModules___closed__4();
lean_mark_persistent(l_Lean_importModules___closed__4);
l_Lean_initFn____x40_Lean_Environment___hyg_2730____closed__1 = _init_l_Lean_initFn____x40_Lean_Environment___hyg_2730____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Environment___hyg_2730____closed__1);
l_Lean_initFn____x40_Lean_Environment___hyg_2730____closed__2 = _init_l_Lean_initFn____x40_Lean_Environment___hyg_2730____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Environment___hyg_2730____closed__2);
l_Lean_initFn____x40_Lean_Environment___hyg_2730____closed__3 = _init_l_Lean_initFn____x40_Lean_Environment___hyg_2730____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Environment___hyg_2730____closed__3);
l_Lean_initFn____x40_Lean_Environment___hyg_2730____closed__4 = _init_l_Lean_initFn____x40_Lean_Environment___hyg_2730____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Environment___hyg_2730____closed__4);
l_Lean_initFn____x40_Lean_Environment___hyg_2730____closed__5 = _init_l_Lean_initFn____x40_Lean_Environment___hyg_2730____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Environment___hyg_2730____closed__5);
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
res = l_Lean_initFn____x40_Lean_Environment___hyg_2730_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_namespacesExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_namespacesExt);
lean_dec_ref(res);
l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___lambda__1___closed__1 = _init_l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___lambda__1___closed__1();
lean_mark_persistent(l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___lambda__1___closed__1);
l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___closed__1 = _init_l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___closed__1();
lean_mark_persistent(l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___closed__1);
l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___closed__2 = _init_l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___closed__2();
lean_mark_persistent(l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___closed__2);
l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___closed__3 = _init_l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___closed__3();
lean_mark_persistent(l_Array_forMAux___at_Lean_Environment_displayStats___spec__11___closed__3);
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

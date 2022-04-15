// Lean compiler output
// Module: Lean.Environment
// Imports: Init Std.Data.HashMap Lean.ImportingFlag Lean.Data.SMap Lean.Declaration Lean.LocalContext Lean.Util.Path Lean.Util.FindExpr Lean.Util.Profile
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
lean_object* l_Lean_initializing(lean_object*);
LEAN_EXPORT lean_object* l_List_toStringAux___at_Lean_Environment_displayStats___spec__2(uint8_t, lean_object*);
static lean_object* l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Environment_hasUnsafe___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__1;
static lean_object* l_Lean_mkMapDeclarationExtension___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_isNamespaceName___boxed(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_importModules___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_isNamespace___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Environment_displayStats___closed__2;
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnvExtensionInterface___lambda__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg___closed__1;
static lean_object* l_Lean_instInhabitedEnvironmentHeader___closed__2;
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_setState___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(lean_object*);
static lean_object* l_Lean_mkMapDeclarationExtension___rarg___closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__2;
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___rarg___lambda__2___boxed(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_instInhabitedEnvExtensionInterface___closed__2;
LEAN_EXPORT uint8_t l_Lean_EnvironmentHeader_quotInit___default;
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__5___boxed(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_Environment_displayStats___closed__6;
lean_object* l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Environment_find_x3f___spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__1___lambda__1(lean_object*, lean_object*);
lean_object* l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(lean_object*);
LEAN_EXPORT lean_object* lean_display_stats(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg(lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lean_mkEmptyEnvironment___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_withImportModules(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Environment_isNamespace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnvironmentHeader;
extern lean_object* l_Lean_NameSet_instInhabitedNameSet;
LEAN_EXPORT lean_object* lean_environment_free_regions(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_setState(lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_initFn____x40_Lean_Environment___hyg_1069_(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_setImportedEntries(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Environment_displayStats___closed__1;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___lambda__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_4639____lambda__1(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnvExtensionInterface___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Environment_displayStats___closed__4;
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_setState(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_setState(lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAtAux___at_Lean_Environment_contains___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_header___default;
LEAN_EXPORT lean_object* l_Lean_Environment_imports(lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt(lean_object*);
extern lean_object* l_Std_Format_defWidth;
static lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__6;
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__5(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Environment_displayStats___closed__8;
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAux___at_Lean_Environment_contains___spec__4(lean_object*, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__1___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabitedSimplePersistentEnvExtension(lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___lambda__1___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_mkTagDeclarationExtension___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_initFn____x40_Lean_Environment___hyg_4639____spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_MapDeclarationExtension_contains___spec__1(lean_object*);
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_initFn____x40_Lean_Environment___hyg_4639____spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_environment_set_main_module(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(lean_object*, lean_object*);
lean_object* lean_update_env_attributes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_isQuotInit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedModuleIdx;
static lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___closed__3;
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* lean_environment_find(lean_object*, lean_object*);
static lean_object* l_Lean_instInhabitedEnvironment___closed__4;
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg___closed__2;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_read_module_data(lean_object*, lean_object*);
lean_object* l_Lean_Name_quickLt___boxed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_finalizePersistentExtensions(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
static lean_object* l_Lean_mkTagDeclarationExtension___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_setState___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_allImportedModuleNames___boxed(lean_object*);
extern lean_object* l_instInhabitedNat;
LEAN_EXPORT lean_object* l_Lean_EnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_TagDeclarationExtension_isTagged___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_getEntriesFor(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_getState(lean_object*);
static lean_object* l_Lean_instInhabitedEnvExtensionInterface___closed__6;
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_Environment___hyg_4639____spec__1(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_invalidExtMsg___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__7(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_EnvExtensionInterfaceUnsafe_setState___spec__1(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9___closed__2;
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__4___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at_Lean_Environment_addAux___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnvExtensionInterface___lambda__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_TagDeclarationExtension_tag___closed__3;
static lean_object* l_Lean_instInhabitedEnvironment___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_freeRegions___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_evalConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_MapDeclarationExtension_find_x3f___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_num_attributes(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_setState___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_insert_x27___at_Lean_importModules___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qpartition_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___rarg___lambda__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState(lean_object*);
LEAN_EXPORT lean_object* l_Lean_importModules___lambda__3(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_readModuleData___boxed(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Environment_compileDecl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Environment_find_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg(lean_object*, lean_object*);
static lean_object* l_Nat_foldAux___at_Lean_mkModuleData___spec__1___closed__1;
static lean_object* l_Lean_TagDeclarationExtension_tag___closed__5;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_freeRegions___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadEnv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Environment_find_x3f___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_NameMap_contains___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_modifyState(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at_Lean_importModules___spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldAux___at_Lean_mkModuleData___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___lambda__1___closed__3;
lean_object* l_Lean_findOLean(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnvExtensionInterface___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_EnvExtensionStateSpec___closed__1;
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabitedTagDeclarationExtension;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at_Lean_MapDeclarationExtension_contains___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_contains___boxed(lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_invalidExtMsg;
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_setState(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAux___at_Lean_Environment_contains___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findUnsafe_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_MapDeclarationExtension_contains___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkEmptyEnvironment___lambda__1(uint32_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtensionDescr_toArrayFn___default___rarg(lean_object*);
static lean_object* l_Lean_instInhabitedEnvExtensionInterface___closed__1;
static lean_object* l_Lean_instInhabitedEnvironment___closed__3;
LEAN_EXPORT lean_object* l_Lean_EnvironmentHeader_moduleNames___default;
LEAN_EXPORT lean_object* l_Lean_ImportState_moduleNameSet___default;
LEAN_EXPORT uint8_t l_Lean_Environment_isConstructor(lean_object*, lean_object*);
static lean_object* l_Lean_Environment_displayStats___closed__7;
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Environment_displayStats___closed__5;
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at_Lean_initFn____x40_Lean_Environment___hyg_4639____spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MapDeclarationExtension_insert___rarg___closed__4;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Environment_find_x3f___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_write_module(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at_Lean_TagDeclarationExtension_isTagged___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_ensureExtensionsArraySize_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__9(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at_Lean_importModules___spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_hasUnsafe___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg___closed__3;
LEAN_EXPORT lean_object* l_Nat_foldAux___at_Lean_mkModuleData___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_instInhabitedEnvExtensionInterface___closed__4;
lean_object* l_EStateM_bind___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__3(lean_object*);
LEAN_EXPORT uint8_t lean_environment_quot_init(lean_object*);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___lambda__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributes___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSSet_instInhabitedNameSSet;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_4639____lambda__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_getEntriesFor___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop___closed__1;
static lean_object* l_Lean_mkEmptyEnvironment___closed__1;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___closed__1;
LEAN_EXPORT lean_object* l_Lean_EnvironmentHeader_mainModule___default;
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__3(lean_object*, lean_object*);
static lean_object* l_Lean_instInhabitedPersistentEnvExtension___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_mkInitialExtensionStates(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_Environment_addAux___spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_importModules_importMods___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_instInhabitedEnvironment___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_ensureExtensionsArraySize(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_ensureExtensionsArraySize(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_Environment_addAux___spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3___boxed(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
static lean_object* l_Lean_instInhabitedPersistentEnvExtension___closed__4;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_addEntry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toStringAux___at_Lean_Environment_displayStats___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_List_toStringAux___at_Lean_Environment_displayStats___spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_setImportedEntries___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Environment_0__Lean_Environment_isNamespaceName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___rarg___lambda__2(lean_object*);
static lean_object* l_Lean_instInhabitedPersistentEnvExtension___closed__1;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MapDeclarationExtension_insert___rarg___closed__1;
lean_object* l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_initFn____x40_Lean_Environment___hyg_4639____spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_evalConstCheck(lean_object*);
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_contains___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instInhabitedModuleData___closed__1;
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CompactedRegion_isMemoryMapped___boxed(lean_object*);
uint8_t lean_compacted_region_is_memory_mapped(size_t);
static lean_object* l_Lean_MapDeclarationExtension_insert___rarg___closed__2;
LEAN_EXPORT uint8_t l_Lean_SMap_contains___at_Lean_Environment_contains___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_modifyState(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__1(lean_object*);
static lean_object* l_Lean_Environment_displayStats___closed__3;
static lean_object* l_Lean_mkEmptyEnvironment___closed__2;
LEAN_EXPORT lean_object* l_Lean_importModules_importMods___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_importModules_importMods___closed__1;
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Environment_addAux___spec__10(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at_Lean_importModules___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lambda__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_getTrustLevel___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadEnv___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_instInhabitedEnvExtension(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static lean_object* l_Lean_importModules_importMods___closed__2;
lean_object* lean_array_to_list(lean_object*, lean_object*);
lean_object* lean_eval_const(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_contains___at_Lean_Environment_contains___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___lambda__3___boxed(lean_object*);
LEAN_EXPORT uint32_t lean_environment_trust_level(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__4;
static lean_object* l_Lean_Environment_evalConstCheck___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_persistentEnvExtensionsRef;
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportState_regions___default;
LEAN_EXPORT lean_object* lean_environment_add(lean_object*, lean_object*);
lean_object* lean_save_module_data(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withImportModules___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportState_moduleNames___default;
LEAN_EXPORT lean_object* l_Lean_EnvExtension_getState___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
static lean_object* l_Lean_Environment_displayStats___closed__10;
LEAN_EXPORT lean_object* l_Lean_saveModuleData___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkModuleData(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_instInhabitedMapDeclarationExtension(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__3___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkEmptyEnvironment___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2___closed__2;
static lean_object* l_Lean_mkEmptyEnvironment___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_modifyState(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_contains___at_Lean_Environment_contains___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtensionDescr_statsFn___default___boxed(lean_object*, lean_object*);
static uint32_t l_Lean_instInhabitedEnvironmentHeader___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getState___rarg___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_registerEnvExtension(lean_object*);
LEAN_EXPORT lean_object* l_Lean_importModules___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getState(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionEntrySpec;
static lean_object* l_Lean_importModules___closed__1;
LEAN_EXPORT lean_object* l_Lean_Environment_addDecl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_kernel_is_def_eq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CompactedRegion_free___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnvExtensionInterface;
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg___closed__1;
static lean_object* l_Lean_TagDeclarationExtension_instInhabitedTagDeclarationExtension___closed__1;
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__1(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_instInhabitedEnvironment___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedModuleData;
extern lean_object* l_Lean_NameSet_empty;
static lean_object* l_Lean_MapDeclarationExtension_insert___rarg___closed__3;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Environment_find_x3f___spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at_Lean_Environment_find_x3f___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_getModuleIdx_x3f___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__1;
static lean_object* l_Lean_MapDeclarationExtension_instInhabitedMapDeclarationExtension___closed__1;
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_importModules___spec__7(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__2;
LEAN_EXPORT lean_object* l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Environment_evalConstCheck___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvironmentHeader_regions___default;
static lean_object* l_List_toString___at_Lean_Environment_displayStats___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instInhabitedModuleData___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkEmptyEnvironment___boxed(lean_object*, lean_object*);
lean_object* lean_kernel_whnf(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_TagDeclarationExtension_tag___closed__4;
LEAN_EXPORT lean_object* l_Lean_Environment_evalConstCheck___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_MapDeclarationExtension_find_x3f___spec__1(lean_object*);
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___closed__2;
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at_Lean_Environment_addAux___spec__7(lean_object*, lean_object*);
static lean_object* l_Lean_instInhabitedEnvironment___closed__2;
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp;
uint8_t l_Lean_SMap_contains___at_Lean_NameSSet_contains___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Environment_addAux___spec__4(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_initFn____x40_Lean_Environment___hyg_4639____spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1(lean_object*);
static lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_mkModuleData___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_setState___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_getModuleIdx_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_modifyState___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_empty_environment(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Environment_addAux___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_import_modules(lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Environment_getModuleIdxFor_x3f___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnvironment;
static lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__8;
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___closed__1;
lean_object* l_List_redLength___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instToStringImport___closed__1;
LEAN_EXPORT lean_object* l_Std_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__6(lean_object*);
static lean_object* l_Lean_TagDeclarationExtension_tag___closed__2;
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__4;
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___lambda__3(lean_object*);
extern uint8_t l_instInhabitedBool;
LEAN_EXPORT lean_object* l_Lean_importModules_importMods(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_TagDeclarationExtension_tag___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_toString___at_Lean_Environment_displayStats___spec__1___closed__2;
LEAN_EXPORT lean_object* lean_environment_main_module(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtensionDescr_toArrayFn___default(lean_object*);
lean_object* lean_list_to_array(lean_object*, lean_object*);
static lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_MapDeclarationExtension_find_x3f___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__4(lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Id_instMonadId;
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt(lean_object*);
extern lean_object* l_Lean_SMap_empty___at_Lean_NameSSet_empty___spec__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f(lean_object*);
static lean_object* l_Lean_importModules_importMods___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getModuleEntries(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_MapDeclarationExtension_find_x3f___spec__1___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_modifyState___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withImportModules___rarg(lean_object*, lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_registerNamePrefixes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries(lean_object*, lean_object*);
static lean_object* l_Lean_Environment_registerNamespace___closed__1;
LEAN_EXPORT lean_object* l_Lean_Environment_addAndCompile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Environment_hasUnsafe___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_registerNamespace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnvExtensionInterface___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_getNamespaceSet(lean_object*);
static lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1;
static lean_object* l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg___closed__3;
static lean_object* l_List_toString___at_Lean_Environment_displayStats___spec__1___closed__1;
static lean_object* l_Lean_instInhabitedPersistentEnvExtension___closed__3;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAtAux___at_Lean_Environment_contains___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_whnf___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_MapDeclarationExtension_find_x3f___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___closed__3;
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__2;
lean_object* l_panic___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_ensureExtensionsArraySize_loop___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Environment_find_x3f___spec__3(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_instInhabitedEnvExtension___boxed(lean_object*, lean_object*);
static size_t l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___closed__2;
static lean_object* l_Lean_instInhabitedEnvExtensionInterface___closed__3;
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Environment_addAux___spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_instInhabitedEnvironment___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_importModules___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_instInhabitedPersistentEnvExtension___closed__5;
lean_object* l_Lean_withImporting___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_instToStringImport___closed__2;
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__10(size_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadEnv___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_importModules___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_mkModuleData___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__3;
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg___closed__1;
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at_Lean_Environment_displayStats___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_setState___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Environment_header___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtensionDescr_statsFn___default(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_4639_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_2057_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___rarg(lean_object*);
static lean_object* l_Lean_instInhabitedEnvExtensionInterface___closed__5;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l___private_Lean_Environment_0__Lean_getEntriesFor___closed__1;
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState___rarg___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedName;
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at_Lean_Environment_addAux___spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Environment_getModuleIdxFor_x3f___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at_Lean_importModules___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getNumBuiltiAttributes___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__6___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Import_runtimeOnly___default;
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_importModules___spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_MapDeclarationExtension_find_x3f___spec__1___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__7;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_addAux(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MapDeclarationExtension_contains___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg___closed__2;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_profileitIOUnsafe___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabitedSimplePersistentEnvExtension___rarg(lean_object*);
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__5;
LEAN_EXPORT uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__1;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtensionState(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Environment_getModuleIdx_x3f___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_getNamespaceSet___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Environment_getModuleIdxFor_x3f___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__5;
lean_object* lean_io_initializing(lean_object*);
static lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToStringImport(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MapDeclarationExtension_find_x3f___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_isTagged___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
lean_object* l_IO_println___at_Lean_instEval___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_isConstructor___boxed(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_imports___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_setState___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_namespacesExt;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_mkModuleData___spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates___spec__1(size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__3;
static lean_object* l_Lean_TagDeclarationExtension_isTagged___closed__1;
lean_object* lean_compile_decl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportState_moduleData___default;
lean_object* l_Array_findIdx_x3f_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_importModules___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___lambda__4(lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_EnvironmentHeader_imports___default;
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_envExtensionsRef;
uint8_t l_List_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Environment_addAux___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMapImp_contains___at_Lean_Environment_contains___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at_Lean_Environment_addAux___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_getModuleIdx_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at_Lean_Environment_addAux___spec__7___boxed(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnvExtension___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_addAndCompile___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_pure___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_contains___at_Lean_Environment_contains___spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Environment_find_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lambda__3(lean_object*);
lean_object* l_Lean_SMap_insert___at_Lean_NameSSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__6;
static lean_object* l_Lean_Environment_displayStats___closed__9;
static size_t l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvironmentHeader_moduleData___default;
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_EnvironmentHeader_trustLevel___default;
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg___closed__2;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_mkTagDeclarationExtension___closed__3;
lean_object* l_Std_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_object* l_Lean_importModules___closed__2;
LEAN_EXPORT lean_object* l_Lean_Kernel_isDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_compacted_region_free(size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_instInhabitedEnvironment___spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_contains(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lambda__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_setState___rarg___lambda__1(lean_object*, lean_object*);
uint8_t l_Std_Format_isNil(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnvExtensionState;
LEAN_EXPORT lean_object* l_Lean_EnvExtensionStateSpec;
LEAN_EXPORT lean_object* lean_environment_mark_quot_init(lean_object*);
lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__1___rarg___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_add_decl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_contains___at_Lean_Environment_contains___spec__2___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Lean_EnvExtensionStateSpec___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, lean_box(0));
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_EnvExtensionStateSpec() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_EnvExtensionStateSpec___closed__1;
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
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_instToStringImport___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" (runtime)");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringImport(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = 1;
x_4 = l_Lean_Name_toString(x_2, x_3);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_dec(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_instToStringImport___closed__1;
x_7 = lean_string_append(x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_instToStringImport___closed__2;
x_9 = lean_string_append(x_4, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CompactedRegion_isMemoryMapped___boxed(lean_object* x_1) {
_start:
{
size_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = lean_compacted_region_is_memory_mapped(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_CompactedRegion_free___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_compacted_region_free(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_EnvExtensionEntrySpec() {
_start:
{
return lean_box(0);
}
}
static lean_object* _init_l_Lean_instInhabitedModuleData___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedModuleData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedModuleData___closed__1;
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
x_1 = l_Lean_instInhabitedModuleData___closed__2;
return x_1;
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
x_1 = l_Lean_instInhabitedModuleData___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_EnvironmentHeader_regions___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedModuleData___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_EnvironmentHeader_moduleNames___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedModuleData___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_EnvironmentHeader_moduleData___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedModuleData___closed__1;
return x_1;
}
}
static uint32_t _init_l_Lean_instInhabitedEnvironmentHeader___closed__1() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedEnvironmentHeader___closed__2() {
_start:
{
uint32_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_instInhabitedEnvironmentHeader___closed__1;
x_2 = 0;
x_3 = lean_box(0);
x_4 = l_Lean_instInhabitedModuleData___closed__1;
x_5 = lean_alloc_ctor(0, 5, 5);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set(x_5, 4, x_4);
lean_ctor_set_uint32(x_5, sizeof(void*)*5, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*5 + 4, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_instInhabitedEnvironmentHeader() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedEnvironmentHeader___closed__2;
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
x_4 = l_Lean_instInhabitedModuleData___closed__1;
x_5 = lean_alloc_ctor(0, 5, 5);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set(x_5, 4, x_4);
lean_ctor_set_uint32(x_5, sizeof(void*)*5, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*5 + 4, x_2);
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
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_instInhabitedEnvironment___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_instInhabitedEnvironment___spec__2(lean_object* x_1) {
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
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedEnvironment___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedEnvironment___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedEnvironment___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedEnvironment___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instInhabitedEnvironment___closed__4() {
_start:
{
uint32_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_instInhabitedEnvironmentHeader___closed__1;
x_2 = 0;
x_3 = lean_box(0);
x_4 = l_Lean_instInhabitedModuleData___closed__1;
x_5 = lean_alloc_ctor(0, 5, 5);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set(x_5, 4, x_4);
lean_ctor_set_uint32(x_5, sizeof(void*)*5, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*5 + 4, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_instInhabitedEnvironment() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
x_3 = 1;
x_4 = l_Lean_instInhabitedEnvironment___closed__3;
lean_inc(x_2);
x_5 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_3);
x_6 = l_Lean_instInhabitedModuleData___closed__1;
x_7 = l_Lean_instInhabitedEnvironment___closed__4;
x_8 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_6);
lean_ctor_set(x_8, 3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_instInhabitedEnvironment___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMap___at_Lean_instInhabitedEnvironment___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_instInhabitedEnvironment___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMap___at_Lean_instInhabitedEnvironment___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Environment_addAux___spec__4(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_9; lean_object* x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Name_hash(x_9);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 1;
x_14 = lean_usize_sub(x_1, x_13);
x_15 = 5;
x_16 = lean_usize_mul(x_15, x_14);
x_17 = lean_usize_shift_right(x_12, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Environment_addAux___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static size_t _init_l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___closed__2;
x_11 = lean_usize_land(x_2, x_10);
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
x_16 = lean_box(0);
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
x_36 = lean_usize_shift_right(x_2, x_9);
x_37 = lean_usize_add(x_3, x_8);
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
x_41 = lean_usize_shift_right(x_2, x_9);
x_42 = lean_usize_add(x_3, x_8);
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
x_51 = l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___closed__2;
x_52 = lean_usize_land(x_2, x_51);
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
x_58 = lean_box(0);
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
x_73 = lean_usize_shift_right(x_2, x_50);
x_74 = lean_usize_add(x_3, x_49);
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
x_86 = lean_usize_dec_le(x_85, x_3);
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
x_92 = l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___closed__3;
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
x_100 = lean_usize_dec_le(x_99, x_3);
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
x_106 = l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___closed__3;
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at_Lean_Environment_addAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Name_hash(x_2);
x_8 = lean_uint64_to_usize(x_7);
x_9 = 1;
x_10 = l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3(x_5, x_8, x_9, x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_6, x_11);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; uint64_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l_Lean_Name_hash(x_2);
x_16 = lean_uint64_to_usize(x_15);
x_17 = 1;
x_18 = l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3(x_13, x_16, x_17, x_2, x_3);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_14, x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at_Lean_Environment_addAux___spec__7(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Environment_addAux___spec__10(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash(x_4);
x_8 = lean_uint64_to_usize(x_7);
x_9 = lean_usize_modn(x_8, x_6);
lean_dec(x_6);
x_10 = lean_array_uget(x_1, x_9);
lean_ctor_set(x_2, 2, x_10);
x_11 = lean_array_uset(x_1, x_9, x_2);
x_1 = x_11;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_16 = lean_array_get_size(x_1);
x_17 = l_Lean_Name_hash(x_13);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_modn(x_18, x_16);
lean_dec(x_16);
x_20 = lean_array_uget(x_1, x_19);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_array_uset(x_1, x_19, x_21);
x_1 = x_22;
x_2 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Environment_addAux___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at_Lean_Environment_addAux___spec__8(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_Environment_addAux___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_Environment_addAux___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash(x_2);
x_9 = lean_uint64_to_usize(x_8);
x_10 = lean_usize_modn(x_9, x_7);
x_11 = lean_array_uget(x_6, x_10);
x_12 = l_Std_AssocList_contains___at_Lean_Environment_addAux___spec__7(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_11);
x_16 = lean_array_uset(x_6, x_10, x_15);
x_17 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_14);
x_18 = lean_nat_dec_le(x_17, x_7);
lean_dec(x_7);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = l_Std_HashMapImp_expand___at_Lean_Environment_addAux___spec__8(x_14, x_16);
return x_19;
}
else
{
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_20 = l_Std_AssocList_replace___at_Lean_Environment_addAux___spec__11(x_2, x_3, x_11);
x_21 = lean_array_uset(x_6, x_10, x_20);
lean_ctor_set(x_1, 1, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_24 = lean_array_get_size(x_23);
x_25 = l_Lean_Name_hash(x_2);
x_26 = lean_uint64_to_usize(x_25);
x_27 = lean_usize_modn(x_26, x_24);
x_28 = lean_array_uget(x_23, x_27);
x_29 = l_Std_AssocList_contains___at_Lean_Environment_addAux___spec__7(x_2, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_22, x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_3);
lean_ctor_set(x_32, 2, x_28);
x_33 = lean_array_uset(x_23, x_27, x_32);
x_34 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_31);
x_35 = lean_nat_dec_le(x_34, x_24);
lean_dec(x_24);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Std_HashMapImp_expand___at_Lean_Environment_addAux___spec__8(x_31, x_33);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_24);
x_38 = l_Std_AssocList_replace___at_Lean_Environment_addAux___spec__11(x_2, x_3, x_28);
x_39 = lean_array_uset(x_23, x_27, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at_Lean_Environment_addAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_16 = l_Std_HashMap_insert___at_Lean_Environment_addAux___spec__6(x_15, x_2, x_3);
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
x_20 = l_Std_HashMap_insert___at_Lean_Environment_addAux___spec__6(x_18, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_Environment_addAux(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Environment_addAux___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at_Lean_Environment_addAux___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Environment_find_x3f___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Environment_find_x3f___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___closed__2;
x_7 = lean_usize_land(x_2, x_6);
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
x_17 = lean_usize_shift_right(x_2, x_5);
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Environment_find_x3f___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Environment_find_x3f___spec__3(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Environment_find_x3f___spec__6(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_uint64_to_usize(x_5);
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
lean_dec(x_3);
x_9 = l_Std_AssocList_find_x3f___at_Lean_Environment_find_x3f___spec__6(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at_Lean_Environment_find_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
lean_inc(x_2);
x_6 = l_Std_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(x_4, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_Std_PersistentHashMap_find_x3f___at_Lean_Environment_find_x3f___spec__2(x_5, x_2);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_5);
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
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
return x_12;
}
}
}
LEAN_EXPORT lean_object* lean_environment_find(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_SMap_find_x3f_x27___at_Lean_Environment_find_x3f___spec__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Environment_find_x3f___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Environment_find_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Environment_find_x3f___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_Environment_find_x3f___spec__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_HashMapImp_contains___at_Lean_Environment_contains___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_uint64_to_usize(x_5);
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
x_9 = l_Std_AssocList_contains___at_Lean_Environment_addAux___spec__7(x_2, x_8);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAtAux___at_Lean_Environment_contains___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAux___at_Lean_Environment_contains___spec__4(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___closed__2;
x_7 = lean_usize_land(x_2, x_6);
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
x_14 = lean_usize_shift_right(x_2, x_5);
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
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_contains___at_Lean_Environment_contains___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Std_PersistentHashMap_containsAux___at_Lean_Environment_contains___spec__4(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_SMap_contains___at_Lean_Environment_contains___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_dec(x_2);
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
lean_dec(x_2);
lean_dec(x_9);
return x_10;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Environment_contains(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_contains___at_Lean_Environment_contains___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAtAux___at_Lean_Environment_contains___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAux___at_Lean_Environment_contains___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_contains___at_Lean_Environment_contains___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_PersistentHashMap_contains___at_Lean_Environment_contains___spec__3(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_contains___at_Lean_Environment_contains___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_SMap_contains___at_Lean_Environment_contains___spec__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_contains___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Environment_contains(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_imports(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_imports___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Environment_imports(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_allImportedModuleNames(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_allImportedModuleNames___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Environment_allImportedModuleNames(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_environment_set_main_module(lean_object* x_1, lean_object* x_2) {
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
uint32_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get_uint32(x_4, sizeof(void*)*5);
x_8 = lean_ctor_get_uint8(x_4, sizeof(void*)*5 + 4);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_4, 2);
x_11 = lean_ctor_get(x_4, 3);
x_12 = lean_ctor_get(x_4, 4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 5, 5);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_9);
lean_ctor_set(x_13, 2, x_10);
lean_ctor_set(x_13, 3, x_11);
lean_ctor_set(x_13, 4, x_12);
lean_ctor_set_uint32(x_13, sizeof(void*)*5, x_7);
lean_ctor_set_uint8(x_13, sizeof(void*)*5 + 4, x_8);
lean_ctor_set(x_1, 3, x_13);
return x_1;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint32_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_14 = lean_ctor_get(x_1, 3);
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_18 = lean_ctor_get_uint32(x_14, sizeof(void*)*5);
x_19 = lean_ctor_get_uint8(x_14, sizeof(void*)*5 + 4);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_14, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_14, 3);
lean_inc(x_22);
x_23 = lean_ctor_get(x_14, 4);
lean_inc(x_23);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 lean_ctor_release(x_14, 4);
 x_24 = x_14;
} else {
 lean_dec_ref(x_14);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(0, 5, 5);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_20);
lean_ctor_set(x_25, 2, x_21);
lean_ctor_set(x_25, 3, x_22);
lean_ctor_set(x_25, 4, x_23);
lean_ctor_set_uint32(x_25, sizeof(void*)*5, x_18);
lean_ctor_set_uint8(x_25, sizeof(void*)*5 + 4, x_19);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 2, x_17);
lean_ctor_set(x_26, 3, x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* lean_environment_main_module(lean_object* x_1) {
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
LEAN_EXPORT lean_object* lean_environment_mark_quot_init(lean_object* x_1) {
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
lean_ctor_set_uint8(x_3, sizeof(void*)*5 + 4, x_5);
return x_1;
}
else
{
uint32_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_6 = lean_ctor_get_uint32(x_3, sizeof(void*)*5);
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_3, 2);
x_10 = lean_ctor_get(x_3, 3);
x_11 = lean_ctor_get(x_3, 4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_12 = 1;
x_13 = lean_alloc_ctor(0, 5, 5);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_9);
lean_ctor_set(x_13, 3, x_10);
lean_ctor_set(x_13, 4, x_11);
lean_ctor_set_uint32(x_13, sizeof(void*)*5, x_6);
lean_ctor_set_uint8(x_13, sizeof(void*)*5 + 4, x_12);
lean_ctor_set(x_1, 3, x_13);
return x_1;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint32_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_1, 3);
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_18 = lean_ctor_get_uint32(x_14, sizeof(void*)*5);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_14, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_14, 3);
lean_inc(x_22);
x_23 = lean_ctor_get(x_14, 4);
lean_inc(x_23);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 lean_ctor_release(x_14, 4);
 x_24 = x_14;
} else {
 lean_dec_ref(x_14);
 x_24 = lean_box(0);
}
x_25 = 1;
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 5, 5);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 3, x_22);
lean_ctor_set(x_26, 4, x_23);
lean_ctor_set_uint32(x_26, sizeof(void*)*5, x_18);
lean_ctor_set_uint8(x_26, sizeof(void*)*5 + 4, x_25);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_16);
lean_ctor_set(x_27, 2, x_17);
lean_ctor_set(x_27, 3, x_26);
return x_27;
}
}
}
LEAN_EXPORT uint8_t lean_environment_quot_init(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*5 + 4);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_isQuotInit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_environment_quot_init(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint32_t lean_environment_trust_level(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get_uint32(x_2, sizeof(void*)*5);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_getTrustLevel___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_environment_trust_level(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Environment_getModuleIdxFor_x3f___spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Environment_getModuleIdxFor_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_uint64_to_usize(x_5);
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
lean_dec(x_3);
x_9 = l_Std_AssocList_find_x3f___at_Lean_Environment_getModuleIdxFor_x3f___spec__2(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Std_HashMapImp_find_x3f___at_Lean_Environment_getModuleIdxFor_x3f___spec__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Environment_getModuleIdxFor_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_Environment_getModuleIdxFor_x3f___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Environment_isConstructor(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Environment_isConstructor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Environment_isConstructor(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Environment_getModuleIdx_x3f___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_name_eq(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getModuleIdx_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = lean_ctor_get(x_3, 3);
x_5 = lean_alloc_closure((void*)(l_Lean_Environment_getModuleIdx_x3f___lambda__1___boxed), 2, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = lean_array_get_size(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_findIdx_x3f_loop___rarg(x_4, x_5, x_6, x_7, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getModuleIdx_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Environment_getModuleIdx_x3f___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getModuleIdx_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Environment_getModuleIdx_x3f(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_addDecl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_add_decl(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_compileDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_compile_decl(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_addAndCompile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Environment_addAndCompile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_addAndCompile(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnvExtensionInterface___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnvExtensionInterface___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnvExtensionInterface___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_1 = l_Lean_instInhabitedModuleData___closed__1;
x_2 = lean_alloc_closure((void*)(l_EStateM_pure___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedEnvExtensionInterface___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instInhabitedEnvExtensionInterface___lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedEnvExtensionInterface___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instInhabitedEnvExtensionInterface___lambda__2), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedEnvExtensionInterface___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instInhabitedEnvExtensionInterface___lambda__3___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedEnvExtensionInterface___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_EStateM_pure___rarg), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedEnvExtensionInterface___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_instInhabitedEnvExtensionInterface___closed__2;
x_2 = l_Lean_instInhabitedEnvExtensionInterface___closed__3;
x_3 = l_Lean_instInhabitedEnvExtensionInterface___closed__4;
x_4 = l_Lean_instInhabitedEnvExtensionInterface___closed__1;
x_5 = l_Lean_instInhabitedEnvExtensionInterface___closed__5;
x_6 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_3);
lean_ctor_set(x_6, 4, x_3);
lean_ctor_set(x_6, 5, x_4);
lean_ctor_set(x_6, 6, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_instInhabitedEnvExtensionInterface() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedEnvExtensionInterface___closed__6;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnvExtensionInterface___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instInhabitedEnvExtensionInterface___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnvExtensionInterface___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_instInhabitedEnvExtensionInterface___lambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1___closed__1() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_instInhabitedEnvironmentHeader___closed__1;
x_3 = l_Lean_instToStringImport___closed__1;
x_4 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint32(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__2;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_initFn____x40_Lean_Environment___hyg_1069_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_instInhabitedModuleData___closed__1;
x_3 = lean_st_mk_ref(x_2, x_1);
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
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_ensureExtensionsArraySize_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_envExtensionsRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_ensureExtensionsArraySize_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_ensureExtensionsArraySize_loop___closed__1;
x_5 = lean_st_ref_get(x_4, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_array_get_size(x_7);
x_10 = lean_nat_dec_lt(x_1, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_7);
lean_dec(x_1);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_free_object(x_5);
x_11 = l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__2;
x_12 = lean_array_get(x_11, x_7, x_1);
lean_dec(x_7);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_1(x_13, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_2, 2);
x_19 = lean_array_push(x_18, x_15);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_1, x_20);
lean_dec(x_1);
x_1 = x_21;
x_3 = x_16;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_2, 2);
x_26 = lean_ctor_get(x_2, 3);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_2);
x_27 = lean_array_push(x_25, x_15);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_26);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_1, x_29);
lean_dec(x_1);
x_1 = x_30;
x_2 = x_28;
x_3 = x_16;
goto _start;
}
}
else
{
uint8_t x_32; 
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
return x_14;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_14, 0);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_14);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_5, 0);
x_37 = lean_ctor_get(x_5, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_5);
x_38 = lean_array_get_size(x_36);
x_39 = lean_nat_dec_lt(x_1, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_36);
lean_dec(x_1);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_2);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__2;
x_42 = lean_array_get(x_41, x_36, x_1);
lean_dec(x_36);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_apply_1(x_43, x_37);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_2, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 3);
lean_inc(x_50);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 x_51 = x_2;
} else {
 lean_dec_ref(x_2);
 x_51 = lean_box(0);
}
x_52 = lean_array_push(x_49, x_45);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 4, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_48);
lean_ctor_set(x_53, 2, x_52);
lean_ctor_set(x_53, 3, x_50);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_1, x_54);
lean_dec(x_1);
x_1 = x_55;
x_2 = x_53;
x_3 = x_46;
goto _start;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_ctor_get(x_44, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_44, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_59 = x_44;
} else {
 lean_dec_ref(x_44);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_ensureExtensionsArraySize(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_5 = l_Lean_EnvExtensionInterfaceUnsafe_ensureExtensionsArraySize_loop(x_4, x_1, x_2);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_invalidExtMsg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid environment extension has been accessed");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_invalidExtMsg() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_invalidExtMsg___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_EnvExtensionInterfaceUnsafe_setState___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedEnvironment;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Environment");
return x_1;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.EnvExtensionInterfaceUnsafe.setState");
return x_1;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg___closed__1;
x_2 = l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg___closed__2;
x_3 = lean_unsigned_to_nat(219u);
x_4 = lean_unsigned_to_nat(4u);
x_5 = l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_invalidExtMsg;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_array_get_size(x_8);
x_11 = lean_nat_dec_lt(x_4, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_12 = l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg___closed__3;
x_13 = l_panic___at_Lean_EnvExtensionInterfaceUnsafe_setState___spec__1(x_12);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_array_fset(x_8, x_4, x_3);
lean_dec(x_4);
lean_ctor_set(x_2, 2, x_14);
return x_2;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_ctor_get(x_2, 2);
x_18 = lean_ctor_get(x_2, 3);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_2);
x_19 = lean_array_get_size(x_17);
x_20 = lean_nat_dec_lt(x_4, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
x_21 = l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg___closed__3;
x_22 = l_panic___at_Lean_EnvExtensionInterfaceUnsafe_setState___spec__1(x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_array_fset(x_17, x_4, x_3);
lean_dec(x_4);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set(x_24, 3, x_18);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_setState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.EnvExtensionInterfaceUnsafe.modifyState");
return x_1;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg___closed__1;
x_2 = l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg___closed__1;
x_3 = lean_unsigned_to_nat(229u);
x_4 = lean_unsigned_to_nat(4u);
x_5 = l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_invalidExtMsg;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_array_get_size(x_8);
x_11 = lean_nat_dec_lt(x_5, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_12 = l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg___closed__2;
x_13 = l_panic___at_Lean_EnvExtensionInterfaceUnsafe_setState___spec__1(x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_fget(x_8, x_5);
x_15 = lean_box(0);
x_16 = lean_array_fset(x_8, x_5, x_15);
x_17 = lean_apply_1(x_3, x_14);
x_18 = lean_array_fset(x_16, x_5, x_17);
lean_ctor_set(x_2, 2, x_18);
return x_2;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_2, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
x_24 = lean_array_get_size(x_22);
x_25 = lean_nat_dec_lt(x_19, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_3);
x_26 = l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg___closed__2;
x_27 = l_panic___at_Lean_EnvExtensionInterfaceUnsafe_setState___spec__1(x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_array_fget(x_22, x_19);
x_29 = lean_box(0);
x_30 = lean_array_fset(x_22, x_19, x_29);
x_31 = lean_apply_1(x_3, x_28);
x_32 = lean_array_fset(x_30, x_19, x_31);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_20);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_23);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_modifyState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.EnvExtensionInterfaceUnsafe.getState");
return x_1;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg___closed__1;
x_2 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg___closed__1;
x_3 = lean_unsigned_to_nat(236u);
x_4 = lean_unsigned_to_nat(4u);
x_5 = l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_invalidExtMsg;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_3, 2);
x_6 = lean_array_get_size(x_5);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg___closed__2;
x_9 = l_panic___rarg(x_1, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_array_fget(x_5, x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_ensureExtensionsArraySize_loop___closed__1;
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
x_13 = lean_array_push(x_11, x_9);
x_14 = lean_st_ref_set(x_4, x_13, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_9);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_17);
return x_18;
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
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_initializing(x_2);
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
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_2, x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_array_uget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_3, x_2, x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_apply_1(x_10, x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_9, x_2, x_12);
x_2 = x_15;
x_3 = x_16;
x_4 = x_13;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_9);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_2 = l_Lean_EnvExtensionInterfaceUnsafe_ensureExtensionsArraySize_loop___closed__1;
x_3 = lean_st_ref_get(x_2, x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_array_get_size(x_4);
x_7 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_8 = 0;
x_9 = l_Array_mapMUnsafe_map___at_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates___spec__1(x_7, x_8, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__1___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_array_get_size(x_8);
x_11 = lean_nat_dec_lt(x_5, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_12 = l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg___closed__2;
x_13 = l_panic___at_Lean_EnvExtensionInterfaceUnsafe_setState___spec__1(x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_fget(x_8, x_5);
x_15 = lean_box(0);
x_16 = lean_array_fset(x_8, x_5, x_15);
x_17 = lean_apply_1(x_3, x_14);
x_18 = lean_array_fset(x_16, x_5, x_17);
lean_ctor_set(x_2, 2, x_18);
return x_2;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_2, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
x_24 = lean_array_get_size(x_22);
x_25 = lean_nat_dec_lt(x_19, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_3);
x_26 = l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg___closed__2;
x_27 = l_panic___at_Lean_EnvExtensionInterfaceUnsafe_setState___spec__1(x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_array_fget(x_22, x_19);
x_29 = lean_box(0);
x_30 = lean_array_fset(x_22, x_19, x_29);
x_31 = lean_apply_1(x_3, x_28);
x_32 = lean_array_fset(x_30, x_19, x_31);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_20);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_23);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__3___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__4___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__4___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__5(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_ensureExtensionsArraySize), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__1;
x_2 = l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__2;
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__3;
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__4;
x_5 = l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__5;
x_6 = l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__6;
x_7 = l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__7;
x_8 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 3, x_4);
lean_ctor_set(x_8, 4, x_5);
lean_ctor_set(x_8, 5, x_6);
lean_ctor_set(x_8, 6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_imp() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__8;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__1___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__5(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_ensureExtensionsArraySize(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_ensureExtensionsArraySize(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_instInhabitedEnvExtension(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__2;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_instInhabitedEnvExtension___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EnvExtension_instInhabitedEnvExtension(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_setState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_setState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_EnvExtension_setState___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_EnvExtension_modifyState___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnvExtension_modifyState___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_getState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_getState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_EnvExtension_getState___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_getState___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnvExtension_getState___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnvExtension___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnvExtension(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_registerEnvExtension___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_mkInitialExtensionStates(lean_object* x_1) {
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkEmptyEnvironment___lambda__1___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_mkEmptyEnvironment___lambda__1___closed__1;
x_3 = l_Lean_instInhabitedEnvironment___closed__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkEmptyEnvironment___lambda__1(uint32_t x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Lean_instInhabitedModuleData___closed__1;
x_10 = lean_alloc_ctor(0, 5, 5);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_9);
lean_ctor_set(x_10, 3, x_9);
lean_ctor_set(x_10, 4, x_9);
lean_ctor_set_uint32(x_10, sizeof(void*)*5, x_1);
lean_ctor_set_uint8(x_10, sizeof(void*)*5 + 4, x_7);
x_11 = l_Lean_mkEmptyEnvironment___lambda__1___closed__1;
x_12 = l_Lean_mkEmptyEnvironment___lambda__1___closed__2;
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
x_18 = l_Lean_instInhabitedModuleData___closed__1;
x_19 = lean_alloc_ctor(0, 5, 5);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set(x_19, 3, x_18);
lean_ctor_set(x_19, 4, x_18);
lean_ctor_set_uint32(x_19, sizeof(void*)*5, x_1);
lean_ctor_set_uint8(x_19, sizeof(void*)*5 + 4, x_16);
x_20 = l_Lean_mkEmptyEnvironment___lambda__1___closed__1;
x_21 = l_Lean_mkEmptyEnvironment___lambda__1___closed__2;
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
LEAN_EXPORT lean_object* lean_mk_empty_environment(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_io_initializing(x_2);
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
}
LEAN_EXPORT lean_object* l_Lean_mkEmptyEnvironment___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_mkEmptyEnvironment___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_empty_environment(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedModuleData___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtensionState(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instInhabitedPersistentEnvExtensionState___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1___closed__1;
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___lambda__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instInhabitedModuleData___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___lambda__4(lean_object* x_1) {
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
x_1 = lean_alloc_closure((void*)(l_Lean_instInhabitedPersistentEnvExtension___lambda__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedPersistentEnvExtension___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instInhabitedPersistentEnvExtension___lambda__3___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedPersistentEnvExtension___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instInhabitedPersistentEnvExtension___lambda__4___boxed), 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_instInhabitedPersistentEnvExtension___closed__5;
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instInhabitedPersistentEnvExtension___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instInhabitedPersistentEnvExtension___lambda__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___lambda__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instInhabitedPersistentEnvExtension___lambda__3(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___lambda__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instInhabitedPersistentEnvExtension___lambda__4(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_instInhabitedPersistentEnvExtension(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_instInhabitedPersistentEnvExtensionState___rarg(x_1);
x_6 = lean_ctor_get(x_2, 0);
x_7 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_5, x_6, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_instInhabitedModuleData___closed__1;
x_10 = lean_array_get(x_9, x_8, x_4);
lean_dec(x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getModuleEntries(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentEnvExtension_getModuleEntries___rarg___boxed), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentEnvExtension_getModuleEntries___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_addEntry(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentEnvExtension_addEntry___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_instInhabitedPersistentEnvExtensionState___rarg(x_1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_4, x_5, x_3);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getState(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentEnvExtension_getState___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getState___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentEnvExtension_getState___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_setState___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_setState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_setState(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentEnvExtension_setState___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_setState___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentEnvExtension_setState___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_modifyState___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_modifyState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_modifyState(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentEnvExtension_modifyState___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_modifyState___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentEnvExtension_modifyState___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_2057_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_instInhabitedModuleData___closed__1;
x_3 = lean_st_mk_ref(x_2, x_1);
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
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtensionDescr_statsFn___default(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtensionDescr_statsFn___default___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentEnvExtensionDescr_statsFn___default(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_name_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg___boxed), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_instInhabitedModuleData___closed__1;
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
static lean_object* _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_persistentEnvExtensionsRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
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
x_16 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2___closed__2;
x_17 = lean_st_ref_take(x_16, x_14);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_15);
x_20 = lean_array_push(x_18, x_15);
x_21 = lean_st_ref_set(x_16, x_20, x_19);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_15);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_15);
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
x_26 = !lean_is_exclusive(x_12);
if (x_26 == 0)
{
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
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
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2___closed__2;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_free_object(x_4);
lean_dec(x_6);
x_11 = lean_box(0);
x_12 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_11, x_7);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_8, x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_free_object(x_4);
lean_dec(x_6);
x_14 = lean_box(0);
x_15 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_14, x_7);
return x_15;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_18 = l_Array_anyMUnsafe_any___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg(x_1, x_6, x_16, x_17);
lean_dec(x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_4);
x_19 = lean_box(0);
x_20 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_19, x_7);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = 1;
x_23 = l_Lean_Name_toString(x_21, x_22);
x_24 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_28);
return x_4;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_ctor_get(x_4, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_4);
x_31 = lean_array_get_size(x_29);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_lt(x_32, x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_31);
lean_dec(x_29);
x_34 = lean_box(0);
x_35 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_34, x_30);
return x_35;
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_31, x_31);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_31);
lean_dec(x_29);
x_37 = lean_box(0);
x_38 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_37, x_30);
return x_38;
}
else
{
size_t x_39; size_t x_40; uint8_t x_41; 
x_39 = 0;
x_40 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_41 = l_Array_anyMUnsafe_any___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg(x_1, x_29, x_39, x_40);
lean_dec(x_29);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_box(0);
x_43 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_42, x_30);
return x_43;
}
else
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
lean_dec(x_1);
x_45 = 1;
x_46 = l_Lean_Name_toString(x_44, x_45);
x_47 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_48 = lean_string_append(x_47, x_46);
lean_dec(x_46);
x_49 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_50 = lean_string_append(x_48, x_49);
x_51 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_30);
return x_52;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_registerPersistentEnvExtensionUnsafe___rarg), 2, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_registerPersistentEnvExtensionUnsafe___spec__1___rarg(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_registerPersistentEnvExtensionUnsafe(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Id_instMonadId;
x_11 = l_Array_foldlMUnsafe_fold___rarg(x_10, x_1, x_3, x_8, x_9, x_2);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_alloc_closure((void*)(l_Lean_mkStateFromImportedEntries___rarg___lambda__1), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_array_get_size(x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_5);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Id_instMonadId;
x_12 = l_Array_foldlMUnsafe_fold___rarg(x_11, x_4, x_3, x_9, x_10, x_2);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_mkStateFromImportedEntries___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtensionDescr_toArrayFn___default___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtensionDescr_toArrayFn___default(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtensionDescr_toArrayFn___default___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__3(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_lengthTRAux___rarg(x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_box(0);
x_6 = l_Lean_instInhabitedModuleData___closed__1;
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
x_15 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg(x_14, x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_registerSimplePersistentEnvExtension(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabitedSimplePersistentEnvExtension___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabitedSimplePersistentEnvExtension(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_instInhabitedSimplePersistentEnvExtension___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
x_6 = l_Lean_PersistentEnvExtension_getState___rarg(x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_getEntries___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_SimplePersistentEnvExtension_getEntries___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
x_6 = l_Lean_PersistentEnvExtension_getState___rarg(x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_getState___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_setState___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_setState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_setState___rarg___lambda__1), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = l_Lean_PersistentEnvExtension_modifyState___rarg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_setState(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_setState___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_setState___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_SimplePersistentEnvExtension_setState___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_modifyState___rarg___lambda__1), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = l_Lean_PersistentEnvExtension_modifyState___rarg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_modifyState(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_modifyState___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_SimplePersistentEnvExtension_modifyState___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
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
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_15 = lean_nat_add(x_3, x_4);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_nat_div(x_15, x_16);
lean_dec(x_15);
lean_inc(x_1);
x_41 = lean_array_get(x_1, x_2, x_17);
lean_inc(x_1);
x_42 = lean_array_get(x_1, x_2, x_3);
x_43 = l_Lean_Name_quickLt(x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
if (x_43 == 0)
{
x_18 = x_2;
goto block_40;
}
else
{
lean_object* x_44; 
x_44 = lean_array_swap(x_2, x_3, x_17);
x_18 = x_44;
goto block_40;
}
block_40:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_inc(x_1);
x_19 = lean_array_get(x_1, x_18, x_4);
lean_inc(x_1);
x_20 = lean_array_get(x_1, x_18, x_3);
x_21 = l_Lean_Name_quickLt(x_19, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
lean_inc(x_1);
x_22 = lean_array_get(x_1, x_18, x_17);
x_23 = l_Lean_Name_quickLt(x_22, x_19);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_17);
x_24 = l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1___closed__1;
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_25 = l_Array_qpartition_loop___rarg(x_1, x_24, x_4, x_19, x_18, x_3, x_3);
x_5 = x_25;
goto block_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_19);
x_26 = lean_array_swap(x_18, x_17, x_4);
lean_dec(x_17);
lean_inc(x_1);
x_27 = lean_array_get(x_1, x_26, x_4);
x_28 = l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1___closed__1;
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_29 = l_Array_qpartition_loop___rarg(x_1, x_28, x_4, x_27, x_26, x_3, x_3);
x_5 = x_29;
goto block_13;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_19);
x_30 = lean_array_swap(x_18, x_3, x_4);
lean_inc(x_1);
x_31 = lean_array_get(x_1, x_30, x_17);
lean_inc(x_1);
x_32 = lean_array_get(x_1, x_30, x_4);
x_33 = l_Lean_Name_quickLt(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_17);
x_34 = l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1___closed__1;
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_35 = l_Array_qpartition_loop___rarg(x_1, x_34, x_4, x_32, x_30, x_3, x_3);
x_5 = x_35;
goto block_13;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_32);
x_36 = lean_array_swap(x_30, x_17, x_4);
lean_dec(x_17);
lean_inc(x_1);
x_37 = lean_array_get(x_1, x_36, x_4);
x_38 = l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1___closed__1;
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_39 = l_Array_qpartition_loop___rarg(x_1, x_38, x_4, x_37, x_36, x_3, x_3);
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
x_9 = l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1(x_1, x_7, x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_NameSet_empty;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lambda__3(lean_object* x_1) {
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
x_8 = l_Lean_instInhabitedName;
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1(x_8, x_4, x_9, x_7);
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
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_registerSimplePersistentEnvExtension___rarg(x_6, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lambda__2___boxed(lean_object* x_1) {
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
static lean_object* _init_l_Lean_TagDeclarationExtension_tag___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("assertion violation: ");
return x_1;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_tag___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("env.getModuleIdxFor? declName |>.isNone -- See comment at `TagDeclarationExtension`\n  ");
return x_1;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_tag___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_TagDeclarationExtension_tag___closed__1;
x_2 = l_Lean_TagDeclarationExtension_tag___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_tag___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.TagDeclarationExtension.tag");
return x_1;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_tag___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg___closed__1;
x_2 = l_Lean_TagDeclarationExtension_tag___closed__4;
x_3 = lean_unsigned_to_nat(467u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_TagDeclarationExtension_tag___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_tag(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Environment_getModuleIdxFor_x3f(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Lean_TagDeclarationExtension_tag___closed__5;
x_7 = l_panic___at_Lean_EnvExtensionInterfaceUnsafe_setState___spec__1(x_6);
return x_7;
}
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at_Lean_TagDeclarationExtension_isTagged___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_nat_add(x_5, x_6);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
lean_inc(x_1);
x_12 = lean_array_get(x_1, x_3, x_11);
x_13 = l_Lean_Name_quickLt(x_12, x_4);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_6);
x_14 = l_Lean_Name_quickLt(x_4, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_15 = 1;
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_11, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_11, x_18);
lean_dec(x_11);
x_6 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_21 = 0;
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_12);
lean_dec(x_5);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_11, x_22);
lean_dec(x_11);
x_5 = x_23;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_isTagged___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_NameSet_instInhabitedNameSet;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Environment_getModuleIdxFor_x3f(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_NameSet_instInhabitedNameSet;
x_6 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_5, x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_NameSet_contains(x_6, x_3);
lean_dec(x_3);
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = l_Lean_TagDeclarationExtension_isTagged___closed__1;
x_10 = l_Lean_PersistentEnvExtension_getModuleEntries___rarg(x_9, x_1, x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_11, x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_11);
lean_dec(x_11);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_3);
x_16 = 0;
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; uint8_t x_19; 
x_17 = l_Lean_instInhabitedName;
x_18 = l_instInhabitedBool;
x_19 = l_Array_binSearchAux___at_Lean_TagDeclarationExtension_isTagged___spec__1(x_17, x_18, x_10, x_3, x_14, x_13);
lean_dec(x_3);
lean_dec(x_10);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_TagDeclarationExtension_isTagged___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Array_binSearchAux___at_Lean_TagDeclarationExtension_isTagged___spec__1(x_1, x_7, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_isTagged___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_TagDeclarationExtension_isTagged(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Name_quickLt(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__1___rarg___lambda__1___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_15 = lean_nat_add(x_3, x_4);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_nat_div(x_15, x_16);
lean_dec(x_15);
lean_inc(x_1);
x_46 = lean_array_get(x_1, x_2, x_17);
lean_inc(x_1);
x_47 = lean_array_get(x_1, x_2, x_3);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_Name_quickLt(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
if (x_50 == 0)
{
x_18 = x_2;
goto block_45;
}
else
{
lean_object* x_51; 
x_51 = lean_array_swap(x_2, x_3, x_17);
x_18 = x_51;
goto block_45;
}
block_45:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_inc(x_1);
x_19 = lean_array_get(x_1, x_18, x_4);
lean_inc(x_1);
x_20 = lean_array_get(x_1, x_18, x_3);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Name_quickLt(x_21, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_inc(x_1);
x_24 = lean_array_get(x_1, x_18, x_17);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_Name_quickLt(x_25, x_21);
lean_dec(x_21);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_17);
x_27 = l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__1___rarg___closed__1;
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_28 = l_Array_qpartition_loop___rarg(x_1, x_27, x_4, x_19, x_18, x_3, x_3);
x_5 = x_28;
goto block_13;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_19);
x_29 = lean_array_swap(x_18, x_17, x_4);
lean_dec(x_17);
lean_inc(x_1);
x_30 = lean_array_get(x_1, x_29, x_4);
x_31 = l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__1___rarg___closed__1;
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_32 = l_Array_qpartition_loop___rarg(x_1, x_31, x_4, x_30, x_29, x_3, x_3);
x_5 = x_32;
goto block_13;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_21);
lean_dec(x_19);
x_33 = lean_array_swap(x_18, x_3, x_4);
lean_inc(x_1);
x_34 = lean_array_get(x_1, x_33, x_17);
lean_inc(x_1);
x_35 = lean_array_get(x_1, x_33, x_4);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = l_Lean_Name_quickLt(x_36, x_37);
lean_dec(x_37);
lean_dec(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_17);
x_39 = l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__1___rarg___closed__1;
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_40 = l_Array_qpartition_loop___rarg(x_1, x_39, x_4, x_35, x_33, x_3, x_3);
x_5 = x_40;
goto block_13;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_35);
x_41 = lean_array_swap(x_33, x_17, x_4);
lean_dec(x_17);
lean_inc(x_1);
x_42 = lean_array_get(x_1, x_41, x_4);
x_43 = l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__1___rarg___closed__1;
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_44 = l_Array_qpartition_loop___rarg(x_1, x_43, x_4, x_42, x_41, x_3, x_3);
x_5 = x_44;
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
x_9 = l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__1___rarg(x_1, x_7, x_3, x_6);
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
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___rarg___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___rarg___lambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = l_Lean_instInhabitedName;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
x_5 = l_List_redLength___rarg(x_2);
x_6 = lean_mk_empty_array_with_capacity(x_5);
lean_dec(x_5);
x_7 = l_List_toArrayAux___rarg(x_2, x_6);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_8, x_9);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__1___rarg(x_4, x_7, x_11, x_10);
lean_dec(x_10);
return x_12;
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
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_alloc_closure((void*)(l_Lean_mkMapDeclarationExtension___rarg___lambda__3), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_mkMapDeclarationExtension___rarg___closed__1;
x_6 = l_Lean_mkMapDeclarationExtension___rarg___closed__2;
x_7 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
lean_ctor_set(x_7, 3, x_4);
x_8 = l_Lean_registerSimplePersistentEnvExtension___rarg(x_7, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_mkMapDeclarationExtension___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__1___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___rarg___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkMapDeclarationExtension___rarg___lambda__2(x_1);
lean_dec(x_1);
return x_2;
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
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_instInhabitedMapDeclarationExtension(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MapDeclarationExtension_instInhabitedMapDeclarationExtension___closed__1;
return x_2;
}
}
static lean_object* _init_l_Lean_MapDeclarationExtension_insert___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("env.getModuleIdxFor? declName |>.isNone -- See comment at `MapDeclarationExtension`\n  ");
return x_1;
}
}
static lean_object* _init_l_Lean_MapDeclarationExtension_insert___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_TagDeclarationExtension_tag___closed__1;
x_2 = l_Lean_MapDeclarationExtension_insert___rarg___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MapDeclarationExtension_insert___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.MapDeclarationExtension.insert");
return x_1;
}
}
static lean_object* _init_l_Lean_MapDeclarationExtension_insert___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg___closed__1;
x_2 = l_Lean_MapDeclarationExtension_insert___rarg___closed__3;
x_3 = lean_unsigned_to_nat(496u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_MapDeclarationExtension_insert___rarg___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_Environment_getModuleIdxFor_x3f(x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_1, x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = l_Lean_MapDeclarationExtension_insert___rarg___closed__4;
x_9 = l_panic___at_Lean_EnvExtensionInterfaceUnsafe_setState___spec__1(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MapDeclarationExtension_insert___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_MapDeclarationExtension_find_x3f___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_MapDeclarationExtension_find_x3f___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_find___at_Lean_MapDeclarationExtension_find_x3f___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_MapDeclarationExtension_find_x3f___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_nat_add(x_5, x_6);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
lean_inc(x_1);
x_12 = lean_array_get(x_1, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
x_15 = l_Lean_Name_quickLt(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Name_quickLt(x_14, x_13);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_12);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_12);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_11, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_11, x_20);
lean_dec(x_11);
x_6 = x_21;
goto _start;
}
else
{
lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_11, x_24);
lean_dec(x_11);
x_5 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_MapDeclarationExtension_find_x3f___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_MapDeclarationExtension_find_x3f___spec__2___rarg___boxed), 6, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_MapDeclarationExtension_find_x3f___rarg___closed__1() {
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
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_4);
lean_inc(x_3);
x_5 = l_Lean_Environment_getModuleIdxFor_x3f(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_6, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_8 = l_Std_RBNode_find___at_Lean_MapDeclarationExtension_find_x3f___spec__1___rarg(x_7, x_4);
lean_dec(x_4);
lean_dec(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = l_Lean_instInhabitedName;
lean_inc(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = l_Lean_MapDeclarationExtension_find_x3f___rarg___closed__1;
x_13 = l_Lean_PersistentEnvExtension_getModuleEntries___rarg(x_12, x_2, x_3, x_9);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_array_get_size(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_15, x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_lt(x_18, x_15);
lean_dec(x_15);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
x_20 = lean_box(0);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l_Array_binSearchAux___at_Lean_MapDeclarationExtension_find_x3f___spec__2___rarg(x_11, x_21, x_13, x_14, x_18, x_17);
lean_dec(x_14);
lean_dec(x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_box(0);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MapDeclarationExtension_find_x3f___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_MapDeclarationExtension_find_x3f___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_MapDeclarationExtension_find_x3f___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_MapDeclarationExtension_find_x3f___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_binSearchAux___at_Lean_MapDeclarationExtension_find_x3f___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at_Lean_MapDeclarationExtension_contains___spec__1___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_nat_add(x_5, x_6);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
lean_inc(x_1);
x_12 = lean_array_get(x_1, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_4, 0);
x_15 = l_Lean_Name_quickLt(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Name_quickLt(x_14, x_13);
lean_dec(x_13);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_17 = 1;
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_11, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_11, x_20);
lean_dec(x_11);
x_6 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_23 = 0;
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_13);
lean_dec(x_5);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_11, x_24);
lean_dec(x_11);
x_5 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_MapDeclarationExtension_contains___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_MapDeclarationExtension_contains___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_MapDeclarationExtension_contains___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_4);
lean_inc(x_3);
x_5 = l_Lean_Environment_getModuleIdxFor_x3f(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_6, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_8 = l_Lean_NameMap_contains___rarg(x_7, x_4);
lean_dec(x_4);
lean_dec(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = l_Lean_instInhabitedName;
lean_inc(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = l_Lean_MapDeclarationExtension_find_x3f___rarg___closed__1;
x_13 = l_Lean_PersistentEnvExtension_getModuleEntries___rarg(x_12, x_2, x_3, x_9);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_array_get_size(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_15, x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_lt(x_18, x_15);
lean_dec(x_15);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
x_20 = 0;
return x_20;
}
else
{
uint8_t x_21; uint8_t x_22; 
x_21 = l_instInhabitedBool;
x_22 = l_Array_binSearchAux___at_Lean_MapDeclarationExtension_contains___spec__1___rarg(x_11, x_21, x_13, x_14, x_18, x_17);
lean_dec(x_14);
lean_dec(x_13);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_contains(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MapDeclarationExtension_contains___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_MapDeclarationExtension_contains___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Array_binSearchAux___at_Lean_MapDeclarationExtension_contains___spec__1___rarg(x_1, x_7, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_contains___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_MapDeclarationExtension_contains___rarg(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_saveModuleData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_save_module_data(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_readModuleData___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_read_module_data(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_freeRegions___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; lean_object* x_9; 
lean_dec(x_4);
x_7 = lean_array_uget(x_1, x_2);
x_8 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_9 = lean_compacted_region_free(x_8, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
x_5 = x_11;
goto _start;
}
else
{
uint8_t x_15; 
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
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_5);
return x_19;
}
}
}
LEAN_EXPORT lean_object* lean_environment_free_regions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_5, x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
return x_12;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_15 = lean_box(0);
x_16 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_freeRegions___spec__1(x_4, x_13, x_14, x_15, x_2);
lean_dec(x_4);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_freeRegions___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_freeRegions___spec__1(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
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
LEAN_EXPORT lean_object* l_Nat_foldAux___at_Lean_mkModuleData___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
lean_dec(x_4);
x_10 = lean_nat_add(x_9, x_8);
x_11 = lean_nat_sub(x_3, x_10);
lean_dec(x_10);
x_12 = l_Nat_foldAux___at_Lean_mkModuleData___spec__1___closed__1;
x_13 = lean_array_get(x_12, x_2, x_11);
lean_dec(x_11);
x_14 = l_Lean_instInhabitedEnvExtensionState;
x_15 = l_Lean_PersistentEnvExtension_getState___rarg(x_14, x_13, x_1);
x_16 = lean_ctor_get(x_13, 4);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_apply_1(x_16, x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_array_push(x_5, x_19);
x_4 = x_9;
x_5 = x_20;
goto _start;
}
else
{
lean_dec(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_mkModuleData___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_array_push(x_4, x_9);
x_2 = x_8;
x_4 = x_10;
goto _start;
}
case 1:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec(x_6);
x_13 = l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3(x_12, x_4);
x_2 = x_8;
x_4 = x_13;
goto _start;
}
default: 
{
x_2 = x_8;
goto _start;
}
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__5___rarg___boxed), 6, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_mkModuleData___spec__4(x_3, x_8, x_9, x_2);
lean_dec(x_3);
return x_10;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___closed__1;
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__5___rarg(x_13, x_11, x_12, lean_box(0), x_14, x_2);
lean_dec(x_12);
lean_dec(x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_mkModuleData___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkModuleData(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2___closed__2;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_instInhabitedModuleData___closed__1;
lean_inc(x_7);
x_9 = l_Nat_foldAux___at_Lean_mkModuleData___spec__1(x_1, x_6, x_7, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Std_PersistentHashMap_foldlM___at_Lean_mkModuleData___spec__2(x_13, x_8);
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
x_19 = l_Lean_instInhabitedModuleData___closed__1;
lean_inc(x_18);
x_20 = l_Nat_foldAux___at_Lean_mkModuleData___spec__1(x_1, x_16, x_18, x_18, x_19);
lean_dec(x_18);
lean_dec(x_16);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Std_PersistentHashMap_foldlM___at_Lean_mkModuleData___spec__2(x_24, x_19);
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
LEAN_EXPORT lean_object* l_Nat_foldAux___at_Lean_mkModuleData___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_mkModuleData___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_mkModuleData___spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_write_module(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_4 = l_Lean_mkModuleData(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_environment_main_module(x_1);
x_8 = lean_save_module_data(x_2, x_7, x_5, x_6);
lean_dec(x_5);
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Environment_0__Lean_getEntriesFor___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedName;
x_2 = l_Lean_instInhabitedModuleData___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_getEntriesFor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_7 = l_Lean_instInhabitedModuleData___closed__1;
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
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_getEntriesFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Environment_0__Lean_getEntriesFor(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__1___lambda__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_4, x_3);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_array_uget(x_9, x_4);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l___private_Lean_Environment_0__Lean_getEntriesFor(x_1, x_11, x_12);
lean_dec(x_11);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_closure((void*)(l_Subarray_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__1___lambda__1), 2, 1);
lean_closure_set(x_15, 0, x_13);
x_16 = l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg(x_14, x_5, x_15);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_4, x_17);
x_4 = x_18;
x_5 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_5, x_4);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_10 = lean_array_uget(x_3, x_5);
x_11 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_2);
x_12 = l_Array_toSubarray___rarg(x_2, x_1, x_11);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = l_Subarray_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__1(x_10, x_12, x_14, x_16, x_6, x_7);
lean_dec(x_12);
lean_dec(x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_5, x_20);
x_5 = x_21;
x_6 = x_18;
x_7 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_setImportedEntries(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; uint8_t x_13; 
x_5 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2___closed__2;
x_6 = lean_st_ref_get(x_5, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_array_get_size(x_2);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__2(x_3, x_7, x_2, x_10, x_11, x_1, x_8);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Subarray_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__1(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_forInUnsafe_loop___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__2(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_setImportedEntries___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Environment_0__Lean_setImportedEntries(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributes___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_update_env_attributes(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltiAttributes___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_num_attributes(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
lean_dec(x_1);
x_9 = l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop(x_2, x_3, x_8, x_4, x_6);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedEnvExtensionState;
x_2 = l_Lean_instInhabitedPersistentEnvExtensionState___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2___closed__2;
x_7 = lean_st_ref_get(x_6, x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_array_get_size(x_9);
x_12 = lean_nat_dec_lt(x_3, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_free_object(x_7);
x_13 = l_Nat_foldAux___at_Lean_mkModuleData___spec__1___closed__1;
x_14 = lean_array_get(x_13, x_9, x_3);
lean_dec(x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop___closed__1;
x_17 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_16, x_15, x_4);
x_18 = lean_st_ref_get(x_6, x_10);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_array_get_size(x_19);
lean_dec(x_19);
x_22 = lean_get_num_attributes(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_14, 2);
lean_inc(x_25);
lean_dec(x_14);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_dec(x_28);
lean_inc(x_2);
lean_inc(x_4);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_2);
lean_inc(x_27);
x_30 = lean_apply_3(x_25, x_27, x_29, x_24);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_ctor_set(x_17, 1, x_31);
x_33 = l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg(x_15, x_4, x_17);
x_34 = l_Lean_EnvExtensionInterfaceUnsafe_ensureExtensionsArraySize(x_33, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_st_ref_get(x_6, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_get_num_attributes(x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_array_get_size(x_38);
lean_dec(x_38);
x_44 = lean_nat_dec_lt(x_21, x_43);
lean_dec(x_43);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = lean_nat_dec_lt(x_23, x_41);
lean_dec(x_41);
lean_dec(x_23);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_21);
x_46 = lean_box(0);
x_47 = l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop___lambda__1(x_3, x_1, x_2, x_35, x_46, x_42);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = l___private_Lean_Environment_0__Lean_setImportedEntries(x_35, x_1, x_21, x_42);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_update_env_attributes(x_49, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_box(0);
x_55 = l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop___lambda__1(x_3, x_1, x_2, x_52, x_54, x_53);
return x_55;
}
else
{
uint8_t x_56; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_51);
if (x_56 == 0)
{
return x_51;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_51, 0);
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_51);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_41);
lean_dec(x_23);
x_60 = l___private_Lean_Environment_0__Lean_setImportedEntries(x_35, x_1, x_21, x_42);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_update_env_attributes(x_61, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_box(0);
x_67 = l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop___lambda__1(x_3, x_1, x_2, x_64, x_66, x_65);
return x_67;
}
else
{
uint8_t x_68; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_63);
if (x_68 == 0)
{
return x_63;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_63, 0);
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_63);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_40);
if (x_72 == 0)
{
return x_40;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_40, 0);
x_74 = lean_ctor_get(x_40, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_40);
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
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_34);
if (x_76 == 0)
{
return x_34;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_34, 0);
x_78 = lean_ctor_get(x_34, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_34);
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
lean_free_object(x_17);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_30);
if (x_80 == 0)
{
return x_30;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_30, 0);
x_82 = lean_ctor_get(x_30, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_30);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_17, 0);
lean_inc(x_84);
lean_dec(x_17);
lean_inc(x_2);
lean_inc(x_4);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_4);
lean_ctor_set(x_85, 1, x_2);
lean_inc(x_84);
x_86 = lean_apply_3(x_25, x_84, x_85, x_24);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_84);
lean_ctor_set(x_89, 1, x_87);
x_90 = l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg(x_15, x_4, x_89);
x_91 = l_Lean_EnvExtensionInterfaceUnsafe_ensureExtensionsArraySize(x_90, x_88);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_st_ref_get(x_6, x_93);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_get_num_attributes(x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_array_get_size(x_95);
lean_dec(x_95);
x_101 = lean_nat_dec_lt(x_21, x_100);
lean_dec(x_100);
if (x_101 == 0)
{
uint8_t x_102; 
x_102 = lean_nat_dec_lt(x_23, x_98);
lean_dec(x_98);
lean_dec(x_23);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_21);
x_103 = lean_box(0);
x_104 = l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop___lambda__1(x_3, x_1, x_2, x_92, x_103, x_99);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = l___private_Lean_Environment_0__Lean_setImportedEntries(x_92, x_1, x_21, x_99);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_update_env_attributes(x_106, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_box(0);
x_112 = l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop___lambda__1(x_3, x_1, x_2, x_109, x_111, x_110);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_98);
lean_dec(x_23);
x_117 = l___private_Lean_Environment_0__Lean_setImportedEntries(x_92, x_1, x_21, x_99);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_update_env_attributes(x_118, x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_box(0);
x_124 = l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop___lambda__1(x_3, x_1, x_2, x_121, x_123, x_122);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_125 = lean_ctor_get(x_120, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_120, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_127 = x_120;
} else {
 lean_dec_ref(x_120);
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
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_95);
lean_dec(x_92);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_129 = lean_ctor_get(x_97, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_97, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_131 = x_97;
} else {
 lean_dec_ref(x_97);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_133 = lean_ctor_get(x_91, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_91, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_135 = x_91;
} else {
 lean_dec_ref(x_91);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_84);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_137 = lean_ctor_get(x_86, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_86, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_139 = x_86;
} else {
 lean_dec_ref(x_86);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_141 = !lean_is_exclusive(x_22);
if (x_141 == 0)
{
return x_22;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_22, 0);
x_143 = lean_ctor_get(x_22, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_22);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_145 = lean_ctor_get(x_7, 0);
x_146 = lean_ctor_get(x_7, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_7);
x_147 = lean_array_get_size(x_145);
x_148 = lean_nat_dec_lt(x_3, x_147);
lean_dec(x_147);
if (x_148 == 0)
{
lean_object* x_149; 
lean_dec(x_145);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_4);
lean_ctor_set(x_149, 1, x_146);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_150 = l_Nat_foldAux___at_Lean_mkModuleData___spec__1___closed__1;
x_151 = lean_array_get(x_150, x_145, x_3);
lean_dec(x_145);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop___closed__1;
x_154 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_153, x_152, x_4);
x_155 = lean_st_ref_get(x_6, x_146);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = lean_array_get_size(x_156);
lean_dec(x_156);
x_159 = lean_get_num_attributes(x_157);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_ctor_get(x_151, 2);
lean_inc(x_162);
lean_dec(x_151);
x_163 = lean_ctor_get(x_154, 0);
lean_inc(x_163);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_164 = x_154;
} else {
 lean_dec_ref(x_154);
 x_164 = lean_box(0);
}
lean_inc(x_2);
lean_inc(x_4);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_4);
lean_ctor_set(x_165, 1, x_2);
lean_inc(x_163);
x_166 = lean_apply_3(x_162, x_163, x_165, x_161);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
if (lean_is_scalar(x_164)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_164;
}
lean_ctor_set(x_169, 0, x_163);
lean_ctor_set(x_169, 1, x_167);
x_170 = l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg(x_152, x_4, x_169);
x_171 = l_Lean_EnvExtensionInterfaceUnsafe_ensureExtensionsArraySize(x_170, x_168);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_st_ref_get(x_6, x_173);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
x_177 = lean_get_num_attributes(x_176);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_array_get_size(x_175);
lean_dec(x_175);
x_181 = lean_nat_dec_lt(x_158, x_180);
lean_dec(x_180);
if (x_181 == 0)
{
uint8_t x_182; 
x_182 = lean_nat_dec_lt(x_160, x_178);
lean_dec(x_178);
lean_dec(x_160);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; 
lean_dec(x_158);
x_183 = lean_box(0);
x_184 = l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop___lambda__1(x_3, x_1, x_2, x_172, x_183, x_179);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_185 = l___private_Lean_Environment_0__Lean_setImportedEntries(x_172, x_1, x_158, x_179);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = lean_update_env_attributes(x_186, x_187);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_box(0);
x_192 = l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop___lambda__1(x_3, x_1, x_2, x_189, x_191, x_190);
return x_192;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_193 = lean_ctor_get(x_188, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_188, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_195 = x_188;
} else {
 lean_dec_ref(x_188);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 2, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set(x_196, 1, x_194);
return x_196;
}
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_178);
lean_dec(x_160);
x_197 = l___private_Lean_Environment_0__Lean_setImportedEntries(x_172, x_1, x_158, x_179);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_200 = lean_update_env_attributes(x_198, x_199);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_203 = lean_box(0);
x_204 = l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop___lambda__1(x_3, x_1, x_2, x_201, x_203, x_202);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_205 = lean_ctor_get(x_200, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_200, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_207 = x_200;
} else {
 lean_dec_ref(x_200);
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
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_175);
lean_dec(x_172);
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_209 = lean_ctor_get(x_177, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_177, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_211 = x_177;
} else {
 lean_dec_ref(x_177);
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
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_213 = lean_ctor_get(x_171, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_171, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_215 = x_171;
} else {
 lean_dec_ref(x_171);
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
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_152);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_217 = lean_ctor_get(x_166, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_166, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_219 = x_166;
} else {
 lean_dec_ref(x_166);
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
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_158);
lean_dec(x_154);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_221 = lean_ctor_get(x_159, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_159, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_223 = x_159;
} else {
 lean_dec_ref(x_159);
 x_223 = lean_box(0);
}
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(1, 2, 0);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_221);
lean_ctor_set(x_224, 1, x_222);
return x_224;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_finalizePersistentExtensions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop(x_2, x_3, x_5, x_1, x_4);
return x_6;
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
x_1 = l_Lean_instInhabitedModuleData___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_ImportState_moduleData___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedModuleData___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_ImportState_regions___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedModuleData___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_importModules_importMods___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_read_module_data(x_1, x_6);
lean_dec(x_1);
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
lean_inc(x_5);
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
lean_dec(x_5);
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
lean_dec(x_5);
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
LEAN_EXPORT lean_object* l_Lean_importModules_importMods(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_box(0);
lean_inc(x_13);
x_21 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_19, x_13, x_20);
lean_ctor_set(x_16, 0, x_21);
x_22 = lean_st_ref_set(x_2, x_16, x_17);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
lean_inc(x_13);
x_24 = l_Lean_findOLean(x_13, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_System_FilePath_pathExists(x_25, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
uint8_t x_30; 
lean_dec(x_7);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_ctor_get(x_27, 0);
lean_dec(x_31);
x_32 = l_Lean_importModules_importMods___closed__1;
x_33 = lean_string_append(x_32, x_25);
lean_dec(x_25);
x_34 = l_Lean_importModules_importMods___closed__2;
x_35 = lean_string_append(x_33, x_34);
x_36 = 1;
x_37 = l_Lean_Name_toString(x_13, x_36);
x_38 = lean_string_append(x_35, x_37);
lean_dec(x_37);
x_39 = l_Lean_importModules_importMods___closed__3;
x_40 = lean_string_append(x_38, x_39);
x_41 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 0, x_41);
return x_27;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_42 = lean_ctor_get(x_27, 1);
lean_inc(x_42);
lean_dec(x_27);
x_43 = l_Lean_importModules_importMods___closed__1;
x_44 = lean_string_append(x_43, x_25);
lean_dec(x_25);
x_45 = l_Lean_importModules_importMods___closed__2;
x_46 = lean_string_append(x_44, x_45);
x_47 = 1;
x_48 = l_Lean_Name_toString(x_13, x_47);
x_49 = lean_string_append(x_46, x_48);
lean_dec(x_48);
x_50 = l_Lean_importModules_importMods___closed__3;
x_51 = lean_string_append(x_49, x_50);
x_52 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_42);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_27, 1);
lean_inc(x_54);
lean_dec(x_27);
x_55 = l_Lean_importModules_importMods___lambda__1(x_25, x_13, x_7, x_20, x_2, x_54);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_24);
if (x_56 == 0)
{
return x_24;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_24, 0);
x_58 = lean_ctor_get(x_24, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_24);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_60 = lean_ctor_get(x_16, 0);
x_61 = lean_ctor_get(x_16, 1);
x_62 = lean_ctor_get(x_16, 2);
x_63 = lean_ctor_get(x_16, 3);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_16);
x_64 = lean_box(0);
lean_inc(x_13);
x_65 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_60, x_13, x_64);
x_66 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_61);
lean_ctor_set(x_66, 2, x_62);
lean_ctor_set(x_66, 3, x_63);
x_67 = lean_st_ref_set(x_2, x_66, x_17);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
lean_inc(x_13);
x_69 = l_Lean_findOLean(x_13, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_System_FilePath_pathExists(x_70, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_7);
lean_dec(x_2);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_76 = x_72;
} else {
 lean_dec_ref(x_72);
 x_76 = lean_box(0);
}
x_77 = l_Lean_importModules_importMods___closed__1;
x_78 = lean_string_append(x_77, x_70);
lean_dec(x_70);
x_79 = l_Lean_importModules_importMods___closed__2;
x_80 = lean_string_append(x_78, x_79);
x_81 = 1;
x_82 = l_Lean_Name_toString(x_13, x_81);
x_83 = lean_string_append(x_80, x_82);
lean_dec(x_82);
x_84 = l_Lean_importModules_importMods___closed__3;
x_85 = lean_string_append(x_83, x_84);
x_86 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_86, 0, x_85);
if (lean_is_scalar(x_76)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_76;
 lean_ctor_set_tag(x_87, 1);
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_75);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_72, 1);
lean_inc(x_88);
lean_dec(x_72);
x_89 = l_Lean_importModules_importMods___lambda__1(x_70, x_13, x_7, x_64, x_2, x_88);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_2);
x_90 = lean_ctor_get(x_69, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_69, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_92 = x_69;
} else {
 lean_dec_ref(x_69);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
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
lean_object* x_95; 
lean_dec(x_6);
x_95 = lean_ctor_get(x_8, 1);
lean_inc(x_95);
lean_dec(x_8);
x_1 = x_7;
x_3 = x_95;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_importModules_importMods___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_importModules_importMods___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_8 = lean_array_uget(x_1, x_3);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_array_get_size(x_9);
lean_dec(x_9);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_10);
lean_dec(x_4);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
x_4 = x_11;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at_Lean_importModules___spec__3(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_importModules___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash(x_4);
x_8 = lean_uint64_to_usize(x_7);
x_9 = lean_usize_modn(x_8, x_6);
lean_dec(x_6);
x_10 = lean_array_uget(x_1, x_9);
lean_ctor_set(x_2, 2, x_10);
x_11 = lean_array_uset(x_1, x_9, x_2);
x_1 = x_11;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_16 = lean_array_get_size(x_1);
x_17 = l_Lean_Name_hash(x_13);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_modn(x_18, x_16);
lean_dec(x_16);
x_20 = lean_array_uget(x_1, x_19);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_array_uset(x_1, x_19, x_21);
x_1 = x_22;
x_2 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at_Lean_importModules___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at_Lean_importModules___spec__4(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_importModules___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_importModules___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash(x_2);
x_9 = lean_uint64_to_usize(x_8);
x_10 = lean_usize_modn(x_9, x_7);
x_11 = lean_array_uget(x_6, x_10);
x_12 = l_Std_AssocList_contains___at_Lean_importModules___spec__3(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_11);
x_16 = lean_array_uset(x_6, x_10, x_15);
x_17 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_14);
x_18 = lean_nat_dec_le(x_17, x_7);
lean_dec(x_7);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = l_Std_HashMapImp_expand___at_Lean_importModules___spec__4(x_14, x_16);
return x_19;
}
else
{
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_20 = l_Std_AssocList_replace___at_Lean_importModules___spec__7(x_2, x_3, x_11);
x_21 = lean_array_uset(x_6, x_10, x_20);
lean_ctor_set(x_1, 1, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_24 = lean_array_get_size(x_23);
x_25 = l_Lean_Name_hash(x_2);
x_26 = lean_uint64_to_usize(x_25);
x_27 = lean_usize_modn(x_26, x_24);
x_28 = lean_array_uget(x_23, x_27);
x_29 = l_Std_AssocList_contains___at_Lean_importModules___spec__3(x_2, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_22, x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_3);
lean_ctor_set(x_32, 2, x_28);
x_33 = lean_array_uset(x_23, x_27, x_32);
x_34 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_31);
x_35 = lean_nat_dec_le(x_34, x_24);
lean_dec(x_24);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Std_HashMapImp_expand___at_Lean_importModules___spec__4(x_31, x_33);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_24);
x_38 = l_Std_AssocList_replace___at_Lean_importModules___spec__7(x_2, x_3, x_28);
x_39 = lean_array_uset(x_23, x_27, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insert_x27___at_Lean_importModules___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash(x_2);
x_9 = lean_uint64_to_usize(x_8);
x_10 = lean_usize_modn(x_9, x_7);
x_11 = lean_array_uget(x_6, x_10);
x_12 = l_Std_AssocList_contains___at_Lean_Environment_addAux___spec__7(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_11);
x_16 = lean_array_uset(x_6, x_10, x_15);
x_17 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_14);
x_18 = lean_nat_dec_le(x_17, x_7);
lean_dec(x_7);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
lean_free_object(x_1);
x_19 = l_Std_HashMapImp_expand___at_Lean_Environment_addAux___spec__8(x_14, x_16);
x_20 = 0;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
else
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; 
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_14);
x_23 = 0;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_7);
x_26 = l_Std_AssocList_replace___at_Lean_Environment_addAux___spec__11(x_2, x_3, x_11);
x_27 = lean_array_uset(x_6, x_10, x_26);
lean_ctor_set(x_1, 1, x_27);
x_28 = 1;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint64_t x_34; size_t x_35; size_t x_36; lean_object* x_37; uint8_t x_38; 
x_31 = lean_ctor_get(x_1, 0);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_1);
x_33 = lean_array_get_size(x_32);
x_34 = l_Lean_Name_hash(x_2);
x_35 = lean_uint64_to_usize(x_34);
x_36 = lean_usize_modn(x_35, x_33);
x_37 = lean_array_uget(x_32, x_36);
x_38 = l_Std_AssocList_contains___at_Lean_Environment_addAux___spec__7(x_2, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_31, x_39);
lean_dec(x_31);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set(x_41, 1, x_3);
lean_ctor_set(x_41, 2, x_37);
x_42 = lean_array_uset(x_32, x_36, x_41);
x_43 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_40);
x_44 = lean_nat_dec_le(x_43, x_33);
lean_dec(x_33);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_45 = l_Std_HashMapImp_expand___at_Lean_Environment_addAux___spec__8(x_40, x_42);
x_46 = 0;
x_47 = lean_box(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
else
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_40);
lean_ctor_set(x_49, 1, x_42);
x_50 = 0;
x_51 = lean_box(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_33);
x_53 = l_Std_AssocList_replace___at_Lean_Environment_addAux___spec__11(x_2, x_3, x_37);
x_54 = lean_array_uset(x_32, x_36, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_31);
lean_ctor_set(x_55, 1, x_54);
x_56 = 1;
x_57 = lean_box(x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("import failed, environment already contains '");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_4, x_3);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_array_uget(x_2, x_4);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = l_Lean_ConstantInfo_name(x_9);
lean_inc(x_1);
lean_inc(x_12);
x_13 = l_Std_HashMap_insert___at_Lean_importModules___spec__2(x_11, x_12, x_1);
lean_inc(x_12);
x_14 = l_Std_HashMap_insert_x27___at_Lean_importModules___spec__8(x_10, x_12, x_9);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
lean_dec(x_12);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
x_19 = 1;
x_20 = lean_usize_add(x_4, x_19);
x_4 = x_20;
x_5 = x_18;
goto _start;
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
x_22 = 1;
x_23 = l_Lean_Name_toString(x_12, x_22);
x_24 = l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9___closed__2;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_6);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__10(size_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_4, x_3);
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
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_uget(x_2, x_4);
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_5, 1);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
lean_ctor_set(x_11, 0, x_13);
x_16 = lean_array_get_size(x_15);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
lean_inc(x_14);
x_18 = l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9(x_14, x_15, x_17, x_1, x_11, x_6);
lean_dec(x_15);
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
x_24 = lean_nat_add(x_14, x_23);
lean_dec(x_14);
lean_ctor_set(x_19, 0, x_24);
lean_ctor_set(x_5, 1, x_19);
lean_ctor_set(x_5, 0, x_22);
x_25 = 1;
x_26 = lean_usize_add(x_4, x_25);
x_4 = x_26;
x_6 = x_20;
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
x_31 = lean_nat_add(x_14, x_30);
lean_dec(x_14);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_5, 1, x_32);
lean_ctor_set(x_5, 0, x_28);
x_33 = 1;
x_34 = lean_usize_add(x_4, x_33);
x_4 = x_34;
x_6 = x_20;
goto _start;
}
}
else
{
uint8_t x_36; 
lean_dec(x_14);
lean_free_object(x_5);
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
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_5, 0);
x_41 = lean_ctor_get(x_11, 0);
x_42 = lean_ctor_get(x_11, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_11);
x_43 = lean_ctor_get(x_9, 1);
lean_inc(x_43);
lean_dec(x_9);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_array_get_size(x_43);
x_46 = lean_usize_of_nat(x_45);
lean_dec(x_45);
lean_inc(x_41);
x_47 = l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9(x_41, x_43, x_46, x_1, x_44, x_6);
lean_dec(x_43);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_52 = x_48;
} else {
 lean_dec_ref(x_48);
 x_52 = lean_box(0);
}
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_41, x_53);
lean_dec(x_41);
if (lean_is_scalar(x_52)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_52;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
lean_ctor_set(x_5, 1, x_55);
lean_ctor_set(x_5, 0, x_50);
x_56 = 1;
x_57 = lean_usize_add(x_4, x_56);
x_4 = x_57;
x_6 = x_49;
goto _start;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_41);
lean_free_object(x_5);
x_59 = lean_ctor_get(x_47, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_47, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_61 = x_47;
} else {
 lean_dec_ref(x_47);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; size_t x_71; lean_object* x_72; 
x_63 = lean_ctor_get(x_5, 1);
x_64 = lean_ctor_get(x_5, 0);
lean_inc(x_63);
lean_inc(x_64);
lean_dec(x_5);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_67 = x_63;
} else {
 lean_dec_ref(x_63);
 x_67 = lean_box(0);
}
x_68 = lean_ctor_get(x_9, 1);
lean_inc(x_68);
lean_dec(x_9);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_64);
lean_ctor_set(x_69, 1, x_66);
x_70 = lean_array_get_size(x_68);
x_71 = lean_usize_of_nat(x_70);
lean_dec(x_70);
lean_inc(x_65);
x_72 = l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9(x_65, x_68, x_71, x_1, x_69, x_6);
lean_dec(x_68);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; size_t x_82; size_t x_83; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_77 = x_73;
} else {
 lean_dec_ref(x_73);
 x_77 = lean_box(0);
}
x_78 = lean_unsigned_to_nat(1u);
x_79 = lean_nat_add(x_65, x_78);
lean_dec(x_65);
if (lean_is_scalar(x_77)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_77;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_76);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_75);
lean_ctor_set(x_81, 1, x_80);
x_82 = 1;
x_83 = lean_usize_add(x_4, x_82);
x_4 = x_83;
x_5 = x_81;
x_6 = x_74;
goto _start;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_65);
x_85 = lean_ctor_get(x_72, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_72, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_87 = x_72;
} else {
 lean_dec_ref(x_72);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_importModules___lambda__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_importModules___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
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
lean_dec(x_2);
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
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_importModules___lambda__3(lean_object* x_1, uint32_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
x_8 = lean_array_get_size(x_7);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_forInUnsafe_loop___at_Lean_importModules___spec__1(x_7, x_9, x_10, x_11, x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Std_mkHashMapImp___rarg(x_13);
lean_dec(x_13);
lean_inc(x_15);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Array_forInUnsafe_loop___at_Lean_importModules___spec__10(x_10, x_7, x_9, x_10, x_17, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = 0;
x_25 = l_Lean_instInhabitedEnvironment___closed__3;
x_26 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_24);
x_27 = l_Lean_EnvExtensionInterfaceUnsafe_mkInitialExtStates(x_21);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_List_isEmpty___rarg(x_1);
x_31 = l_List_redLength___rarg(x_1);
x_32 = lean_mk_empty_array_with_capacity(x_31);
lean_dec(x_31);
x_33 = l_List_toArrayAux___rarg(x_1, x_32);
if (x_30 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_34 = lean_ctor_get(x_6, 3);
lean_inc(x_34);
x_35 = lean_ctor_get(x_6, 1);
lean_inc(x_35);
lean_dec(x_6);
x_36 = 1;
x_37 = lean_box(0);
lean_inc(x_7);
x_38 = lean_alloc_ctor(0, 5, 5);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
lean_ctor_set(x_38, 2, x_34);
lean_ctor_set(x_38, 3, x_35);
lean_ctor_set(x_38, 4, x_7);
lean_ctor_set_uint32(x_38, sizeof(void*)*5, x_2);
lean_ctor_set_uint8(x_38, sizeof(void*)*5 + 4, x_36);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_23);
lean_ctor_set(x_39, 1, x_26);
lean_ctor_set(x_39, 2, x_28);
lean_ctor_set(x_39, 3, x_38);
x_40 = l___private_Lean_Environment_0__Lean_setImportedEntries(x_39, x_7, x_11, x_29);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop(x_7, x_3, x_11, x_41, x_42);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_43);
if (x_48 == 0)
{
return x_43;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_43, 0);
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_43);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_6, 3);
lean_inc(x_52);
x_53 = lean_ctor_get(x_6, 1);
lean_inc(x_53);
lean_dec(x_6);
x_54 = lean_box(0);
lean_inc(x_7);
x_55 = lean_alloc_ctor(0, 5, 5);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_33);
lean_ctor_set(x_55, 2, x_52);
lean_ctor_set(x_55, 3, x_53);
lean_ctor_set(x_55, 4, x_7);
lean_ctor_set_uint32(x_55, sizeof(void*)*5, x_2);
lean_ctor_set_uint8(x_55, sizeof(void*)*5 + 4, x_24);
x_56 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_56, 0, x_23);
lean_ctor_set(x_56, 1, x_26);
lean_ctor_set(x_56, 2, x_28);
lean_ctor_set(x_56, 3, x_55);
x_57 = l___private_Lean_Environment_0__Lean_setImportedEntries(x_56, x_7, x_11, x_29);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop(x_7, x_3, x_11, x_58, x_59);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
return x_60;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_60);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
else
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_60);
if (x_65 == 0)
{
return x_60;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_60, 0);
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_60);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_27);
if (x_69 == 0)
{
return x_27;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_27, 0);
x_71 = lean_ctor_get(x_27, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_27);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_18);
if (x_73 == 0)
{
return x_18;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_18, 0);
x_75 = lean_ctor_get(x_18, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_18);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
static lean_object* _init_l_Lean_importModules___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_NameSet_empty;
x_2 = l_Lean_instInhabitedModuleData___closed__1;
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
lean_object* x_1; 
x_1 = lean_mk_string("import");
return x_1;
}
}
LEAN_EXPORT lean_object* lean_import_modules(lean_object* x_1, lean_object* x_2, uint32_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = l_Lean_importModules___closed__1;
x_6 = lean_alloc_closure((void*)(l_Lean_importModules___lambda__1), 2, 1);
lean_closure_set(x_6, 0, x_5);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_importModules___lambda__2), 3, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_box_uint32(x_3);
lean_inc(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_importModules___lambda__3___boxed), 5, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_2);
x_11 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_withImporting___rarg), 2, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = l_Lean_importModules___closed__2;
x_14 = l_Lean_profileitIOUnsafe___rarg(x_13, x_2, x_12, x_4);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forInUnsafe_loop___at_Lean_importModules___spec__1(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at_Lean_importModules___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_importModules___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_forInUnsafe_loop___at_Lean_importModules___spec__10(x_7, x_2, x_8, x_9, x_5, x_6);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_importModules___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint32_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_7 = l_Lean_importModules___lambda__3(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_importModules___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_6 = lean_import_modules(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_withImportModules___rarg(lean_object* x_1, lean_object* x_2, uint32_t x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_withImportModules(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_withImportModules___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_withImportModules___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint32_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_7 = l_Lean_withImportModules___rarg(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_initFn____x40_Lean_Environment___hyg_4639____spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_box(0);
x_8 = l_Lean_SMap_insert___at_Lean_NameSSet_insert___spec__1(x_4, x_6, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_initFn____x40_Lean_Environment___hyg_4639____spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
x_2 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_7, x_7);
if (x_13 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
x_2 = x_11;
goto _start;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_17 = l_Array_foldlMUnsafe_fold___at_Lean_initFn____x40_Lean_Environment___hyg_4639____spec__2(x_6, x_15, x_16, x_4);
lean_dec(x_6);
x_2 = x_11;
x_4 = x_17;
goto _start;
}
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_Environment___hyg_4639____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_3, x_3);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_initFn____x40_Lean_Environment___hyg_4639____spec__3(x_2, x_7, x_8, x_1);
lean_dec(x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at_Lean_initFn____x40_Lean_Environment___hyg_4639____spec__4(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_4639____lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Lean_SMap_insert___at_Lean_NameSSet_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_4639____lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_SMap_empty___at_Lean_NameSSet_empty___spec__1;
x_3 = l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_Environment___hyg_4639____spec__1(x_2, x_1);
x_4 = l_Lean_SMap_switch___at_Lean_initFn____x40_Lean_Environment___hyg_4639____spec__4(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("namespaces");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lean_list_to_array), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_initFn____x40_Lean_Environment___hyg_4639____lambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_initFn____x40_Lean_Environment___hyg_4639____lambda__2), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__2;
x_2 = l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__4;
x_3 = l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__5;
x_4 = l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_4639_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__6;
x_3 = l_Lean_registerSimplePersistentEnvExtension___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_initFn____x40_Lean_Environment___hyg_4639____spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_initFn____x40_Lean_Environment___hyg_4639____spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_initFn____x40_Lean_Environment___hyg_4639____spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_initFn____x40_Lean_Environment___hyg_4639____spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Environment_registerNamespace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_namespacesExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_registerNamespace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = l_Lean_NameSSet_instInhabitedNameSSet;
x_4 = l_Lean_Environment_registerNamespace___closed__1;
x_5 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_3, x_4, x_1);
lean_inc(x_2);
x_6 = l_Lean_SMap_contains___at_Lean_NameSSet_contains___spec__1(x_5, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_4, x_1, x_2);
return x_7;
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Environment_isNamespace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = l_Lean_NameSSet_instInhabitedNameSSet;
x_4 = l_Lean_Environment_registerNamespace___closed__1;
x_5 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_3, x_4, x_1);
x_6 = l_Lean_SMap_contains___at_Lean_NameSSet_contains___spec__1(x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_isNamespace___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Environment_isNamespace(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getNamespaceSet(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_NameSSet_instInhabitedNameSSet;
x_3 = l_Lean_Environment_registerNamespace___closed__1;
x_4 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getNamespaceSet___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Environment_getNamespaceSet(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Environment_0__Lean_Environment_isNamespaceName(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_isNamespaceName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Environment_0__Lean_Environment_isNamespaceName(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_registerNamePrefixes(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* lean_environment_add(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_ConstantInfo_name(x_2);
x_4 = l___private_Lean_Environment_0__Lean_Environment_registerNamePrefixes(x_1, x_3);
x_5 = l_Lean_Environment_addAux(x_4, x_2);
return x_5;
}
}
static lean_object* _init_l_List_toStringAux___at_Lean_Environment_displayStats___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", ");
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_toStringAux___at_Lean_Environment_displayStats___spec__2(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_Lean_instToStringImport___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = 1;
x_8 = l_Lean_Name_toString(x_6, x_7);
x_9 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_dec(x_4);
x_10 = 0;
x_11 = l_List_toStringAux___at_Lean_Environment_displayStats___spec__2(x_10, x_5);
if (x_9 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_instToStringImport___closed__1;
x_13 = lean_string_append(x_8, x_12);
x_14 = l_List_toStringAux___at_Lean_Environment_displayStats___spec__2___closed__1;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = lean_string_append(x_15, x_11);
lean_dec(x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = l_Lean_instToStringImport___closed__2;
x_18 = lean_string_append(x_8, x_17);
x_19 = l_List_toStringAux___at_Lean_Environment_displayStats___spec__2___closed__1;
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
x_22 = l_Lean_instToStringImport___closed__1;
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
lean_dec(x_2);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = 1;
x_27 = l_Lean_Name_toString(x_25, x_26);
x_28 = lean_ctor_get_uint8(x_23, sizeof(void*)*1);
lean_dec(x_23);
x_29 = 0;
x_30 = l_List_toStringAux___at_Lean_Environment_displayStats___spec__2(x_29, x_24);
if (x_28 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Lean_instToStringImport___closed__1;
x_32 = lean_string_append(x_27, x_31);
x_33 = lean_string_append(x_32, x_30);
lean_dec(x_30);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = l_Lean_instToStringImport___closed__2;
x_35 = lean_string_append(x_27, x_34);
x_36 = lean_string_append(x_35, x_30);
lean_dec(x_30);
return x_36;
}
}
}
}
}
static lean_object* _init_l_List_toString___at_Lean_Environment_displayStats___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[]");
return x_1;
}
}
static lean_object* _init_l_List_toString___at_Lean_Environment_displayStats___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[");
return x_1;
}
}
static lean_object* _init_l_List_toString___at_Lean_Environment_displayStats___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("]");
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_toString___at_Lean_Environment_displayStats___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_toString___at_Lean_Environment_displayStats___spec__1___closed__1;
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
x_6 = l_List_toString___at_Lean_Environment_displayStats___spec__1___closed__2;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_List_toString___at_Lean_Environment_displayStats___spec__1___closed__3;
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
x_15 = l_List_toString___at_Lean_Environment_displayStats___spec__1___closed__2;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_List_toString___at_Lean_Environment_displayStats___spec__1___closed__3;
x_18 = lean_string_append(x_16, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Std_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_array_get_size(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Std_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__6(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_nat_add(x_4, x_7);
lean_dec(x_7);
lean_dec(x_4);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Nat_repr(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  number of imported entries: ");
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___lambda__1___closed__2;
x_2 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___lambda__1___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___lambda__1___closed__3;
x_9 = l_IO_println___at_Lean_instEval___spec__1(x_8, x_3);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_5, x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___lambda__1___closed__3;
x_12 = l_IO_println___at_Lean_instEval___spec__1(x_11, x_3);
return x_12;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__7(x_4, x_13, x_14, x_6);
x_16 = l_Nat_repr(x_15);
x_17 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___lambda__1___closed__2;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_IO_println___at_Lean_instEval___spec__1(x_18, x_3);
return x_19;
}
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("extension '");
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  ");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_8 = lean_array_uget(x_2, x_3);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = 1;
x_11 = l_Lean_Name_toString(x_9, x_10);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_IO_println___at_Lean_instEval___spec__1(x_15, x_6);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
x_19 = l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop___closed__1;
x_20 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_19, x_18, x_1);
lean_dec(x_18);
x_21 = lean_ctor_get(x_8, 5);
lean_inc(x_21);
lean_dec(x_8);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
x_23 = lean_apply_1(x_21, x_22);
x_24 = l_Std_Format_isNil(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___closed__2;
x_26 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
x_27 = l_Std_Format_defWidth;
x_28 = lean_format_pretty(x_26, x_27);
x_29 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___closed__3;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = l_IO_println___at_Lean_instEval___spec__1(x_30, x_17);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___lambda__1(x_20, x_32, x_33);
lean_dec(x_32);
lean_dec(x_20);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = 1;
x_38 = lean_usize_add(x_3, x_37);
x_3 = x_38;
x_5 = x_35;
x_6 = x_36;
goto _start;
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_34);
if (x_40 == 0)
{
return x_34;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_34, 0);
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_34);
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
lean_dec(x_20);
x_44 = !lean_is_exclusive(x_31);
if (x_44 == 0)
{
return x_31;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_31, 0);
x_46 = lean_ctor_get(x_31, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_31);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_23);
x_48 = lean_box(0);
x_49 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___lambda__1(x_20, x_48, x_17);
lean_dec(x_20);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = 1;
x_53 = lean_usize_add(x_3, x_52);
x_3 = x_53;
x_5 = x_50;
x_6 = x_51;
goto _start;
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_49);
if (x_55 == 0)
{
return x_49;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_49, 0);
x_57 = lean_ctor_get(x_49, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_49);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_8);
x_59 = !lean_is_exclusive(x_16);
if (x_59 == 0)
{
return x_16;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_16, 0);
x_61 = lean_ctor_get(x_16, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_16);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_5);
lean_ctor_set(x_63, 1, x_6);
return x_63;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__9(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; uint8_t x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_8 = lean_compacted_region_is_memory_mapped(x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
if (x_8 == 0)
{
x_2 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box_usize(x_7);
x_13 = lean_array_push(x_4, x_12);
x_2 = x_10;
x_4 = x_13;
goto _start;
}
}
else
{
return x_4;
}
}
}
static lean_object* _init_l_Lean_Environment_displayStats___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("#");
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_displayStats___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("direct imports:                        ");
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_displayStats___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("number of imported modules:            ");
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_displayStats___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("number of memory-mapped modules:       ");
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_displayStats___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("number of consts:                      ");
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_displayStats___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("number of imported consts:             ");
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_displayStats___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("number of local consts:                ");
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_displayStats___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("number of buckets for imported consts: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_displayStats___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("trust level:                           ");
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_displayStats___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("number of extensions:                  ");
return x_1;
}
}
LEAN_EXPORT lean_object* lean_display_stats(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_3 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2___closed__2;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_array_to_list(lean_box(0), x_8);
x_10 = l_List_toString___at_Lean_Environment_displayStats___spec__1(x_9);
x_11 = l_Lean_Environment_displayStats___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_Environment_displayStats___closed__2;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_IO_println___at_Lean_instEval___spec__1(x_14, x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_7, 2);
lean_inc(x_17);
x_18 = lean_array_get_size(x_17);
lean_inc(x_18);
x_19 = l_Nat_repr(x_18);
x_20 = l_Lean_Environment_displayStats___closed__3;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = l_IO_println___at_Lean_instEval___spec__1(x_21, x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_125; uint8_t x_126; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_125 = lean_unsigned_to_nat(0u);
x_126 = lean_nat_dec_lt(x_125, x_18);
if (x_126 == 0)
{
lean_object* x_127; 
lean_dec(x_18);
lean_dec(x_17);
x_127 = l_Lean_instInhabitedModuleData___closed__1;
x_24 = x_127;
goto block_124;
}
else
{
uint8_t x_128; 
x_128 = lean_nat_dec_le(x_18, x_18);
if (x_128 == 0)
{
lean_object* x_129; 
lean_dec(x_18);
lean_dec(x_17);
x_129 = l_Lean_instInhabitedModuleData___closed__1;
x_24 = x_129;
goto block_124;
}
else
{
size_t x_130; size_t x_131; lean_object* x_132; lean_object* x_133; 
x_130 = 0;
x_131 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_132 = l_Lean_instInhabitedModuleData___closed__1;
x_133 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__9(x_17, x_130, x_131, x_132);
lean_dec(x_17);
x_24 = x_133;
goto block_124;
}
}
block_124:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_array_get_size(x_24);
lean_dec(x_24);
x_26 = l_Nat_repr(x_25);
x_27 = l_Lean_Environment_displayStats___closed__4;
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_29 = l_IO_println___at_Lean_instEval___spec__1(x_28, x_23);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
x_32 = l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3(x_31);
x_33 = l_Nat_repr(x_32);
x_34 = l_Lean_Environment_displayStats___closed__5;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = l_IO_println___at_Lean_instEval___spec__1(x_35, x_30);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4(x_31);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = l_Nat_repr(x_39);
x_41 = l_Lean_Environment_displayStats___closed__6;
x_42 = lean_string_append(x_41, x_40);
lean_dec(x_40);
x_43 = l_IO_println___at_Lean_instEval___spec__1(x_42, x_37);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_dec(x_38);
x_46 = l_Nat_repr(x_45);
x_47 = l_Lean_Environment_displayStats___closed__7;
x_48 = lean_string_append(x_47, x_46);
lean_dec(x_46);
x_49 = l_IO_println___at_Lean_instEval___spec__1(x_48, x_44);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(x_31);
lean_dec(x_31);
x_52 = l_Nat_repr(x_51);
x_53 = l_Lean_Environment_displayStats___closed__8;
x_54 = lean_string_append(x_53, x_52);
lean_dec(x_52);
x_55 = l_IO_println___at_Lean_instEval___spec__1(x_54, x_50);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; uint32_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_ctor_get_uint32(x_7, sizeof(void*)*5);
lean_dec(x_7);
x_58 = lean_uint32_to_nat(x_57);
x_59 = l_Nat_repr(x_58);
x_60 = l_Lean_Environment_displayStats___closed__9;
x_61 = lean_string_append(x_60, x_59);
lean_dec(x_59);
x_62 = l_IO_println___at_Lean_instEval___spec__1(x_61, x_56);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_ctor_get(x_1, 2);
lean_inc(x_64);
x_65 = lean_array_get_size(x_64);
lean_dec(x_64);
x_66 = l_Nat_repr(x_65);
x_67 = l_Lean_Environment_displayStats___closed__10;
x_68 = lean_string_append(x_67, x_66);
lean_dec(x_66);
x_69 = l_IO_println___at_Lean_instEval___spec__1(x_68, x_63);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_69, 1);
x_72 = lean_ctor_get(x_69, 0);
lean_dec(x_72);
x_73 = lean_array_get_size(x_5);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_nat_dec_lt(x_74, x_73);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_73);
lean_dec(x_5);
lean_dec(x_1);
x_76 = lean_box(0);
lean_ctor_set(x_69, 0, x_76);
return x_69;
}
else
{
uint8_t x_77; 
x_77 = lean_nat_dec_le(x_73, x_73);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_73);
lean_dec(x_5);
lean_dec(x_1);
x_78 = lean_box(0);
lean_ctor_set(x_69, 0, x_78);
return x_69;
}
else
{
size_t x_79; size_t x_80; lean_object* x_81; lean_object* x_82; 
lean_free_object(x_69);
x_79 = 0;
x_80 = lean_usize_of_nat(x_73);
lean_dec(x_73);
x_81 = lean_box(0);
x_82 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8(x_1, x_5, x_79, x_80, x_81, x_71);
lean_dec(x_5);
lean_dec(x_1);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_83 = lean_ctor_get(x_69, 1);
lean_inc(x_83);
lean_dec(x_69);
x_84 = lean_array_get_size(x_5);
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_nat_dec_lt(x_85, x_84);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_84);
lean_dec(x_5);
lean_dec(x_1);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_83);
return x_88;
}
else
{
uint8_t x_89; 
x_89 = lean_nat_dec_le(x_84, x_84);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_84);
lean_dec(x_5);
lean_dec(x_1);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_83);
return x_91;
}
else
{
size_t x_92; size_t x_93; lean_object* x_94; lean_object* x_95; 
x_92 = 0;
x_93 = lean_usize_of_nat(x_84);
lean_dec(x_84);
x_94 = lean_box(0);
x_95 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8(x_1, x_5, x_92, x_93, x_94, x_83);
lean_dec(x_5);
lean_dec(x_1);
return x_95;
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_5);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_69);
if (x_96 == 0)
{
return x_69;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_69, 0);
x_98 = lean_ctor_get(x_69, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_69);
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
lean_dec(x_5);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_62);
if (x_100 == 0)
{
return x_62;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_62, 0);
x_102 = lean_ctor_get(x_62, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_62);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_55);
if (x_104 == 0)
{
return x_55;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_55, 0);
x_106 = lean_ctor_get(x_55, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_55);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_31);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_49);
if (x_108 == 0)
{
return x_49;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_49, 0);
x_110 = lean_ctor_get(x_49, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_49);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_38);
lean_dec(x_31);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_43);
if (x_112 == 0)
{
return x_43;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_43, 0);
x_114 = lean_ctor_get(x_43, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_43);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_31);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_36);
if (x_116 == 0)
{
return x_36;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_36, 0);
x_118 = lean_ctor_get(x_36, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_36);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_29);
if (x_120 == 0)
{
return x_29;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_29, 0);
x_122 = lean_ctor_get(x_29, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_29);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
else
{
uint8_t x_134; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_134 = !lean_is_exclusive(x_22);
if (x_134 == 0)
{
return x_22;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_22, 0);
x_136 = lean_ctor_get(x_22, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_22);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
else
{
uint8_t x_138; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_138 = !lean_is_exclusive(x_15);
if (x_138 == 0)
{
return x_15;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_15, 0);
x_140 = lean_ctor_get(x_15, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_15);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toStringAux___at_Lean_Environment_displayStats___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_toStringAux___at_Lean_Environment_displayStats___spec__2(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SMap_size___at_Lean_Environment_displayStats___spec__3(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SMap_stageSizes___at_Lean_Environment_displayStats___spec__4(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__6___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_HashMap_numBuckets___at_Lean_Environment_displayStats___spec__6(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SMap_numBuckets___at_Lean_Environment_displayStats___spec__5(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__7(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__9(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_evalConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_3 = 1;
x_4 = l_Lean_Name_toString(x_2, x_3);
x_5 = l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg___closed__2;
x_8 = lean_string_append(x_6, x_7);
x_9 = l_Lean_Name_toString(x_1, x_3);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
x_11 = l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg___closed__3;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Environment_evalConstCheck___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown constant '");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_evalConstCheck___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_4);
lean_inc(x_1);
x_5 = lean_environment_find(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = 1;
x_7 = l_Lean_Name_toString(x_4, x_6);
x_8 = l_Lean_Environment_evalConstCheck___rarg___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_Environment_evalConstCheck(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Environment_evalConstCheck___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_evalConstCheck___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_evalConstCheck___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Environment_hasUnsafe___lambda__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_Lean_Environment_hasUnsafe(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Environment_hasUnsafe___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 1;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_hasUnsafe___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Environment_hasUnsafe___lambda__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_hasUnsafe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Environment_hasUnsafe(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_isDefEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_kernel_is_def_eq(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_whnf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_kernel_whnf(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadEnv___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_instMonadEnv___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_instMonadEnv(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instMonadEnv___rarg), 2, 0);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_HashMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ImportingFlag(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_SMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Declaration(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_LocalContext(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Path(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FindExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Profile(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ImportingFlag(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_SMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Declaration(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LocalContext(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Path(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FindExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Profile(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_EnvExtensionStateSpec___closed__1 = _init_l_Lean_EnvExtensionStateSpec___closed__1();
lean_mark_persistent(l_Lean_EnvExtensionStateSpec___closed__1);
l_Lean_EnvExtensionStateSpec = _init_l_Lean_EnvExtensionStateSpec();
lean_mark_persistent(l_Lean_EnvExtensionStateSpec);
l_Lean_instInhabitedEnvExtensionState = _init_l_Lean_instInhabitedEnvExtensionState();
lean_mark_persistent(l_Lean_instInhabitedEnvExtensionState);
l_Lean_instInhabitedModuleIdx = _init_l_Lean_instInhabitedModuleIdx();
lean_mark_persistent(l_Lean_instInhabitedModuleIdx);
l_Lean_Import_runtimeOnly___default = _init_l_Lean_Import_runtimeOnly___default();
l_Lean_instToStringImport___closed__1 = _init_l_Lean_instToStringImport___closed__1();
lean_mark_persistent(l_Lean_instToStringImport___closed__1);
l_Lean_instToStringImport___closed__2 = _init_l_Lean_instToStringImport___closed__2();
lean_mark_persistent(l_Lean_instToStringImport___closed__2);
l_Lean_EnvExtensionEntrySpec = _init_l_Lean_EnvExtensionEntrySpec();
l_Lean_instInhabitedModuleData___closed__1 = _init_l_Lean_instInhabitedModuleData___closed__1();
lean_mark_persistent(l_Lean_instInhabitedModuleData___closed__1);
l_Lean_instInhabitedModuleData___closed__2 = _init_l_Lean_instInhabitedModuleData___closed__2();
lean_mark_persistent(l_Lean_instInhabitedModuleData___closed__2);
l_Lean_instInhabitedModuleData = _init_l_Lean_instInhabitedModuleData();
lean_mark_persistent(l_Lean_instInhabitedModuleData);
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
l_Lean_EnvironmentHeader_moduleData___default = _init_l_Lean_EnvironmentHeader_moduleData___default();
lean_mark_persistent(l_Lean_EnvironmentHeader_moduleData___default);
l_Lean_instInhabitedEnvironmentHeader___closed__1 = _init_l_Lean_instInhabitedEnvironmentHeader___closed__1();
l_Lean_instInhabitedEnvironmentHeader___closed__2 = _init_l_Lean_instInhabitedEnvironmentHeader___closed__2();
lean_mark_persistent(l_Lean_instInhabitedEnvironmentHeader___closed__2);
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
l_Lean_instInhabitedEnvironment = _init_l_Lean_instInhabitedEnvironment();
lean_mark_persistent(l_Lean_instInhabitedEnvironment);
l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___closed__1 = _init_l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___closed__1();
l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___closed__2 = _init_l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___closed__2();
l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___closed__3 = _init_l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___closed__3();
lean_mark_persistent(l_Std_PersistentHashMap_insertAux___at_Lean_Environment_addAux___spec__3___closed__3);
l_Lean_instInhabitedEnvExtensionInterface___closed__1 = _init_l_Lean_instInhabitedEnvExtensionInterface___closed__1();
lean_mark_persistent(l_Lean_instInhabitedEnvExtensionInterface___closed__1);
l_Lean_instInhabitedEnvExtensionInterface___closed__2 = _init_l_Lean_instInhabitedEnvExtensionInterface___closed__2();
lean_mark_persistent(l_Lean_instInhabitedEnvExtensionInterface___closed__2);
l_Lean_instInhabitedEnvExtensionInterface___closed__3 = _init_l_Lean_instInhabitedEnvExtensionInterface___closed__3();
lean_mark_persistent(l_Lean_instInhabitedEnvExtensionInterface___closed__3);
l_Lean_instInhabitedEnvExtensionInterface___closed__4 = _init_l_Lean_instInhabitedEnvExtensionInterface___closed__4();
lean_mark_persistent(l_Lean_instInhabitedEnvExtensionInterface___closed__4);
l_Lean_instInhabitedEnvExtensionInterface___closed__5 = _init_l_Lean_instInhabitedEnvExtensionInterface___closed__5();
lean_mark_persistent(l_Lean_instInhabitedEnvExtensionInterface___closed__5);
l_Lean_instInhabitedEnvExtensionInterface___closed__6 = _init_l_Lean_instInhabitedEnvExtensionInterface___closed__6();
lean_mark_persistent(l_Lean_instInhabitedEnvExtensionInterface___closed__6);
l_Lean_instInhabitedEnvExtensionInterface = _init_l_Lean_instInhabitedEnvExtensionInterface();
lean_mark_persistent(l_Lean_instInhabitedEnvExtensionInterface);
l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1___closed__1 = _init_l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1___closed__1();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1___closed__1);
l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__1 = _init_l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__1();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__1);
l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__2 = _init_l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__2();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__2);
if (builtin) {res = l_Lean_EnvExtensionInterfaceUnsafe_initFn____x40_Lean_Environment___hyg_1069_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_envExtensionsRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_envExtensionsRef);
lean_dec_ref(res);
}l_Lean_EnvExtensionInterfaceUnsafe_ensureExtensionsArraySize_loop___closed__1 = _init_l_Lean_EnvExtensionInterfaceUnsafe_ensureExtensionsArraySize_loop___closed__1();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_ensureExtensionsArraySize_loop___closed__1);
l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_invalidExtMsg___closed__1 = _init_l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_invalidExtMsg___closed__1();
lean_mark_persistent(l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_invalidExtMsg___closed__1);
l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_invalidExtMsg = _init_l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_invalidExtMsg();
lean_mark_persistent(l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_invalidExtMsg);
l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg___closed__1 = _init_l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg___closed__1();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg___closed__1);
l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg___closed__2 = _init_l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg___closed__2();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg___closed__2);
l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg___closed__3 = _init_l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg___closed__3();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_setState___rarg___closed__3);
l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg___closed__1 = _init_l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg___closed__1();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg___closed__1);
l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg___closed__2 = _init_l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg___closed__2();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_modifyState___rarg___closed__2);
l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg___closed__1 = _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg___closed__1();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg___closed__1);
l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg___closed__2 = _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg___closed__2();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg___closed__2);
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
l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__8 = _init_l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__8();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_imp___closed__8);
l_Lean_EnvExtensionInterfaceUnsafe_imp = _init_l_Lean_EnvExtensionInterfaceUnsafe_imp();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_imp);
l_Lean_mkEmptyEnvironment___lambda__1___closed__1 = _init_l_Lean_mkEmptyEnvironment___lambda__1___closed__1();
lean_mark_persistent(l_Lean_mkEmptyEnvironment___lambda__1___closed__1);
l_Lean_mkEmptyEnvironment___lambda__1___closed__2 = _init_l_Lean_mkEmptyEnvironment___lambda__1___closed__2();
lean_mark_persistent(l_Lean_mkEmptyEnvironment___lambda__1___closed__2);
l_Lean_mkEmptyEnvironment___closed__1 = _init_l_Lean_mkEmptyEnvironment___closed__1();
lean_mark_persistent(l_Lean_mkEmptyEnvironment___closed__1);
l_Lean_mkEmptyEnvironment___closed__2 = _init_l_Lean_mkEmptyEnvironment___closed__2();
lean_mark_persistent(l_Lean_mkEmptyEnvironment___closed__2);
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
if (builtin) {res = l_Lean_initFn____x40_Lean_Environment___hyg_2057_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_persistentEnvExtensionsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_persistentEnvExtensionsRef);
lean_dec_ref(res);
}l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2___closed__1 = _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2___closed__1);
l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2___closed__2 = _init_l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2___closed__2();
lean_mark_persistent(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2___closed__2);
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
l_Lean_TagDeclarationExtension_instInhabitedTagDeclarationExtension___closed__1 = _init_l_Lean_TagDeclarationExtension_instInhabitedTagDeclarationExtension___closed__1();
lean_mark_persistent(l_Lean_TagDeclarationExtension_instInhabitedTagDeclarationExtension___closed__1);
l_Lean_TagDeclarationExtension_instInhabitedTagDeclarationExtension = _init_l_Lean_TagDeclarationExtension_instInhabitedTagDeclarationExtension();
lean_mark_persistent(l_Lean_TagDeclarationExtension_instInhabitedTagDeclarationExtension);
l_Lean_TagDeclarationExtension_tag___closed__1 = _init_l_Lean_TagDeclarationExtension_tag___closed__1();
lean_mark_persistent(l_Lean_TagDeclarationExtension_tag___closed__1);
l_Lean_TagDeclarationExtension_tag___closed__2 = _init_l_Lean_TagDeclarationExtension_tag___closed__2();
lean_mark_persistent(l_Lean_TagDeclarationExtension_tag___closed__2);
l_Lean_TagDeclarationExtension_tag___closed__3 = _init_l_Lean_TagDeclarationExtension_tag___closed__3();
lean_mark_persistent(l_Lean_TagDeclarationExtension_tag___closed__3);
l_Lean_TagDeclarationExtension_tag___closed__4 = _init_l_Lean_TagDeclarationExtension_tag___closed__4();
lean_mark_persistent(l_Lean_TagDeclarationExtension_tag___closed__4);
l_Lean_TagDeclarationExtension_tag___closed__5 = _init_l_Lean_TagDeclarationExtension_tag___closed__5();
lean_mark_persistent(l_Lean_TagDeclarationExtension_tag___closed__5);
l_Lean_TagDeclarationExtension_isTagged___closed__1 = _init_l_Lean_TagDeclarationExtension_isTagged___closed__1();
lean_mark_persistent(l_Lean_TagDeclarationExtension_isTagged___closed__1);
l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__1___rarg___closed__1 = _init_l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__1___rarg___closed__1();
lean_mark_persistent(l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__1___rarg___closed__1);
l_Lean_mkMapDeclarationExtension___rarg___closed__1 = _init_l_Lean_mkMapDeclarationExtension___rarg___closed__1();
lean_mark_persistent(l_Lean_mkMapDeclarationExtension___rarg___closed__1);
l_Lean_mkMapDeclarationExtension___rarg___closed__2 = _init_l_Lean_mkMapDeclarationExtension___rarg___closed__2();
lean_mark_persistent(l_Lean_mkMapDeclarationExtension___rarg___closed__2);
l_Lean_MapDeclarationExtension_instInhabitedMapDeclarationExtension___closed__1 = _init_l_Lean_MapDeclarationExtension_instInhabitedMapDeclarationExtension___closed__1();
lean_mark_persistent(l_Lean_MapDeclarationExtension_instInhabitedMapDeclarationExtension___closed__1);
l_Lean_MapDeclarationExtension_insert___rarg___closed__1 = _init_l_Lean_MapDeclarationExtension_insert___rarg___closed__1();
lean_mark_persistent(l_Lean_MapDeclarationExtension_insert___rarg___closed__1);
l_Lean_MapDeclarationExtension_insert___rarg___closed__2 = _init_l_Lean_MapDeclarationExtension_insert___rarg___closed__2();
lean_mark_persistent(l_Lean_MapDeclarationExtension_insert___rarg___closed__2);
l_Lean_MapDeclarationExtension_insert___rarg___closed__3 = _init_l_Lean_MapDeclarationExtension_insert___rarg___closed__3();
lean_mark_persistent(l_Lean_MapDeclarationExtension_insert___rarg___closed__3);
l_Lean_MapDeclarationExtension_insert___rarg___closed__4 = _init_l_Lean_MapDeclarationExtension_insert___rarg___closed__4();
lean_mark_persistent(l_Lean_MapDeclarationExtension_insert___rarg___closed__4);
l_Lean_MapDeclarationExtension_find_x3f___rarg___closed__1 = _init_l_Lean_MapDeclarationExtension_find_x3f___rarg___closed__1();
lean_mark_persistent(l_Lean_MapDeclarationExtension_find_x3f___rarg___closed__1);
l_Nat_foldAux___at_Lean_mkModuleData___spec__1___closed__1 = _init_l_Nat_foldAux___at_Lean_mkModuleData___spec__1___closed__1();
lean_mark_persistent(l_Nat_foldAux___at_Lean_mkModuleData___spec__1___closed__1);
l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___closed__1 = _init_l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___closed__1();
lean_mark_persistent(l_Std_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___closed__1);
l___private_Lean_Environment_0__Lean_getEntriesFor___closed__1 = _init_l___private_Lean_Environment_0__Lean_getEntriesFor___closed__1();
lean_mark_persistent(l___private_Lean_Environment_0__Lean_getEntriesFor___closed__1);
l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop___closed__1 = _init_l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop___closed__1();
lean_mark_persistent(l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop___closed__1);
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
l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9___closed__1);
l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_importModules___spec__9___closed__2);
l_Lean_importModules___closed__1 = _init_l_Lean_importModules___closed__1();
lean_mark_persistent(l_Lean_importModules___closed__1);
l_Lean_importModules___closed__2 = _init_l_Lean_importModules___closed__2();
lean_mark_persistent(l_Lean_importModules___closed__2);
l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__1 = _init_l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__1);
l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__2 = _init_l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__2);
l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__3 = _init_l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__3);
l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__4 = _init_l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__4);
l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__5 = _init_l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__5);
l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__6 = _init_l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__6();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Environment___hyg_4639____closed__6);
if (builtin) {res = l_Lean_initFn____x40_Lean_Environment___hyg_4639_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_namespacesExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_namespacesExt);
lean_dec_ref(res);
}l_Lean_Environment_registerNamespace___closed__1 = _init_l_Lean_Environment_registerNamespace___closed__1();
lean_mark_persistent(l_Lean_Environment_registerNamespace___closed__1);
l_List_toStringAux___at_Lean_Environment_displayStats___spec__2___closed__1 = _init_l_List_toStringAux___at_Lean_Environment_displayStats___spec__2___closed__1();
lean_mark_persistent(l_List_toStringAux___at_Lean_Environment_displayStats___spec__2___closed__1);
l_List_toString___at_Lean_Environment_displayStats___spec__1___closed__1 = _init_l_List_toString___at_Lean_Environment_displayStats___spec__1___closed__1();
lean_mark_persistent(l_List_toString___at_Lean_Environment_displayStats___spec__1___closed__1);
l_List_toString___at_Lean_Environment_displayStats___spec__1___closed__2 = _init_l_List_toString___at_Lean_Environment_displayStats___spec__1___closed__2();
lean_mark_persistent(l_List_toString___at_Lean_Environment_displayStats___spec__1___closed__2);
l_List_toString___at_Lean_Environment_displayStats___spec__1___closed__3 = _init_l_List_toString___at_Lean_Environment_displayStats___spec__1___closed__3();
lean_mark_persistent(l_List_toString___at_Lean_Environment_displayStats___spec__1___closed__3);
l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___lambda__1___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___lambda__1___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___lambda__1___closed__1);
l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___lambda__1___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___lambda__1___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___lambda__1___closed__2);
l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___lambda__1___closed__3 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___lambda__1___closed__3();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___lambda__1___closed__3);
l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___closed__1);
l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___closed__2);
l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___closed__3 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___closed__3();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___closed__3);
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
l_Lean_Environment_displayStats___closed__10 = _init_l_Lean_Environment_displayStats___closed__10();
lean_mark_persistent(l_Lean_Environment_displayStats___closed__10);
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

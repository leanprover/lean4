// Lean compiler output
// Module: Lake.Build.Library
// Imports: Lake.Build.Common Lake.Build.Targets
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_fetchTargetJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_LeanLib_defaultFacet;
LEAN_EXPORT lean_object* l_Lake_LeanLib_initFacetConfigs;
lean_object* l_Lake_ensureJob___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JobResult_prependLog___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_modulesFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
static lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__3;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___closed__4;
lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Target_fetchIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_initFacetConfigs___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_modulesFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildShared___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildDefaultFacets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__8_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_nameToSharedLib(lean_object*);
static lean_object* l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__0;
lean_object* l_System_FilePath_normalize(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_sharedFacetConfig;
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_LeanLib_recCollectLocalModules___closed__3;
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recBuildExtraDepTargets_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT uint8_t l_Array_toJson___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__1___lam__0(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Package_findModule_x3f_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lake_LeanLib_modulesFacet;
lean_object* l_Lake_LeanLib_getModuleArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0;
static lean_object* l_Lake_OrdHashSet_empty___at___Lake_LeanLib_recBuildShared_spec__6___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildDefaultFacets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_ExternLib_dynlibFacet;
extern lean_object* l_Lake_Package_keyword;
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildExtraDepTargets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___lam__0(uint8_t, lean_object*);
static lean_object* l_Lake_LeanLib_leanArtsFacetConfig___closed__0;
extern lean_object* l_Lake_Module_transImportsFacet;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_empty___at___Lake_LeanLib_recBuildShared_spec__6;
extern lean_object* l_Lake_LeanLib_extraDepFacet;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3(lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EquipT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recCollectLocalModules_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recBuildShared___closed__0;
lean_object* l_Lake_buildStaticLib(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_ModuleFacet_fetch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_LeanLib_sharedFacetConfig_spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recCollectLocalModules___closed__4;
static lean_object* l_Lake_LeanLib_initFacetConfigs___closed__2;
static lean_object* l_Lake_LeanLib_initFacetConfigs___closed__3;
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_buildLeanSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_modulesFacetConfig;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildDefaultFacets_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_mix___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_toJson___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1_spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_initFacetConfigs___closed__5;
static lean_object* l_Lake_LeanLib_recBuildDefaultFacets___closed__0;
lean_object* l_Lake_EStateT_instFunctor___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lake_nullFormat___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__4;
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___lam__0(lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_LeanLib_leanArtsFacet;
extern lean_object* l_Lake_instDataKindUnit;
extern lean_object* l_Lake_Module_leanArtsFacet;
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_defaultFacetConfig___closed__0;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildShared_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_initLibraryFacetConfigs;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindFilePath;
static lean_object* l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lake_LeanLib_modulesFacetConfig___lam__0(uint8_t, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildLean(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_PartialBuildKey_toString(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__13___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__3_spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recCollectLocalModules_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recBuildExtraDepTargets_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lake_LeanLib_recCollectLocalModules_go_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lake_LeanLib_recCollectLocalModules_go_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recBuildStatic___closed__4;
lean_object* l_Lake_EStateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_LeanLib_sharedFacetConfig_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig;
static lean_object* l_Lake_LeanLib_sharedFacetConfig___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildShared___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_LeanLib_staticFacetConfig_spec__7(uint8_t, lean_object*);
static lean_object* l_Lake_LeanLib_recCollectLocalModules___closed__1;
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_renew___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__13___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_initFacetConfigs___closed__6;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__8_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_LeanLib_staticFacet;
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
lean_object* l_Array_mapMUnsafe_map___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___closed__1;
uint8_t l_Lake_LeanLib_isPlugin(lean_object*);
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recCollectLocalModules___closed__2;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recBuildExtraDepTargets_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recCollectLocalModules___closed__0;
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recBuildLean___closed__2;
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
static lean_object* l_Lake_LeanLib_leanArtsFacetConfig___closed__2;
static lean_object* l_Lake_LeanLib_recCollectLocalModules___closed__5;
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recBuildStatic___lam__4___closed__0;
static lean_object* l_Lake_LeanLib_leanArtsFacetConfig___closed__1;
static lean_object* l_Lake_LeanLib_recBuildExtraDepTargets___closed__0;
extern lean_object* l_Lake_LeanLib_staticExportFacet;
LEAN_EXPORT uint8_t l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__1(uint8_t, lean_object*);
uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__11_spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__13___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildLean_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lake_Package_extraDepFacet;
lean_object* l_panic___at___Lean_Name_getString_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5___lam__0(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recBuildLean___closed__3;
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_LeanLib_staticFacetConfig_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildLean_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_modulesFacetConfig___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recCollectLocalModules_go_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recBuildExtraDepTargets___closed__1;
LEAN_EXPORT lean_object* l_Lake_LeanLib_defaultFacetConfig;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__11_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindDynlib;
static lean_object* l_Lake_LeanLib_extraDepFacetConfig___closed__1;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_prevn(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
static lean_object* l_Lake_LeanLib_recBuildStatic___closed__2;
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0(uint8_t, lean_object*);
static lean_object* l_Lake_LeanLib_recBuildStatic___lam__4___closed__1;
lean_object* l_Lake_Job_mixArray___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_modulesFacetConfig___closed__0;
static lean_object* l_Lake_LeanLib_recBuildStatic___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lake_mkRelPathString(lean_object*);
static lean_object* l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__2;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
extern lean_object* l_Lake_Module_importsFacet;
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig;
static lean_object* l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__3;
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___closed__2;
lean_object* l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_nameToStaticLib(lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_LeanLib_sharedFacetConfig___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__3_spec__3___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recBuildStatic___closed__1;
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
extern lean_object* l_Lake_Module_keyword;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_staticExportFacetConfig___closed__0;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_initFacetConfigs___closed__1;
static lean_object* l_Lake_LeanLib_recBuildLean___closed__4;
lean_object* lean_io_wait(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lake_LeanLib_recBuildLean___closed__0;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__1(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_LeanLib_extraDepFacetConfig;
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recBuildStatic___closed__0;
lean_object* l_Lake_EquipT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__1___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_LeanLib_sharedFacet;
extern uint8_t l_System_Platform_isWindows;
static lean_object* l_Lake_LeanLib_recBuildLean___closed__1;
static lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__3_spec__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lake_ExternLib_keyword;
lean_object* l_Lake_BuildInfo_fetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recCollectLocalModules_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recBuildExtraDepTargets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_initFacetConfigs___closed__0;
static lean_object* l_Lake_OrdHashSet_empty___at___Lake_LeanLib_recBuildShared_spec__6___closed__0;
static lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_toJson___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_LeanLib_sharedFacetConfig___lam__0(uint8_t, lean_object*);
static lean_object* l_Lake_LeanLib_extraDepFacetConfig___closed__0;
static lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__2;
static lean_object* l_Lake_LeanLib_defaultFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recCollectLocalModules_go_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_4, x_3);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_10);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_11);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_array_uget(x_2, x_4);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_1, 1);
x_29 = lean_name_eq(x_27, x_28);
lean_dec(x_27);
if (x_29 == 0)
{
lean_dec(x_25);
x_12 = x_5;
x_13 = x_10;
x_14 = x_11;
goto block_18;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_30 = l_Lake_LeanLib_recCollectLocalModules_go(x_1, x_25, x_24, x_23, x_6, x_7, x_8, x_9, x_10, x_11);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
lean_ctor_set(x_5, 1, x_35);
lean_ctor_set(x_5, 0, x_36);
x_12 = x_5;
x_13 = x_34;
x_14 = x_33;
goto block_18;
}
else
{
uint8_t x_37; 
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_37 = !lean_is_exclusive(x_30);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_30, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
return x_30;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_31, 0);
x_41 = lean_ctor_get(x_31, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_31);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_30, 0, x_42);
return x_30;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_30, 1);
lean_inc(x_43);
lean_dec(x_30);
x_44 = lean_ctor_get(x_31, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_31, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_46 = x_31;
} else {
 lean_dec_ref(x_31);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_43);
return x_48;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_49 = lean_ctor_get(x_5, 0);
x_50 = lean_ctor_get(x_5, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_5);
x_51 = lean_array_uget(x_2, x_4);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_ctor_get(x_1, 1);
x_55 = lean_name_eq(x_53, x_54);
lean_dec(x_53);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_51);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_50);
x_12 = x_56;
x_13 = x_10;
x_14 = x_11;
goto block_18;
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_57 = l_Lake_LeanLib_recCollectLocalModules_go(x_1, x_51, x_50, x_49, x_6, x_7, x_8, x_9, x_10, x_11);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_12 = x_64;
x_13 = x_61;
x_14 = x_60;
goto block_18;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_65 = lean_ctor_get(x_57, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_66 = x_57;
} else {
 lean_dec_ref(x_57);
 x_66 = lean_box(0);
}
x_67 = lean_ctor_get(x_58, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_58, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_69 = x_58;
} else {
 lean_dec_ref(x_58);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
if (lean_is_scalar(x_66)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_66;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_65);
return x_71;
}
}
}
}
block_18:
{
size_t x_15; size_t x_16; 
x_15 = 1;
x_16 = lean_usize_add(x_4, x_15);
x_4 = x_16;
x_5 = x_12;
x_10 = x_13;
x_11 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
x_9 = lean_box(0);
x_10 = lean_array_push(x_5, x_8);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_9;
x_5 = x_10;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_5, 2);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_name_eq(x_7, x_8);
if (x_9 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
return x_9;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lake_LeanLib_recCollectLocalModules_go_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
x_7 = lean_array_get_size(x_1);
x_8 = l_Lean_Name_hash___override(x_6);
lean_dec(x_6);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget(x_1, x_19);
lean_ctor_set(x_2, 2, x_20);
x_21 = lean_array_uset(x_1, x_19, x_2);
x_1 = x_21;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; size_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_2, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_2);
x_26 = lean_ctor_get(x_23, 2);
lean_inc(x_26);
x_27 = lean_array_get_size(x_1);
x_28 = l_Lean_Name_hash___override(x_26);
lean_dec(x_26);
x_29 = 32;
x_30 = lean_uint64_shift_right(x_28, x_29);
x_31 = lean_uint64_xor(x_28, x_30);
x_32 = 16;
x_33 = lean_uint64_shift_right(x_31, x_32);
x_34 = lean_uint64_xor(x_31, x_33);
x_35 = lean_uint64_to_usize(x_34);
x_36 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_37 = 1;
x_38 = lean_usize_sub(x_36, x_37);
x_39 = lean_usize_land(x_35, x_38);
x_40 = lean_array_uget(x_1, x_39);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_23);
lean_ctor_set(x_41, 1, x_24);
lean_ctor_set(x_41, 2, x_40);
x_42 = lean_array_uset(x_1, x_39, x_41);
x_1 = x_42;
x_2 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__3_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__3_spec__3___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__3___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; uint64_t x_116; uint64_t x_117; uint64_t x_118; uint64_t x_119; size_t x_120; size_t x_121; size_t x_122; size_t x_123; size_t x_124; lean_object* x_125; uint8_t x_126; 
x_53 = lean_ctor_get(x_4, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_4, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_2, 2);
lean_inc(x_55);
x_112 = lean_array_get_size(x_54);
x_113 = l_Lean_Name_hash___override(x_55);
x_114 = 32;
x_115 = lean_uint64_shift_right(x_113, x_114);
x_116 = lean_uint64_xor(x_113, x_115);
x_117 = 16;
x_118 = lean_uint64_shift_right(x_116, x_117);
x_119 = lean_uint64_xor(x_116, x_118);
x_120 = lean_uint64_to_usize(x_119);
x_121 = lean_usize_of_nat(x_112);
lean_dec(x_112);
x_122 = 1;
x_123 = lean_usize_sub(x_121, x_122);
x_124 = lean_usize_land(x_120, x_123);
x_125 = lean_array_uget(x_54, x_124);
x_126 = l_Std_DHashMap_Internal_AssocList_contains___at___Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg(x_2, x_125);
if (x_126 == 0)
{
if (x_126 == 0)
{
uint8_t x_127; 
x_127 = !lean_is_exclusive(x_4);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_128 = lean_ctor_get(x_4, 1);
lean_dec(x_128);
x_129 = lean_ctor_get(x_4, 0);
lean_dec(x_129);
x_130 = lean_box(0);
x_131 = lean_unsigned_to_nat(1u);
x_132 = lean_nat_add(x_53, x_131);
lean_dec(x_53);
lean_inc(x_2);
x_133 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_133, 0, x_2);
lean_ctor_set(x_133, 1, x_130);
lean_ctor_set(x_133, 2, x_125);
x_134 = lean_array_uset(x_54, x_124, x_133);
x_135 = lean_unsigned_to_nat(4u);
x_136 = lean_nat_mul(x_132, x_135);
x_137 = lean_unsigned_to_nat(3u);
x_138 = lean_nat_div(x_136, x_137);
lean_dec(x_136);
x_139 = lean_array_get_size(x_134);
x_140 = lean_nat_dec_le(x_138, x_139);
lean_dec(x_139);
lean_dec(x_138);
if (x_140 == 0)
{
lean_object* x_141; 
x_141 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3___redArg(x_134);
lean_ctor_set(x_4, 1, x_141);
lean_ctor_set(x_4, 0, x_132);
x_56 = x_4;
goto block_111;
}
else
{
lean_ctor_set(x_4, 1, x_134);
lean_ctor_set(x_4, 0, x_132);
x_56 = x_4;
goto block_111;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
lean_dec(x_4);
x_142 = lean_box(0);
x_143 = lean_unsigned_to_nat(1u);
x_144 = lean_nat_add(x_53, x_143);
lean_dec(x_53);
lean_inc(x_2);
x_145 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_145, 0, x_2);
lean_ctor_set(x_145, 1, x_142);
lean_ctor_set(x_145, 2, x_125);
x_146 = lean_array_uset(x_54, x_124, x_145);
x_147 = lean_unsigned_to_nat(4u);
x_148 = lean_nat_mul(x_144, x_147);
x_149 = lean_unsigned_to_nat(3u);
x_150 = lean_nat_div(x_148, x_149);
lean_dec(x_148);
x_151 = lean_array_get_size(x_146);
x_152 = lean_nat_dec_le(x_150, x_151);
lean_dec(x_151);
lean_dec(x_150);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
x_153 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3___redArg(x_146);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_144);
lean_ctor_set(x_154, 1, x_153);
x_56 = x_154;
goto block_111;
}
else
{
lean_object* x_155; 
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_144);
lean_ctor_set(x_155, 1, x_146);
x_56 = x_155;
goto block_111;
}
}
}
else
{
lean_dec(x_125);
lean_dec(x_54);
lean_dec(x_53);
x_56 = x_4;
goto block_111;
}
}
else
{
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_17 = x_4;
x_18 = x_3;
x_19 = x_9;
x_20 = x_10;
goto block_24;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
block_24:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_17);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
block_52:
{
lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_3);
x_30 = lean_array_size(x_26);
x_31 = 0;
x_32 = l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recCollectLocalModules_go_spec__0(x_1, x_26, x_30, x_31, x_29, x_5, x_6, x_7, x_8, x_27, x_28);
lean_dec(x_26);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_array_push(x_38, x_2);
x_17 = x_37;
x_18 = x_39;
x_19 = x_36;
x_20 = x_35;
goto block_24;
}
else
{
uint8_t x_40; 
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_32);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_32, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_33);
if (x_42 == 0)
{
return x_32;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_33, 0);
x_44 = lean_ctor_get(x_33, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_33);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_32, 0, x_45);
return x_32;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_32, 1);
lean_inc(x_46);
lean_dec(x_32);
x_47 = lean_ctor_get(x_33, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_33, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_49 = x_33;
} else {
 lean_dec_ref(x_33);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_46);
return x_51;
}
}
}
block_111:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = l_Lake_Module_importsFacet;
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_55);
x_59 = l_Lake_Module_keyword;
lean_inc(x_2);
x_60 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_60, 2, x_2);
lean_ctor_set(x_60, 3, x_57);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_61 = lean_apply_6(x_5, x_60, x_6, x_7, x_8, x_9, x_10);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_ctor_get(x_63, 0);
lean_inc(x_66);
lean_dec(x_63);
x_67 = lean_io_wait(x_66, x_64);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_ctor_get(x_68, 0);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_ctor_get(x_69, 0);
lean_inc(x_72);
lean_dec(x_69);
x_73 = lean_unsigned_to_nat(0u);
x_74 = lean_array_get_size(x_72);
x_75 = lean_nat_dec_lt(x_73, x_74);
if (x_75 == 0)
{
lean_dec(x_74);
lean_dec(x_72);
x_25 = x_56;
x_26 = x_71;
x_27 = x_65;
x_28 = x_70;
goto block_52;
}
else
{
uint8_t x_76; 
x_76 = lean_nat_dec_le(x_74, x_74);
if (x_76 == 0)
{
lean_dec(x_74);
lean_dec(x_72);
x_25 = x_56;
x_26 = x_71;
x_27 = x_65;
x_28 = x_70;
goto block_52;
}
else
{
lean_object* x_77; size_t x_78; size_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_77 = lean_box(0);
x_78 = 0;
x_79 = lean_usize_of_nat(x_74);
lean_dec(x_74);
x_80 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1(x_72, x_78, x_79, x_77, x_65, x_70);
lean_dec(x_72);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_25 = x_56;
x_26 = x_71;
x_27 = x_83;
x_28 = x_82;
goto block_52;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
lean_dec(x_56);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_84 = lean_ctor_get(x_68, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_67, 1);
lean_inc(x_85);
lean_dec(x_67);
x_86 = lean_ctor_get(x_68, 0);
lean_inc(x_86);
lean_dec(x_68);
x_87 = lean_ctor_get(x_84, 0);
lean_inc(x_87);
lean_dec(x_84);
x_88 = lean_unsigned_to_nat(0u);
x_89 = lean_array_get_size(x_87);
x_90 = lean_nat_dec_lt(x_88, x_89);
if (x_90 == 0)
{
lean_dec(x_89);
lean_dec(x_87);
x_11 = x_86;
x_12 = x_65;
x_13 = x_85;
goto block_16;
}
else
{
uint8_t x_91; 
x_91 = lean_nat_dec_le(x_89, x_89);
if (x_91 == 0)
{
lean_dec(x_89);
lean_dec(x_87);
x_11 = x_86;
x_12 = x_65;
x_13 = x_85;
goto block_16;
}
else
{
lean_object* x_92; size_t x_93; size_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_92 = lean_box(0);
x_93 = 0;
x_94 = lean_usize_of_nat(x_89);
lean_dec(x_89);
x_95 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1(x_87, x_93, x_94, x_92, x_65, x_85);
lean_dec(x_87);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_11 = x_86;
x_12 = x_98;
x_13 = x_97;
goto block_16;
}
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_56);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_99 = !lean_is_exclusive(x_61);
if (x_99 == 0)
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_ctor_get(x_61, 0);
lean_dec(x_100);
x_101 = !lean_is_exclusive(x_62);
if (x_101 == 0)
{
return x_61;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_62, 0);
x_103 = lean_ctor_get(x_62, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_62);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set(x_61, 0, x_104);
return x_61;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_105 = lean_ctor_get(x_61, 1);
lean_inc(x_105);
lean_dec(x_61);
x_106 = lean_ctor_get(x_62, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_62, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_108 = x_62;
} else {
 lean_dec_ref(x_62);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_105);
return x_110;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recCollectLocalModules_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recCollectLocalModules_go_spec__0(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lake_LeanLib_recCollectLocalModules_go_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lake_LeanLib_recCollectLocalModules_go_spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_LeanLib_recCollectLocalModules_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recCollectLocalModules_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
x_18 = lean_array_uget(x_2, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Lake_LeanLib_recCollectLocalModules_go(x_1, x_18, x_17, x_16, x_6, x_7, x_8, x_9, x_10, x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
lean_ctor_set(x_5, 1, x_24);
lean_ctor_set(x_5, 0, x_25);
x_26 = 1;
x_27 = lean_usize_add(x_4, x_26);
x_4 = x_27;
x_10 = x_23;
x_11 = x_22;
goto _start;
}
else
{
uint8_t x_29; 
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_19, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_20);
if (x_31 == 0)
{
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_20);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_19, 0, x_34);
return x_19;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_dec(x_19);
x_36 = lean_ctor_get(x_20, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_20, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_38 = x_20;
} else {
 lean_dec_ref(x_20);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_35);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_5, 0);
x_42 = lean_ctor_get(x_5, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_5);
x_43 = lean_array_uget(x_2, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_44 = l_Lake_LeanLib_recCollectLocalModules_go(x_1, x_43, x_42, x_41, x_6, x_7, x_8, x_9, x_10, x_11);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = 1;
x_53 = lean_usize_add(x_4, x_52);
x_4 = x_53;
x_5 = x_51;
x_10 = x_48;
x_11 = x_47;
goto _start;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_55 = lean_ctor_get(x_44, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_56 = x_44;
} else {
 lean_dec_ref(x_44);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_45, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_45, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_59 = x_45;
} else {
 lean_dec_ref(x_45);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
if (lean_is_scalar(x_56)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_56;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_55);
return x_61;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_get_set_stdout(x_1, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_get_set_stdout(x_1, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
lean_inc(x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__1___redArg___lam__0(x_16, x_21, x_24, x_23, x_20);
lean_dec(x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_22);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_25, 0, x_31);
return x_25;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_22);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_19, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_dec(x_19);
x_40 = lean_box(0);
x_41 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__1___redArg___lam__0(x_16, x_21, x_40, x_39, x_20);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_9 = x_38;
x_10 = x_44;
x_11 = x_43;
goto block_14;
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_get_set_stdin(x_1, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_get_set_stdin(x_1, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
lean_inc(x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__2___redArg___lam__0(x_16, x_21, x_24, x_23, x_20);
lean_dec(x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_22);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_25, 0, x_31);
return x_25;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_22);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_19, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_dec(x_19);
x_40 = lean_box(0);
x_41 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__2___redArg___lam__0(x_16, x_21, x_40, x_39, x_20);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_9 = x_38;
x_10 = x_44;
x_11 = x_43;
goto block_14;
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_get_set_stderr(x_1, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_get_set_stderr(x_1, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
lean_inc(x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__3___redArg___lam__0(x_16, x_21, x_24, x_23, x_20);
lean_dec(x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_22);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_25, 0, x_31);
return x_25;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_22);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_19, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_dec(x_19);
x_40 = lean_box(0);
x_41 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__3___redArg___lam__0(x_16, x_21, x_40, x_39, x_20);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_9 = x_38;
x_10 = x_44;
x_11 = x_43;
goto block_14;
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_ByteArray_empty;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.String.Extra", 22, 22);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String.fromUTF8!", 16, 16);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid UTF-8 string", 20, 20);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___closed__3;
x_2 = lean_unsigned_to_nat(47u);
x_3 = lean_unsigned_to_nat(129u);
x_4 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___closed__2;
x_5 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___closed__1;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___closed__0;
x_18 = lean_st_mk_ref(x_17, x_8);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_mk_ref(x_17, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_IO_FS_Stream_ofBuffer(x_19);
lean_inc(x_22);
x_25 = l_IO_FS_Stream_ofBuffer(x_22);
if (x_2 == 0)
{
x_26 = x_1;
goto block_53;
}
else
{
lean_object* x_54; 
lean_inc(x_25);
x_54 = lean_alloc_closure((void*)(l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__3), 9, 3);
lean_closure_set(x_54, 0, lean_box(0));
lean_closure_set(x_54, 1, x_25);
lean_closure_set(x_54, 2, x_1);
x_26 = x_54;
goto block_53;
}
block_16:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
block_53:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_alloc_closure((void*)(l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__1), 9, 3);
lean_closure_set(x_27, 0, lean_box(0));
lean_closure_set(x_27, 1, x_25);
lean_closure_set(x_27, 2, x_26);
x_28 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__2___redArg(x_24, x_27, x_3, x_4, x_5, x_6, x_7, x_23);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_st_ref_get(x_22, x_30);
lean_dec(x_22);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_string_validate_utf8(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_36);
x_38 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___closed__4;
x_39 = l_panic___at___Lean_Name_getString_x21_spec__0(x_38);
x_9 = x_35;
x_10 = x_31;
x_11 = x_32;
x_12 = x_39;
goto block_16;
}
else
{
lean_object* x_40; 
x_40 = lean_string_from_utf8_unchecked(x_36);
lean_dec(x_36);
x_9 = x_35;
x_10 = x_31;
x_11 = x_32;
x_12 = x_40;
goto block_16;
}
}
else
{
uint8_t x_41; 
lean_dec(x_22);
x_41 = !lean_is_exclusive(x_28);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_28, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_29);
if (x_43 == 0)
{
return x_28;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_29, 0);
x_45 = lean_ctor_get(x_29, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_29);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_28, 0, x_46);
return x_28;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_28, 1);
lean_inc(x_47);
lean_dec(x_28);
x_48 = lean_ctor_get(x_29, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_29, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_50 = x_29;
} else {
 lean_dec_ref(x_29);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_47);
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_JobResult_prependLog___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
static lean_object* _init_l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<nil>", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__1;
x_2 = l_Lake_BuildTrace_nil(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_35; 
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
x_14 = lean_box(0);
x_15 = lean_array_get_size(x_6);
lean_dec(x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
lean_dec(x_13);
x_96 = lean_ctor_get(x_11, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_11, 1);
lean_inc(x_97);
lean_dec(x_11);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_dec(x_96);
x_100 = lean_string_utf8_byte_size(x_98);
x_101 = lean_unsigned_to_nat(0u);
x_102 = lean_nat_dec_eq(x_100, x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_103 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__3;
x_104 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_98, x_100, x_101);
x_105 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_98, x_104, x_100);
x_106 = lean_string_utf8_extract(x_98, x_104, x_105);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_98);
x_107 = lean_string_append(x_103, x_106);
lean_dec(x_106);
x_108 = lean_box(1);
x_109 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_109, 0, x_107);
x_110 = lean_unbox(x_108);
lean_ctor_set_uint8(x_109, sizeof(void*)*1, x_110);
x_111 = lean_box(0);
x_112 = lean_array_push(x_97, x_109);
x_113 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___lam__1(x_99, x_111, x_2, x_3, x_4, x_5, x_112, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = x_113;
goto block_95;
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_100);
lean_dec(x_98);
x_114 = lean_box(0);
x_115 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___lam__1(x_99, x_114, x_2, x_3, x_4, x_5, x_97, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = x_115;
goto block_95;
}
}
else
{
lean_object* x_116; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_116 = lean_ctor_get(x_11, 1);
lean_inc(x_116);
lean_dec(x_11);
x_16 = x_116;
x_17 = x_12;
goto block_34;
}
block_34:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
lean_inc(x_16);
x_18 = l_Array_shrink___redArg(x_16, x_15);
x_19 = lean_array_get_size(x_16);
x_20 = l_Array_extract___redArg(x_16, x_15, x_19);
lean_dec(x_16);
x_21 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__0;
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_box(0);
x_24 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__2;
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_unbox(x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_26);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_task_pure(x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_14);
lean_ctor_set(x_30, 2, x_21);
x_31 = lean_unbox(x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_31);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_18);
if (lean_is_scalar(x_13)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_13;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_17);
return x_33;
}
block_95:
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_36, 0);
x_40 = lean_ctor_get(x_36, 1);
x_41 = lean_array_get_size(x_40);
x_42 = lean_nat_dec_lt(x_15, x_41);
if (x_42 == 0)
{
lean_dec(x_41);
lean_free_object(x_36);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_15);
return x_35;
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_35);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_35, 1);
lean_dec(x_44);
x_45 = lean_ctor_get(x_35, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_39);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_39, 0);
x_48 = lean_ctor_get(x_39, 1);
lean_dec(x_48);
lean_inc(x_40);
x_49 = l_Array_shrink___redArg(x_40, x_15);
x_50 = l_Array_extract___redArg(x_40, x_15, x_41);
lean_dec(x_40);
x_51 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___lam__0), 2, 1);
lean_closure_set(x_51, 0, x_50);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_unbox(x_8);
x_54 = lean_task_map(x_51, x_47, x_52, x_53);
lean_ctor_set(x_39, 1, x_14);
lean_ctor_set(x_39, 0, x_54);
lean_ctor_set(x_36, 1, x_49);
return x_35;
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; 
x_55 = lean_ctor_get(x_39, 0);
x_56 = lean_ctor_get(x_39, 2);
x_57 = lean_ctor_get_uint8(x_39, sizeof(void*)*3);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_39);
lean_inc(x_40);
x_58 = l_Array_shrink___redArg(x_40, x_15);
x_59 = l_Array_extract___redArg(x_40, x_15, x_41);
lean_dec(x_40);
x_60 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___lam__0), 2, 1);
lean_closure_set(x_60, 0, x_59);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_unbox(x_8);
x_63 = lean_task_map(x_60, x_55, x_61, x_62);
x_64 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_14);
lean_ctor_set(x_64, 2, x_56);
lean_ctor_set_uint8(x_64, sizeof(void*)*3, x_57);
lean_ctor_set(x_36, 1, x_58);
lean_ctor_set(x_36, 0, x_64);
return x_35;
}
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_35);
x_65 = lean_ctor_get(x_39, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_39, 2);
lean_inc(x_66);
x_67 = lean_ctor_get_uint8(x_39, sizeof(void*)*3);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 x_68 = x_39;
} else {
 lean_dec_ref(x_39);
 x_68 = lean_box(0);
}
lean_inc(x_40);
x_69 = l_Array_shrink___redArg(x_40, x_15);
x_70 = l_Array_extract___redArg(x_40, x_15, x_41);
lean_dec(x_40);
x_71 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___lam__0), 2, 1);
lean_closure_set(x_71, 0, x_70);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_unbox(x_8);
x_74 = lean_task_map(x_71, x_65, x_72, x_73);
if (lean_is_scalar(x_68)) {
 x_75 = lean_alloc_ctor(0, 3, 1);
} else {
 x_75 = x_68;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_14);
lean_ctor_set(x_75, 2, x_66);
lean_ctor_set_uint8(x_75, sizeof(void*)*3, x_67);
lean_ctor_set(x_36, 1, x_69);
lean_ctor_set(x_36, 0, x_75);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_36);
lean_ctor_set(x_76, 1, x_37);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_36, 0);
x_78 = lean_ctor_get(x_36, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_36);
x_79 = lean_array_get_size(x_78);
x_80 = lean_nat_dec_lt(x_15, x_79);
if (x_80 == 0)
{
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_37);
lean_dec(x_15);
return x_35;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_81 = x_35;
} else {
 lean_dec_ref(x_35);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get(x_77, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_77, 2);
lean_inc(x_83);
x_84 = lean_ctor_get_uint8(x_77, sizeof(void*)*3);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 x_85 = x_77;
} else {
 lean_dec_ref(x_77);
 x_85 = lean_box(0);
}
lean_inc(x_78);
x_86 = l_Array_shrink___redArg(x_78, x_15);
x_87 = l_Array_extract___redArg(x_78, x_15, x_79);
lean_dec(x_78);
x_88 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___lam__0), 2, 1);
lean_closure_set(x_88, 0, x_87);
x_89 = lean_unsigned_to_nat(0u);
x_90 = lean_unbox(x_8);
x_91 = lean_task_map(x_88, x_82, x_89, x_90);
if (lean_is_scalar(x_85)) {
 x_92 = lean_alloc_ctor(0, 3, 1);
} else {
 x_92 = x_85;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_14);
lean_ctor_set(x_92, 2, x_83);
lean_ctor_set_uint8(x_92, sizeof(void*)*3, x_84);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_86);
if (lean_is_scalar(x_81)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_81;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_37);
return x_94;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_1);
x_12 = l_Lake_LeanLib_getModuleArray(x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
x_16 = lean_array_size(x_13);
x_17 = 0;
x_18 = l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recCollectLocalModules_spec__0(x_1, x_13, x_16, x_17, x_15, x_6, x_7, x_8, x_9, x_10, x_14);
lean_dec(x_13);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_19, 1);
x_25 = lean_ctor_get(x_19, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_27 = lean_ctor_get(x_20, 1);
x_28 = lean_ctor_get(x_20, 0);
lean_dec(x_28);
x_29 = lean_mk_empty_array_with_capacity(x_4);
x_30 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__0;
x_31 = lean_box(0);
x_32 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__2;
x_33 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_unbox(x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_34);
lean_ctor_set(x_19, 1, x_33);
lean_ctor_set(x_19, 0, x_27);
x_35 = lean_task_pure(x_19);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_5);
lean_ctor_set(x_37, 2, x_30);
x_38 = lean_unbox(x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_38);
lean_ctor_set(x_20, 1, x_24);
lean_ctor_set(x_20, 0, x_37);
lean_ctor_set(x_18, 0, x_20);
return x_18;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_39 = lean_ctor_get(x_20, 1);
lean_inc(x_39);
lean_dec(x_20);
x_40 = lean_mk_empty_array_with_capacity(x_4);
x_41 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__0;
x_42 = lean_box(0);
x_43 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__2;
x_44 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_unbox(x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*2, x_45);
lean_ctor_set(x_19, 1, x_44);
lean_ctor_set(x_19, 0, x_39);
x_46 = lean_task_pure(x_19);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_5);
lean_ctor_set(x_48, 2, x_41);
x_49 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*3, x_49);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_24);
lean_ctor_set(x_18, 0, x_50);
return x_18;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; 
x_51 = lean_ctor_get(x_19, 1);
lean_inc(x_51);
lean_dec(x_19);
x_52 = lean_ctor_get(x_20, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_53 = x_20;
} else {
 lean_dec_ref(x_20);
 x_53 = lean_box(0);
}
x_54 = lean_mk_empty_array_with_capacity(x_4);
x_55 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__0;
x_56 = lean_box(0);
x_57 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__2;
x_58 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_58, 0, x_54);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_unbox(x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_59);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_52);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_task_pure(x_60);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_5);
lean_ctor_set(x_63, 2, x_55);
x_64 = lean_unbox(x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*3, x_64);
if (lean_is_scalar(x_53)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_53;
}
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_51);
lean_ctor_set(x_18, 0, x_65);
return x_18;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; 
x_66 = lean_ctor_get(x_18, 1);
lean_inc(x_66);
lean_dec(x_18);
x_67 = lean_ctor_get(x_19, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_68 = x_19;
} else {
 lean_dec_ref(x_19);
 x_68 = lean_box(0);
}
x_69 = lean_ctor_get(x_20, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_70 = x_20;
} else {
 lean_dec_ref(x_20);
 x_70 = lean_box(0);
}
x_71 = lean_mk_empty_array_with_capacity(x_4);
x_72 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__0;
x_73 = lean_box(0);
x_74 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__2;
x_75 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_75, 0, x_71);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_unbox(x_73);
lean_ctor_set_uint8(x_75, sizeof(void*)*2, x_76);
if (lean_is_scalar(x_68)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_68;
}
lean_ctor_set(x_77, 0, x_69);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_task_pure(x_77);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_5);
lean_ctor_set(x_80, 2, x_72);
x_81 = lean_unbox(x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*3, x_81);
if (lean_is_scalar(x_70)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_70;
}
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_67);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_66);
return x_83;
}
}
else
{
uint8_t x_84; 
lean_dec(x_5);
x_84 = !lean_is_exclusive(x_18);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_18, 0);
lean_dec(x_85);
x_86 = !lean_is_exclusive(x_19);
if (x_86 == 0)
{
return x_18;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_19, 0);
x_88 = lean_ctor_get(x_19, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_19);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_18, 0, x_89);
return x_18;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_90 = lean_ctor_get(x_18, 1);
lean_inc(x_90);
lean_dec(x_18);
x_91 = lean_ctor_get(x_19, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_19, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_93 = x_19;
} else {
 lean_dec_ref(x_19);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_90);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_12);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_97 = lean_ctor_get(x_12, 0);
x_98 = lean_io_error_to_string(x_97);
x_99 = lean_box(3);
x_100 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_100, 0, x_98);
x_101 = lean_unbox(x_99);
lean_ctor_set_uint8(x_100, sizeof(void*)*1, x_101);
x_102 = lean_array_get_size(x_10);
x_103 = lean_array_push(x_10, x_100);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_104);
return x_12;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_105 = lean_ctor_get(x_12, 0);
x_106 = lean_ctor_get(x_12, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_12);
x_107 = lean_io_error_to_string(x_105);
x_108 = lean_box(3);
x_109 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_109, 0, x_107);
x_110 = lean_unbox(x_108);
lean_ctor_set_uint8(x_109, sizeof(void*)*1, x_110);
x_111 = lean_array_get_size(x_10);
x_112 = lean_array_push(x_10, x_109);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_106);
return x_114;
}
}
}
}
static lean_object* _init_l_Lake_LeanLib_recCollectLocalModules___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanLib_recCollectLocalModules___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_recCollectLocalModules___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_recCollectLocalModules___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_LeanLib_recCollectLocalModules___closed__2;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanLib_recCollectLocalModules___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanLib_recCollectLocalModules___closed__3;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_recCollectLocalModules___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_LeanLib_recCollectLocalModules___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_box(0);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lake_LeanLib_recCollectLocalModules___closed__0;
x_11 = l_Lake_LeanLib_recCollectLocalModules___closed__5;
x_12 = lean_alloc_closure((void*)(l_Lake_LeanLib_recCollectLocalModules___lam__0___boxed), 11, 5);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_10);
lean_closure_set(x_12, 3, x_9);
lean_closure_set(x_12, 4, x_8);
x_13 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1(x_12, x_2, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recCollectLocalModules_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recCollectLocalModules_spec__0(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__2___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__3___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_LeanLib_recCollectLocalModules___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(x_5);
x_9 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_Name_toString(x_7, x_11, x_9);
x_13 = lean_string_append(x_4, x_12);
lean_dec(x_12);
x_14 = l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0;
x_15 = lean_string_append(x_13, x_14);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_2 = x_17;
x_4 = x_15;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_toJson___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_array_uset(x_4, x_3, x_8);
lean_inc(x_1);
x_10 = l_Lean_Name_toString(x_7, x_5, x_1);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_14 = lean_array_uset(x_9, x_3, x_11);
x_3 = x_13;
x_4 = x_14;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Array_toJson___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__1___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_alloc_closure((void*)(l_Array_toJson___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__1___lam__0___boxed), 1, 0);
x_3 = lean_array_size(x_1);
x_4 = 0;
x_5 = l_Array_mapMUnsafe_map___at___Array_toJson___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__1(x_2, x_3, x_4, x_1);
x_6 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
if (x_1 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__0;
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_2);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec(x_2);
x_3 = x_11;
goto block_10;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_2);
x_3 = x_11;
goto block_10;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_18 = l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(x_2, x_16, x_17, x_11);
lean_dec(x_2);
x_3 = x_18;
goto block_10;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Array_toJson___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__1(x_2);
x_20 = l_Lean_Json_compress(x_19);
return x_20;
}
block_10:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_string_utf8_byte_size(x_3);
lean_inc(x_6);
lean_inc(x_3);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = l_Substring_prevn(x_7, x_4, x_6);
lean_dec(x_7);
x_9 = lean_string_utf8_extract(x_3, x_5, x_8);
lean_dec(x_8);
lean_dec(x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_modulesFacetConfig___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_modulesFacetConfig___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_lib", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_modulesFacetConfig___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_LeanLib_modulesFacetConfig___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanLib_modulesFacetConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_recCollectLocalModules), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_modulesFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_modulesFacetConfig___lam__0___boxed), 2, 0);
x_2 = lean_box(0);
x_3 = l_Lake_LeanLib_modulesFacetConfig___closed__1;
x_4 = l_Lake_LeanLib_modulesFacetConfig___closed__2;
x_5 = lean_box(0);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_2);
lean_ctor_set(x_7, 3, x_1);
x_8 = lean_unbox(x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*4, x_8);
x_9 = lean_unbox(x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*4 + 1, x_9);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_toJson___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Array_toJson___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__1(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__1___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Array_toJson___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__1___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_modulesFacetConfig___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_LeanLib_modulesFacetConfig___lam__0(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildLean_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
x_14 = l_Lake_Module_leanArtsFacet;
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = l_Lake_Module_keyword;
x_17 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_12);
lean_ctor_set(x_17, 3, x_14);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = lean_apply_6(x_5, x_17, x_6, x_7, x_8, x_9, x_10);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l_Lake_Job_mix___redArg(x_4, x_21);
x_24 = 1;
x_25 = lean_usize_add(x_2, x_24);
x_2 = x_25;
x_4 = x_23;
x_9 = x_22;
x_10 = x_20;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_18, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_18, 0, x_32);
return x_18;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_dec(x_18);
x_34 = lean_ctor_get(x_19, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_36 = x_19;
} else {
 lean_dec_ref(x_19);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_4);
lean_ctor_set(x_39, 1, x_9);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_10);
return x_40;
}
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildLean___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildLean___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_1 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__2;
x_2 = lean_box(0);
x_3 = l_Lake_LeanLib_recBuildLean___closed__0;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
x_5 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_5);
return x_4;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildLean___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_LeanLib_recBuildLean___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildLean___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_LeanLib_recBuildLean___closed__2;
x_2 = lean_task_pure(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildLean___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_1 = lean_box(0);
x_2 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__0;
x_3 = lean_box(0);
x_4 = l_Lake_LeanLib_recBuildLean___closed__3;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
x_6 = lean_unbox(x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_6);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildLean(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lake_LeanLib_modulesFacet;
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_31);
x_35 = l_Lake_LeanLib_modulesFacetConfig___closed__1;
x_36 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_1);
lean_ctor_set(x_36, 3, x_33);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_37 = lean_apply_6(x_2, x_36, x_3, x_4, x_5, x_6, x_7);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_io_wait(x_42, x_40);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_ctor_get(x_45, 0);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_array_get_size(x_48);
x_51 = lean_nat_dec_lt(x_49, x_50);
if (x_51 == 0)
{
lean_dec(x_50);
lean_dec(x_48);
x_14 = x_47;
x_15 = x_41;
x_16 = x_46;
goto block_29;
}
else
{
uint8_t x_52; 
x_52 = lean_nat_dec_le(x_50, x_50);
if (x_52 == 0)
{
lean_dec(x_50);
lean_dec(x_48);
x_14 = x_47;
x_15 = x_41;
x_16 = x_46;
goto block_29;
}
else
{
lean_object* x_53; size_t x_54; size_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_box(0);
x_54 = 0;
x_55 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_56 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1(x_48, x_54, x_55, x_53, x_41, x_46);
lean_dec(x_48);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_14 = x_47;
x_15 = x_59;
x_16 = x_58;
goto block_29;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_60 = lean_ctor_get(x_44, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_43, 1);
lean_inc(x_61);
lean_dec(x_43);
x_62 = lean_ctor_get(x_44, 0);
lean_inc(x_62);
lean_dec(x_44);
x_63 = lean_ctor_get(x_60, 0);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_array_get_size(x_63);
x_66 = lean_nat_dec_lt(x_64, x_65);
if (x_66 == 0)
{
lean_dec(x_65);
lean_dec(x_63);
x_8 = x_62;
x_9 = x_41;
x_10 = x_61;
goto block_13;
}
else
{
uint8_t x_67; 
x_67 = lean_nat_dec_le(x_65, x_65);
if (x_67 == 0)
{
lean_dec(x_65);
lean_dec(x_63);
x_8 = x_62;
x_9 = x_41;
x_10 = x_61;
goto block_13;
}
else
{
lean_object* x_68; size_t x_69; size_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_68 = lean_box(0);
x_69 = 0;
x_70 = lean_usize_of_nat(x_65);
lean_dec(x_65);
x_71 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1(x_63, x_69, x_70, x_68, x_41, x_61);
lean_dec(x_63);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_8 = x_62;
x_9 = x_74;
x_10 = x_73;
goto block_13;
}
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_37);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_37, 0);
lean_dec(x_76);
x_77 = !lean_is_exclusive(x_38);
if (x_77 == 0)
{
return x_37;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_38, 0);
x_79 = lean_ctor_get(x_38, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_38);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set(x_37, 0, x_80);
return x_37;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_37, 1);
lean_inc(x_81);
lean_dec(x_37);
x_82 = lean_ctor_get(x_38, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_38, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_84 = x_38;
} else {
 lean_dec_ref(x_38);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_81);
return x_86;
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
block_29:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lake_LeanLib_recBuildLean___closed__4;
x_19 = lean_array_get_size(x_14);
x_20 = lean_nat_dec_lt(x_17, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_19, x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_16);
return x_25;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
x_26 = 0;
x_27 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_28 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildLean_spec__0(x_14, x_26, x_27, x_18, x_2, x_3, x_4, x_5, x_15, x_16);
lean_dec(x_14);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildLean_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildLean_spec__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildLean), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_nullFormat___boxed), 3, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_1 = l_Lake_LeanLib_leanArtsFacetConfig___closed__1;
x_2 = lean_box(1);
x_3 = l_Lake_instDataKindUnit;
x_4 = l_Lake_LeanLib_leanArtsFacetConfig___closed__0;
x_5 = l_Lake_LeanLib_modulesFacetConfig___closed__1;
x_6 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_1);
x_7 = lean_unbox(x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_7);
x_8 = lean_unbox(x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*4 + 1, x_8);
return x_6;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_LeanLib_leanArtsFacetConfig___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(0);
x_6 = lean_array_push(x_3, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lake_Target_fetchIn___redArg(x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_ModuleFacet_fetch___redArg(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 8);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lam__1), 8, 1);
lean_closure_set(x_14, 0, x_4);
x_15 = lean_box(x_1);
x_16 = lean_apply_1(x_13, x_15);
x_17 = lean_array_size(x_16);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___redArg(x_2, x_14, x_17, x_18, x_16);
x_20 = lean_apply_6(x_19, x_5, x_6, x_7, x_8, x_9, x_10);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = l_Array_append___redArg(x_3, x_25);
lean_dec(x_25);
lean_ctor_set(x_21, 0, x_26);
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = l_Array_append___redArg(x_3, x_27);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_20, 0, x_30);
return x_20;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_dec(x_20);
x_32 = lean_ctor_get(x_21, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_34 = x_21;
} else {
 lean_dec_ref(x_21);
 x_34 = lean_box(0);
}
x_35 = l_Array_append___redArg(x_3, x_32);
lean_dec(x_32);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
}
else
{
lean_dec(x_21);
lean_dec(x_3);
return x_20;
}
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildStatic___lam__4___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("export", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildStatic___lam__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_9, 0);
lean_inc(x_120);
lean_dec(x_9);
x_121 = lean_io_wait(x_120, x_15);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
lean_dec(x_8);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_dec(x_121);
x_125 = lean_ctor_get(x_122, 0);
lean_inc(x_125);
lean_dec(x_122);
x_126 = lean_ctor_get(x_123, 0);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_unsigned_to_nat(0u);
x_128 = lean_array_get_size(x_126);
x_129 = lean_nat_dec_lt(x_127, x_128);
if (x_129 == 0)
{
lean_dec(x_128);
lean_dec(x_126);
lean_dec(x_7);
lean_dec(x_6);
x_91 = x_125;
x_92 = x_14;
x_93 = x_124;
goto block_119;
}
else
{
uint8_t x_130; 
x_130 = lean_nat_dec_le(x_128, x_128);
if (x_130 == 0)
{
lean_dec(x_128);
lean_dec(x_126);
lean_dec(x_7);
lean_dec(x_6);
x_91 = x_125;
x_92 = x_14;
x_93 = x_124;
goto block_119;
}
else
{
lean_object* x_131; size_t x_132; size_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_131 = lean_box(0);
x_132 = 0;
x_133 = lean_usize_of_nat(x_128);
lean_dec(x_128);
x_134 = l_Array_foldlMUnsafe_fold___redArg(x_6, x_7, x_126, x_132, x_133, x_131);
x_135 = lean_apply_2(x_134, x_14, x_124);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_91 = x_125;
x_92 = x_138;
x_93 = x_137;
goto block_119;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_125);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_139 = lean_ctor_get(x_135, 1);
lean_inc(x_139);
lean_dec(x_135);
x_140 = lean_ctor_get(x_136, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_136, 1);
lean_inc(x_141);
lean_dec(x_136);
x_16 = x_140;
x_17 = x_141;
x_18 = x_139;
goto block_21;
}
}
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_142 = lean_ctor_get(x_122, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_121, 1);
lean_inc(x_143);
lean_dec(x_121);
x_144 = lean_ctor_get(x_122, 0);
lean_inc(x_144);
lean_dec(x_122);
x_145 = lean_ctor_get(x_142, 0);
lean_inc(x_145);
lean_dec(x_142);
x_146 = lean_unsigned_to_nat(0u);
x_147 = lean_array_get_size(x_145);
x_148 = lean_nat_dec_lt(x_146, x_147);
if (x_148 == 0)
{
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_8);
lean_dec(x_6);
x_16 = x_144;
x_17 = x_14;
x_18 = x_143;
goto block_21;
}
else
{
uint8_t x_149; 
x_149 = lean_nat_dec_le(x_147, x_147);
if (x_149 == 0)
{
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_8);
lean_dec(x_6);
x_16 = x_144;
x_17 = x_14;
x_18 = x_143;
goto block_21;
}
else
{
lean_object* x_150; size_t x_151; size_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_150 = lean_box(0);
x_151 = 0;
x_152 = lean_usize_of_nat(x_147);
lean_dec(x_147);
x_153 = l_Array_foldlMUnsafe_fold___redArg(x_6, x_8, x_145, x_151, x_152, x_150);
x_154 = lean_apply_2(x_153, x_14, x_143);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_16 = x_144;
x_17 = x_157;
x_18 = x_156;
goto block_21;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_144);
x_158 = lean_ctor_get(x_154, 1);
lean_inc(x_158);
lean_dec(x_154);
x_159 = lean_ctor_get(x_155, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_155, 1);
lean_inc(x_160);
lean_dec(x_155);
x_16 = x_159;
x_17 = x_160;
x_18 = x_158;
goto block_21;
}
}
}
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
block_37:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = l_Array_append___redArg(x_25, x_23);
lean_dec(x_23);
x_28 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__2;
x_29 = l_Lake_buildStaticLib(x_26, x_27, x_1, x_10, x_11, x_12, x_13, x_28, x_22);
lean_dec(x_27);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_29);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_24);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
block_90:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_41 = lean_ctor_get(x_2, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 3);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_2, 2);
lean_inc(x_44);
lean_dec(x_2);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_ctor_get(x_42, 6);
lean_inc(x_47);
x_48 = lean_ctor_get(x_42, 8);
lean_inc(x_48);
lean_dec(x_42);
x_49 = lean_ctor_get(x_43, 6);
lean_inc(x_49);
lean_dec(x_43);
x_50 = lean_ctor_get(x_44, 4);
lean_inc(x_50);
lean_dec(x_44);
x_51 = lean_ctor_get(x_45, 6);
lean_inc(x_51);
lean_dec(x_45);
x_52 = l_Array_append___redArg(x_49, x_51);
lean_dec(x_51);
x_53 = lean_array_size(x_52);
x_54 = 0;
x_55 = l_Array_mapMUnsafe_map___redArg(x_3, x_4, x_53, x_54, x_52);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_56 = lean_apply_6(x_55, x_10, x_11, x_12, x_13, x_39, x_40);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
if (x_1 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = l_System_FilePath_normalize(x_47);
x_62 = l_Lake_joinRelative(x_46, x_61);
lean_dec(x_61);
x_63 = l_System_FilePath_normalize(x_48);
x_64 = l_Lake_joinRelative(x_62, x_63);
lean_dec(x_63);
x_65 = l_Lake_nameToStaticLib(x_50);
x_66 = l_Lake_joinRelative(x_64, x_65);
lean_dec(x_65);
x_22 = x_58;
x_23 = x_59;
x_24 = x_60;
x_25 = x_38;
x_26 = x_66;
goto block_37;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_67 = lean_ctor_get(x_56, 1);
lean_inc(x_67);
lean_dec(x_56);
x_68 = lean_ctor_get(x_57, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_57, 1);
lean_inc(x_69);
lean_dec(x_57);
x_70 = l_System_FilePath_normalize(x_47);
x_71 = l_Lake_joinRelative(x_46, x_70);
lean_dec(x_70);
x_72 = l_System_FilePath_normalize(x_48);
x_73 = l_Lake_joinRelative(x_71, x_72);
lean_dec(x_72);
x_74 = l_Lake_nameToStaticLib(x_50);
x_75 = l_Lake_LeanLib_recBuildStatic___lam__4___closed__0;
x_76 = l_System_FilePath_addExtension(x_74, x_75);
x_77 = l_Lake_joinRelative(x_73, x_76);
lean_dec(x_76);
x_22 = x_67;
x_23 = x_68;
x_24 = x_69;
x_25 = x_38;
x_26 = x_77;
goto block_37;
}
}
else
{
uint8_t x_78; 
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_38);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_78 = !lean_is_exclusive(x_56);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_56, 0);
lean_dec(x_79);
x_80 = !lean_is_exclusive(x_57);
if (x_80 == 0)
{
return x_56;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_57, 0);
x_82 = lean_ctor_get(x_57, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_57);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set(x_56, 0, x_83);
return x_56;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_56, 1);
lean_inc(x_84);
lean_dec(x_56);
x_85 = lean_ctor_get(x_57, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_57, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_87 = x_57;
} else {
 lean_dec_ref(x_57);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_84);
return x_89;
}
}
}
block_119:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_94 = l_Lake_LeanLib_recBuildStatic___lam__4___closed__1;
x_95 = lean_unsigned_to_nat(0u);
x_96 = lean_array_get_size(x_91);
x_97 = lean_nat_dec_lt(x_95, x_96);
if (x_97 == 0)
{
lean_dec(x_96);
lean_dec(x_91);
lean_dec(x_5);
x_38 = x_94;
x_39 = x_92;
x_40 = x_93;
goto block_90;
}
else
{
uint8_t x_98; 
x_98 = lean_nat_dec_le(x_96, x_96);
if (x_98 == 0)
{
lean_dec(x_96);
lean_dec(x_91);
lean_dec(x_5);
x_38 = x_94;
x_39 = x_92;
x_40 = x_93;
goto block_90;
}
else
{
size_t x_99; size_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = 0;
x_100 = lean_usize_of_nat(x_96);
lean_dec(x_96);
lean_inc(x_3);
x_101 = l_Array_foldlMUnsafe_fold___redArg(x_3, x_5, x_91, x_99, x_100, x_94);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_102 = lean_apply_6(x_101, x_10, x_11, x_12, x_13, x_92, x_93);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_38 = x_105;
x_39 = x_106;
x_40 = x_104;
goto block_90;
}
else
{
uint8_t x_107; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_107 = !lean_is_exclusive(x_102);
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_102, 0);
lean_dec(x_108);
x_109 = !lean_is_exclusive(x_103);
if (x_109 == 0)
{
return x_102;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_103, 0);
x_111 = lean_ctor_get(x_103, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_103);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set(x_102, 0, x_112);
return x_102;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_113 = lean_ctor_get(x_102, 1);
lean_inc(x_113);
lean_dec(x_102);
x_114 = lean_ctor_get(x_103, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_103, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_116 = x_103;
} else {
 lean_dec_ref(x_103);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_113);
return x_118;
}
}
}
}
}
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildStatic___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildStatic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_toJson___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__1___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildStatic___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":static", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildStatic___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" (without exports)", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildStatic___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" (with exports)", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lake_LeanLib_recBuildStatic___closed__0;
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; 
x_13 = lean_ctor_get(x_9, 1);
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_ctor_get(x_11, 4);
lean_dec(x_16);
x_17 = lean_ctor_get(x_11, 3);
lean_dec(x_17);
x_18 = lean_ctor_get(x_11, 2);
lean_dec(x_18);
lean_inc(x_13);
lean_inc(x_15);
x_19 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_19, 0, x_15);
lean_closure_set(x_19, 1, x_13);
lean_inc(x_13);
lean_inc(x_15);
x_20 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_20, 0, x_15);
lean_closure_set(x_20, 1, x_13);
lean_inc(x_19);
lean_inc(x_15);
x_21 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_21, 0, x_15);
lean_closure_set(x_21, 1, x_19);
lean_inc(x_15);
lean_inc(x_14);
x_22 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_22, 0, x_14);
lean_closure_set(x_22, 1, x_15);
lean_closure_set(x_22, 2, x_13);
x_23 = l_Lake_EStateT_instFunctor___redArg(x_14);
x_24 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_24, 0, x_15);
lean_ctor_set(x_11, 4, x_20);
lean_ctor_set(x_11, 3, x_21);
lean_ctor_set(x_11, 2, x_22);
lean_ctor_set(x_11, 1, x_24);
lean_ctor_set(x_11, 0, x_23);
lean_ctor_set(x_9, 1, x_19);
lean_inc(x_9);
x_25 = l_ReaderT_instMonad___redArg(x_9);
x_26 = l_ReaderT_instMonad___redArg(x_25);
x_27 = l_ReaderT_instMonad___redArg(x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_inc(x_27);
x_29 = l_Lake_EquipT_instMonad___redArg(x_27);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = lean_ctor_get(x_6, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_6, 3);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_31, sizeof(void*)*1 + 3);
lean_dec(x_31);
x_34 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lam__0___boxed), 4, 0);
x_35 = l_Lake_LeanLib_recBuildStatic___closed__1;
x_36 = l_Lake_instDataKindFilePath;
lean_inc(x_1);
x_122 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lam__3), 9, 2);
lean_closure_set(x_122, 0, x_1);
lean_closure_set(x_122, 1, x_36);
x_123 = lean_box(x_2);
lean_inc(x_29);
x_124 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lam__2___boxed), 10, 2);
lean_closure_set(x_124, 0, x_123);
lean_closure_set(x_124, 1, x_29);
x_125 = lean_box(2);
x_126 = lean_unbox(x_125);
x_127 = l_Lake_instDecidableEqVerbosity(x_33, x_126);
x_128 = lean_box(x_2);
lean_inc(x_34);
lean_inc(x_1);
x_129 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lam__4___boxed), 15, 8);
lean_closure_set(x_129, 0, x_128);
lean_closure_set(x_129, 1, x_1);
lean_closure_set(x_129, 2, x_29);
lean_closure_set(x_129, 3, x_122);
lean_closure_set(x_129, 4, x_124);
lean_closure_set(x_129, 5, x_9);
lean_closure_set(x_129, 6, x_34);
lean_closure_set(x_129, 7, x_34);
if (x_127 == 0)
{
lean_object* x_130; 
x_130 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__0;
x_37 = x_129;
x_38 = x_130;
goto block_121;
}
else
{
if (x_2 == 0)
{
lean_object* x_131; 
x_131 = l_Lake_LeanLib_recBuildStatic___closed__3;
x_37 = x_129;
x_38 = x_131;
goto block_121;
}
else
{
lean_object* x_132; 
x_132 = l_Lake_LeanLib_recBuildStatic___closed__4;
x_37 = x_129;
x_38 = x_132;
goto block_121;
}
}
block_121:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lake_LeanLib_modulesFacet;
lean_inc(x_40);
if (lean_is_scalar(x_30)) {
 x_43 = lean_alloc_ctor(2, 2, 0);
} else {
 x_43 = x_30;
 lean_ctor_set_tag(x_43, 2);
}
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_40);
x_44 = l_Lake_LeanLib_modulesFacetConfig___closed__1;
x_45 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_1);
lean_ctor_set(x_45, 3, x_42);
x_46 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch), 9, 3);
lean_closure_set(x_46, 0, lean_box(0));
lean_closure_set(x_46, 1, x_45);
lean_closure_set(x_46, 2, lean_box(0));
x_47 = lean_alloc_closure((void*)(l_Lake_EquipT_bind), 8, 7);
lean_closure_set(x_47, 0, lean_box(0));
lean_closure_set(x_47, 1, lean_box(0));
lean_closure_set(x_47, 2, x_28);
lean_closure_set(x_47, 3, lean_box(0));
lean_closure_set(x_47, 4, lean_box(0));
lean_closure_set(x_47, 5, x_46);
lean_closure_set(x_47, 6, x_37);
x_48 = l_Lake_ensureJob___redArg(x_36, x_47, x_3, x_4, x_5, x_6, x_7, x_8);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_49, 0);
lean_dec(x_53);
x_54 = !lean_is_exclusive(x_50);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_55 = lean_ctor_get(x_50, 2);
lean_dec(x_55);
x_56 = lean_st_ref_take(x_32, x_51);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_box(1);
x_60 = lean_unbox(x_59);
x_61 = l_Lean_Name_toString(x_40, x_60, x_35);
x_62 = l_Lake_LeanLib_recBuildStatic___closed__2;
x_63 = lean_string_append(x_61, x_62);
x_64 = lean_string_append(x_63, x_38);
lean_dec(x_38);
x_65 = lean_box(0);
lean_ctor_set(x_50, 2, x_64);
x_66 = lean_unbox(x_65);
lean_ctor_set_uint8(x_50, sizeof(void*)*3, x_66);
lean_inc(x_50);
x_67 = l_Lake_Job_toOpaque___redArg(x_50);
x_68 = lean_array_push(x_57, x_67);
x_69 = lean_st_ref_set(x_32, x_68, x_58);
lean_dec(x_32);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 0);
lean_dec(x_71);
x_72 = l_Lake_Job_renew___redArg(x_50);
lean_ctor_set(x_49, 0, x_72);
lean_ctor_set(x_69, 0, x_49);
return x_69;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
lean_dec(x_69);
x_74 = l_Lake_Job_renew___redArg(x_50);
lean_ctor_set(x_49, 0, x_74);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_49);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_76 = lean_ctor_get(x_50, 0);
x_77 = lean_ctor_get(x_50, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_50);
x_78 = lean_st_ref_take(x_32, x_51);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_box(1);
x_82 = lean_unbox(x_81);
x_83 = l_Lean_Name_toString(x_40, x_82, x_35);
x_84 = l_Lake_LeanLib_recBuildStatic___closed__2;
x_85 = lean_string_append(x_83, x_84);
x_86 = lean_string_append(x_85, x_38);
lean_dec(x_38);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_88, 0, x_76);
lean_ctor_set(x_88, 1, x_77);
lean_ctor_set(x_88, 2, x_86);
x_89 = lean_unbox(x_87);
lean_ctor_set_uint8(x_88, sizeof(void*)*3, x_89);
lean_inc(x_88);
x_90 = l_Lake_Job_toOpaque___redArg(x_88);
x_91 = lean_array_push(x_79, x_90);
x_92 = lean_st_ref_set(x_32, x_91, x_80);
lean_dec(x_32);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
x_95 = l_Lake_Job_renew___redArg(x_88);
lean_ctor_set(x_49, 0, x_95);
if (lean_is_scalar(x_94)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_94;
}
lean_ctor_set(x_96, 0, x_49);
lean_ctor_set(x_96, 1, x_93);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_97 = lean_ctor_get(x_49, 1);
lean_inc(x_97);
lean_dec(x_49);
x_98 = lean_ctor_get(x_50, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_50, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 lean_ctor_release(x_50, 2);
 x_100 = x_50;
} else {
 lean_dec_ref(x_50);
 x_100 = lean_box(0);
}
x_101 = lean_st_ref_take(x_32, x_51);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_box(1);
x_105 = lean_unbox(x_104);
x_106 = l_Lean_Name_toString(x_40, x_105, x_35);
x_107 = l_Lake_LeanLib_recBuildStatic___closed__2;
x_108 = lean_string_append(x_106, x_107);
x_109 = lean_string_append(x_108, x_38);
lean_dec(x_38);
x_110 = lean_box(0);
if (lean_is_scalar(x_100)) {
 x_111 = lean_alloc_ctor(0, 3, 1);
} else {
 x_111 = x_100;
}
lean_ctor_set(x_111, 0, x_98);
lean_ctor_set(x_111, 1, x_99);
lean_ctor_set(x_111, 2, x_109);
x_112 = lean_unbox(x_110);
lean_ctor_set_uint8(x_111, sizeof(void*)*3, x_112);
lean_inc(x_111);
x_113 = l_Lake_Job_toOpaque___redArg(x_111);
x_114 = lean_array_push(x_102, x_113);
x_115 = lean_st_ref_set(x_32, x_114, x_103);
lean_dec(x_32);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_117 = x_115;
} else {
 lean_dec_ref(x_115);
 x_117 = lean_box(0);
}
x_118 = l_Lake_Job_renew___redArg(x_111);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_97);
if (lean_is_scalar(x_117)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_117;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_116);
return x_120;
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; 
x_133 = lean_ctor_get(x_9, 1);
x_134 = lean_ctor_get(x_11, 0);
x_135 = lean_ctor_get(x_11, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_11);
lean_inc(x_133);
lean_inc(x_135);
x_136 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_136, 0, x_135);
lean_closure_set(x_136, 1, x_133);
lean_inc(x_133);
lean_inc(x_135);
x_137 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_137, 0, x_135);
lean_closure_set(x_137, 1, x_133);
lean_inc(x_136);
lean_inc(x_135);
x_138 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_138, 0, x_135);
lean_closure_set(x_138, 1, x_136);
lean_inc(x_135);
lean_inc(x_134);
x_139 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_139, 0, x_134);
lean_closure_set(x_139, 1, x_135);
lean_closure_set(x_139, 2, x_133);
x_140 = l_Lake_EStateT_instFunctor___redArg(x_134);
x_141 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_141, 0, x_135);
x_142 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set(x_142, 2, x_139);
lean_ctor_set(x_142, 3, x_138);
lean_ctor_set(x_142, 4, x_137);
lean_ctor_set(x_9, 1, x_136);
lean_ctor_set(x_9, 0, x_142);
lean_inc(x_9);
x_143 = l_ReaderT_instMonad___redArg(x_9);
x_144 = l_ReaderT_instMonad___redArg(x_143);
x_145 = l_ReaderT_instMonad___redArg(x_144);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_inc(x_145);
x_147 = l_Lake_EquipT_instMonad___redArg(x_145);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_148 = x_145;
} else {
 lean_dec_ref(x_145);
 x_148 = lean_box(0);
}
x_149 = lean_ctor_get(x_6, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_6, 3);
lean_inc(x_150);
x_151 = lean_ctor_get_uint8(x_149, sizeof(void*)*1 + 3);
lean_dec(x_149);
x_152 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lam__0___boxed), 4, 0);
x_153 = l_Lake_LeanLib_recBuildStatic___closed__1;
x_154 = l_Lake_instDataKindFilePath;
lean_inc(x_1);
x_196 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lam__3), 9, 2);
lean_closure_set(x_196, 0, x_1);
lean_closure_set(x_196, 1, x_154);
x_197 = lean_box(x_2);
lean_inc(x_147);
x_198 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lam__2___boxed), 10, 2);
lean_closure_set(x_198, 0, x_197);
lean_closure_set(x_198, 1, x_147);
x_199 = lean_box(2);
x_200 = lean_unbox(x_199);
x_201 = l_Lake_instDecidableEqVerbosity(x_151, x_200);
x_202 = lean_box(x_2);
lean_inc(x_152);
lean_inc(x_1);
x_203 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lam__4___boxed), 15, 8);
lean_closure_set(x_203, 0, x_202);
lean_closure_set(x_203, 1, x_1);
lean_closure_set(x_203, 2, x_147);
lean_closure_set(x_203, 3, x_196);
lean_closure_set(x_203, 4, x_198);
lean_closure_set(x_203, 5, x_9);
lean_closure_set(x_203, 6, x_152);
lean_closure_set(x_203, 7, x_152);
if (x_201 == 0)
{
lean_object* x_204; 
x_204 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__0;
x_155 = x_203;
x_156 = x_204;
goto block_195;
}
else
{
if (x_2 == 0)
{
lean_object* x_205; 
x_205 = l_Lake_LeanLib_recBuildStatic___closed__3;
x_155 = x_203;
x_156 = x_205;
goto block_195;
}
else
{
lean_object* x_206; 
x_206 = l_Lake_LeanLib_recBuildStatic___closed__4;
x_155 = x_203;
x_156 = x_206;
goto block_195;
}
}
block_195:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_157 = lean_ctor_get(x_1, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_1, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
lean_dec(x_157);
x_160 = l_Lake_LeanLib_modulesFacet;
lean_inc(x_158);
if (lean_is_scalar(x_148)) {
 x_161 = lean_alloc_ctor(2, 2, 0);
} else {
 x_161 = x_148;
 lean_ctor_set_tag(x_161, 2);
}
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_158);
x_162 = l_Lake_LeanLib_modulesFacetConfig___closed__1;
x_163 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
lean_ctor_set(x_163, 2, x_1);
lean_ctor_set(x_163, 3, x_160);
x_164 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch), 9, 3);
lean_closure_set(x_164, 0, lean_box(0));
lean_closure_set(x_164, 1, x_163);
lean_closure_set(x_164, 2, lean_box(0));
x_165 = lean_alloc_closure((void*)(l_Lake_EquipT_bind), 8, 7);
lean_closure_set(x_165, 0, lean_box(0));
lean_closure_set(x_165, 1, lean_box(0));
lean_closure_set(x_165, 2, x_146);
lean_closure_set(x_165, 3, lean_box(0));
lean_closure_set(x_165, 4, lean_box(0));
lean_closure_set(x_165, 5, x_164);
lean_closure_set(x_165, 6, x_155);
x_166 = l_Lake_ensureJob___redArg(x_154, x_165, x_3, x_4, x_5, x_6, x_7, x_8);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_166, 1);
lean_inc(x_169);
lean_dec(x_166);
x_170 = lean_ctor_get(x_167, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_171 = x_167;
} else {
 lean_dec_ref(x_167);
 x_171 = lean_box(0);
}
x_172 = lean_ctor_get(x_168, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_168, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 lean_ctor_release(x_168, 2);
 x_174 = x_168;
} else {
 lean_dec_ref(x_168);
 x_174 = lean_box(0);
}
x_175 = lean_st_ref_take(x_150, x_169);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_box(1);
x_179 = lean_unbox(x_178);
x_180 = l_Lean_Name_toString(x_158, x_179, x_153);
x_181 = l_Lake_LeanLib_recBuildStatic___closed__2;
x_182 = lean_string_append(x_180, x_181);
x_183 = lean_string_append(x_182, x_156);
lean_dec(x_156);
x_184 = lean_box(0);
if (lean_is_scalar(x_174)) {
 x_185 = lean_alloc_ctor(0, 3, 1);
} else {
 x_185 = x_174;
}
lean_ctor_set(x_185, 0, x_172);
lean_ctor_set(x_185, 1, x_173);
lean_ctor_set(x_185, 2, x_183);
x_186 = lean_unbox(x_184);
lean_ctor_set_uint8(x_185, sizeof(void*)*3, x_186);
lean_inc(x_185);
x_187 = l_Lake_Job_toOpaque___redArg(x_185);
x_188 = lean_array_push(x_176, x_187);
x_189 = lean_st_ref_set(x_150, x_188, x_177);
lean_dec(x_150);
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_191 = x_189;
} else {
 lean_dec_ref(x_189);
 x_191 = lean_box(0);
}
x_192 = l_Lake_Job_renew___redArg(x_185);
if (lean_is_scalar(x_171)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_171;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_170);
if (lean_is_scalar(x_191)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_191;
}
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_190);
return x_194;
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; uint8_t x_278; lean_object* x_279; lean_object* x_280; 
x_207 = lean_ctor_get(x_9, 0);
x_208 = lean_ctor_get(x_9, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_9);
x_209 = lean_ctor_get(x_207, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_207, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 lean_ctor_release(x_207, 4);
 x_211 = x_207;
} else {
 lean_dec_ref(x_207);
 x_211 = lean_box(0);
}
lean_inc(x_208);
lean_inc(x_210);
x_212 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_212, 0, x_210);
lean_closure_set(x_212, 1, x_208);
lean_inc(x_208);
lean_inc(x_210);
x_213 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_213, 0, x_210);
lean_closure_set(x_213, 1, x_208);
lean_inc(x_212);
lean_inc(x_210);
x_214 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_214, 0, x_210);
lean_closure_set(x_214, 1, x_212);
lean_inc(x_210);
lean_inc(x_209);
x_215 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_215, 0, x_209);
lean_closure_set(x_215, 1, x_210);
lean_closure_set(x_215, 2, x_208);
x_216 = l_Lake_EStateT_instFunctor___redArg(x_209);
x_217 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_217, 0, x_210);
if (lean_is_scalar(x_211)) {
 x_218 = lean_alloc_ctor(0, 5, 0);
} else {
 x_218 = x_211;
}
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
lean_ctor_set(x_218, 2, x_215);
lean_ctor_set(x_218, 3, x_214);
lean_ctor_set(x_218, 4, x_213);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_212);
lean_inc(x_219);
x_220 = l_ReaderT_instMonad___redArg(x_219);
x_221 = l_ReaderT_instMonad___redArg(x_220);
x_222 = l_ReaderT_instMonad___redArg(x_221);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
lean_inc(x_222);
x_224 = l_Lake_EquipT_instMonad___redArg(x_222);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_225 = x_222;
} else {
 lean_dec_ref(x_222);
 x_225 = lean_box(0);
}
x_226 = lean_ctor_get(x_6, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_6, 3);
lean_inc(x_227);
x_228 = lean_ctor_get_uint8(x_226, sizeof(void*)*1 + 3);
lean_dec(x_226);
x_229 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lam__0___boxed), 4, 0);
x_230 = l_Lake_LeanLib_recBuildStatic___closed__1;
x_231 = l_Lake_instDataKindFilePath;
lean_inc(x_1);
x_273 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lam__3), 9, 2);
lean_closure_set(x_273, 0, x_1);
lean_closure_set(x_273, 1, x_231);
x_274 = lean_box(x_2);
lean_inc(x_224);
x_275 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lam__2___boxed), 10, 2);
lean_closure_set(x_275, 0, x_274);
lean_closure_set(x_275, 1, x_224);
x_276 = lean_box(2);
x_277 = lean_unbox(x_276);
x_278 = l_Lake_instDecidableEqVerbosity(x_228, x_277);
x_279 = lean_box(x_2);
lean_inc(x_229);
lean_inc(x_1);
x_280 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lam__4___boxed), 15, 8);
lean_closure_set(x_280, 0, x_279);
lean_closure_set(x_280, 1, x_1);
lean_closure_set(x_280, 2, x_224);
lean_closure_set(x_280, 3, x_273);
lean_closure_set(x_280, 4, x_275);
lean_closure_set(x_280, 5, x_219);
lean_closure_set(x_280, 6, x_229);
lean_closure_set(x_280, 7, x_229);
if (x_278 == 0)
{
lean_object* x_281; 
x_281 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__0;
x_232 = x_280;
x_233 = x_281;
goto block_272;
}
else
{
if (x_2 == 0)
{
lean_object* x_282; 
x_282 = l_Lake_LeanLib_recBuildStatic___closed__3;
x_232 = x_280;
x_233 = x_282;
goto block_272;
}
else
{
lean_object* x_283; 
x_283 = l_Lake_LeanLib_recBuildStatic___closed__4;
x_232 = x_280;
x_233 = x_283;
goto block_272;
}
}
block_272:
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_234 = lean_ctor_get(x_1, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_1, 1);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 0);
lean_inc(x_236);
lean_dec(x_234);
x_237 = l_Lake_LeanLib_modulesFacet;
lean_inc(x_235);
if (lean_is_scalar(x_225)) {
 x_238 = lean_alloc_ctor(2, 2, 0);
} else {
 x_238 = x_225;
 lean_ctor_set_tag(x_238, 2);
}
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_235);
x_239 = l_Lake_LeanLib_modulesFacetConfig___closed__1;
x_240 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
lean_ctor_set(x_240, 2, x_1);
lean_ctor_set(x_240, 3, x_237);
x_241 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch), 9, 3);
lean_closure_set(x_241, 0, lean_box(0));
lean_closure_set(x_241, 1, x_240);
lean_closure_set(x_241, 2, lean_box(0));
x_242 = lean_alloc_closure((void*)(l_Lake_EquipT_bind), 8, 7);
lean_closure_set(x_242, 0, lean_box(0));
lean_closure_set(x_242, 1, lean_box(0));
lean_closure_set(x_242, 2, x_223);
lean_closure_set(x_242, 3, lean_box(0));
lean_closure_set(x_242, 4, lean_box(0));
lean_closure_set(x_242, 5, x_241);
lean_closure_set(x_242, 6, x_232);
x_243 = l_Lake_ensureJob___redArg(x_231, x_242, x_3, x_4, x_5, x_6, x_7, x_8);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_243, 1);
lean_inc(x_246);
lean_dec(x_243);
x_247 = lean_ctor_get(x_244, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_248 = x_244;
} else {
 lean_dec_ref(x_244);
 x_248 = lean_box(0);
}
x_249 = lean_ctor_get(x_245, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_245, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 lean_ctor_release(x_245, 2);
 x_251 = x_245;
} else {
 lean_dec_ref(x_245);
 x_251 = lean_box(0);
}
x_252 = lean_st_ref_take(x_227, x_246);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
x_255 = lean_box(1);
x_256 = lean_unbox(x_255);
x_257 = l_Lean_Name_toString(x_235, x_256, x_230);
x_258 = l_Lake_LeanLib_recBuildStatic___closed__2;
x_259 = lean_string_append(x_257, x_258);
x_260 = lean_string_append(x_259, x_233);
lean_dec(x_233);
x_261 = lean_box(0);
if (lean_is_scalar(x_251)) {
 x_262 = lean_alloc_ctor(0, 3, 1);
} else {
 x_262 = x_251;
}
lean_ctor_set(x_262, 0, x_249);
lean_ctor_set(x_262, 1, x_250);
lean_ctor_set(x_262, 2, x_260);
x_263 = lean_unbox(x_261);
lean_ctor_set_uint8(x_262, sizeof(void*)*3, x_263);
lean_inc(x_262);
x_264 = l_Lake_Job_toOpaque___redArg(x_262);
x_265 = lean_array_push(x_253, x_264);
x_266 = lean_st_ref_set(x_227, x_265, x_254);
lean_dec(x_227);
x_267 = lean_ctor_get(x_266, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_268 = x_266;
} else {
 lean_dec_ref(x_266);
 x_268 = lean_box(0);
}
x_269 = l_Lake_Job_renew___redArg(x_262);
if (lean_is_scalar(x_248)) {
 x_270 = lean_alloc_ctor(0, 2, 0);
} else {
 x_270 = x_248;
}
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_247);
if (lean_is_scalar(x_268)) {
 x_271 = lean_alloc_ctor(0, 2, 0);
} else {
 x_271 = x_268;
}
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_267);
return x_271;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_LeanLib_recBuildStatic___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lake_LeanLib_recBuildStatic___lam__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_1);
lean_dec(x_1);
x_17 = l_Lake_LeanLib_recBuildStatic___lam__4(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lake_LeanLib_recBuildStatic(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type mismtach in target '", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("': expected '", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', got ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
lean_inc_n(x_2, 2);
x_11 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(x_1, x_2, x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_16 = x_11;
} else {
 lean_dec_ref(x_11);
 x_16 = lean_box(0);
}
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_18 = x_12;
} else {
 lean_dec_ref(x_12);
 x_18 = lean_box(0);
}
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
x_20 = l_Lake_instDataKindFilePath;
x_21 = lean_name_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_44; 
lean_dec(x_14);
x_22 = lean_box(x_21);
x_23 = lean_alloc_closure((void*)(l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(x_23, 0, x_22);
x_44 = l_Lean_Name_isAnonymous(x_19);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_box(x_44);
x_46 = lean_alloc_closure((void*)(l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(x_46, 0, x_45);
x_47 = l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__3;
x_48 = lean_unbox(x_9);
x_49 = l_Lean_Name_toString(x_19, x_48, x_46);
x_50 = lean_string_append(x_47, x_49);
lean_dec(x_49);
x_51 = lean_string_append(x_50, x_47);
x_24 = x_51;
goto block_43;
}
else
{
lean_object* x_52; 
lean_dec(x_19);
x_52 = l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__4;
x_24 = x_52;
goto block_43;
}
block_43:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_25 = l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__0;
x_26 = l_Lake_PartialBuildKey_toString(x_2);
x_27 = lean_string_append(x_25, x_26);
lean_dec(x_26);
x_28 = l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__1;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_unbox(x_9);
x_31 = l_Lean_Name_toString(x_20, x_30, x_23);
x_32 = lean_string_append(x_29, x_31);
lean_dec(x_31);
x_33 = l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__2;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_string_append(x_34, x_24);
lean_dec(x_24);
x_36 = lean_box(3);
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_35);
x_38 = lean_unbox(x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_38);
x_39 = lean_array_get_size(x_17);
x_40 = lean_array_push(x_17, x_37);
if (lean_is_scalar(x_18)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_18;
 lean_ctor_set_tag(x_41, 1);
}
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
if (lean_is_scalar(x_16)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_16;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_15);
return x_42;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_19);
lean_dec(x_2);
if (lean_is_scalar(x_18)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_18;
}
lean_ctor_set(x_53, 0, x_14);
lean_ctor_set(x_53, 1, x_17);
if (lean_is_scalar(x_16)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_16;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_15);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_11);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_11, 0);
lean_dec(x_56);
x_57 = !lean_is_exclusive(x_12);
if (x_57 == 0)
{
return x_11;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_12, 0);
x_59 = lean_ctor_get(x_12, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_12);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_11, 0, x_60);
return x_11;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_11, 1);
lean_inc(x_61);
lean_dec(x_11);
x_62 = lean_ctor_get(x_12, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_12, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_64 = x_12;
} else {
 lean_dec_ref(x_12);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_61);
return x_66;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_array_uget(x_4, x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_15 = l_Lake_ModuleFacet_fetch___redArg(x_14, x_1, x_5, x_6, x_7, x_8, x_9, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_box(0);
x_21 = lean_array_uset(x_4, x_3, x_20);
x_22 = 1;
x_23 = lean_usize_add(x_3, x_22);
x_24 = lean_array_uset(x_21, x_3, x_18);
x_3 = x_23;
x_4 = x_24;
x_9 = x_19;
x_10 = x_17;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_15, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
return x_15;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_15, 0, x_31);
return x_15;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_dec(x_15);
x_33 = lean_ctor_get(x_16, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_35 = x_16;
} else {
 lean_dec_ref(x_16);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_32);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_array_uget(x_4, x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0(x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = lean_array_uset(x_4, x_3, x_21);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_25 = lean_array_uset(x_22, x_3, x_19);
x_3 = x_24;
x_4 = x_25;
x_9 = x_20;
x_10 = x_18;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_16, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_17);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_16, 0, x_32);
return x_16;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_dec(x_16);
x_34 = lean_ctor_get(x_17, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_17, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_36 = x_17;
} else {
 lean_dec_ref(x_17);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__3_spec__3(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_19; 
x_19 = lean_usize_dec_eq(x_3, x_4);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_array_uget(x_2, x_3);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 2);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 8);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(x_1);
x_25 = lean_apply_1(x_23, x_24);
x_26 = lean_array_size(x_25);
x_27 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_28 = l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__1(x_20, x_26, x_27, x_25, x_6, x_7, x_8, x_9, x_10, x_11);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = l_Array_append___redArg(x_5, x_31);
lean_dec(x_31);
x_12 = x_33;
x_13 = x_32;
x_14 = x_30;
goto block_18;
}
else
{
lean_object* x_34; 
lean_dec(x_29);
lean_dec(x_5);
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_dec(x_28);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_12 = x_36;
x_13 = x_37;
x_14 = x_35;
goto block_18;
}
else
{
lean_dec(x_34);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_28;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_5);
lean_ctor_set(x_38, 1, x_10);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_11);
return x_39;
}
block_18:
{
size_t x_15; size_t x_16; 
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
x_5 = x_12;
x_10 = x_13;
x_11 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__3(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_19; 
x_19 = lean_usize_dec_eq(x_3, x_4);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_array_uget(x_2, x_3);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 2);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 8);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(x_1);
x_25 = lean_apply_1(x_23, x_24);
x_26 = lean_array_size(x_25);
x_27 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_28 = l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__1(x_20, x_26, x_27, x_25, x_6, x_7, x_8, x_9, x_10, x_11);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = l_Array_append___redArg(x_5, x_31);
lean_dec(x_31);
x_12 = x_33;
x_13 = x_32;
x_14 = x_30;
goto block_18;
}
else
{
lean_object* x_34; 
lean_dec(x_29);
lean_dec(x_5);
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_dec(x_28);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_12 = x_36;
x_13 = x_37;
x_14 = x_35;
goto block_18;
}
else
{
lean_dec(x_34);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_28;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_5);
lean_ctor_set(x_38, 1, x_10);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_11);
return x_39;
}
block_18:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_17 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__3_spec__3(x_1, x_2, x_16, x_4, x_12, x_6, x_7, x_8, x_9, x_13, x_14);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_JobResult_prependLog___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_35; 
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
x_14 = l_Lake_instDataKindFilePath;
x_15 = lean_array_get_size(x_6);
lean_dec(x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
lean_dec(x_13);
x_96 = lean_ctor_get(x_11, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_11, 1);
lean_inc(x_97);
lean_dec(x_11);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_dec(x_96);
x_100 = lean_string_utf8_byte_size(x_98);
x_101 = lean_unsigned_to_nat(0u);
x_102 = lean_nat_dec_eq(x_100, x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_103 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__3;
x_104 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_98, x_100, x_101);
x_105 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_98, x_104, x_100);
x_106 = lean_string_utf8_extract(x_98, x_104, x_105);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_98);
x_107 = lean_string_append(x_103, x_106);
lean_dec(x_106);
x_108 = lean_box(1);
x_109 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_109, 0, x_107);
x_110 = lean_unbox(x_108);
lean_ctor_set_uint8(x_109, sizeof(void*)*1, x_110);
x_111 = lean_box(0);
x_112 = lean_array_push(x_97, x_109);
x_113 = l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5___lam__1(x_99, x_111, x_2, x_3, x_4, x_5, x_112, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = x_113;
goto block_95;
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_100);
lean_dec(x_98);
x_114 = lean_box(0);
x_115 = l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5___lam__1(x_99, x_114, x_2, x_3, x_4, x_5, x_97, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = x_115;
goto block_95;
}
}
else
{
lean_object* x_116; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_116 = lean_ctor_get(x_11, 1);
lean_inc(x_116);
lean_dec(x_11);
x_16 = x_116;
x_17 = x_12;
goto block_34;
}
block_34:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
lean_inc(x_16);
x_18 = l_Array_shrink___redArg(x_16, x_15);
x_19 = lean_array_get_size(x_16);
x_20 = l_Array_extract___redArg(x_16, x_15, x_19);
lean_dec(x_16);
x_21 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__0;
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_box(0);
x_24 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__2;
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_unbox(x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_26);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_task_pure(x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_14);
lean_ctor_set(x_30, 2, x_21);
x_31 = lean_unbox(x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_31);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_18);
if (lean_is_scalar(x_13)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_13;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_17);
return x_33;
}
block_95:
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_36, 0);
x_40 = lean_ctor_get(x_36, 1);
x_41 = lean_array_get_size(x_40);
x_42 = lean_nat_dec_lt(x_15, x_41);
if (x_42 == 0)
{
lean_dec(x_41);
lean_free_object(x_36);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_15);
return x_35;
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_35);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_35, 1);
lean_dec(x_44);
x_45 = lean_ctor_get(x_35, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_39);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_39, 0);
x_48 = lean_ctor_get(x_39, 1);
lean_dec(x_48);
lean_inc(x_40);
x_49 = l_Array_shrink___redArg(x_40, x_15);
x_50 = l_Array_extract___redArg(x_40, x_15, x_41);
lean_dec(x_40);
x_51 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5___lam__0), 2, 1);
lean_closure_set(x_51, 0, x_50);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_unbox(x_8);
x_54 = lean_task_map(x_51, x_47, x_52, x_53);
lean_ctor_set(x_39, 1, x_14);
lean_ctor_set(x_39, 0, x_54);
lean_ctor_set(x_36, 1, x_49);
return x_35;
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; 
x_55 = lean_ctor_get(x_39, 0);
x_56 = lean_ctor_get(x_39, 2);
x_57 = lean_ctor_get_uint8(x_39, sizeof(void*)*3);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_39);
lean_inc(x_40);
x_58 = l_Array_shrink___redArg(x_40, x_15);
x_59 = l_Array_extract___redArg(x_40, x_15, x_41);
lean_dec(x_40);
x_60 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5___lam__0), 2, 1);
lean_closure_set(x_60, 0, x_59);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_unbox(x_8);
x_63 = lean_task_map(x_60, x_55, x_61, x_62);
x_64 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_14);
lean_ctor_set(x_64, 2, x_56);
lean_ctor_set_uint8(x_64, sizeof(void*)*3, x_57);
lean_ctor_set(x_36, 1, x_58);
lean_ctor_set(x_36, 0, x_64);
return x_35;
}
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_35);
x_65 = lean_ctor_get(x_39, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_39, 2);
lean_inc(x_66);
x_67 = lean_ctor_get_uint8(x_39, sizeof(void*)*3);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 x_68 = x_39;
} else {
 lean_dec_ref(x_39);
 x_68 = lean_box(0);
}
lean_inc(x_40);
x_69 = l_Array_shrink___redArg(x_40, x_15);
x_70 = l_Array_extract___redArg(x_40, x_15, x_41);
lean_dec(x_40);
x_71 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5___lam__0), 2, 1);
lean_closure_set(x_71, 0, x_70);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_unbox(x_8);
x_74 = lean_task_map(x_71, x_65, x_72, x_73);
if (lean_is_scalar(x_68)) {
 x_75 = lean_alloc_ctor(0, 3, 1);
} else {
 x_75 = x_68;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_14);
lean_ctor_set(x_75, 2, x_66);
lean_ctor_set_uint8(x_75, sizeof(void*)*3, x_67);
lean_ctor_set(x_36, 1, x_69);
lean_ctor_set(x_36, 0, x_75);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_36);
lean_ctor_set(x_76, 1, x_37);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_36, 0);
x_78 = lean_ctor_get(x_36, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_36);
x_79 = lean_array_get_size(x_78);
x_80 = lean_nat_dec_lt(x_15, x_79);
if (x_80 == 0)
{
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_37);
lean_dec(x_15);
return x_35;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_81 = x_35;
} else {
 lean_dec_ref(x_35);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get(x_77, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_77, 2);
lean_inc(x_83);
x_84 = lean_ctor_get_uint8(x_77, sizeof(void*)*3);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 x_85 = x_77;
} else {
 lean_dec_ref(x_77);
 x_85 = lean_box(0);
}
lean_inc(x_78);
x_86 = l_Array_shrink___redArg(x_78, x_15);
x_87 = l_Array_extract___redArg(x_78, x_15, x_79);
lean_dec(x_78);
x_88 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5___lam__0), 2, 1);
lean_closure_set(x_88, 0, x_87);
x_89 = lean_unsigned_to_nat(0u);
x_90 = lean_unbox(x_8);
x_91 = lean_task_map(x_88, x_82, x_89, x_90);
if (lean_is_scalar(x_85)) {
 x_92 = lean_alloc_ctor(0, 3, 1);
} else {
 x_92 = x_85;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_14);
lean_ctor_set(x_92, 2, x_83);
lean_ctor_set_uint8(x_92, sizeof(void*)*3, x_84);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_86);
if (lean_is_scalar(x_81)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_81;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_37);
return x_94;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_111; lean_object* x_112; 
lean_inc(x_7);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_111 = lean_apply_6(x_7, x_1, x_8, x_9, x_10, x_11, x_12);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
lean_dec(x_111);
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
lean_dec(x_112);
x_116 = lean_ctor_get(x_113, 0);
lean_inc(x_116);
lean_dec(x_113);
x_117 = lean_io_wait(x_116, x_114);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
lean_dec(x_117);
x_121 = lean_ctor_get(x_118, 0);
lean_inc(x_121);
lean_dec(x_118);
x_122 = lean_ctor_get(x_119, 0);
lean_inc(x_122);
lean_dec(x_119);
x_123 = lean_unsigned_to_nat(0u);
x_124 = lean_array_get_size(x_122);
x_125 = lean_nat_dec_lt(x_123, x_124);
if (x_125 == 0)
{
lean_dec(x_124);
lean_dec(x_122);
x_83 = x_121;
x_84 = x_115;
x_85 = x_120;
goto block_110;
}
else
{
uint8_t x_126; 
x_126 = lean_nat_dec_le(x_124, x_124);
if (x_126 == 0)
{
lean_dec(x_124);
lean_dec(x_122);
x_83 = x_121;
x_84 = x_115;
x_85 = x_120;
goto block_110;
}
else
{
lean_object* x_127; size_t x_128; size_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_127 = lean_box(0);
x_128 = 0;
x_129 = lean_usize_of_nat(x_124);
lean_dec(x_124);
x_130 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1(x_122, x_128, x_129, x_127, x_115, x_120);
lean_dec(x_122);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_83 = x_121;
x_84 = x_133;
x_85 = x_132;
goto block_110;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_134 = lean_ctor_get(x_118, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_117, 1);
lean_inc(x_135);
lean_dec(x_117);
x_136 = lean_ctor_get(x_118, 0);
lean_inc(x_136);
lean_dec(x_118);
x_137 = lean_ctor_get(x_134, 0);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_unsigned_to_nat(0u);
x_139 = lean_array_get_size(x_137);
x_140 = lean_nat_dec_lt(x_138, x_139);
if (x_140 == 0)
{
lean_dec(x_139);
lean_dec(x_137);
x_13 = x_136;
x_14 = x_115;
x_15 = x_135;
goto block_18;
}
else
{
uint8_t x_141; 
x_141 = lean_nat_dec_le(x_139, x_139);
if (x_141 == 0)
{
lean_dec(x_139);
lean_dec(x_137);
x_13 = x_136;
x_14 = x_115;
x_15 = x_135;
goto block_18;
}
else
{
lean_object* x_142; size_t x_143; size_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_142 = lean_box(0);
x_143 = 0;
x_144 = lean_usize_of_nat(x_139);
lean_dec(x_139);
x_145 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1(x_137, x_143, x_144, x_142, x_115, x_135);
lean_dec(x_137);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_13 = x_136;
x_14 = x_148;
x_15 = x_147;
goto block_18;
}
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_149 = !lean_is_exclusive(x_111);
if (x_149 == 0)
{
lean_object* x_150; uint8_t x_151; 
x_150 = lean_ctor_get(x_111, 0);
lean_dec(x_150);
x_151 = !lean_is_exclusive(x_112);
if (x_151 == 0)
{
return x_111;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_112, 0);
x_153 = lean_ctor_get(x_112, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_112);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
lean_ctor_set(x_111, 0, x_154);
return x_111;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_155 = lean_ctor_get(x_111, 1);
lean_inc(x_155);
lean_dec(x_111);
x_156 = lean_ctor_get(x_112, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_112, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_158 = x_112;
} else {
 lean_dec_ref(x_112);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_155);
return x_160;
}
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
block_34:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = l_Array_append___redArg(x_20, x_22);
lean_dec(x_22);
x_25 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__2;
x_26 = l_Lake_buildStaticLib(x_23, x_24, x_2, x_7, x_8, x_9, x_10, x_25, x_21);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_19);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_19);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
block_82:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; lean_object* x_49; 
x_38 = lean_ctor_get(x_3, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_4, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_3, 6);
lean_inc(x_40);
x_41 = lean_ctor_get(x_3, 8);
lean_inc(x_41);
lean_dec(x_3);
x_42 = lean_ctor_get(x_38, 6);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_ctor_get(x_4, 4);
lean_inc(x_43);
lean_dec(x_4);
x_44 = lean_ctor_get(x_39, 6);
lean_inc(x_44);
lean_dec(x_39);
x_45 = l_Array_append___redArg(x_42, x_44);
lean_dec(x_44);
x_46 = lean_array_size(x_45);
x_47 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_48 = l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__2(x_5, x_46, x_47, x_45, x_7, x_8, x_9, x_10, x_36, x_37);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
if (x_2 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = l_System_FilePath_normalize(x_40);
x_54 = l_Lake_joinRelative(x_6, x_53);
lean_dec(x_53);
x_55 = l_System_FilePath_normalize(x_41);
x_56 = l_Lake_joinRelative(x_54, x_55);
lean_dec(x_55);
x_57 = l_Lake_nameToStaticLib(x_43);
x_58 = l_Lake_joinRelative(x_56, x_57);
lean_dec(x_57);
x_19 = x_52;
x_20 = x_35;
x_21 = x_50;
x_22 = x_51;
x_23 = x_58;
goto block_34;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_59 = lean_ctor_get(x_48, 1);
lean_inc(x_59);
lean_dec(x_48);
x_60 = lean_ctor_get(x_49, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_49, 1);
lean_inc(x_61);
lean_dec(x_49);
x_62 = l_System_FilePath_normalize(x_40);
x_63 = l_Lake_joinRelative(x_6, x_62);
lean_dec(x_62);
x_64 = l_System_FilePath_normalize(x_41);
x_65 = l_Lake_joinRelative(x_63, x_64);
lean_dec(x_64);
x_66 = l_Lake_nameToStaticLib(x_43);
x_67 = l_Lake_LeanLib_recBuildStatic___lam__4___closed__0;
x_68 = l_System_FilePath_addExtension(x_66, x_67);
x_69 = l_Lake_joinRelative(x_65, x_68);
lean_dec(x_68);
x_19 = x_61;
x_20 = x_35;
x_21 = x_59;
x_22 = x_60;
x_23 = x_69;
goto block_34;
}
}
else
{
uint8_t x_70; 
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_35);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_70 = !lean_is_exclusive(x_48);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_48, 0);
lean_dec(x_71);
x_72 = !lean_is_exclusive(x_49);
if (x_72 == 0)
{
return x_48;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_49, 0);
x_74 = lean_ctor_get(x_49, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_49);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set(x_48, 0, x_75);
return x_48;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_48, 1);
lean_inc(x_76);
lean_dec(x_48);
x_77 = lean_ctor_get(x_49, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_49, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_79 = x_49;
} else {
 lean_dec_ref(x_49);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_76);
return x_81;
}
}
}
block_110:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = l_Lake_LeanLib_recBuildStatic___lam__4___closed__1;
x_87 = lean_unsigned_to_nat(0u);
x_88 = lean_array_get_size(x_83);
x_89 = lean_nat_dec_lt(x_87, x_88);
if (x_89 == 0)
{
lean_dec(x_88);
lean_dec(x_83);
x_35 = x_86;
x_36 = x_84;
x_37 = x_85;
goto block_82;
}
else
{
uint8_t x_90; 
x_90 = lean_nat_dec_le(x_88, x_88);
if (x_90 == 0)
{
lean_dec(x_88);
lean_dec(x_83);
x_35 = x_86;
x_36 = x_84;
x_37 = x_85;
goto block_82;
}
else
{
size_t x_91; size_t x_92; lean_object* x_93; lean_object* x_94; 
x_91 = 0;
x_92 = lean_usize_of_nat(x_88);
lean_dec(x_88);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_93 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__3(x_2, x_83, x_91, x_92, x_86, x_7, x_8, x_9, x_10, x_84, x_85);
lean_dec(x_83);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec(x_94);
x_35 = x_96;
x_36 = x_97;
x_37 = x_95;
goto block_82;
}
else
{
uint8_t x_98; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_98 = !lean_is_exclusive(x_93);
if (x_98 == 0)
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_ctor_get(x_93, 0);
lean_dec(x_99);
x_100 = !lean_is_exclusive(x_94);
if (x_100 == 0)
{
return x_93;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_94, 0);
x_102 = lean_ctor_get(x_94, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_94);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set(x_93, 0, x_103);
return x_93;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_93, 1);
lean_inc(x_104);
lean_dec(x_93);
x_105 = lean_ctor_get(x_94, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_94, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_107 = x_94;
} else {
 lean_dec_ref(x_94);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_104);
return x_109;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_100; uint8_t x_101; uint8_t x_102; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 3);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_9, sizeof(void*)*1 + 3);
lean_dec(x_9);
x_12 = l_Lake_LeanLib_recBuildStatic___closed__1;
x_100 = lean_box(2);
x_101 = lean_unbox(x_100);
x_102 = l_Lake_instDecidableEqVerbosity(x_11, x_101);
if (x_102 == 0)
{
lean_object* x_103; 
x_103 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__0;
x_13 = x_103;
goto block_99;
}
else
{
if (x_3 == 0)
{
lean_object* x_104; 
x_104 = l_Lake_LeanLib_recBuildStatic___closed__3;
x_13 = x_104;
goto block_99;
}
else
{
lean_object* x_105; 
x_105 = l_Lake_LeanLib_recBuildStatic___closed__4;
x_13 = x_105;
goto block_99;
}
}
block_99:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_14, 3);
lean_inc(x_19);
lean_dec(x_14);
x_20 = l_Lake_LeanLib_modulesFacet;
lean_inc(x_15);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_15);
x_22 = l_Lake_LeanLib_modulesFacetConfig___closed__1;
lean_inc(x_2);
x_23 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_2);
lean_ctor_set(x_23, 3, x_20);
x_24 = lean_box(x_3);
x_25 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed), 12, 6);
lean_closure_set(x_25, 0, x_23);
lean_closure_set(x_25, 1, x_24);
lean_closure_set(x_25, 2, x_19);
lean_closure_set(x_25, 3, x_16);
lean_closure_set(x_25, 4, x_2);
lean_closure_set(x_25, 5, x_18);
x_26 = l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5(x_25, x_1, x_4, x_5, x_6, x_7, x_8);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_27, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_33 = lean_ctor_get(x_28, 2);
lean_dec(x_33);
x_34 = lean_st_ref_take(x_10, x_29);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_box(1);
x_38 = lean_unbox(x_37);
x_39 = l_Lean_Name_toString(x_15, x_38, x_12);
x_40 = l_Lake_LeanLib_recBuildStatic___closed__2;
x_41 = lean_string_append(x_39, x_40);
x_42 = lean_string_append(x_41, x_13);
lean_dec(x_13);
x_43 = lean_box(0);
lean_ctor_set(x_28, 2, x_42);
x_44 = lean_unbox(x_43);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_44);
lean_inc(x_28);
x_45 = l_Lake_Job_toOpaque___redArg(x_28);
x_46 = lean_array_push(x_35, x_45);
x_47 = lean_st_ref_set(x_10, x_46, x_36);
lean_dec(x_10);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = l_Lake_Job_renew___redArg(x_28);
lean_ctor_set(x_27, 0, x_50);
lean_ctor_set(x_47, 0, x_27);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = l_Lake_Job_renew___redArg(x_28);
lean_ctor_set(x_27, 0, x_52);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_27);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_54 = lean_ctor_get(x_28, 0);
x_55 = lean_ctor_get(x_28, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_28);
x_56 = lean_st_ref_take(x_10, x_29);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_box(1);
x_60 = lean_unbox(x_59);
x_61 = l_Lean_Name_toString(x_15, x_60, x_12);
x_62 = l_Lake_LeanLib_recBuildStatic___closed__2;
x_63 = lean_string_append(x_61, x_62);
x_64 = lean_string_append(x_63, x_13);
lean_dec(x_13);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_66, 0, x_54);
lean_ctor_set(x_66, 1, x_55);
lean_ctor_set(x_66, 2, x_64);
x_67 = lean_unbox(x_65);
lean_ctor_set_uint8(x_66, sizeof(void*)*3, x_67);
lean_inc(x_66);
x_68 = l_Lake_Job_toOpaque___redArg(x_66);
x_69 = lean_array_push(x_57, x_68);
x_70 = lean_st_ref_set(x_10, x_69, x_58);
lean_dec(x_10);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
x_73 = l_Lake_Job_renew___redArg(x_66);
lean_ctor_set(x_27, 0, x_73);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_27);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_75 = lean_ctor_get(x_27, 1);
lean_inc(x_75);
lean_dec(x_27);
x_76 = lean_ctor_get(x_28, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_28, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 x_78 = x_28;
} else {
 lean_dec_ref(x_28);
 x_78 = lean_box(0);
}
x_79 = lean_st_ref_take(x_10, x_29);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_box(1);
x_83 = lean_unbox(x_82);
x_84 = l_Lean_Name_toString(x_15, x_83, x_12);
x_85 = l_Lake_LeanLib_recBuildStatic___closed__2;
x_86 = lean_string_append(x_84, x_85);
x_87 = lean_string_append(x_86, x_13);
lean_dec(x_13);
x_88 = lean_box(0);
if (lean_is_scalar(x_78)) {
 x_89 = lean_alloc_ctor(0, 3, 1);
} else {
 x_89 = x_78;
}
lean_ctor_set(x_89, 0, x_76);
lean_ctor_set(x_89, 1, x_77);
lean_ctor_set(x_89, 2, x_87);
x_90 = lean_unbox(x_88);
lean_ctor_set_uint8(x_89, sizeof(void*)*3, x_90);
lean_inc(x_89);
x_91 = l_Lake_Job_toOpaque___redArg(x_89);
x_92 = lean_array_push(x_80, x_91);
x_93 = lean_st_ref_set(x_10, x_92, x_81);
lean_dec(x_10);
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
x_96 = l_Lake_Job_renew___redArg(x_89);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_75);
if (lean_is_scalar(x_95)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_95;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_94);
return x_98;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_LeanLib_staticFacetConfig_spec__7(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lake_mkRelPathString(x_2);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_Lean_Json_compress(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
x_10 = l_Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0(x_2, x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at___Lake_LeanLib_staticFacetConfig_spec__7(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_staticFacetConfig___lam__0), 7, 0);
x_2 = lean_alloc_closure((void*)(l_Lake_LeanLib_staticFacetConfig___lam__1___boxed), 2, 0);
x_3 = l_Lake_instDataKindFilePath;
x_4 = l_Lake_LeanLib_modulesFacetConfig___closed__1;
x_5 = lean_box(1);
x_6 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
x_7 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_7);
x_8 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*4 + 1, x_8);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__2(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__3_spec__3(x_12, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__3(x_12, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0___lam__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_LeanLib_staticFacetConfig_spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_stdFormat___at___Lake_LeanLib_staticFacetConfig_spec__7(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_LeanLib_staticFacetConfig___lam__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
x_10 = l_Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0(x_2, x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_staticFacetConfig___lam__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_staticExportFacetConfig___lam__0), 7, 0);
x_2 = l_Lake_LeanLib_staticExportFacetConfig___closed__0;
x_3 = l_Lake_instDataKindFilePath;
x_4 = l_Lake_LeanLib_modulesFacetConfig___closed__1;
x_5 = lean_box(1);
x_6 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
x_7 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_7);
x_8 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*4 + 1, x_8);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildShared_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
lean_inc_n(x_2, 2);
x_11 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(x_1, x_2, x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_16 = x_11;
} else {
 lean_dec_ref(x_11);
 x_16 = lean_box(0);
}
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_18 = x_12;
} else {
 lean_dec_ref(x_12);
 x_18 = lean_box(0);
}
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
x_20 = l_Lake_instDataKindDynlib;
x_21 = lean_name_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_44; 
lean_dec(x_14);
x_22 = lean_box(x_21);
x_23 = lean_alloc_closure((void*)(l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(x_23, 0, x_22);
x_44 = l_Lean_Name_isAnonymous(x_19);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_box(x_44);
x_46 = lean_alloc_closure((void*)(l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(x_46, 0, x_45);
x_47 = l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__3;
x_48 = lean_unbox(x_9);
x_49 = l_Lean_Name_toString(x_19, x_48, x_46);
x_50 = lean_string_append(x_47, x_49);
lean_dec(x_49);
x_51 = lean_string_append(x_50, x_47);
x_24 = x_51;
goto block_43;
}
else
{
lean_object* x_52; 
lean_dec(x_19);
x_52 = l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__4;
x_24 = x_52;
goto block_43;
}
block_43:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_25 = l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__0;
x_26 = l_Lake_PartialBuildKey_toString(x_2);
x_27 = lean_string_append(x_25, x_26);
lean_dec(x_26);
x_28 = l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__1;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_unbox(x_9);
x_31 = l_Lean_Name_toString(x_20, x_30, x_23);
x_32 = lean_string_append(x_29, x_31);
lean_dec(x_31);
x_33 = l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__2;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_string_append(x_34, x_24);
lean_dec(x_24);
x_36 = lean_box(3);
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_35);
x_38 = lean_unbox(x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_38);
x_39 = lean_array_get_size(x_17);
x_40 = lean_array_push(x_17, x_37);
if (lean_is_scalar(x_18)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_18;
 lean_ctor_set_tag(x_41, 1);
}
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
if (lean_is_scalar(x_16)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_16;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_15);
return x_42;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_19);
lean_dec(x_2);
if (lean_is_scalar(x_18)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_18;
}
lean_ctor_set(x_53, 0, x_14);
lean_ctor_set(x_53, 1, x_17);
if (lean_is_scalar(x_16)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_16;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_15);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_11);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_11, 0);
lean_dec(x_56);
x_57 = !lean_is_exclusive(x_12);
if (x_57 == 0)
{
return x_11;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_12, 0);
x_59 = lean_ctor_get(x_12, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_12);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_11, 0, x_60);
return x_11;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_11, 1);
lean_inc(x_61);
lean_dec(x_11);
x_62 = lean_ctor_get(x_12, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_12, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_64 = x_12;
} else {
 lean_dec_ref(x_12);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_61);
return x_66;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; size_t x_20; size_t x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
x_12 = lean_array_get_size(x_10);
x_13 = l_Lean_Name_hash___override(x_11);
lean_dec(x_11);
x_14 = 32;
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = lean_uint64_xor(x_13, x_15);
x_17 = 16;
x_18 = lean_uint64_shift_right(x_16, x_17);
x_19 = lean_uint64_xor(x_16, x_18);
x_20 = lean_uint64_to_usize(x_19);
x_21 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_22 = 1;
x_23 = lean_usize_sub(x_21, x_22);
x_24 = lean_usize_land(x_20, x_23);
x_25 = lean_array_uget(x_10, x_24);
x_26 = l_Std_DHashMap_Internal_AssocList_contains___at___Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg(x_2, x_25);
if (x_26 == 0)
{
lean_dec(x_1);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_3);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_28 = lean_ctor_get(x_3, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_3, 0);
lean_dec(x_29);
x_30 = lean_box(0);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_9, x_31);
lean_dec(x_9);
lean_inc(x_2);
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set(x_33, 2, x_25);
x_34 = lean_array_uset(x_10, x_24, x_33);
x_35 = lean_unsigned_to_nat(4u);
x_36 = lean_nat_mul(x_32, x_35);
x_37 = lean_unsigned_to_nat(3u);
x_38 = lean_nat_div(x_36, x_37);
lean_dec(x_36);
x_39 = lean_array_get_size(x_34);
x_40 = lean_nat_dec_le(x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3___redArg(x_34);
lean_ctor_set(x_3, 1, x_41);
lean_ctor_set(x_3, 0, x_32);
x_5 = x_3;
goto block_8;
}
else
{
lean_ctor_set(x_3, 1, x_34);
lean_ctor_set(x_3, 0, x_32);
x_5 = x_3;
goto block_8;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_3);
x_42 = lean_box(0);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_9, x_43);
lean_dec(x_9);
lean_inc(x_2);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_2);
lean_ctor_set(x_45, 1, x_42);
lean_ctor_set(x_45, 2, x_25);
x_46 = lean_array_uset(x_10, x_24, x_45);
x_47 = lean_unsigned_to_nat(4u);
x_48 = lean_nat_mul(x_44, x_47);
x_49 = lean_unsigned_to_nat(3u);
x_50 = lean_nat_div(x_48, x_49);
lean_dec(x_48);
x_51 = lean_array_get_size(x_46);
x_52 = lean_nat_dec_le(x_50, x_51);
lean_dec(x_51);
lean_dec(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3___redArg(x_46);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_53);
x_5 = x_54;
goto block_8;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_44);
lean_ctor_set(x_55, 1, x_46);
x_5 = x_55;
goto block_8;
}
}
}
else
{
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
x_5 = x_3;
goto block_8;
}
}
else
{
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_push(x_4, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lake_OrdHashSet_insert___at___Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1_spec__1(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_1;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1_spec__2(x_2, x_7, x_8, x_1);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lake_ExternLib_dynlibFacet;
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_14);
x_18 = l_Lake_ExternLib_keyword;
x_19 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_12);
lean_ctor_set(x_19, 3, x_16);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = lean_apply_6(x_5, x_19, x_6, x_7, x_8, x_9, x_10);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_array_push(x_4, x_23);
x_26 = 1;
x_27 = lean_usize_add(x_2, x_26);
x_2 = x_27;
x_4 = x_25;
x_9 = x_24;
x_10 = x_22;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_20, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
return x_20;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_20, 0, x_34);
return x_20;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_dec(x_20);
x_36 = lean_ctor_get(x_21, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_38 = x_21;
} else {
 lean_dec_ref(x_21);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_35);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_4);
lean_ctor_set(x_41, 1, x_9);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_10);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_array_uget(x_2, x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildShared_spec__0(x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_array_push(x_5, x_18);
x_21 = 1;
x_22 = lean_usize_add(x_3, x_21);
x_3 = x_22;
x_5 = x_20;
x_10 = x_19;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
return x_15;
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
lean_ctor_set(x_15, 0, x_29);
return x_15;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_dec(x_15);
x_31 = lean_ctor_get(x_16, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_33 = x_16;
} else {
 lean_dec_ref(x_16);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_5);
lean_ctor_set(x_36, 1, x_10);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_11);
return x_37;
}
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___Lake_LeanLib_recBuildShared_spec__6___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___Lake_LeanLib_recBuildShared_spec__6___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_OrdHashSet_empty___at___Lake_LeanLib_recBuildShared_spec__6___closed__0;
x_2 = l_Lake_LeanLib_recCollectLocalModules___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___Lake_LeanLib_recBuildShared_spec__6() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_OrdHashSet_empty___at___Lake_LeanLib_recBuildShared_spec__6___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_18; 
x_18 = lean_usize_dec_eq(x_2, x_3);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
x_21 = lean_array_uget(x_1, x_2);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
x_25 = l_Lean_NameSet_contains(x_19, x_24);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_4);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_4, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_4, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec(x_23);
x_30 = l_Lake_LeanLib_sharedFacet;
lean_inc(x_24);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_24);
x_32 = l_Lake_LeanLib_modulesFacetConfig___closed__1;
x_33 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_22);
lean_ctor_set(x_33, 3, x_30);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_34 = lean_apply_6(x_5, x_33, x_6, x_7, x_8, x_9, x_10);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_array_push(x_20, x_37);
x_40 = l_Lean_NameSet_insert(x_19, x_24);
lean_ctor_set(x_4, 1, x_39);
lean_ctor_set(x_4, 0, x_40);
x_11 = x_4;
x_12 = x_38;
x_13 = x_36;
goto block_17;
}
else
{
uint8_t x_41; 
lean_free_object(x_4);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_41 = !lean_is_exclusive(x_34);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_34, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_35);
if (x_43 == 0)
{
return x_34;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_35, 0);
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_35);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_34, 0, x_46);
return x_34;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_34, 1);
lean_inc(x_47);
lean_dec(x_34);
x_48 = lean_ctor_get(x_35, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_35, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_50 = x_35;
} else {
 lean_dec_ref(x_35);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_47);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_4);
x_53 = lean_ctor_get(x_23, 0);
lean_inc(x_53);
lean_dec(x_23);
x_54 = l_Lake_LeanLib_sharedFacet;
lean_inc(x_24);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_24);
x_56 = l_Lake_LeanLib_modulesFacetConfig___closed__1;
x_57 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_22);
lean_ctor_set(x_57, 3, x_54);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_58 = lean_apply_6(x_5, x_57, x_6, x_7, x_8, x_9, x_10);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_array_push(x_20, x_61);
x_64 = l_Lean_NameSet_insert(x_19, x_24);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_11 = x_65;
x_12 = x_62;
x_13 = x_60;
goto block_17;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_66 = lean_ctor_get(x_58, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_67 = x_58;
} else {
 lean_dec_ref(x_58);
 x_67 = lean_box(0);
}
x_68 = lean_ctor_get(x_59, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_59, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_70 = x_59;
} else {
 lean_dec_ref(x_59);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
if (lean_is_scalar(x_67)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_67;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_66);
return x_72;
}
}
}
else
{
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
x_11 = x_4;
x_12 = x_9;
x_13 = x_10;
goto block_17;
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_4);
lean_ctor_set(x_73, 1, x_9);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_10);
return x_74;
}
block_17:
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_4 = x_11;
x_9 = x_12;
x_10 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__8_spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_25; 
x_25 = lean_usize_dec_eq(x_2, x_3);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_array_uget(x_1, x_2);
x_27 = lean_ctor_get(x_26, 2);
lean_inc(x_27);
x_28 = l_Lake_Module_transImportsFacet;
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_27);
x_30 = l_Lake_Module_keyword;
x_31 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_26);
lean_ctor_set(x_31, 3, x_28);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_32 = lean_apply_6(x_5, x_31, x_6, x_7, x_8, x_9, x_10);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_io_wait(x_37, x_35);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_array_get_size(x_43);
x_46 = lean_nat_dec_lt(x_44, x_45);
if (x_46 == 0)
{
lean_dec(x_45);
lean_dec(x_43);
x_17 = x_42;
x_18 = x_36;
x_19 = x_41;
goto block_24;
}
else
{
uint8_t x_47; 
x_47 = lean_nat_dec_le(x_45, x_45);
if (x_47 == 0)
{
lean_dec(x_45);
lean_dec(x_43);
x_17 = x_42;
x_18 = x_36;
x_19 = x_41;
goto block_24;
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_box(0);
x_49 = 0;
x_50 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_51 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1(x_43, x_49, x_50, x_48, x_36, x_41);
lean_dec(x_43);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_17 = x_42;
x_18 = x_54;
x_19 = x_53;
goto block_24;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_55 = lean_ctor_get(x_39, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_38, 1);
lean_inc(x_56);
lean_dec(x_38);
x_57 = lean_ctor_get(x_39, 0);
lean_inc(x_57);
lean_dec(x_39);
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_array_get_size(x_58);
x_61 = lean_nat_dec_lt(x_59, x_60);
if (x_61 == 0)
{
lean_dec(x_60);
lean_dec(x_58);
x_11 = x_57;
x_12 = x_36;
x_13 = x_56;
goto block_16;
}
else
{
uint8_t x_62; 
x_62 = lean_nat_dec_le(x_60, x_60);
if (x_62 == 0)
{
lean_dec(x_60);
lean_dec(x_58);
x_11 = x_57;
x_12 = x_36;
x_13 = x_56;
goto block_16;
}
else
{
lean_object* x_63; size_t x_64; size_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_box(0);
x_64 = 0;
x_65 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_66 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1(x_58, x_64, x_65, x_63, x_36, x_56);
lean_dec(x_58);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_11 = x_57;
x_12 = x_69;
x_13 = x_68;
goto block_16;
}
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_70 = !lean_is_exclusive(x_32);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_32, 0);
lean_dec(x_71);
x_72 = !lean_is_exclusive(x_33);
if (x_72 == 0)
{
return x_32;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_33, 0);
x_74 = lean_ctor_get(x_33, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_33);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set(x_32, 0, x_75);
return x_32;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_32, 1);
lean_inc(x_76);
lean_dec(x_32);
x_77 = lean_ctor_get(x_33, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_33, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_79 = x_33;
} else {
 lean_dec_ref(x_33);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_76);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_4);
lean_ctor_set(x_82, 1, x_9);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_10);
return x_83;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
block_24:
{
lean_object* x_20; size_t x_21; size_t x_22; 
x_20 = l_Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1(x_4, x_17);
lean_dec(x_17);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_2 = x_22;
x_4 = x_20;
x_9 = x_18;
x_10 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_25; 
x_25 = lean_usize_dec_eq(x_2, x_3);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_array_uget(x_1, x_2);
x_27 = lean_ctor_get(x_26, 2);
lean_inc(x_27);
x_28 = l_Lake_Module_transImportsFacet;
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_27);
x_30 = l_Lake_Module_keyword;
x_31 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_26);
lean_ctor_set(x_31, 3, x_28);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_32 = lean_apply_6(x_5, x_31, x_6, x_7, x_8, x_9, x_10);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_io_wait(x_37, x_35);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_array_get_size(x_43);
x_46 = lean_nat_dec_lt(x_44, x_45);
if (x_46 == 0)
{
lean_dec(x_45);
lean_dec(x_43);
x_17 = x_42;
x_18 = x_36;
x_19 = x_41;
goto block_24;
}
else
{
uint8_t x_47; 
x_47 = lean_nat_dec_le(x_45, x_45);
if (x_47 == 0)
{
lean_dec(x_45);
lean_dec(x_43);
x_17 = x_42;
x_18 = x_36;
x_19 = x_41;
goto block_24;
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_box(0);
x_49 = 0;
x_50 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_51 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1(x_43, x_49, x_50, x_48, x_36, x_41);
lean_dec(x_43);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_17 = x_42;
x_18 = x_54;
x_19 = x_53;
goto block_24;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_55 = lean_ctor_get(x_39, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_38, 1);
lean_inc(x_56);
lean_dec(x_38);
x_57 = lean_ctor_get(x_39, 0);
lean_inc(x_57);
lean_dec(x_39);
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_array_get_size(x_58);
x_61 = lean_nat_dec_lt(x_59, x_60);
if (x_61 == 0)
{
lean_dec(x_60);
lean_dec(x_58);
x_11 = x_57;
x_12 = x_36;
x_13 = x_56;
goto block_16;
}
else
{
uint8_t x_62; 
x_62 = lean_nat_dec_le(x_60, x_60);
if (x_62 == 0)
{
lean_dec(x_60);
lean_dec(x_58);
x_11 = x_57;
x_12 = x_36;
x_13 = x_56;
goto block_16;
}
else
{
lean_object* x_63; size_t x_64; size_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_box(0);
x_64 = 0;
x_65 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_66 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1(x_58, x_64, x_65, x_63, x_36, x_56);
lean_dec(x_58);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_11 = x_57;
x_12 = x_69;
x_13 = x_68;
goto block_16;
}
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_70 = !lean_is_exclusive(x_32);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_32, 0);
lean_dec(x_71);
x_72 = !lean_is_exclusive(x_33);
if (x_72 == 0)
{
return x_32;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_33, 0);
x_74 = lean_ctor_get(x_33, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_33);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set(x_32, 0, x_75);
return x_32;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_32, 1);
lean_inc(x_76);
lean_dec(x_32);
x_77 = lean_ctor_get(x_33, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_33, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_79 = x_33;
} else {
 lean_dec_ref(x_33);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_76);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_4);
lean_ctor_set(x_82, 1, x_9);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_10);
return x_83;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
block_24:
{
lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_20 = l_Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1(x_4, x_17);
lean_dec(x_17);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_23 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__8_spec__8(x_1, x_22, x_3, x_20, x_5, x_6, x_7, x_8, x_18, x_19);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__10(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_array_uget(x_2, x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0(x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_array_push(x_5, x_18);
x_21 = 1;
x_22 = lean_usize_add(x_3, x_21);
x_3 = x_22;
x_5 = x_20;
x_10 = x_19;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
return x_15;
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
lean_ctor_set(x_15, 0, x_29);
return x_15;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_dec(x_15);
x_31 = lean_ctor_get(x_16, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_33 = x_16;
} else {
 lean_dec_ref(x_16);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_5);
lean_ctor_set(x_36, 1, x_10);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_11);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__11_spec__11(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_18; 
x_18 = lean_usize_dec_eq(x_2, x_3);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_array_uget(x_1, x_2);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 2);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 8);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(1);
x_24 = lean_apply_1(x_22, x_23);
x_25 = lean_array_size(x_24);
x_26 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_27 = l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__1(x_19, x_25, x_26, x_24, x_5, x_6, x_7, x_8, x_9, x_10);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Array_append___redArg(x_4, x_30);
lean_dec(x_30);
x_11 = x_32;
x_12 = x_31;
x_13 = x_29;
goto block_17;
}
else
{
lean_object* x_33; 
lean_dec(x_28);
lean_dec(x_4);
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_dec(x_27);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_11 = x_35;
x_12 = x_36;
x_13 = x_34;
goto block_17;
}
else
{
lean_dec(x_33);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_27;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_4);
lean_ctor_set(x_37, 1, x_9);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_10);
return x_38;
}
block_17:
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_4 = x_11;
x_9 = x_12;
x_10 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__11(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_18; 
x_18 = lean_usize_dec_eq(x_2, x_3);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_array_uget(x_1, x_2);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 2);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 8);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(1);
x_24 = lean_apply_1(x_22, x_23);
x_25 = lean_array_size(x_24);
x_26 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_27 = l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__1(x_19, x_25, x_26, x_24, x_5, x_6, x_7, x_8, x_9, x_10);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Array_append___redArg(x_4, x_30);
lean_dec(x_30);
x_11 = x_32;
x_12 = x_31;
x_13 = x_29;
goto block_17;
}
else
{
lean_object* x_33; 
lean_dec(x_28);
lean_dec(x_4);
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_dec(x_27);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_11 = x_35;
x_12 = x_36;
x_13 = x_34;
goto block_17;
}
else
{
lean_dec(x_33);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_27;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_4);
lean_ctor_set(x_37, 1, x_9);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_10);
return x_38;
}
block_17:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__11_spec__11(x_1, x_15, x_3, x_11, x_5, x_6, x_7, x_8, x_12, x_13);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__13___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_JobResult_prependLog___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__13___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_35; 
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
x_14 = l_Lake_instDataKindDynlib;
x_15 = lean_array_get_size(x_6);
lean_dec(x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
lean_dec(x_13);
x_96 = lean_ctor_get(x_11, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_11, 1);
lean_inc(x_97);
lean_dec(x_11);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_dec(x_96);
x_100 = lean_string_utf8_byte_size(x_98);
x_101 = lean_unsigned_to_nat(0u);
x_102 = lean_nat_dec_eq(x_100, x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_103 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__3;
x_104 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_98, x_100, x_101);
x_105 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_98, x_104, x_100);
x_106 = lean_string_utf8_extract(x_98, x_104, x_105);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_98);
x_107 = lean_string_append(x_103, x_106);
lean_dec(x_106);
x_108 = lean_box(1);
x_109 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_109, 0, x_107);
x_110 = lean_unbox(x_108);
lean_ctor_set_uint8(x_109, sizeof(void*)*1, x_110);
x_111 = lean_box(0);
x_112 = lean_array_push(x_97, x_109);
x_113 = l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__13___lam__1(x_99, x_111, x_2, x_3, x_4, x_5, x_112, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = x_113;
goto block_95;
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_100);
lean_dec(x_98);
x_114 = lean_box(0);
x_115 = l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__13___lam__1(x_99, x_114, x_2, x_3, x_4, x_5, x_97, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = x_115;
goto block_95;
}
}
else
{
lean_object* x_116; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_116 = lean_ctor_get(x_11, 1);
lean_inc(x_116);
lean_dec(x_11);
x_16 = x_116;
x_17 = x_12;
goto block_34;
}
block_34:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
lean_inc(x_16);
x_18 = l_Array_shrink___redArg(x_16, x_15);
x_19 = lean_array_get_size(x_16);
x_20 = l_Array_extract___redArg(x_16, x_15, x_19);
lean_dec(x_16);
x_21 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__0;
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_box(0);
x_24 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__2;
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_unbox(x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_26);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_task_pure(x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_14);
lean_ctor_set(x_30, 2, x_21);
x_31 = lean_unbox(x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_31);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_18);
if (lean_is_scalar(x_13)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_13;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_17);
return x_33;
}
block_95:
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_36, 0);
x_40 = lean_ctor_get(x_36, 1);
x_41 = lean_array_get_size(x_40);
x_42 = lean_nat_dec_lt(x_15, x_41);
if (x_42 == 0)
{
lean_dec(x_41);
lean_free_object(x_36);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_15);
return x_35;
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_35);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_35, 1);
lean_dec(x_44);
x_45 = lean_ctor_get(x_35, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_39);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_39, 0);
x_48 = lean_ctor_get(x_39, 1);
lean_dec(x_48);
lean_inc(x_40);
x_49 = l_Array_shrink___redArg(x_40, x_15);
x_50 = l_Array_extract___redArg(x_40, x_15, x_41);
lean_dec(x_40);
x_51 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__13___lam__0), 2, 1);
lean_closure_set(x_51, 0, x_50);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_unbox(x_8);
x_54 = lean_task_map(x_51, x_47, x_52, x_53);
lean_ctor_set(x_39, 1, x_14);
lean_ctor_set(x_39, 0, x_54);
lean_ctor_set(x_36, 1, x_49);
return x_35;
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; 
x_55 = lean_ctor_get(x_39, 0);
x_56 = lean_ctor_get(x_39, 2);
x_57 = lean_ctor_get_uint8(x_39, sizeof(void*)*3);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_39);
lean_inc(x_40);
x_58 = l_Array_shrink___redArg(x_40, x_15);
x_59 = l_Array_extract___redArg(x_40, x_15, x_41);
lean_dec(x_40);
x_60 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__13___lam__0), 2, 1);
lean_closure_set(x_60, 0, x_59);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_unbox(x_8);
x_63 = lean_task_map(x_60, x_55, x_61, x_62);
x_64 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_14);
lean_ctor_set(x_64, 2, x_56);
lean_ctor_set_uint8(x_64, sizeof(void*)*3, x_57);
lean_ctor_set(x_36, 1, x_58);
lean_ctor_set(x_36, 0, x_64);
return x_35;
}
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_35);
x_65 = lean_ctor_get(x_39, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_39, 2);
lean_inc(x_66);
x_67 = lean_ctor_get_uint8(x_39, sizeof(void*)*3);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 x_68 = x_39;
} else {
 lean_dec_ref(x_39);
 x_68 = lean_box(0);
}
lean_inc(x_40);
x_69 = l_Array_shrink___redArg(x_40, x_15);
x_70 = l_Array_extract___redArg(x_40, x_15, x_41);
lean_dec(x_40);
x_71 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__13___lam__0), 2, 1);
lean_closure_set(x_71, 0, x_70);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_unbox(x_8);
x_74 = lean_task_map(x_71, x_65, x_72, x_73);
if (lean_is_scalar(x_68)) {
 x_75 = lean_alloc_ctor(0, 3, 1);
} else {
 x_75 = x_68;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_14);
lean_ctor_set(x_75, 2, x_66);
lean_ctor_set_uint8(x_75, sizeof(void*)*3, x_67);
lean_ctor_set(x_36, 1, x_69);
lean_ctor_set(x_36, 0, x_75);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_36);
lean_ctor_set(x_76, 1, x_37);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_36, 0);
x_78 = lean_ctor_get(x_36, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_36);
x_79 = lean_array_get_size(x_78);
x_80 = lean_nat_dec_lt(x_15, x_79);
if (x_80 == 0)
{
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_37);
lean_dec(x_15);
return x_35;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_81 = x_35;
} else {
 lean_dec_ref(x_35);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get(x_77, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_77, 2);
lean_inc(x_83);
x_84 = lean_ctor_get_uint8(x_77, sizeof(void*)*3);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 x_85 = x_77;
} else {
 lean_dec_ref(x_77);
 x_85 = lean_box(0);
}
lean_inc(x_78);
x_86 = l_Array_shrink___redArg(x_78, x_15);
x_87 = l_Array_extract___redArg(x_78, x_15, x_79);
lean_dec(x_78);
x_88 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__13___lam__0), 2, 1);
lean_closure_set(x_88, 0, x_87);
x_89 = lean_unsigned_to_nat(0u);
x_90 = lean_unbox(x_8);
x_91 = lean_task_map(x_88, x_82, x_89, x_90);
if (lean_is_scalar(x_85)) {
 x_92 = lean_alloc_ctor(0, 3, 1);
} else {
 x_92 = x_85;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_14);
lean_ctor_set(x_92, 2, x_83);
lean_ctor_set_uint8(x_92, sizeof(void*)*3, x_84);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_86);
if (lean_is_scalar(x_81)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_81;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_37);
return x_94;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildShared___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_288; lean_object* x_289; 
lean_inc(x_9);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_288 = lean_apply_6(x_9, x_1, x_10, x_11, x_12, x_13, x_14);
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_288, 1);
lean_inc(x_291);
lean_dec(x_288);
x_292 = lean_ctor_get(x_289, 1);
lean_inc(x_292);
lean_dec(x_289);
x_293 = lean_ctor_get(x_290, 0);
lean_inc(x_293);
lean_dec(x_290);
x_294 = lean_io_wait(x_293, x_291);
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; 
x_296 = lean_ctor_get(x_295, 1);
lean_inc(x_296);
x_297 = lean_ctor_get(x_294, 1);
lean_inc(x_297);
lean_dec(x_294);
x_298 = lean_ctor_get(x_295, 0);
lean_inc(x_298);
lean_dec(x_295);
x_299 = lean_ctor_get(x_296, 0);
lean_inc(x_299);
lean_dec(x_296);
x_300 = lean_unsigned_to_nat(0u);
x_301 = lean_array_get_size(x_299);
x_302 = lean_nat_dec_lt(x_300, x_301);
if (x_302 == 0)
{
lean_dec(x_301);
lean_dec(x_299);
x_260 = x_298;
x_261 = x_292;
x_262 = x_297;
goto block_287;
}
else
{
uint8_t x_303; 
x_303 = lean_nat_dec_le(x_301, x_301);
if (x_303 == 0)
{
lean_dec(x_301);
lean_dec(x_299);
x_260 = x_298;
x_261 = x_292;
x_262 = x_297;
goto block_287;
}
else
{
lean_object* x_304; size_t x_305; size_t x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_304 = lean_box(0);
x_305 = 0;
x_306 = lean_usize_of_nat(x_301);
lean_dec(x_301);
x_307 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1(x_299, x_305, x_306, x_304, x_292, x_297);
lean_dec(x_299);
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec(x_307);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
lean_dec(x_308);
x_260 = x_298;
x_261 = x_310;
x_262 = x_309;
goto block_287;
}
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_311 = lean_ctor_get(x_295, 1);
lean_inc(x_311);
x_312 = lean_ctor_get(x_294, 1);
lean_inc(x_312);
lean_dec(x_294);
x_313 = lean_ctor_get(x_295, 0);
lean_inc(x_313);
lean_dec(x_295);
x_314 = lean_ctor_get(x_311, 0);
lean_inc(x_314);
lean_dec(x_311);
x_315 = lean_unsigned_to_nat(0u);
x_316 = lean_array_get_size(x_314);
x_317 = lean_nat_dec_lt(x_315, x_316);
if (x_317 == 0)
{
lean_dec(x_316);
lean_dec(x_314);
x_15 = x_313;
x_16 = x_292;
x_17 = x_312;
goto block_20;
}
else
{
uint8_t x_318; 
x_318 = lean_nat_dec_le(x_316, x_316);
if (x_318 == 0)
{
lean_dec(x_316);
lean_dec(x_314);
x_15 = x_313;
x_16 = x_292;
x_17 = x_312;
goto block_20;
}
else
{
lean_object* x_319; size_t x_320; size_t x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_319 = lean_box(0);
x_320 = 0;
x_321 = lean_usize_of_nat(x_316);
lean_dec(x_316);
x_322 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1(x_314, x_320, x_321, x_319, x_292, x_312);
lean_dec(x_314);
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_322, 1);
lean_inc(x_324);
lean_dec(x_322);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
x_15 = x_313;
x_16 = x_325;
x_17 = x_324;
goto block_20;
}
}
}
}
else
{
uint8_t x_326; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_326 = !lean_is_exclusive(x_288);
if (x_326 == 0)
{
lean_object* x_327; uint8_t x_328; 
x_327 = lean_ctor_get(x_288, 0);
lean_dec(x_327);
x_328 = !lean_is_exclusive(x_289);
if (x_328 == 0)
{
return x_288;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_329 = lean_ctor_get(x_289, 0);
x_330 = lean_ctor_get(x_289, 1);
lean_inc(x_330);
lean_inc(x_329);
lean_dec(x_289);
x_331 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set(x_331, 1, x_330);
lean_ctor_set(x_288, 0, x_331);
return x_288;
}
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_332 = lean_ctor_get(x_288, 1);
lean_inc(x_332);
lean_dec(x_288);
x_333 = lean_ctor_get(x_289, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_289, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_335 = x_289;
} else {
 lean_dec_ref(x_289);
 x_335 = lean_box(0);
}
if (lean_is_scalar(x_335)) {
 x_336 = lean_alloc_ctor(1, 2, 0);
} else {
 x_336 = x_335;
}
lean_ctor_set(x_336, 0, x_333);
lean_ctor_set(x_336, 1, x_334);
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_332);
return x_337;
}
}
block_20:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
block_26:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
block_57:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_38 = l_System_FilePath_normalize(x_27);
x_39 = l_Lake_joinRelative(x_2, x_38);
lean_dec(x_38);
x_40 = l_System_FilePath_normalize(x_29);
x_41 = l_Lake_joinRelative(x_39, x_40);
lean_dec(x_40);
lean_inc(x_32);
x_42 = l_Lake_nameToSharedLib(x_32);
x_43 = l_Lake_joinRelative(x_41, x_42);
lean_dec(x_42);
x_44 = l_Array_append___redArg(x_31, x_28);
lean_dec(x_28);
x_45 = l_Array_append___redArg(x_34, x_33);
lean_dec(x_33);
x_46 = l_Lake_LeanLib_isPlugin(x_3);
x_47 = l_System_Platform_isWindows;
x_48 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__2;
x_49 = l_Lake_buildLeanSharedLib(x_32, x_43, x_30, x_35, x_44, x_45, x_46, x_47, x_9, x_10, x_11, x_12, x_48, x_37);
lean_dec(x_30);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_36);
lean_ctor_set(x_49, 0, x_52);
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_49, 0);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_49);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_36);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
block_84:
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_array_get_size(x_70);
x_72 = lean_nat_dec_lt(x_67, x_71);
if (x_72 == 0)
{
lean_dec(x_71);
lean_dec(x_70);
x_27 = x_59;
x_28 = x_62;
x_29 = x_61;
x_30 = x_63;
x_31 = x_65;
x_32 = x_64;
x_33 = x_69;
x_34 = x_68;
x_35 = x_66;
x_36 = x_60;
x_37 = x_58;
goto block_57;
}
else
{
uint8_t x_73; 
x_73 = lean_nat_dec_le(x_71, x_71);
if (x_73 == 0)
{
lean_dec(x_71);
lean_dec(x_70);
x_27 = x_59;
x_28 = x_62;
x_29 = x_61;
x_30 = x_63;
x_31 = x_65;
x_32 = x_64;
x_33 = x_69;
x_34 = x_68;
x_35 = x_66;
x_36 = x_60;
x_37 = x_58;
goto block_57;
}
else
{
size_t x_74; size_t x_75; lean_object* x_76; lean_object* x_77; 
x_74 = 0;
x_75 = lean_usize_of_nat(x_71);
lean_dec(x_71);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_76 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__4(x_70, x_74, x_75, x_66, x_9, x_10, x_11, x_12, x_60, x_58);
lean_dec(x_70);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_27 = x_59;
x_28 = x_62;
x_29 = x_61;
x_30 = x_63;
x_31 = x_65;
x_32 = x_64;
x_33 = x_69;
x_34 = x_68;
x_35 = x_79;
x_36 = x_80;
x_37 = x_78;
goto block_57;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_81 = lean_ctor_get(x_76, 1);
lean_inc(x_81);
lean_dec(x_76);
x_82 = lean_ctor_get(x_77, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_77, 1);
lean_inc(x_83);
lean_dec(x_77);
x_21 = x_82;
x_22 = x_83;
x_23 = x_81;
goto block_26;
}
}
}
}
block_105:
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_97 = lean_mk_empty_array_with_capacity(x_91);
x_98 = lean_array_get_size(x_4);
x_99 = lean_nat_dec_lt(x_91, x_98);
if (x_99 == 0)
{
lean_dec(x_98);
lean_dec(x_5);
x_58 = x_96;
x_59 = x_85;
x_60 = x_95;
x_61 = x_87;
x_62 = x_86;
x_63 = x_88;
x_64 = x_90;
x_65 = x_89;
x_66 = x_94;
x_67 = x_91;
x_68 = x_93;
x_69 = x_92;
x_70 = x_97;
goto block_84;
}
else
{
uint8_t x_100; 
x_100 = lean_nat_dec_le(x_98, x_98);
if (x_100 == 0)
{
lean_dec(x_98);
lean_dec(x_5);
x_58 = x_96;
x_59 = x_85;
x_60 = x_95;
x_61 = x_87;
x_62 = x_86;
x_63 = x_88;
x_64 = x_90;
x_65 = x_89;
x_66 = x_94;
x_67 = x_91;
x_68 = x_93;
x_69 = x_92;
x_70 = x_97;
goto block_84;
}
else
{
lean_object* x_101; size_t x_102; size_t x_103; lean_object* x_104; 
x_101 = l_Lake_ExternLib_keyword;
x_102 = 0;
x_103 = lean_usize_of_nat(x_98);
lean_dec(x_98);
x_104 = l_Array_foldlMUnsafe_fold___at___Lake_Package_findModule_x3f_spec__1(x_101, x_5, x_4, x_102, x_103, x_97);
x_58 = x_96;
x_59 = x_85;
x_60 = x_95;
x_61 = x_87;
x_62 = x_86;
x_63 = x_88;
x_64 = x_90;
x_65 = x_89;
x_66 = x_94;
x_67 = x_91;
x_68 = x_93;
x_69 = x_92;
x_70 = x_104;
goto block_84;
}
}
}
block_134:
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_120 = l_Array_append___redArg(x_111, x_107);
lean_dec(x_107);
x_121 = lean_array_get_size(x_120);
x_122 = lean_nat_dec_lt(x_114, x_121);
if (x_122 == 0)
{
lean_dec(x_121);
lean_dec(x_120);
x_85 = x_106;
x_86 = x_109;
x_87 = x_108;
x_88 = x_110;
x_89 = x_113;
x_90 = x_112;
x_91 = x_114;
x_92 = x_116;
x_93 = x_115;
x_94 = x_117;
x_95 = x_118;
x_96 = x_119;
goto block_105;
}
else
{
uint8_t x_123; 
x_123 = lean_nat_dec_le(x_121, x_121);
if (x_123 == 0)
{
lean_dec(x_121);
lean_dec(x_120);
x_85 = x_106;
x_86 = x_109;
x_87 = x_108;
x_88 = x_110;
x_89 = x_113;
x_90 = x_112;
x_91 = x_114;
x_92 = x_116;
x_93 = x_115;
x_94 = x_117;
x_95 = x_118;
x_96 = x_119;
goto block_105;
}
else
{
size_t x_124; size_t x_125; lean_object* x_126; lean_object* x_127; 
x_124 = 0;
x_125 = lean_usize_of_nat(x_121);
lean_dec(x_121);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_3);
x_126 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__5(x_3, x_120, x_124, x_125, x_117, x_9, x_10, x_11, x_12, x_118, x_119);
lean_dec(x_120);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
x_85 = x_106;
x_86 = x_109;
x_87 = x_108;
x_88 = x_110;
x_89 = x_113;
x_90 = x_112;
x_91 = x_114;
x_92 = x_116;
x_93 = x_115;
x_94 = x_129;
x_95 = x_130;
x_96 = x_128;
goto block_105;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_106);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_131 = lean_ctor_get(x_126, 1);
lean_inc(x_131);
lean_dec(x_126);
x_132 = lean_ctor_get(x_127, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_127, 1);
lean_inc(x_133);
lean_dec(x_127);
x_21 = x_132;
x_22 = x_133;
x_23 = x_131;
goto block_26;
}
}
}
}
block_188:
{
uint8_t x_149; 
x_149 = !lean_is_exclusive(x_146);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_150 = lean_ctor_get(x_146, 1);
x_151 = lean_ctor_get(x_146, 0);
lean_dec(x_151);
x_152 = lean_mk_empty_array_with_capacity(x_143);
x_153 = lean_array_get_size(x_150);
x_154 = lean_nat_dec_lt(x_143, x_153);
if (x_154 == 0)
{
lean_dec(x_153);
lean_free_object(x_146);
lean_dec(x_150);
lean_dec(x_6);
x_106 = x_135;
x_107 = x_136;
x_108 = x_138;
x_109 = x_137;
x_110 = x_139;
x_111 = x_140;
x_112 = x_142;
x_113 = x_141;
x_114 = x_143;
x_115 = x_145;
x_116 = x_144;
x_117 = x_152;
x_118 = x_147;
x_119 = x_148;
goto block_134;
}
else
{
uint8_t x_155; 
x_155 = lean_nat_dec_le(x_153, x_153);
if (x_155 == 0)
{
lean_dec(x_153);
lean_free_object(x_146);
lean_dec(x_150);
lean_dec(x_6);
x_106 = x_135;
x_107 = x_136;
x_108 = x_138;
x_109 = x_137;
x_110 = x_139;
x_111 = x_140;
x_112 = x_142;
x_113 = x_141;
x_114 = x_143;
x_115 = x_145;
x_116 = x_144;
x_117 = x_152;
x_118 = x_147;
x_119 = x_148;
goto block_134;
}
else
{
lean_object* x_156; lean_object* x_157; size_t x_158; size_t x_159; lean_object* x_160; lean_object* x_161; 
x_156 = lean_box(0);
x_157 = l_Lean_NameSet_insert(x_156, x_6);
lean_ctor_set(x_146, 1, x_152);
lean_ctor_set(x_146, 0, x_157);
x_158 = 0;
x_159 = lean_usize_of_nat(x_153);
lean_dec(x_153);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_160 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__7(x_150, x_158, x_159, x_146, x_9, x_10, x_11, x_12, x_147, x_148);
lean_dec(x_150);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_160, 1);
lean_inc(x_163);
lean_dec(x_160);
x_164 = lean_ctor_get(x_161, 1);
lean_inc(x_164);
lean_dec(x_161);
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
lean_dec(x_162);
x_106 = x_135;
x_107 = x_136;
x_108 = x_138;
x_109 = x_137;
x_110 = x_139;
x_111 = x_140;
x_112 = x_142;
x_113 = x_141;
x_114 = x_143;
x_115 = x_145;
x_116 = x_144;
x_117 = x_165;
x_118 = x_164;
x_119 = x_163;
goto block_134;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_166 = lean_ctor_get(x_160, 1);
lean_inc(x_166);
lean_dec(x_160);
x_167 = lean_ctor_get(x_161, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_161, 1);
lean_inc(x_168);
lean_dec(x_161);
x_21 = x_167;
x_22 = x_168;
x_23 = x_166;
goto block_26;
}
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_169 = lean_ctor_get(x_146, 1);
lean_inc(x_169);
lean_dec(x_146);
x_170 = lean_mk_empty_array_with_capacity(x_143);
x_171 = lean_array_get_size(x_169);
x_172 = lean_nat_dec_lt(x_143, x_171);
if (x_172 == 0)
{
lean_dec(x_171);
lean_dec(x_169);
lean_dec(x_6);
x_106 = x_135;
x_107 = x_136;
x_108 = x_138;
x_109 = x_137;
x_110 = x_139;
x_111 = x_140;
x_112 = x_142;
x_113 = x_141;
x_114 = x_143;
x_115 = x_145;
x_116 = x_144;
x_117 = x_170;
x_118 = x_147;
x_119 = x_148;
goto block_134;
}
else
{
uint8_t x_173; 
x_173 = lean_nat_dec_le(x_171, x_171);
if (x_173 == 0)
{
lean_dec(x_171);
lean_dec(x_169);
lean_dec(x_6);
x_106 = x_135;
x_107 = x_136;
x_108 = x_138;
x_109 = x_137;
x_110 = x_139;
x_111 = x_140;
x_112 = x_142;
x_113 = x_141;
x_114 = x_143;
x_115 = x_145;
x_116 = x_144;
x_117 = x_170;
x_118 = x_147;
x_119 = x_148;
goto block_134;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; size_t x_177; size_t x_178; lean_object* x_179; lean_object* x_180; 
x_174 = lean_box(0);
x_175 = l_Lean_NameSet_insert(x_174, x_6);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_170);
x_177 = 0;
x_178 = lean_usize_of_nat(x_171);
lean_dec(x_171);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_179 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__7(x_169, x_177, x_178, x_176, x_9, x_10, x_11, x_12, x_147, x_148);
lean_dec(x_169);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_179, 1);
lean_inc(x_182);
lean_dec(x_179);
x_183 = lean_ctor_get(x_180, 1);
lean_inc(x_183);
lean_dec(x_180);
x_184 = lean_ctor_get(x_181, 1);
lean_inc(x_184);
lean_dec(x_181);
x_106 = x_135;
x_107 = x_136;
x_108 = x_138;
x_109 = x_137;
x_110 = x_139;
x_111 = x_140;
x_112 = x_142;
x_113 = x_141;
x_114 = x_143;
x_115 = x_145;
x_116 = x_144;
x_117 = x_184;
x_118 = x_183;
x_119 = x_182;
goto block_134;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_185 = lean_ctor_get(x_179, 1);
lean_inc(x_185);
lean_dec(x_179);
x_186 = lean_ctor_get(x_180, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_180, 1);
lean_inc(x_187);
lean_dec(x_180);
x_21 = x_186;
x_22 = x_187;
x_23 = x_185;
goto block_26;
}
}
}
}
}
block_217:
{
lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_203 = l_Lake_OrdHashSet_empty___at___Lake_LeanLib_recBuildShared_spec__6;
x_204 = lean_array_get_size(x_197);
x_205 = lean_nat_dec_lt(x_196, x_204);
if (x_205 == 0)
{
lean_dec(x_204);
lean_dec(x_197);
x_135 = x_189;
x_136 = x_190;
x_137 = x_192;
x_138 = x_191;
x_139 = x_200;
x_140 = x_193;
x_141 = x_195;
x_142 = x_194;
x_143 = x_196;
x_144 = x_199;
x_145 = x_198;
x_146 = x_203;
x_147 = x_201;
x_148 = x_202;
goto block_188;
}
else
{
uint8_t x_206; 
x_206 = lean_nat_dec_le(x_204, x_204);
if (x_206 == 0)
{
lean_dec(x_204);
lean_dec(x_197);
x_135 = x_189;
x_136 = x_190;
x_137 = x_192;
x_138 = x_191;
x_139 = x_200;
x_140 = x_193;
x_141 = x_195;
x_142 = x_194;
x_143 = x_196;
x_144 = x_199;
x_145 = x_198;
x_146 = x_203;
x_147 = x_201;
x_148 = x_202;
goto block_188;
}
else
{
size_t x_207; size_t x_208; lean_object* x_209; lean_object* x_210; 
x_207 = 0;
x_208 = lean_usize_of_nat(x_204);
lean_dec(x_204);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_209 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__8(x_197, x_207, x_208, x_203, x_9, x_10, x_11, x_12, x_201, x_202);
lean_dec(x_197);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = lean_ctor_get(x_210, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_210, 1);
lean_inc(x_213);
lean_dec(x_210);
x_135 = x_189;
x_136 = x_190;
x_137 = x_192;
x_138 = x_191;
x_139 = x_200;
x_140 = x_193;
x_141 = x_195;
x_142 = x_194;
x_143 = x_196;
x_144 = x_199;
x_145 = x_198;
x_146 = x_212;
x_147 = x_213;
x_148 = x_211;
goto block_188;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_214 = lean_ctor_get(x_209, 1);
lean_inc(x_214);
lean_dec(x_209);
x_215 = lean_ctor_get(x_210, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_210, 1);
lean_inc(x_216);
lean_dec(x_210);
x_21 = x_215;
x_22 = x_216;
x_23 = x_214;
goto block_26;
}
}
}
}
block_259:
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_222 = lean_ctor_get(x_7, 1);
lean_inc(x_222);
x_223 = lean_ctor_get(x_8, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_7, 6);
lean_inc(x_224);
x_225 = lean_ctor_get(x_7, 8);
lean_inc(x_225);
lean_dec(x_7);
x_226 = lean_ctor_get(x_222, 6);
lean_inc(x_226);
x_227 = lean_ctor_get(x_222, 7);
lean_inc(x_227);
x_228 = lean_ctor_get(x_222, 8);
lean_inc(x_228);
x_229 = lean_ctor_get(x_222, 9);
lean_inc(x_229);
lean_dec(x_222);
x_230 = lean_ctor_get(x_8, 4);
lean_inc(x_230);
lean_dec(x_8);
x_231 = lean_ctor_get(x_223, 6);
lean_inc(x_231);
x_232 = lean_ctor_get(x_223, 7);
lean_inc(x_232);
x_233 = lean_ctor_get(x_223, 8);
lean_inc(x_233);
x_234 = lean_ctor_get(x_223, 9);
lean_inc(x_234);
lean_dec(x_223);
x_235 = l_Array_append___redArg(x_226, x_231);
lean_dec(x_231);
x_236 = lean_unsigned_to_nat(0u);
x_237 = lean_array_get_size(x_235);
x_238 = lean_nat_dec_lt(x_236, x_237);
if (x_238 == 0)
{
lean_dec(x_237);
lean_dec(x_235);
x_189 = x_224;
x_190 = x_232;
x_191 = x_225;
x_192 = x_234;
x_193 = x_227;
x_194 = x_230;
x_195 = x_229;
x_196 = x_236;
x_197 = x_218;
x_198 = x_228;
x_199 = x_233;
x_200 = x_219;
x_201 = x_220;
x_202 = x_221;
goto block_217;
}
else
{
uint8_t x_239; 
x_239 = lean_nat_dec_le(x_237, x_237);
if (x_239 == 0)
{
lean_dec(x_237);
lean_dec(x_235);
x_189 = x_224;
x_190 = x_232;
x_191 = x_225;
x_192 = x_234;
x_193 = x_227;
x_194 = x_230;
x_195 = x_229;
x_196 = x_236;
x_197 = x_218;
x_198 = x_228;
x_199 = x_233;
x_200 = x_219;
x_201 = x_220;
x_202 = x_221;
goto block_217;
}
else
{
size_t x_240; size_t x_241; lean_object* x_242; lean_object* x_243; 
x_240 = 0;
x_241 = lean_usize_of_nat(x_237);
lean_dec(x_237);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_3);
x_242 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__10(x_3, x_235, x_240, x_241, x_219, x_9, x_10, x_11, x_12, x_220, x_221);
lean_dec(x_235);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_245 = lean_ctor_get(x_243, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_243, 1);
lean_inc(x_246);
lean_dec(x_243);
x_189 = x_224;
x_190 = x_232;
x_191 = x_225;
x_192 = x_234;
x_193 = x_227;
x_194 = x_230;
x_195 = x_229;
x_196 = x_236;
x_197 = x_218;
x_198 = x_228;
x_199 = x_233;
x_200 = x_245;
x_201 = x_246;
x_202 = x_244;
goto block_217;
}
else
{
uint8_t x_247; 
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_218);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_247 = !lean_is_exclusive(x_242);
if (x_247 == 0)
{
lean_object* x_248; uint8_t x_249; 
x_248 = lean_ctor_get(x_242, 0);
lean_dec(x_248);
x_249 = !lean_is_exclusive(x_243);
if (x_249 == 0)
{
return x_242;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_243, 0);
x_251 = lean_ctor_get(x_243, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_243);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
lean_ctor_set(x_242, 0, x_252);
return x_242;
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_253 = lean_ctor_get(x_242, 1);
lean_inc(x_253);
lean_dec(x_242);
x_254 = lean_ctor_get(x_243, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_243, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_256 = x_243;
} else {
 lean_dec_ref(x_243);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_255);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_253);
return x_258;
}
}
}
}
}
block_287:
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_263 = l_Lake_LeanLib_recBuildStatic___lam__4___closed__1;
x_264 = lean_unsigned_to_nat(0u);
x_265 = lean_array_get_size(x_260);
x_266 = lean_nat_dec_lt(x_264, x_265);
if (x_266 == 0)
{
lean_dec(x_265);
x_218 = x_260;
x_219 = x_263;
x_220 = x_261;
x_221 = x_262;
goto block_259;
}
else
{
uint8_t x_267; 
x_267 = lean_nat_dec_le(x_265, x_265);
if (x_267 == 0)
{
lean_dec(x_265);
x_218 = x_260;
x_219 = x_263;
x_220 = x_261;
x_221 = x_262;
goto block_259;
}
else
{
size_t x_268; size_t x_269; lean_object* x_270; lean_object* x_271; 
x_268 = 0;
x_269 = lean_usize_of_nat(x_265);
lean_dec(x_265);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_270 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__11(x_260, x_268, x_269, x_263, x_9, x_10, x_11, x_12, x_261, x_262);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec(x_270);
x_273 = lean_ctor_get(x_271, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_271, 1);
lean_inc(x_274);
lean_dec(x_271);
x_218 = x_260;
x_219 = x_273;
x_220 = x_274;
x_221 = x_272;
goto block_259;
}
else
{
uint8_t x_275; 
lean_dec(x_260);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_275 = !lean_is_exclusive(x_270);
if (x_275 == 0)
{
lean_object* x_276; uint8_t x_277; 
x_276 = lean_ctor_get(x_270, 0);
lean_dec(x_276);
x_277 = !lean_is_exclusive(x_271);
if (x_277 == 0)
{
return x_270;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_271, 0);
x_279 = lean_ctor_get(x_271, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_271);
x_280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
lean_ctor_set(x_270, 0, x_280);
return x_270;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_281 = lean_ctor_get(x_270, 1);
lean_inc(x_281);
lean_dec(x_270);
x_282 = lean_ctor_get(x_271, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_271, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_284 = x_271;
} else {
 lean_dec_ref(x_271);
 x_284 = lean_box(0);
}
if (lean_is_scalar(x_284)) {
 x_285 = lean_alloc_ctor(1, 2, 0);
} else {
 x_285 = x_284;
}
lean_ctor_set(x_285, 0, x_282);
lean_ctor_set(x_285, 1, x_283);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_281);
return x_286;
}
}
}
}
}
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildShared___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":shared", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildShared(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 10);
lean_inc(x_14);
x_15 = l_Lake_LeanLib_modulesFacet;
lean_inc(x_9);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_9);
x_17 = l_Lake_LeanLib_modulesFacetConfig___closed__1;
lean_inc(x_1);
x_18 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_1);
lean_ctor_set(x_18, 3, x_15);
lean_inc(x_9);
x_19 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildShared___lam__0___boxed), 14, 8);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_12);
lean_closure_set(x_19, 2, x_1);
lean_closure_set(x_19, 3, x_14);
lean_closure_set(x_19, 4, x_8);
lean_closure_set(x_19, 5, x_9);
lean_closure_set(x_19, 6, x_13);
lean_closure_set(x_19, 7, x_10);
lean_inc(x_5);
x_20 = l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__13(x_19, x_2, x_3, x_4, x_5, x_6, x_7);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_27 = lean_ctor_get(x_22, 2);
lean_dec(x_27);
x_28 = lean_ctor_get(x_5, 3);
lean_inc(x_28);
lean_dec(x_5);
x_29 = lean_st_ref_take(x_28, x_23);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lake_LeanLib_recBuildStatic___closed__1;
x_33 = lean_box(1);
x_34 = lean_unbox(x_33);
x_35 = l_Lean_Name_toString(x_9, x_34, x_32);
x_36 = l_Lake_LeanLib_recBuildShared___closed__0;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_box(0);
lean_ctor_set(x_22, 2, x_37);
x_39 = lean_unbox(x_38);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_39);
lean_inc(x_22);
x_40 = l_Lake_Job_toOpaque___redArg(x_22);
x_41 = lean_array_push(x_30, x_40);
x_42 = lean_st_ref_set(x_28, x_41, x_31);
lean_dec(x_28);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = l_Lake_Job_renew___redArg(x_22);
lean_ctor_set(x_21, 0, x_45);
lean_ctor_set(x_42, 0, x_21);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = l_Lake_Job_renew___redArg(x_22);
lean_ctor_set(x_21, 0, x_47);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_21);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_49 = lean_ctor_get(x_22, 0);
x_50 = lean_ctor_get(x_22, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_22);
x_51 = lean_ctor_get(x_5, 3);
lean_inc(x_51);
lean_dec(x_5);
x_52 = lean_st_ref_take(x_51, x_23);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lake_LeanLib_recBuildStatic___closed__1;
x_56 = lean_box(1);
x_57 = lean_unbox(x_56);
x_58 = l_Lean_Name_toString(x_9, x_57, x_55);
x_59 = l_Lake_LeanLib_recBuildShared___closed__0;
x_60 = lean_string_append(x_58, x_59);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_62, 0, x_49);
lean_ctor_set(x_62, 1, x_50);
lean_ctor_set(x_62, 2, x_60);
x_63 = lean_unbox(x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*3, x_63);
lean_inc(x_62);
x_64 = l_Lake_Job_toOpaque___redArg(x_62);
x_65 = lean_array_push(x_53, x_64);
x_66 = lean_st_ref_set(x_51, x_65, x_54);
lean_dec(x_51);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
x_69 = l_Lake_Job_renew___redArg(x_62);
lean_ctor_set(x_21, 0, x_69);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_21);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_71 = lean_ctor_get(x_21, 1);
lean_inc(x_71);
lean_dec(x_21);
x_72 = lean_ctor_get(x_22, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_22, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 lean_ctor_release(x_22, 2);
 x_74 = x_22;
} else {
 lean_dec_ref(x_22);
 x_74 = lean_box(0);
}
x_75 = lean_ctor_get(x_5, 3);
lean_inc(x_75);
lean_dec(x_5);
x_76 = lean_st_ref_take(x_75, x_23);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lake_LeanLib_recBuildStatic___closed__1;
x_80 = lean_box(1);
x_81 = lean_unbox(x_80);
x_82 = l_Lean_Name_toString(x_9, x_81, x_79);
x_83 = l_Lake_LeanLib_recBuildShared___closed__0;
x_84 = lean_string_append(x_82, x_83);
x_85 = lean_box(0);
if (lean_is_scalar(x_74)) {
 x_86 = lean_alloc_ctor(0, 3, 1);
} else {
 x_86 = x_74;
}
lean_ctor_set(x_86, 0, x_72);
lean_ctor_set(x_86, 1, x_73);
lean_ctor_set(x_86, 2, x_84);
x_87 = lean_unbox(x_85);
lean_ctor_set_uint8(x_86, sizeof(void*)*3, x_87);
lean_inc(x_86);
x_88 = l_Lake_Job_toOpaque___redArg(x_86);
x_89 = lean_array_push(x_77, x_88);
x_90 = lean_st_ref_set(x_75, x_89, x_78);
lean_dec(x_75);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
x_93 = l_Lake_Job_renew___redArg(x_86);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_71);
if (lean_is_scalar(x_92)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_92;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_91);
return x_95;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1_spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__4(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__5(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__7(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__8_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__8_spec__8(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__8(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__10(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__11_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__11_spec__11(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__11(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__13___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__13___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildShared___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lake_LeanLib_recBuildShared___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_LeanLib_sharedFacetConfig_spec__0(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l_Lean_Json_compress(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_sharedFacetConfig___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at___Lake_LeanLib_sharedFacetConfig_spec__0(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildShared), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_sharedFacetConfig___lam__0___boxed), 2, 0);
x_2 = l_Lake_instDataKindDynlib;
x_3 = l_Lake_LeanLib_modulesFacetConfig___closed__1;
x_4 = l_Lake_LeanLib_sharedFacetConfig___closed__0;
x_5 = lean_box(1);
x_6 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_1);
x_7 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_7);
x_8 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*4 + 1, x_8);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_LeanLib_sharedFacetConfig_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_stdFormat___at___Lake_LeanLib_sharedFacetConfig_spec__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_sharedFacetConfig___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_LeanLib_sharedFacetConfig___lam__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recBuildExtraDepTargets_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_uget(x_2, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_16 = l_Lake_Package_fetchTargetJob(x_1, x_15, x_6, x_7, x_8, x_9, x_10, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Lake_Job_mix___redArg(x_5, x_19);
x_22 = 1;
x_23 = lean_usize_add(x_4, x_22);
x_4 = x_23;
x_5 = x_21;
x_10 = x_20;
x_11 = x_18;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_16, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
return x_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_16, 0, x_30);
return x_16;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_dec(x_16);
x_32 = lean_ctor_get(x_17, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_34 = x_17;
} else {
 lean_dec_ref(x_17);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recBuildExtraDepTargets_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_uget(x_2, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_15);
lean_inc(x_1);
x_16 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(x_1, x_15, x_15, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l_Lake_Job_toOpaque___redArg(x_21);
x_23 = l_Lake_Job_mix___redArg(x_5, x_22);
x_24 = 1;
x_25 = lean_usize_add(x_4, x_24);
x_4 = x_25;
x_5 = x_23;
x_10 = x_20;
x_11 = x_19;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_16, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_17);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_16, 0, x_32);
return x_16;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_dec(x_16);
x_34 = lean_ctor_get(x_17, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_17, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_36 = x_17;
} else {
 lean_dec_ref(x_17);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
}
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildExtraDepTargets___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildExtraDepTargets___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":extraDep", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildExtraDepTargets(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = l_Lake_Package_extraDepFacet;
lean_inc(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = l_Lake_Package_keyword;
lean_inc(x_8);
x_15 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_8);
lean_ctor_set(x_15, 3, x_12);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = lean_apply_6(x_2, x_15, x_3, x_4, x_5, x_6, x_7);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; size_t x_48; size_t x_49; lean_object* x_50; lean_object* x_51; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
x_22 = lean_ctor_get(x_10, 5);
lean_inc(x_22);
x_23 = lean_ctor_get(x_10, 6);
lean_inc(x_23);
lean_dec(x_10);
x_24 = l_Lake_LeanLib_recBuildStatic___closed__1;
x_25 = lean_box(0);
x_26 = lean_box(1);
x_27 = lean_unbox(x_26);
x_28 = l_Lean_Name_toString(x_11, x_27, x_24);
x_29 = l_Lake_LeanLib_recBuildExtraDepTargets___closed__0;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_unbox(x_26);
x_32 = l_Lean_Name_toString(x_9, x_31, x_24);
x_33 = lean_string_append(x_30, x_32);
lean_dec(x_32);
x_34 = l_Lake_LeanLib_recBuildExtraDepTargets___closed__1;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_box(0);
x_37 = l_Lake_LeanLib_recBuildLean___closed__0;
x_38 = lean_box(0);
x_39 = l_Lake_BuildTrace_nil(x_35);
x_40 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_unbox(x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*2, x_41);
lean_ctor_set(x_17, 1, x_40);
lean_ctor_set(x_17, 0, x_36);
x_42 = lean_task_pure(x_17);
x_43 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__0;
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_25);
lean_ctor_set(x_45, 2, x_43);
x_46 = lean_unbox(x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*3, x_46);
x_47 = l_Lake_Job_mix___redArg(x_45, x_20);
x_48 = lean_array_size(x_23);
x_49 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_8);
x_50 = l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recBuildExtraDepTargets_spec__0(x_8, x_23, x_48, x_49, x_47, x_2, x_3, x_4, x_5, x_21, x_18);
lean_dec(x_23);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; size_t x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_array_size(x_22);
x_56 = l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recBuildExtraDepTargets_spec__1(x_8, x_22, x_55, x_49, x_53, x_2, x_3, x_4, x_5, x_54, x_52);
lean_dec(x_22);
return x_56;
}
else
{
lean_dec(x_51);
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_50;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; size_t x_86; size_t x_87; lean_object* x_88; lean_object* x_89; 
x_57 = lean_ctor_get(x_17, 0);
x_58 = lean_ctor_get(x_17, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_17);
x_59 = lean_ctor_get(x_10, 5);
lean_inc(x_59);
x_60 = lean_ctor_get(x_10, 6);
lean_inc(x_60);
lean_dec(x_10);
x_61 = l_Lake_LeanLib_recBuildStatic___closed__1;
x_62 = lean_box(0);
x_63 = lean_box(1);
x_64 = lean_unbox(x_63);
x_65 = l_Lean_Name_toString(x_11, x_64, x_61);
x_66 = l_Lake_LeanLib_recBuildExtraDepTargets___closed__0;
x_67 = lean_string_append(x_65, x_66);
x_68 = lean_unbox(x_63);
x_69 = l_Lean_Name_toString(x_9, x_68, x_61);
x_70 = lean_string_append(x_67, x_69);
lean_dec(x_69);
x_71 = l_Lake_LeanLib_recBuildExtraDepTargets___closed__1;
x_72 = lean_string_append(x_70, x_71);
x_73 = lean_box(0);
x_74 = l_Lake_LeanLib_recBuildLean___closed__0;
x_75 = lean_box(0);
x_76 = l_Lake_BuildTrace_nil(x_72);
x_77 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_unbox(x_75);
lean_ctor_set_uint8(x_77, sizeof(void*)*2, x_78);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_77);
x_80 = lean_task_pure(x_79);
x_81 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__0;
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_62);
lean_ctor_set(x_83, 2, x_81);
x_84 = lean_unbox(x_82);
lean_ctor_set_uint8(x_83, sizeof(void*)*3, x_84);
x_85 = l_Lake_Job_mix___redArg(x_83, x_57);
x_86 = lean_array_size(x_60);
x_87 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_8);
x_88 = l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recBuildExtraDepTargets_spec__0(x_8, x_60, x_86, x_87, x_85, x_2, x_3, x_4, x_5, x_58, x_18);
lean_dec(x_60);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; size_t x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_93 = lean_array_size(x_59);
x_94 = l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recBuildExtraDepTargets_spec__1(x_8, x_59, x_93, x_87, x_91, x_2, x_3, x_4, x_5, x_92, x_90);
lean_dec(x_59);
return x_94;
}
else
{
lean_dec(x_89);
lean_dec(x_59);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_88;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_95 = !lean_is_exclusive(x_16);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_16, 0);
lean_dec(x_96);
return x_16;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_16, 1);
lean_inc(x_97);
lean_dec(x_16);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_17);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recBuildExtraDepTargets_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recBuildExtraDepTargets_spec__0(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recBuildExtraDepTargets_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recBuildExtraDepTargets_spec__1(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildExtraDepTargets), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_1 = l_Lake_LeanLib_leanArtsFacetConfig___closed__1;
x_2 = lean_box(1);
x_3 = l_Lake_instDataKindUnit;
x_4 = l_Lake_LeanLib_extraDepFacetConfig___closed__0;
x_5 = l_Lake_LeanLib_modulesFacetConfig___closed__1;
x_6 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_1);
x_7 = lean_unbox(x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_7);
x_8 = lean_unbox(x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*4 + 1, x_8);
return x_6;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_LeanLib_extraDepFacetConfig___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildDefaultFacets_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_uget(x_4, x_3);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_15);
x_19 = l_Lake_LeanLib_modulesFacetConfig___closed__1;
lean_inc(x_1);
x_20 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_1);
lean_ctor_set(x_20, 3, x_17);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_21 = lean_apply_6(x_5, x_20, x_6, x_7, x_8, x_9, x_10);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
x_24 = lean_box(0);
x_25 = lean_array_uset(x_4, x_3, x_24);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_21);
x_34 = lean_ctor_get(x_22, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
lean_dec(x_22);
x_36 = l_Lake_Job_toOpaque___redArg(x_34);
x_26 = x_36;
x_27 = x_35;
x_28 = x_23;
goto block_33;
}
else
{
lean_object* x_37; 
lean_dec(x_23);
lean_dec(x_22);
x_37 = lean_ctor_get(x_21, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
lean_dec(x_21);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_26 = x_39;
x_27 = x_40;
x_28 = x_38;
goto block_33;
}
else
{
uint8_t x_41; 
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_21);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_21, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_37);
if (x_43 == 0)
{
return x_21;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_37, 0);
x_45 = lean_ctor_get(x_37, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_37);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_21, 0, x_46);
return x_21;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_21, 1);
lean_inc(x_47);
lean_dec(x_21);
x_48 = lean_ctor_get(x_37, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_37, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_50 = x_37;
} else {
 lean_dec_ref(x_37);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_47);
return x_52;
}
}
}
block_33:
{
size_t x_29; size_t x_30; lean_object* x_31; 
x_29 = 1;
x_30 = lean_usize_add(x_3, x_29);
x_31 = lean_array_uset(x_25, x_3, x_26);
x_3 = x_30;
x_4 = x_31;
x_9 = x_27;
x_10 = x_28;
goto _start;
}
}
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildDefaultFacets___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<collection>", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildDefaultFacets(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 7);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_array_size(x_9);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildDefaultFacets_spec__0(x_1, x_10, x_11, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = l_Lake_LeanLib_recBuildDefaultFacets___closed__0;
x_19 = l_Lake_Job_mixArray___redArg(x_17, x_18);
lean_dec(x_17);
lean_ctor_set(x_13, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = l_Lake_LeanLib_recBuildDefaultFacets___closed__0;
x_23 = l_Lake_Job_mixArray___redArg(x_20, x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_12, 0, x_24);
return x_12;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_dec(x_12);
x_26 = lean_ctor_get(x_13, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_28 = x_13;
} else {
 lean_dec_ref(x_13);
 x_28 = lean_box(0);
}
x_29 = l_Lake_LeanLib_recBuildDefaultFacets___closed__0;
x_30 = l_Lake_Job_mixArray___redArg(x_26, x_29);
lean_dec(x_26);
if (lean_is_scalar(x_28)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_28;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_25);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_12);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_12, 0);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_13);
if (x_35 == 0)
{
return x_12;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_13, 0);
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_13);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_12, 0, x_38);
return x_12;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_12, 1);
lean_inc(x_39);
lean_dec(x_12);
x_40 = lean_ctor_get(x_13, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_13, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_42 = x_13;
} else {
 lean_dec_ref(x_13);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_39);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildDefaultFacets_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildDefaultFacets_spec__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildDefaultFacets), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_1 = l_Lake_LeanLib_leanArtsFacetConfig___closed__1;
x_2 = lean_box(1);
x_3 = l_Lake_instDataKindUnit;
x_4 = l_Lake_LeanLib_defaultFacetConfig___closed__0;
x_5 = l_Lake_LeanLib_modulesFacetConfig___closed__1;
x_6 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_1);
x_7 = lean_unbox(x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_7);
x_8 = lean_unbox(x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*4 + 1, x_8);
return x_6;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_LeanLib_defaultFacetConfig___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_LeanLib_defaultFacetConfig;
x_2 = l_Lake_LeanLib_defaultFacet;
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_LeanLib_modulesFacetConfig;
x_2 = l_Lake_LeanLib_modulesFacet;
x_3 = l_Lake_LeanLib_initFacetConfigs___closed__0;
x_4 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_LeanLib_leanArtsFacetConfig;
x_2 = l_Lake_LeanLib_leanArtsFacet;
x_3 = l_Lake_LeanLib_initFacetConfigs___closed__1;
x_4 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_LeanLib_staticFacetConfig;
x_2 = l_Lake_LeanLib_staticFacet;
x_3 = l_Lake_LeanLib_initFacetConfigs___closed__2;
x_4 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_LeanLib_staticExportFacetConfig;
x_2 = l_Lake_LeanLib_staticExportFacet;
x_3 = l_Lake_LeanLib_initFacetConfigs___closed__3;
x_4 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_LeanLib_sharedFacetConfig;
x_2 = l_Lake_LeanLib_sharedFacet;
x_3 = l_Lake_LeanLib_initFacetConfigs___closed__4;
x_4 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_LeanLib_extraDepFacetConfig;
x_2 = l_Lake_LeanLib_extraDepFacet;
x_3 = l_Lake_LeanLib_initFacetConfigs___closed__5;
x_4 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_LeanLib_initFacetConfigs___closed__6;
return x_1;
}
}
static lean_object* _init_l_Lake_initLibraryFacetConfigs() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_LeanLib_initFacetConfigs;
return x_1;
}
}
lean_object* initialize_Lake_Build_Common(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Targets(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Library(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Common(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Targets(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___closed__0 = _init_l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___closed__0();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___closed__0);
l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___closed__1 = _init_l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___closed__1();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___closed__1);
l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___closed__2 = _init_l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___closed__2();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___closed__2);
l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___closed__3 = _init_l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___closed__3();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___closed__3);
l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___closed__4 = _init_l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___closed__4();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___closed__4);
l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__0 = _init_l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__0();
lean_mark_persistent(l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__0);
l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__1 = _init_l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__1();
lean_mark_persistent(l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__1);
l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__2 = _init_l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__2();
lean_mark_persistent(l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__2);
l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__3 = _init_l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__3();
lean_mark_persistent(l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___closed__3);
l_Lake_LeanLib_recCollectLocalModules___closed__0 = _init_l_Lake_LeanLib_recCollectLocalModules___closed__0();
lean_mark_persistent(l_Lake_LeanLib_recCollectLocalModules___closed__0);
l_Lake_LeanLib_recCollectLocalModules___closed__1 = _init_l_Lake_LeanLib_recCollectLocalModules___closed__1();
lean_mark_persistent(l_Lake_LeanLib_recCollectLocalModules___closed__1);
l_Lake_LeanLib_recCollectLocalModules___closed__2 = _init_l_Lake_LeanLib_recCollectLocalModules___closed__2();
lean_mark_persistent(l_Lake_LeanLib_recCollectLocalModules___closed__2);
l_Lake_LeanLib_recCollectLocalModules___closed__3 = _init_l_Lake_LeanLib_recCollectLocalModules___closed__3();
lean_mark_persistent(l_Lake_LeanLib_recCollectLocalModules___closed__3);
l_Lake_LeanLib_recCollectLocalModules___closed__4 = _init_l_Lake_LeanLib_recCollectLocalModules___closed__4();
lean_mark_persistent(l_Lake_LeanLib_recCollectLocalModules___closed__4);
l_Lake_LeanLib_recCollectLocalModules___closed__5 = _init_l_Lake_LeanLib_recCollectLocalModules___closed__5();
lean_mark_persistent(l_Lake_LeanLib_recCollectLocalModules___closed__5);
l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0 = _init_l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0);
l_Lake_LeanLib_modulesFacetConfig___closed__0 = _init_l_Lake_LeanLib_modulesFacetConfig___closed__0();
lean_mark_persistent(l_Lake_LeanLib_modulesFacetConfig___closed__0);
l_Lake_LeanLib_modulesFacetConfig___closed__1 = _init_l_Lake_LeanLib_modulesFacetConfig___closed__1();
lean_mark_persistent(l_Lake_LeanLib_modulesFacetConfig___closed__1);
l_Lake_LeanLib_modulesFacetConfig___closed__2 = _init_l_Lake_LeanLib_modulesFacetConfig___closed__2();
lean_mark_persistent(l_Lake_LeanLib_modulesFacetConfig___closed__2);
l_Lake_LeanLib_modulesFacetConfig = _init_l_Lake_LeanLib_modulesFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_modulesFacetConfig);
l_Lake_LeanLib_recBuildLean___closed__0 = _init_l_Lake_LeanLib_recBuildLean___closed__0();
lean_mark_persistent(l_Lake_LeanLib_recBuildLean___closed__0);
l_Lake_LeanLib_recBuildLean___closed__1 = _init_l_Lake_LeanLib_recBuildLean___closed__1();
lean_mark_persistent(l_Lake_LeanLib_recBuildLean___closed__1);
l_Lake_LeanLib_recBuildLean___closed__2 = _init_l_Lake_LeanLib_recBuildLean___closed__2();
lean_mark_persistent(l_Lake_LeanLib_recBuildLean___closed__2);
l_Lake_LeanLib_recBuildLean___closed__3 = _init_l_Lake_LeanLib_recBuildLean___closed__3();
lean_mark_persistent(l_Lake_LeanLib_recBuildLean___closed__3);
l_Lake_LeanLib_recBuildLean___closed__4 = _init_l_Lake_LeanLib_recBuildLean___closed__4();
lean_mark_persistent(l_Lake_LeanLib_recBuildLean___closed__4);
l_Lake_LeanLib_leanArtsFacetConfig___closed__0 = _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__0();
lean_mark_persistent(l_Lake_LeanLib_leanArtsFacetConfig___closed__0);
l_Lake_LeanLib_leanArtsFacetConfig___closed__1 = _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__1();
lean_mark_persistent(l_Lake_LeanLib_leanArtsFacetConfig___closed__1);
l_Lake_LeanLib_leanArtsFacetConfig___closed__2 = _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__2();
lean_mark_persistent(l_Lake_LeanLib_leanArtsFacetConfig___closed__2);
l_Lake_LeanLib_leanArtsFacetConfig = _init_l_Lake_LeanLib_leanArtsFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_leanArtsFacetConfig);
l_Lake_LeanLib_recBuildStatic___lam__4___closed__0 = _init_l_Lake_LeanLib_recBuildStatic___lam__4___closed__0();
lean_mark_persistent(l_Lake_LeanLib_recBuildStatic___lam__4___closed__0);
l_Lake_LeanLib_recBuildStatic___lam__4___closed__1 = _init_l_Lake_LeanLib_recBuildStatic___lam__4___closed__1();
lean_mark_persistent(l_Lake_LeanLib_recBuildStatic___lam__4___closed__1);
l_Lake_LeanLib_recBuildStatic___closed__0 = _init_l_Lake_LeanLib_recBuildStatic___closed__0();
lean_mark_persistent(l_Lake_LeanLib_recBuildStatic___closed__0);
l_Lake_LeanLib_recBuildStatic___closed__1 = _init_l_Lake_LeanLib_recBuildStatic___closed__1();
lean_mark_persistent(l_Lake_LeanLib_recBuildStatic___closed__1);
l_Lake_LeanLib_recBuildStatic___closed__2 = _init_l_Lake_LeanLib_recBuildStatic___closed__2();
lean_mark_persistent(l_Lake_LeanLib_recBuildStatic___closed__2);
l_Lake_LeanLib_recBuildStatic___closed__3 = _init_l_Lake_LeanLib_recBuildStatic___closed__3();
lean_mark_persistent(l_Lake_LeanLib_recBuildStatic___closed__3);
l_Lake_LeanLib_recBuildStatic___closed__4 = _init_l_Lake_LeanLib_recBuildStatic___closed__4();
lean_mark_persistent(l_Lake_LeanLib_recBuildStatic___closed__4);
l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__0 = _init_l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__0);
l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__1 = _init_l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__1();
lean_mark_persistent(l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__1);
l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__2 = _init_l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__2();
lean_mark_persistent(l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__2);
l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__3 = _init_l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__3();
lean_mark_persistent(l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__3);
l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__4 = _init_l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__4();
lean_mark_persistent(l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___closed__4);
l_Lake_LeanLib_staticFacetConfig = _init_l_Lake_LeanLib_staticFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_staticFacetConfig);
l_Lake_LeanLib_staticExportFacetConfig___closed__0 = _init_l_Lake_LeanLib_staticExportFacetConfig___closed__0();
lean_mark_persistent(l_Lake_LeanLib_staticExportFacetConfig___closed__0);
l_Lake_LeanLib_staticExportFacetConfig = _init_l_Lake_LeanLib_staticExportFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_staticExportFacetConfig);
l_Lake_OrdHashSet_empty___at___Lake_LeanLib_recBuildShared_spec__6___closed__0 = _init_l_Lake_OrdHashSet_empty___at___Lake_LeanLib_recBuildShared_spec__6___closed__0();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at___Lake_LeanLib_recBuildShared_spec__6___closed__0);
l_Lake_OrdHashSet_empty___at___Lake_LeanLib_recBuildShared_spec__6___closed__1 = _init_l_Lake_OrdHashSet_empty___at___Lake_LeanLib_recBuildShared_spec__6___closed__1();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at___Lake_LeanLib_recBuildShared_spec__6___closed__1);
l_Lake_OrdHashSet_empty___at___Lake_LeanLib_recBuildShared_spec__6 = _init_l_Lake_OrdHashSet_empty___at___Lake_LeanLib_recBuildShared_spec__6();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at___Lake_LeanLib_recBuildShared_spec__6);
l_Lake_LeanLib_recBuildShared___closed__0 = _init_l_Lake_LeanLib_recBuildShared___closed__0();
lean_mark_persistent(l_Lake_LeanLib_recBuildShared___closed__0);
l_Lake_LeanLib_sharedFacetConfig___closed__0 = _init_l_Lake_LeanLib_sharedFacetConfig___closed__0();
lean_mark_persistent(l_Lake_LeanLib_sharedFacetConfig___closed__0);
l_Lake_LeanLib_sharedFacetConfig = _init_l_Lake_LeanLib_sharedFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_sharedFacetConfig);
l_Lake_LeanLib_recBuildExtraDepTargets___closed__0 = _init_l_Lake_LeanLib_recBuildExtraDepTargets___closed__0();
lean_mark_persistent(l_Lake_LeanLib_recBuildExtraDepTargets___closed__0);
l_Lake_LeanLib_recBuildExtraDepTargets___closed__1 = _init_l_Lake_LeanLib_recBuildExtraDepTargets___closed__1();
lean_mark_persistent(l_Lake_LeanLib_recBuildExtraDepTargets___closed__1);
l_Lake_LeanLib_extraDepFacetConfig___closed__0 = _init_l_Lake_LeanLib_extraDepFacetConfig___closed__0();
lean_mark_persistent(l_Lake_LeanLib_extraDepFacetConfig___closed__0);
l_Lake_LeanLib_extraDepFacetConfig___closed__1 = _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1();
lean_mark_persistent(l_Lake_LeanLib_extraDepFacetConfig___closed__1);
l_Lake_LeanLib_extraDepFacetConfig = _init_l_Lake_LeanLib_extraDepFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_extraDepFacetConfig);
l_Lake_LeanLib_recBuildDefaultFacets___closed__0 = _init_l_Lake_LeanLib_recBuildDefaultFacets___closed__0();
lean_mark_persistent(l_Lake_LeanLib_recBuildDefaultFacets___closed__0);
l_Lake_LeanLib_defaultFacetConfig___closed__0 = _init_l_Lake_LeanLib_defaultFacetConfig___closed__0();
lean_mark_persistent(l_Lake_LeanLib_defaultFacetConfig___closed__0);
l_Lake_LeanLib_defaultFacetConfig___closed__1 = _init_l_Lake_LeanLib_defaultFacetConfig___closed__1();
lean_mark_persistent(l_Lake_LeanLib_defaultFacetConfig___closed__1);
l_Lake_LeanLib_defaultFacetConfig = _init_l_Lake_LeanLib_defaultFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_defaultFacetConfig);
l_Lake_LeanLib_initFacetConfigs___closed__0 = _init_l_Lake_LeanLib_initFacetConfigs___closed__0();
lean_mark_persistent(l_Lake_LeanLib_initFacetConfigs___closed__0);
l_Lake_LeanLib_initFacetConfigs___closed__1 = _init_l_Lake_LeanLib_initFacetConfigs___closed__1();
lean_mark_persistent(l_Lake_LeanLib_initFacetConfigs___closed__1);
l_Lake_LeanLib_initFacetConfigs___closed__2 = _init_l_Lake_LeanLib_initFacetConfigs___closed__2();
lean_mark_persistent(l_Lake_LeanLib_initFacetConfigs___closed__2);
l_Lake_LeanLib_initFacetConfigs___closed__3 = _init_l_Lake_LeanLib_initFacetConfigs___closed__3();
lean_mark_persistent(l_Lake_LeanLib_initFacetConfigs___closed__3);
l_Lake_LeanLib_initFacetConfigs___closed__4 = _init_l_Lake_LeanLib_initFacetConfigs___closed__4();
lean_mark_persistent(l_Lake_LeanLib_initFacetConfigs___closed__4);
l_Lake_LeanLib_initFacetConfigs___closed__5 = _init_l_Lake_LeanLib_initFacetConfigs___closed__5();
lean_mark_persistent(l_Lake_LeanLib_initFacetConfigs___closed__5);
l_Lake_LeanLib_initFacetConfigs___closed__6 = _init_l_Lake_LeanLib_initFacetConfigs___closed__6();
lean_mark_persistent(l_Lake_LeanLib_initFacetConfigs___closed__6);
l_Lake_LeanLib_initFacetConfigs = _init_l_Lake_LeanLib_initFacetConfigs();
lean_mark_persistent(l_Lake_LeanLib_initFacetConfigs);
l_Lake_initLibraryFacetConfigs = _init_l_Lake_initLibraryFacetConfigs();
lean_mark_persistent(l_Lake_initLibraryFacetConfigs);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

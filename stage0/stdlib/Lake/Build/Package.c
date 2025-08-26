// Lean compiler output
// Module: Lake.Build.Package
// Imports: Lake.Util.Name Lake.Config.FacetConfig Lake.Build.Job.Monad Lake.Build.Infos Lake.Util.Git Lake.Util.Proc Lake.Build.Actions Lake.Build.Common Lake.Build.Targets Lake.Build.Topological Lake.Build.Job.Register Lake.Reservoir
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
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig___lam__1(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__1;
lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__2;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__7;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_fetchTargetJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__0;
lean_object* l_Lake_ensureJob___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JobResult_prependLog___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_contains___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_initPackageFacetConfigs;
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lake_Package_initFacetConfigs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig;
static lean_object* l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9;
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Package_depsFacet;
lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig___lam__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Package_depsFacetConfig___closed__0;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_mapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3;
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_contains___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_transDepsFacetConfig___closed__2;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3;
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__0;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_metadata(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig;
LEAN_EXPORT lean_object* l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_download(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Package_keyword;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__4;
static lean_object* l_Lake_Package_barrelFacetConfig___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Reservoir_lakeHeaders;
static lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1___closed__0;
static lean_object* l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg___closed__1;
static lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
uint8_t l_IO_FS_ordSystemTime____x40_Init_System_IO_1242411632____hygCtx___hyg_51_(lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__0;
static lean_object* l_Lake_formatQuery___at___Lake_Package_optBuildCacheFacetConfig_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(lean_object*, lean_object*);
static lean_object* l_Lake_formatQuery___at___Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
extern lean_object* l_Lake_Package_gitHubReleaseFacet;
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___Lake_Package_extraDepFacetConfig_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___Lake_Package_depsFacetConfig_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__2(lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_formatQuery___at___Lake_Package_depsFacetConfig_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__10_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2;
extern lean_object* l_Lake_instDataKindBool;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__2;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now(lean_object*);
lean_object* lean_task_pure(lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__3;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__5;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_mix___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__3;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1_spec__1___redArg___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_transDepsFacetConfig;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__6;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1_spec__1___redArg___closed__0;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__0;
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__1;
lean_object* l_Lake_readTraceFile(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__3;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__1;
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_formatQuery___at___Lake_Package_depsFacetConfig_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindUnit;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_buildCacheFacetConfig___closed__0;
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__6;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__0;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l_Lake_Package_transDepsFacet;
static lean_object* l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__6;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__7;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___closed__0;
lean_object* l_Lake_JobState_merge(lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4;
static lean_object* l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__0;
LEAN_EXPORT lean_object* l_Array_toJson___at___Lake_formatQuery___at___Lake_Package_depsFacetConfig_spec__0_spec__1(lean_object*);
static lean_object* l_panic___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__5___closed__0;
lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
static lean_object* l_Lake_Package_transDepsFacetConfig___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instQueryJsonUnit___lam__0(lean_object*);
static lean_object* l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_formatQuery___at___Lake_Package_depsFacetConfig_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___Lake_Package_extraDepFacetConfig_spec__0___redArg(uint8_t);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Name_eraseHead(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___Lake_Package_extraDepFacetConfig_spec__0___redArg___boxed(lean_object*);
lean_object* l_Lake_Job_renew___redArg(lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__4;
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instToJsonBool___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_initFacetConfigs;
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_optBarrelFacetConfig___closed__0;
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__0;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Package_buildCacheFacet;
extern lean_object* l_Lake_defaultLakeDir;
lean_object* lean_string_from_utf8_unchecked(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__5;
static lean_object* l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__0(lean_object*, lean_object*);
lean_object* l_Lake_untar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_toJson___at___Lake_formatQuery___at___Lake_Package_depsFacetConfig_spec__0_spec__1_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0;
static lean_object* l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__5;
extern lean_object* l_Lake_Git_defaultRemote;
LEAN_EXPORT lean_object* l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_findTag_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JobM_runSpawnM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_depsFacetConfig;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Package_extraDepFacet;
static lean_object* l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__0;
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0(uint8_t, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_async___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_formatQuery___at___Lake_Package_optBuildCacheFacetConfig_spec__0___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern uint64_t l_Lake_Hash_nil;
static lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lake_Package_initFacetConfigs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Package_optGitHubReleaseFacet;
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_contains___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__1;
static lean_object* l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__4;
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__8;
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_prevn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Lake_uriEncode(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_contains___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__1;
static lean_object* l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__3;
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__2;
uint8_t l_Lake_JobAction_merge(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___Lake_Package_extraDepFacetConfig_spec__0(uint8_t, lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_add___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_toJson___at___Lake_formatQuery___at___Lake_Package_depsFacetConfig_spec__0_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__10_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_FetchM_runJobM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__7(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_instQueryTextUnit___lam__0(lean_object*);
static lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1___closed__0;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___Lake_Package_depsFacetConfig_spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___Lake_Package_optBuildCacheFacetConfig_spec__0___boxed(lean_object*, lean_object*);
extern lean_object* l_Lake_Package_reservoirBarrelFacet;
extern lean_object* l_Lake_Package_optBuildCacheFacet;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__2;
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__2_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__4;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lake_BuildMetadata_writeFile(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_depsFacetConfig___lam__0___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__2;
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___Lake_Package_optBuildCacheFacetConfig_spec__0(uint8_t, uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__1;
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_depsFacetConfig___lam__0(uint8_t, lean_object*);
static lean_object* l_Lake_Package_optBarrelFacetConfig___closed__1;
lean_object* l_Lake_formatQuery___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__1;
lean_object* l_instToStringBool___lam__0___boxed(lean_object*);
static lean_object* l_Lake_Package_extraDepFacetConfig___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_transDepsFacetConfig___closed__0;
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Reservoir_pkgApiUrl(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Package_optReservoirBarrelFacet;
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 4);
x_7 = l_Lean_Name_quickCmp(x_2, x_3);
switch (x_7) {
case 0:
{
x_1 = x_5;
goto _start;
}
case 1:
{
lean_object* x_9; 
lean_inc(x_4);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
default: 
{
x_1 = x_6;
goto _start;
}
}
}
else
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_get_x3f___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__0___redArg(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": package not found for dependency '", 36, 36);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' (this is likely a bug in Lake)", 32, 32);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1_spec__1___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec_ref(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_array_uget(x_4, x_3);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 4);
x_15 = l_Std_DTreeMap_Internal_Impl_get_x3f___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__0___redArg(x_14, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_4);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec_ref(x_1);
x_17 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_16, x_8);
x_18 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1_spec__1___redArg___closed__0;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_13, x_8);
x_21 = lean_string_append(x_19, x_20);
lean_dec_ref(x_20);
x_22 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1_spec__1___redArg___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = 3;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
x_26 = lean_array_get_size(x_6);
x_27 = lean_array_push(x_6, x_25);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_7);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; 
lean_dec(x_13);
x_30 = lean_ctor_get(x_15, 0);
lean_inc(x_30);
lean_dec_ref(x_15);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_array_uset(x_4, x_3, x_31);
x_33 = 1;
x_34 = lean_usize_add(x_3, x_33);
x_35 = lean_array_uset(x_32, x_3, x_30);
x_3 = x_34;
x_4 = x_35;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_uget(x_4, x_3);
x_16 = lean_ctor_get(x_9, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 4);
x_19 = l_Std_DTreeMap_Internal_Impl_get_x3f___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__0___redArg(x_18, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec_ref(x_4);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec_ref(x_1);
x_21 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_20, x_12);
x_22 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1_spec__1___redArg___closed__0;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_17, x_12);
x_25 = lean_string_append(x_23, x_24);
lean_dec_ref(x_24);
x_26 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1_spec__1___redArg___closed__1;
x_27 = lean_string_append(x_25, x_26);
x_28 = 3;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
x_30 = lean_array_get_size(x_10);
x_31 = lean_array_push(x_10, x_29);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_11);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_17);
x_34 = lean_ctor_get(x_19, 0);
lean_inc(x_34);
lean_dec_ref(x_19);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_array_uset(x_4, x_3, x_35);
x_37 = 1;
x_38 = lean_usize_add(x_3, x_37);
x_39 = lean_array_uset(x_36, x_3, x_34);
x_40 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1_spec__1___redArg(x_1, x_2, x_38, x_39, x_9, x_10, x_11);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_get_set_stdout(x_1, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_box(0);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec_ref(x_20);
lean_inc(x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_26 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__3___redArg___lam__0(x_17, x_22, x_25, x_24, x_21);
lean_dec_ref(x_25);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_23);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_26, 0, x_32);
return x_26;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_20, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
lean_dec_ref(x_20);
x_41 = lean_box(0);
x_42 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__3___redArg___lam__0(x_17, x_22, x_41, x_40, x_21);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_10 = x_39;
x_11 = x_45;
x_12 = x_44;
goto block_15;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__4___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_get_set_stdin(x_1, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_box(0);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec_ref(x_20);
lean_inc(x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_26 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__4___redArg___lam__0(x_17, x_22, x_25, x_24, x_21);
lean_dec_ref(x_25);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_23);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_26, 0, x_32);
return x_26;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_20, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
lean_dec_ref(x_20);
x_41 = lean_box(0);
x_42 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__4___redArg___lam__0(x_17, x_22, x_41, x_40, x_21);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_10 = x_39;
x_11 = x_45;
x_12 = x_44;
goto block_15;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__4___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
static lean_object* _init_l_panic___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__5___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__5___closed__0;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__6___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_get_set_stderr(x_1, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_box(0);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec_ref(x_20);
lean_inc(x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_26 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__6___redArg___lam__0(x_17, x_22, x_25, x_24, x_21);
lean_dec_ref(x_25);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_23);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_26, 0, x_32);
return x_26;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_20, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
lean_dec_ref(x_20);
x_41 = lean_box(0);
x_42 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__6___redArg___lam__0(x_17, x_22, x_41, x_40, x_21);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_10 = x_39;
x_11 = x_45;
x_12 = x_44;
goto block_15;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__6___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__0() {
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
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.String.Extra", 22, 22);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String.fromUTF8!", 16, 16);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid UTF-8 string", 20, 20);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__3;
x_2 = lean_unsigned_to_nat(47u);
x_3 = lean_unsigned_to_nat(133u);
x_4 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__2;
x_5 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__1;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__0;
x_19 = lean_st_mk_ref(x_18, x_9);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_st_mk_ref(x_18, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = l_IO_FS_Stream_ofBuffer(x_20);
lean_inc(x_23);
x_26 = l_IO_FS_Stream_ofBuffer(x_23);
if (x_2 == 0)
{
x_27 = x_1;
goto block_54;
}
else
{
lean_object* x_55; 
lean_inc_ref(x_26);
x_55 = lean_alloc_closure((void*)(l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__6), 10, 3);
lean_closure_set(x_55, 0, lean_box(0));
lean_closure_set(x_55, 1, x_26);
lean_closure_set(x_55, 2, x_1);
x_27 = x_55;
goto block_54;
}
block_17:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
block_54:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_closure((void*)(l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__3), 10, 3);
lean_closure_set(x_28, 0, lean_box(0));
lean_closure_set(x_28, 1, x_26);
lean_closure_set(x_28, 2, x_27);
x_29 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__4___redArg(x_25, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec_ref(x_30);
x_34 = lean_st_ref_get(x_23, x_31);
lean_dec(x_23);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc_ref(x_37);
lean_dec(x_35);
x_38 = lean_string_validate_utf8(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec_ref(x_37);
x_39 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__4;
x_40 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__5(x_39);
x_10 = x_32;
x_11 = x_36;
x_12 = x_33;
x_13 = x_40;
goto block_17;
}
else
{
lean_object* x_41; 
x_41 = lean_string_from_utf8_unchecked(x_37);
lean_dec_ref(x_37);
x_10 = x_32;
x_11 = x_36;
x_12 = x_33;
x_13 = x_41;
goto block_17;
}
}
else
{
uint8_t x_42; 
lean_dec(x_23);
x_42 = !lean_is_exclusive(x_29);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_29, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_30);
if (x_44 == 0)
{
return x_29;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_30, 0);
x_46 = lean_ctor_get(x_30, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_30);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_29, 0, x_47);
return x_29;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_29, 1);
lean_inc(x_48);
lean_dec(x_29);
x_49 = lean_ctor_get(x_30, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_30, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_51 = x_30;
} else {
 lean_dec_ref(x_30);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_7; uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_3, x_2);
if (x_9 == 0)
{
return x_3;
}
else
{
uint32_t x_10; uint8_t x_11; uint32_t x_17; uint8_t x_18; 
x_10 = lean_string_utf8_get(x_1, x_3);
x_17 = 32;
x_18 = lean_uint32_dec_eq(x_10, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 9;
x_20 = lean_uint32_dec_eq(x_10, x_19);
x_11 = x_20;
goto block_16;
}
else
{
x_11 = x_18;
goto block_16;
}
block_16:
{
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 13;
x_13 = lean_uint32_dec_eq(x_10, x_12);
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 10;
x_15 = lean_uint32_dec_eq(x_10, x_14);
x_7 = x_15;
goto block_8;
}
else
{
x_7 = x_13;
goto block_8;
}
}
else
{
goto block_6;
}
}
}
block_6:
{
lean_object* x_4; 
x_4 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_4;
goto _start;
}
block_8:
{
if (x_7 == 0)
{
return x_3;
}
else
{
goto block_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; uint8_t x_6; uint32_t x_9; uint8_t x_10; uint32_t x_17; uint8_t x_18; 
x_5 = lean_string_utf8_prev(x_1, x_3);
x_9 = lean_string_utf8_get(x_1, x_5);
x_17 = 32;
x_18 = lean_uint32_dec_eq(x_9, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 9;
x_20 = lean_uint32_dec_eq(x_9, x_19);
x_10 = x_20;
goto block_16;
}
else
{
x_10 = x_18;
goto block_16;
}
block_8:
{
if (x_6 == 0)
{
lean_dec(x_5);
return x_3;
}
else
{
lean_dec(x_3);
x_3 = x_5;
goto _start;
}
}
block_16:
{
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 13;
x_12 = lean_uint32_dec_eq(x_9, x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 10;
x_14 = lean_uint32_dec_eq(x_9, x_13);
x_6 = x_14;
goto block_8;
}
else
{
x_6 = x_12;
goto block_8;
}
}
else
{
lean_dec(x_3);
x_3 = x_5;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_JobResult_prependLog___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
static lean_object* _init_l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<nil>", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__0;
x_2 = l_Lake_BuildTrace_nil(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_33; 
x_9 = 1;
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_15 = lean_array_get_size(x_7);
lean_dec_ref(x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_13);
x_91 = lean_ctor_get(x_11, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_11, 1);
lean_inc(x_92);
lean_dec_ref(x_11);
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec(x_91);
x_95 = lean_string_utf8_byte_size(x_93);
x_96 = lean_unsigned_to_nat(0u);
x_97 = lean_nat_dec_eq(x_95, x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_98 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__2;
x_99 = l_Substring_takeWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__8(x_93, x_95, x_96);
x_100 = l_Substring_takeRightWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__9(x_93, x_99, x_95);
x_101 = lean_string_utf8_extract(x_93, x_99, x_100);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_93);
x_102 = lean_string_append(x_98, x_101);
lean_dec_ref(x_101);
x_103 = 1;
x_104 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set_uint8(x_104, sizeof(void*)*1, x_103);
x_105 = lean_box(0);
x_106 = lean_array_push(x_92, x_104);
x_107 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___lam__1(x_94, x_105, x_2, x_3, x_4, x_5, x_6, x_106, x_12);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_33 = x_107;
goto block_90;
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_95);
lean_dec(x_93);
x_108 = lean_box(0);
x_109 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___lam__1(x_94, x_108, x_2, x_3, x_4, x_5, x_6, x_92, x_12);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_33 = x_109;
goto block_90;
}
}
else
{
lean_object* x_110; 
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_110 = lean_ctor_get(x_11, 1);
lean_inc(x_110);
lean_dec_ref(x_11);
x_16 = x_110;
x_17 = x_12;
goto block_32;
}
block_32:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_inc_ref(x_16);
x_18 = l_Array_shrink___redArg(x_16, x_15);
x_19 = lean_array_get_size(x_16);
x_20 = l_Array_extract___redArg(x_16, x_15, x_19);
lean_dec_ref(x_16);
x_21 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__5___closed__0;
x_22 = lean_unsigned_to_nat(0u);
x_23 = 0;
x_24 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__1;
x_25 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*3, x_23);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_task_pure(x_26);
x_28 = 0;
x_29 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_14);
lean_ctor_set(x_29, 2, x_21);
lean_ctor_set_uint8(x_29, sizeof(void*)*3, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_18);
if (lean_is_scalar(x_13)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_13;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_17);
return x_31;
}
block_90:
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_33, 1);
x_37 = lean_ctor_get(x_34, 0);
x_38 = lean_ctor_get(x_34, 1);
x_39 = lean_array_get_size(x_38);
x_40 = lean_nat_dec_lt(x_15, x_39);
if (x_40 == 0)
{
lean_dec(x_39);
lean_free_object(x_34);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_15);
return x_33;
}
else
{
uint8_t x_41; 
lean_inc(x_36);
x_41 = !lean_is_exclusive(x_33);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_33, 1);
lean_dec(x_42);
x_43 = lean_ctor_get(x_33, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_37, 0);
x_46 = lean_ctor_get(x_37, 1);
lean_dec(x_46);
lean_inc(x_38);
x_47 = l_Array_shrink___redArg(x_38, x_15);
x_48 = l_Array_extract___redArg(x_38, x_15, x_39);
lean_dec(x_38);
x_49 = lean_alloc_closure((void*)(l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___lam__0), 2, 1);
lean_closure_set(x_49, 0, x_48);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_task_map(x_49, x_45, x_50, x_9);
lean_ctor_set(x_37, 1, x_14);
lean_ctor_set(x_37, 0, x_51);
lean_ctor_set(x_34, 1, x_47);
return x_33;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_37, 0);
x_53 = lean_ctor_get(x_37, 2);
x_54 = lean_ctor_get_uint8(x_37, sizeof(void*)*3);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_37);
lean_inc(x_38);
x_55 = l_Array_shrink___redArg(x_38, x_15);
x_56 = l_Array_extract___redArg(x_38, x_15, x_39);
lean_dec(x_38);
x_57 = lean_alloc_closure((void*)(l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___lam__0), 2, 1);
lean_closure_set(x_57, 0, x_56);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_task_map(x_57, x_52, x_58, x_9);
x_60 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_14);
lean_ctor_set(x_60, 2, x_53);
lean_ctor_set_uint8(x_60, sizeof(void*)*3, x_54);
lean_ctor_set(x_34, 1, x_55);
lean_ctor_set(x_34, 0, x_60);
return x_33;
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_33);
x_61 = lean_ctor_get(x_37, 0);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_37, 2);
lean_inc_ref(x_62);
x_63 = lean_ctor_get_uint8(x_37, sizeof(void*)*3);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 x_64 = x_37;
} else {
 lean_dec_ref(x_37);
 x_64 = lean_box(0);
}
lean_inc(x_38);
x_65 = l_Array_shrink___redArg(x_38, x_15);
x_66 = l_Array_extract___redArg(x_38, x_15, x_39);
lean_dec(x_38);
x_67 = lean_alloc_closure((void*)(l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___lam__0), 2, 1);
lean_closure_set(x_67, 0, x_66);
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_task_map(x_67, x_61, x_68, x_9);
if (lean_is_scalar(x_64)) {
 x_70 = lean_alloc_ctor(0, 3, 1);
} else {
 x_70 = x_64;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_14);
lean_ctor_set(x_70, 2, x_62);
lean_ctor_set_uint8(x_70, sizeof(void*)*3, x_63);
lean_ctor_set(x_34, 1, x_65);
lean_ctor_set(x_34, 0, x_70);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_34);
lean_ctor_set(x_71, 1, x_36);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_72 = lean_ctor_get(x_33, 1);
x_73 = lean_ctor_get(x_34, 0);
x_74 = lean_ctor_get(x_34, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_34);
x_75 = lean_array_get_size(x_74);
x_76 = lean_nat_dec_lt(x_15, x_75);
if (x_76 == 0)
{
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_15);
return x_33;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_inc(x_72);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_77 = x_33;
} else {
 lean_dec_ref(x_33);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_73, 0);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_73, 2);
lean_inc_ref(x_79);
x_80 = lean_ctor_get_uint8(x_73, sizeof(void*)*3);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 x_81 = x_73;
} else {
 lean_dec_ref(x_73);
 x_81 = lean_box(0);
}
lean_inc(x_74);
x_82 = l_Array_shrink___redArg(x_74, x_15);
x_83 = l_Array_extract___redArg(x_74, x_15, x_75);
lean_dec(x_74);
x_84 = lean_alloc_closure((void*)(l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___lam__0), 2, 1);
lean_closure_set(x_84, 0, x_83);
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_task_map(x_84, x_78, x_85, x_9);
if (lean_is_scalar(x_81)) {
 x_87 = lean_alloc_ctor(0, 3, 1);
} else {
 x_87 = x_81;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_14);
lean_ctor_set(x_87, 2, x_79);
lean_ctor_set_uint8(x_87, sizeof(void*)*3, x_80);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_82);
if (lean_is_scalar(x_77)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_77;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_72);
return x_89;
}
}
}
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__1;
x_3 = 0;
x_4 = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__0;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_size(x_1);
x_11 = 0;
x_12 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1(x_2, x_10, x_11, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_box(0);
x_19 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__5___closed__0;
x_20 = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__1;
lean_ctor_set(x_13, 1, x_20);
x_21 = lean_task_pure(x_13);
x_22 = 0;
x_23 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_19);
lean_ctor_set_uint8(x_23, sizeof(void*)*3, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
lean_ctor_set(x_12, 0, x_24);
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
x_27 = lean_box(0);
x_28 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__5___closed__0;
x_29 = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__1;
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_task_pure(x_30);
x_32 = 0;
x_33 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_27);
lean_ctor_set(x_33, 2, x_28);
lean_ctor_set_uint8(x_33, sizeof(void*)*3, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_26);
lean_ctor_set(x_12, 0, x_34);
return x_12;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_35 = lean_ctor_get(x_12, 1);
lean_inc(x_35);
lean_dec(x_12);
x_36 = lean_ctor_get(x_13, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_38 = x_13;
} else {
 lean_dec_ref(x_13);
 x_38 = lean_box(0);
}
x_39 = lean_box(0);
x_40 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__5___closed__0;
x_41 = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__1;
if (lean_is_scalar(x_38)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_38;
}
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_task_pure(x_42);
x_44 = 0;
x_45 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_39);
lean_ctor_set(x_45, 2, x_40);
lean_ctor_set_uint8(x_45, sizeof(void*)*3, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_37);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_35);
return x_47;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_12);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_12, 0);
lean_dec(x_49);
x_50 = !lean_is_exclusive(x_13);
if (x_50 == 0)
{
return x_12;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_13, 0);
x_52 = lean_ctor_get(x_13, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_13);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_12, 0, x_53);
return x_12;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_12, 1);
lean_inc(x_54);
lean_dec(x_12);
x_55 = lean_ctor_get(x_13, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_13, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_57 = x_13;
} else {
 lean_dec_ref(x_13);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_54);
return x_59;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 9);
lean_inc_ref(x_9);
x_10 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___boxed), 9, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_1);
x_11 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_get_x3f___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_get_x3f___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1_spec__1___redArg(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec_ref(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1_spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__3___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__4___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__4___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__6___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__6___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__8(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeRightWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__9(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_formatQuery___at___Lake_Package_depsFacetConfig_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_formatQuery___at___Lake_Package_depsFacetConfig_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = 1;
x_9 = l_Lean_Name_toString(x_7, x_8);
x_10 = lean_string_append(x_4, x_9);
lean_dec_ref(x_9);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_formatQuery___at___Lake_Package_depsFacetConfig_spec__0_spec__0___closed__0;
x_12 = lean_string_append(x_10, x_11);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_12;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_toJson___at___Lake_formatQuery___at___Lake_Package_depsFacetConfig_spec__0_spec__1_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_6, x_4);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_13 = lean_array_uset(x_8, x_2, x_10);
x_2 = x_12;
x_3 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___Lake_formatQuery___at___Lake_Package_depsFacetConfig_spec__0_spec__1(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_toJson___at___Lake_formatQuery___at___Lake_Package_depsFacetConfig_spec__0_spec__1_spec__1(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___Lake_Package_depsFacetConfig_spec__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
if (x_1 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__5___closed__0;
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_2);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec_ref(x_2);
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
lean_dec_ref(x_2);
x_3 = x_11;
goto block_10;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_formatQuery___at___Lake_Package_depsFacetConfig_spec__0_spec__0(x_2, x_16, x_17, x_11);
lean_dec_ref(x_2);
x_3 = x_18;
goto block_10;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Array_toJson___at___Lake_formatQuery___at___Lake_Package_depsFacetConfig_spec__0_spec__1(x_2);
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
lean_inc_ref(x_3);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = l_Substring_prevn(x_7, x_4, x_6);
lean_dec_ref(x_7);
x_9 = lean_string_utf8_extract(x_3, x_5, x_8);
lean_dec(x_8);
lean_dec_ref(x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_depsFacetConfig___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_formatQuery___at___Lake_Package_depsFacetConfig_spec__0(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_depsFacetConfig___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_depsFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_depsFacetConfig___lam__0___boxed), 2, 0);
x_2 = lean_box(0);
x_3 = l_Lake_Package_keyword;
x_4 = l_Lake_Package_depsFacetConfig___closed__0;
x_5 = 0;
x_6 = 1;
x_7 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_2);
lean_ctor_set(x_7, 3, x_1);
lean_ctor_set_uint8(x_7, sizeof(void*)*4, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*4 + 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_formatQuery___at___Lake_Package_depsFacetConfig_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_formatQuery___at___Lake_Package_depsFacetConfig_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_toJson___at___Lake_formatQuery___at___Lake_Package_depsFacetConfig_spec__0_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_toJson___at___Lake_formatQuery___at___Lake_Package_depsFacetConfig_spec__0_spec__1_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___Lake_Package_depsFacetConfig_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lake_formatQuery___at___Lake_Package_depsFacetConfig_spec__0(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_depsFacetConfig___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lake_Package_depsFacetConfig___lam__0(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_contains___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_name_eq(x_6, x_7);
if (x_8 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_8;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_contains___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_contains___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; uint8_t x_19; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_array_get_size(x_3);
x_6 = l_Lean_Name_hash___override(x_4);
x_7 = 32;
x_8 = lean_uint64_shift_right(x_6, x_7);
x_9 = lean_uint64_xor(x_6, x_8);
x_10 = 16;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = lean_uint64_to_usize(x_12);
x_14 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_15 = 1;
x_16 = lean_usize_sub(x_14, x_15);
x_17 = lean_usize_land(x_13, x_16);
x_18 = lean_array_uget(x_3, x_17);
x_19 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_contains___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__0___redArg(x_2, x_18);
lean_dec(x_18);
return x_19;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__2_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_array_get_size(x_1);
x_8 = l_Lean_Name_hash___override(x_6);
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
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_array_get_size(x_1);
x_28 = l_Lean_Name_hash___override(x_26);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__2_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__2_spec__2_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__2_spec__2_spec__2___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__2_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__2___redArg(lean_object* x_1) {
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
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__2_spec__2___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__2___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; uint8_t x_21; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_array_get_size(x_5);
x_8 = l_Lean_Name_hash___override(x_6);
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
x_20 = lean_array_uget(x_5, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_contains___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__0___redArg(x_2, x_20);
if (x_21 == 0)
{
uint8_t x_22; 
lean_inc_ref(x_5);
lean_inc(x_4);
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_4, x_25);
lean_dec(x_4);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_3);
lean_ctor_set(x_27, 2, x_20);
x_28 = lean_array_uset(x_5, x_19, x_27);
x_29 = lean_unsigned_to_nat(4u);
x_30 = lean_nat_mul(x_26, x_29);
x_31 = lean_unsigned_to_nat(3u);
x_32 = lean_nat_div(x_30, x_31);
lean_dec(x_30);
x_33 = lean_array_get_size(x_28);
x_34 = lean_nat_dec_le(x_32, x_33);
lean_dec(x_33);
lean_dec(x_32);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__2___redArg(x_28);
lean_ctor_set(x_1, 1, x_35);
lean_ctor_set(x_1, 0, x_26);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_28);
lean_ctor_set(x_1, 0, x_26);
return x_1;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_1);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_4, x_36);
lean_dec(x_4);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_3);
lean_ctor_set(x_38, 2, x_20);
x_39 = lean_array_uset(x_5, x_19, x_38);
x_40 = lean_unsigned_to_nat(4u);
x_41 = lean_nat_mul(x_37, x_40);
x_42 = lean_unsigned_to_nat(3u);
x_43 = lean_nat_div(x_41, x_42);
lean_dec(x_41);
x_44 = lean_array_get_size(x_39);
x_45 = lean_nat_dec_le(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__2___redArg(x_39);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_37);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_37);
lean_ctor_set(x_48, 1, x_39);
return x_48;
}
}
}
else
{
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(x_3, x_2);
if (x_5 == 0)
{
uint8_t x_6; 
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 1);
lean_dec(x_7);
x_8 = lean_ctor_get(x_1, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_inc_ref(x_2);
x_10 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2___redArg(x_3, x_2, x_9);
x_11 = lean_array_push(x_4, x_2);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_12 = lean_box(0);
lean_inc_ref(x_2);
x_13 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2___redArg(x_3, x_2, x_12);
x_14 = lean_array_push(x_4, x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_dec_ref(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(x_4, x_6);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
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
static lean_object* _init_l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__5;
x_2 = l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__6;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__10_spec__10(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_19; 
x_19 = lean_usize_dec_eq(x_3, x_4);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_array_uget(x_2, x_3);
x_21 = lean_ctor_get(x_10, 1);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_ctor_get(x_21, 4);
x_24 = l_Std_DTreeMap_Internal_Impl_get_x3f___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__0___redArg(x_23, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec_ref(x_1);
x_26 = 1;
x_27 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_25, x_26);
x_28 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1_spec__1___redArg___closed__0;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_22, x_26);
x_31 = lean_string_append(x_29, x_30);
lean_dec_ref(x_30);
x_32 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1_spec__1___redArg___closed__1;
x_33 = lean_string_append(x_31, x_32);
x_34 = 3;
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = lean_array_get_size(x_11);
x_37 = lean_array_push(x_11, x_35);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_12);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_22);
x_40 = !lean_is_exclusive(x_24);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_41 = lean_ctor_get(x_24, 0);
x_61 = lean_ctor_get(x_41, 0);
x_62 = l_Lake_Package_transDepsFacet;
lean_inc(x_61);
lean_ctor_set(x_24, 0, x_61);
x_63 = l_Lake_Package_keyword;
lean_inc(x_41);
x_64 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_64, 0, x_24);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_41);
lean_ctor_set(x_64, 3, x_62);
lean_inc_ref(x_6);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_65 = lean_apply_7(x_6, x_64, x_7, x_8, x_9, x_10, x_11, x_12);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec_ref(x_65);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec_ref(x_66);
x_70 = lean_ctor_get(x_67, 0);
lean_inc_ref(x_70);
lean_dec(x_67);
x_71 = lean_io_wait(x_70, x_68);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec_ref(x_71);
x_75 = lean_ctor_get(x_72, 0);
lean_inc(x_75);
lean_dec_ref(x_72);
x_76 = lean_ctor_get(x_73, 0);
lean_inc_ref(x_76);
lean_dec(x_73);
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_array_get_size(x_76);
x_79 = lean_nat_dec_lt(x_77, x_78);
if (x_79 == 0)
{
lean_dec(x_78);
lean_dec_ref(x_76);
x_50 = x_75;
x_51 = x_69;
x_52 = x_74;
goto block_60;
}
else
{
uint8_t x_80; 
x_80 = lean_nat_dec_le(x_78, x_78);
if (x_80 == 0)
{
lean_dec(x_78);
lean_dec_ref(x_76);
x_50 = x_75;
x_51 = x_69;
x_52 = x_74;
goto block_60;
}
else
{
lean_object* x_81; size_t x_82; size_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_81 = lean_box(0);
x_82 = 0;
x_83 = lean_usize_of_nat(x_78);
lean_dec(x_78);
x_84 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__8(x_76, x_82, x_83, x_81, x_69, x_74);
lean_dec_ref(x_76);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec_ref(x_84);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_50 = x_75;
x_51 = x_87;
x_52 = x_86;
goto block_60;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
lean_dec(x_41);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_88 = lean_ctor_get(x_72, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_71, 1);
lean_inc(x_89);
lean_dec_ref(x_71);
x_90 = lean_ctor_get(x_72, 0);
lean_inc(x_90);
lean_dec_ref(x_72);
x_91 = lean_ctor_get(x_88, 0);
lean_inc_ref(x_91);
lean_dec(x_88);
x_92 = lean_unsigned_to_nat(0u);
x_93 = lean_array_get_size(x_91);
x_94 = lean_nat_dec_lt(x_92, x_93);
if (x_94 == 0)
{
lean_dec(x_93);
lean_dec_ref(x_91);
x_13 = x_90;
x_14 = x_69;
x_15 = x_89;
goto block_18;
}
else
{
uint8_t x_95; 
x_95 = lean_nat_dec_le(x_93, x_93);
if (x_95 == 0)
{
lean_dec(x_93);
lean_dec_ref(x_91);
x_13 = x_90;
x_14 = x_69;
x_15 = x_89;
goto block_18;
}
else
{
lean_object* x_96; size_t x_97; size_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_96 = lean_box(0);
x_97 = 0;
x_98 = lean_usize_of_nat(x_93);
lean_dec(x_93);
x_99 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__8(x_91, x_97, x_98, x_96, x_69, x_89);
lean_dec_ref(x_91);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec_ref(x_99);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_13 = x_90;
x_14 = x_102;
x_15 = x_101;
goto block_18;
}
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_41);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_103 = !lean_is_exclusive(x_65);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_65, 0);
lean_dec(x_104);
x_105 = !lean_is_exclusive(x_66);
if (x_105 == 0)
{
return x_65;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_66, 0);
x_107 = lean_ctor_get(x_66, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_66);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set(x_65, 0, x_108);
return x_65;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_109 = lean_ctor_get(x_65, 1);
lean_inc(x_109);
lean_dec(x_65);
x_110 = lean_ctor_get(x_66, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_66, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_112 = x_66;
} else {
 lean_dec_ref(x_66);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_109);
return x_114;
}
}
block_49:
{
lean_object* x_45; size_t x_46; size_t x_47; 
x_45 = l_Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(x_44, x_41);
x_46 = 1;
x_47 = lean_usize_add(x_3, x_46);
x_3 = x_47;
x_5 = x_45;
x_11 = x_43;
x_12 = x_42;
goto _start;
}
block_60:
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_array_get_size(x_50);
x_55 = lean_nat_dec_lt(x_53, x_54);
if (x_55 == 0)
{
lean_dec(x_54);
lean_dec_ref(x_50);
x_42 = x_52;
x_43 = x_51;
x_44 = x_5;
goto block_49;
}
else
{
uint8_t x_56; 
x_56 = lean_nat_dec_le(x_54, x_54);
if (x_56 == 0)
{
lean_dec(x_54);
lean_dec_ref(x_50);
x_42 = x_52;
x_43 = x_51;
x_44 = x_5;
goto block_49;
}
else
{
size_t x_57; size_t x_58; lean_object* x_59; 
x_57 = 0;
x_58 = lean_usize_of_nat(x_54);
lean_dec(x_54);
x_59 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__7(x_50, x_57, x_58, x_5);
lean_dec_ref(x_50);
x_42 = x_52;
x_43 = x_51;
x_44 = x_59;
goto block_49;
}
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_115 = lean_ctor_get(x_24, 0);
lean_inc(x_115);
lean_dec(x_24);
x_135 = lean_ctor_get(x_115, 0);
x_136 = l_Lake_Package_transDepsFacet;
lean_inc(x_135);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_135);
x_138 = l_Lake_Package_keyword;
lean_inc(x_115);
x_139 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
lean_ctor_set(x_139, 2, x_115);
lean_ctor_set(x_139, 3, x_136);
lean_inc_ref(x_6);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_140 = lean_apply_7(x_6, x_139, x_7, x_8, x_9, x_10, x_11, x_12);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
lean_dec_ref(x_140);
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
lean_dec_ref(x_141);
x_145 = lean_ctor_get(x_142, 0);
lean_inc_ref(x_145);
lean_dec(x_142);
x_146 = lean_io_wait(x_145, x_143);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
x_149 = lean_ctor_get(x_146, 1);
lean_inc(x_149);
lean_dec_ref(x_146);
x_150 = lean_ctor_get(x_147, 0);
lean_inc(x_150);
lean_dec_ref(x_147);
x_151 = lean_ctor_get(x_148, 0);
lean_inc_ref(x_151);
lean_dec(x_148);
x_152 = lean_unsigned_to_nat(0u);
x_153 = lean_array_get_size(x_151);
x_154 = lean_nat_dec_lt(x_152, x_153);
if (x_154 == 0)
{
lean_dec(x_153);
lean_dec_ref(x_151);
x_124 = x_150;
x_125 = x_144;
x_126 = x_149;
goto block_134;
}
else
{
uint8_t x_155; 
x_155 = lean_nat_dec_le(x_153, x_153);
if (x_155 == 0)
{
lean_dec(x_153);
lean_dec_ref(x_151);
x_124 = x_150;
x_125 = x_144;
x_126 = x_149;
goto block_134;
}
else
{
lean_object* x_156; size_t x_157; size_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_156 = lean_box(0);
x_157 = 0;
x_158 = lean_usize_of_nat(x_153);
lean_dec(x_153);
x_159 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__8(x_151, x_157, x_158, x_156, x_144, x_149);
lean_dec_ref(x_151);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec_ref(x_159);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_124 = x_150;
x_125 = x_162;
x_126 = x_161;
goto block_134;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
lean_dec(x_115);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_163 = lean_ctor_get(x_147, 1);
lean_inc(x_163);
x_164 = lean_ctor_get(x_146, 1);
lean_inc(x_164);
lean_dec_ref(x_146);
x_165 = lean_ctor_get(x_147, 0);
lean_inc(x_165);
lean_dec_ref(x_147);
x_166 = lean_ctor_get(x_163, 0);
lean_inc_ref(x_166);
lean_dec(x_163);
x_167 = lean_unsigned_to_nat(0u);
x_168 = lean_array_get_size(x_166);
x_169 = lean_nat_dec_lt(x_167, x_168);
if (x_169 == 0)
{
lean_dec(x_168);
lean_dec_ref(x_166);
x_13 = x_165;
x_14 = x_144;
x_15 = x_164;
goto block_18;
}
else
{
uint8_t x_170; 
x_170 = lean_nat_dec_le(x_168, x_168);
if (x_170 == 0)
{
lean_dec(x_168);
lean_dec_ref(x_166);
x_13 = x_165;
x_14 = x_144;
x_15 = x_164;
goto block_18;
}
else
{
lean_object* x_171; size_t x_172; size_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_171 = lean_box(0);
x_172 = 0;
x_173 = lean_usize_of_nat(x_168);
lean_dec(x_168);
x_174 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__8(x_166, x_172, x_173, x_171, x_144, x_164);
lean_dec_ref(x_166);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec_ref(x_174);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_13 = x_165;
x_14 = x_177;
x_15 = x_176;
goto block_18;
}
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_115);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_178 = lean_ctor_get(x_140, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_179 = x_140;
} else {
 lean_dec_ref(x_140);
 x_179 = lean_box(0);
}
x_180 = lean_ctor_get(x_141, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_141, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_182 = x_141;
} else {
 lean_dec_ref(x_141);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
if (lean_is_scalar(x_179)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_179;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_178);
return x_184;
}
block_123:
{
lean_object* x_119; size_t x_120; size_t x_121; 
x_119 = l_Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(x_118, x_115);
x_120 = 1;
x_121 = lean_usize_add(x_3, x_120);
x_3 = x_121;
x_5 = x_119;
x_11 = x_117;
x_12 = x_116;
goto _start;
}
block_134:
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_127 = lean_unsigned_to_nat(0u);
x_128 = lean_array_get_size(x_124);
x_129 = lean_nat_dec_lt(x_127, x_128);
if (x_129 == 0)
{
lean_dec(x_128);
lean_dec_ref(x_124);
x_116 = x_126;
x_117 = x_125;
x_118 = x_5;
goto block_123;
}
else
{
uint8_t x_130; 
x_130 = lean_nat_dec_le(x_128, x_128);
if (x_130 == 0)
{
lean_dec(x_128);
lean_dec_ref(x_124);
x_116 = x_126;
x_117 = x_125;
x_118 = x_5;
goto block_123;
}
else
{
size_t x_131; size_t x_132; lean_object* x_133; 
x_131 = 0;
x_132 = lean_usize_of_nat(x_128);
lean_dec(x_128);
x_133 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__7(x_124, x_131, x_132, x_5);
lean_dec_ref(x_124);
x_116 = x_126;
x_117 = x_125;
x_118 = x_133;
goto block_123;
}
}
}
}
}
}
else
{
lean_object* x_185; lean_object* x_186; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_5);
lean_ctor_set(x_185, 1, x_11);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_12);
return x_186;
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__10(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_19; 
x_19 = lean_usize_dec_eq(x_3, x_4);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_array_uget(x_2, x_3);
x_21 = lean_ctor_get(x_10, 1);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_ctor_get(x_21, 4);
x_24 = l_Std_DTreeMap_Internal_Impl_get_x3f___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__0___redArg(x_23, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec_ref(x_1);
x_26 = 1;
x_27 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_25, x_26);
x_28 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1_spec__1___redArg___closed__0;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_22, x_26);
x_31 = lean_string_append(x_29, x_30);
lean_dec_ref(x_30);
x_32 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1_spec__1___redArg___closed__1;
x_33 = lean_string_append(x_31, x_32);
x_34 = 3;
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = lean_array_get_size(x_11);
x_37 = lean_array_push(x_11, x_35);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_12);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_22);
x_40 = !lean_is_exclusive(x_24);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_41 = lean_ctor_get(x_24, 0);
x_61 = lean_ctor_get(x_41, 0);
x_62 = l_Lake_Package_transDepsFacet;
lean_inc(x_61);
lean_ctor_set(x_24, 0, x_61);
x_63 = l_Lake_Package_keyword;
lean_inc(x_41);
x_64 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_64, 0, x_24);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_41);
lean_ctor_set(x_64, 3, x_62);
lean_inc_ref(x_6);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_65 = lean_apply_7(x_6, x_64, x_7, x_8, x_9, x_10, x_11, x_12);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec_ref(x_65);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec_ref(x_66);
x_70 = lean_ctor_get(x_67, 0);
lean_inc_ref(x_70);
lean_dec(x_67);
x_71 = lean_io_wait(x_70, x_68);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec_ref(x_71);
x_75 = lean_ctor_get(x_72, 0);
lean_inc(x_75);
lean_dec_ref(x_72);
x_76 = lean_ctor_get(x_73, 0);
lean_inc_ref(x_76);
lean_dec(x_73);
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_array_get_size(x_76);
x_79 = lean_nat_dec_lt(x_77, x_78);
if (x_79 == 0)
{
lean_dec(x_78);
lean_dec_ref(x_76);
x_50 = x_75;
x_51 = x_69;
x_52 = x_74;
goto block_60;
}
else
{
uint8_t x_80; 
x_80 = lean_nat_dec_le(x_78, x_78);
if (x_80 == 0)
{
lean_dec(x_78);
lean_dec_ref(x_76);
x_50 = x_75;
x_51 = x_69;
x_52 = x_74;
goto block_60;
}
else
{
lean_object* x_81; size_t x_82; size_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_81 = lean_box(0);
x_82 = 0;
x_83 = lean_usize_of_nat(x_78);
lean_dec(x_78);
x_84 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__8(x_76, x_82, x_83, x_81, x_69, x_74);
lean_dec_ref(x_76);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec_ref(x_84);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_50 = x_75;
x_51 = x_87;
x_52 = x_86;
goto block_60;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
lean_dec(x_41);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_88 = lean_ctor_get(x_72, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_71, 1);
lean_inc(x_89);
lean_dec_ref(x_71);
x_90 = lean_ctor_get(x_72, 0);
lean_inc(x_90);
lean_dec_ref(x_72);
x_91 = lean_ctor_get(x_88, 0);
lean_inc_ref(x_91);
lean_dec(x_88);
x_92 = lean_unsigned_to_nat(0u);
x_93 = lean_array_get_size(x_91);
x_94 = lean_nat_dec_lt(x_92, x_93);
if (x_94 == 0)
{
lean_dec(x_93);
lean_dec_ref(x_91);
x_13 = x_90;
x_14 = x_69;
x_15 = x_89;
goto block_18;
}
else
{
uint8_t x_95; 
x_95 = lean_nat_dec_le(x_93, x_93);
if (x_95 == 0)
{
lean_dec(x_93);
lean_dec_ref(x_91);
x_13 = x_90;
x_14 = x_69;
x_15 = x_89;
goto block_18;
}
else
{
lean_object* x_96; size_t x_97; size_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_96 = lean_box(0);
x_97 = 0;
x_98 = lean_usize_of_nat(x_93);
lean_dec(x_93);
x_99 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__8(x_91, x_97, x_98, x_96, x_69, x_89);
lean_dec_ref(x_91);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec_ref(x_99);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_13 = x_90;
x_14 = x_102;
x_15 = x_101;
goto block_18;
}
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_41);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_103 = !lean_is_exclusive(x_65);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_65, 0);
lean_dec(x_104);
x_105 = !lean_is_exclusive(x_66);
if (x_105 == 0)
{
return x_65;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_66, 0);
x_107 = lean_ctor_get(x_66, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_66);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set(x_65, 0, x_108);
return x_65;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_109 = lean_ctor_get(x_65, 1);
lean_inc(x_109);
lean_dec(x_65);
x_110 = lean_ctor_get(x_66, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_66, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_112 = x_66;
} else {
 lean_dec_ref(x_66);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_109);
return x_114;
}
}
block_49:
{
lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; 
x_45 = l_Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(x_44, x_41);
x_46 = 1;
x_47 = lean_usize_add(x_3, x_46);
x_48 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__10_spec__10(x_1, x_2, x_47, x_4, x_45, x_6, x_7, x_8, x_9, x_10, x_42, x_43);
return x_48;
}
block_60:
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_array_get_size(x_50);
x_55 = lean_nat_dec_lt(x_53, x_54);
if (x_55 == 0)
{
lean_dec(x_54);
lean_dec_ref(x_50);
x_42 = x_51;
x_43 = x_52;
x_44 = x_5;
goto block_49;
}
else
{
uint8_t x_56; 
x_56 = lean_nat_dec_le(x_54, x_54);
if (x_56 == 0)
{
lean_dec(x_54);
lean_dec_ref(x_50);
x_42 = x_51;
x_43 = x_52;
x_44 = x_5;
goto block_49;
}
else
{
size_t x_57; size_t x_58; lean_object* x_59; 
x_57 = 0;
x_58 = lean_usize_of_nat(x_54);
lean_dec(x_54);
x_59 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__7(x_50, x_57, x_58, x_5);
lean_dec_ref(x_50);
x_42 = x_51;
x_43 = x_52;
x_44 = x_59;
goto block_49;
}
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_115 = lean_ctor_get(x_24, 0);
lean_inc(x_115);
lean_dec(x_24);
x_135 = lean_ctor_get(x_115, 0);
x_136 = l_Lake_Package_transDepsFacet;
lean_inc(x_135);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_135);
x_138 = l_Lake_Package_keyword;
lean_inc(x_115);
x_139 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
lean_ctor_set(x_139, 2, x_115);
lean_ctor_set(x_139, 3, x_136);
lean_inc_ref(x_6);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_140 = lean_apply_7(x_6, x_139, x_7, x_8, x_9, x_10, x_11, x_12);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
lean_dec_ref(x_140);
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
lean_dec_ref(x_141);
x_145 = lean_ctor_get(x_142, 0);
lean_inc_ref(x_145);
lean_dec(x_142);
x_146 = lean_io_wait(x_145, x_143);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
x_149 = lean_ctor_get(x_146, 1);
lean_inc(x_149);
lean_dec_ref(x_146);
x_150 = lean_ctor_get(x_147, 0);
lean_inc(x_150);
lean_dec_ref(x_147);
x_151 = lean_ctor_get(x_148, 0);
lean_inc_ref(x_151);
lean_dec(x_148);
x_152 = lean_unsigned_to_nat(0u);
x_153 = lean_array_get_size(x_151);
x_154 = lean_nat_dec_lt(x_152, x_153);
if (x_154 == 0)
{
lean_dec(x_153);
lean_dec_ref(x_151);
x_124 = x_150;
x_125 = x_144;
x_126 = x_149;
goto block_134;
}
else
{
uint8_t x_155; 
x_155 = lean_nat_dec_le(x_153, x_153);
if (x_155 == 0)
{
lean_dec(x_153);
lean_dec_ref(x_151);
x_124 = x_150;
x_125 = x_144;
x_126 = x_149;
goto block_134;
}
else
{
lean_object* x_156; size_t x_157; size_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_156 = lean_box(0);
x_157 = 0;
x_158 = lean_usize_of_nat(x_153);
lean_dec(x_153);
x_159 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__8(x_151, x_157, x_158, x_156, x_144, x_149);
lean_dec_ref(x_151);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec_ref(x_159);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_124 = x_150;
x_125 = x_162;
x_126 = x_161;
goto block_134;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
lean_dec(x_115);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_163 = lean_ctor_get(x_147, 1);
lean_inc(x_163);
x_164 = lean_ctor_get(x_146, 1);
lean_inc(x_164);
lean_dec_ref(x_146);
x_165 = lean_ctor_get(x_147, 0);
lean_inc(x_165);
lean_dec_ref(x_147);
x_166 = lean_ctor_get(x_163, 0);
lean_inc_ref(x_166);
lean_dec(x_163);
x_167 = lean_unsigned_to_nat(0u);
x_168 = lean_array_get_size(x_166);
x_169 = lean_nat_dec_lt(x_167, x_168);
if (x_169 == 0)
{
lean_dec(x_168);
lean_dec_ref(x_166);
x_13 = x_165;
x_14 = x_144;
x_15 = x_164;
goto block_18;
}
else
{
uint8_t x_170; 
x_170 = lean_nat_dec_le(x_168, x_168);
if (x_170 == 0)
{
lean_dec(x_168);
lean_dec_ref(x_166);
x_13 = x_165;
x_14 = x_144;
x_15 = x_164;
goto block_18;
}
else
{
lean_object* x_171; size_t x_172; size_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_171 = lean_box(0);
x_172 = 0;
x_173 = lean_usize_of_nat(x_168);
lean_dec(x_168);
x_174 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__8(x_166, x_172, x_173, x_171, x_144, x_164);
lean_dec_ref(x_166);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec_ref(x_174);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_13 = x_165;
x_14 = x_177;
x_15 = x_176;
goto block_18;
}
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_115);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_178 = lean_ctor_get(x_140, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_179 = x_140;
} else {
 lean_dec_ref(x_140);
 x_179 = lean_box(0);
}
x_180 = lean_ctor_get(x_141, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_141, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_182 = x_141;
} else {
 lean_dec_ref(x_141);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
if (lean_is_scalar(x_179)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_179;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_178);
return x_184;
}
block_123:
{
lean_object* x_119; size_t x_120; size_t x_121; lean_object* x_122; 
x_119 = l_Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(x_118, x_115);
x_120 = 1;
x_121 = lean_usize_add(x_3, x_120);
x_122 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__10_spec__10(x_1, x_2, x_121, x_4, x_119, x_6, x_7, x_8, x_9, x_10, x_116, x_117);
return x_122;
}
block_134:
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_127 = lean_unsigned_to_nat(0u);
x_128 = lean_array_get_size(x_124);
x_129 = lean_nat_dec_lt(x_127, x_128);
if (x_129 == 0)
{
lean_dec(x_128);
lean_dec_ref(x_124);
x_116 = x_125;
x_117 = x_126;
x_118 = x_5;
goto block_123;
}
else
{
uint8_t x_130; 
x_130 = lean_nat_dec_le(x_128, x_128);
if (x_130 == 0)
{
lean_dec(x_128);
lean_dec_ref(x_124);
x_116 = x_125;
x_117 = x_126;
x_118 = x_5;
goto block_123;
}
else
{
size_t x_131; size_t x_132; lean_object* x_133; 
x_131 = 0;
x_132 = lean_usize_of_nat(x_128);
lean_dec(x_128);
x_133 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__7(x_124, x_131, x_132, x_5);
lean_dec_ref(x_124);
x_116 = x_125;
x_117 = x_126;
x_118 = x_133;
goto block_123;
}
}
}
}
}
}
else
{
lean_object* x_185; lean_object* x_186; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_5);
lean_ctor_set(x_185, 1, x_11);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_12);
return x_186;
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
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_44; 
x_44 = lean_nat_dec_lt(x_1, x_2);
if (x_44 == 0)
{
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
x_13 = x_3;
x_14 = x_11;
x_15 = x_12;
goto block_43;
}
else
{
uint8_t x_45; 
x_45 = lean_nat_dec_le(x_2, x_2);
if (x_45 == 0)
{
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
x_13 = x_3;
x_14 = x_11;
x_15 = x_12;
goto block_43;
}
else
{
size_t x_46; size_t x_47; lean_object* x_48; lean_object* x_49; 
x_46 = 0;
x_47 = lean_usize_of_nat(x_2);
x_48 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__10(x_4, x_5, x_46, x_47, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec_ref(x_48);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec_ref(x_49);
x_13 = x_51;
x_14 = x_52;
x_15 = x_50;
goto block_43;
}
else
{
uint8_t x_53; 
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_48);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_48, 0);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_49);
if (x_55 == 0)
{
return x_48;
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
lean_ctor_set(x_48, 0, x_58);
return x_48;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_48, 1);
lean_inc(x_59);
lean_dec(x_48);
x_60 = lean_ctor_get(x_49, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_49, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_62 = x_49;
} else {
 lean_dec_ref(x_49);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_59);
return x_64;
}
}
}
}
block_43:
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
x_19 = lean_box(0);
x_20 = lean_mk_empty_array_with_capacity(x_1);
x_21 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__5___closed__0;
x_22 = 0;
x_23 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__1;
x_24 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_1);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_22);
lean_ctor_set(x_13, 1, x_24);
lean_ctor_set(x_13, 0, x_17);
x_25 = lean_task_pure(x_13);
x_26 = 0;
x_27 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 2, x_21);
lean_ctor_set_uint8(x_27, sizeof(void*)*3, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_14);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_15);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_dec(x_13);
x_31 = lean_box(0);
x_32 = lean_mk_empty_array_with_capacity(x_1);
x_33 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__5___closed__0;
x_34 = 0;
x_35 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__1;
x_36 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_1);
lean_ctor_set_uint8(x_36, sizeof(void*)*3, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_task_pure(x_37);
x_39 = 0;
x_40 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_31);
lean_ctor_set(x_40, 2, x_33);
lean_ctor_set_uint8(x_40, sizeof(void*)*3, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_14);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_15);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 9);
lean_inc_ref(x_9);
x_10 = l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9;
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get_size(x_9);
x_13 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0___boxed), 12, 5);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_10);
lean_closure_set(x_13, 3, x_1);
lean_closure_set(x_13, 4, x_9);
x_14 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_contains___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_contains___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_contains___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_contains___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lake_OrdHashSet_insert___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__7(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__8(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__10_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__10_spec__10(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__10(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_5);
lean_dec(x_2);
return x_13;
}
}
static lean_object* _init_l_Lake_Package_transDepsFacetConfig___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_depsFacetConfig___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_transDepsFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_transDepsFacetConfig___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = 1;
x_2 = l_Lake_Package_transDepsFacetConfig___closed__0;
x_3 = 0;
x_4 = lean_box(0);
x_5 = l_Lake_Package_transDepsFacetConfig___closed__1;
x_6 = l_Lake_Package_keyword;
x_7 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_2);
lean_ctor_set_uint8(x_7, sizeof(void*)*4, x_3);
lean_ctor_set_uint8(x_7, sizeof(void*)*4 + 1, x_1);
return x_7;
}
}
static lean_object* _init_l_Lake_Package_transDepsFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_transDepsFacetConfig___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_ctor_get_uint8(x_9, sizeof(void*)*26 + 2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = l_Lake_Package_optReservoirBarrelFacet;
lean_inc(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = l_Lake_Package_keyword;
x_15 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_1);
lean_ctor_set(x_15, 3, x_12);
x_16 = lean_apply_7(x_2, x_15, x_3, x_4, x_5, x_6, x_7, x_8);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = l_Lake_Package_optGitHubReleaseFacet;
lean_inc(x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_17);
x_20 = l_Lake_Package_keyword;
x_21 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_1);
lean_ctor_set(x_21, 3, x_18);
x_22 = lean_apply_7(x_2, x_21, x_3, x_4, x_5, x_6, x_7, x_8);
return x_22;
}
}
}
static lean_object* _init_l_Lake_formatQuery___at___Lake_Package_optBuildCacheFacetConfig_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_formatQuery___at___Lake_Package_optBuildCacheFacetConfig_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___Lake_Package_optBuildCacheFacetConfig_spec__0(uint8_t x_1, uint8_t x_2) {
_start:
{
if (x_1 == 0)
{
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = l_Lake_formatQuery___at___Lake_Package_optBuildCacheFacetConfig_spec__0___closed__0;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = l_Lake_formatQuery___at___Lake_Package_optBuildCacheFacetConfig_spec__0___closed__1;
return x_4;
}
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_5, 0, x_2);
x_6 = l_Lean_Json_compress(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig___lam__1(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_formatQuery___at___Lake_Package_optBuildCacheFacetConfig_spec__0(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_optBuildCacheFacetConfig___lam__0), 8, 0);
x_2 = lean_alloc_closure((void*)(l_Lake_Package_optBuildCacheFacetConfig___lam__1___boxed), 2, 0);
x_3 = l_Lake_instDataKindBool;
x_4 = l_Lake_Package_keyword;
x_5 = 1;
x_6 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*4 + 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___Lake_Package_optBuildCacheFacetConfig_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lake_formatQuery___at___Lake_Package_optBuildCacheFacetConfig_spec__0(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lake_Package_optBuildCacheFacetConfig___lam__1(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__1;
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__0;
x_2 = lean_task_pure(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("leanprover", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("leanprover-community", 20, 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_6, 1);
x_39 = lean_ctor_get(x_38, 1);
x_40 = lean_ctor_get_uint8(x_39, sizeof(void*)*13);
x_41 = lean_ctor_get(x_39, 12);
if (x_40 == 0)
{
uint8_t x_66; 
x_66 = 1;
x_42 = x_66;
x_43 = x_7;
x_44 = x_8;
goto block_65;
}
else
{
uint8_t x_67; 
x_67 = 0;
x_42 = x_67;
x_43 = x_7;
x_44 = x_8;
goto block_65;
}
block_18:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_box(0);
x_13 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__5___closed__0;
x_14 = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__1;
x_15 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set(x_15, 2, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
block_27:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = l_Lake_Package_optBuildCacheFacet;
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_24 = l_Lake_Package_keyword;
x_25 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_1);
lean_ctor_set(x_25, 3, x_22);
x_26 = lean_apply_7(x_2, x_25, x_3, x_4, x_5, x_6, x_21, x_19);
return x_26;
}
block_37:
{
if (x_33 == 0)
{
lean_dec_ref(x_31);
lean_dec(x_29);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_9 = x_28;
x_10 = x_32;
x_11 = x_33;
goto block_18;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_string_utf8_byte_size(x_31);
lean_dec_ref(x_31);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_nat_dec_eq(x_34, x_35);
lean_dec(x_34);
if (x_36 == 0)
{
x_19 = x_28;
x_20 = x_29;
x_21 = x_32;
goto block_27;
}
else
{
if (x_30 == 0)
{
lean_dec(x_29);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_9 = x_28;
x_10 = x_32;
x_11 = x_30;
goto block_18;
}
else
{
x_19 = x_28;
x_20 = x_29;
x_21 = x_32;
goto block_27;
}
}
}
}
block_65:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_1, 3);
x_46 = lean_ctor_get(x_1, 0);
x_47 = lean_ctor_get(x_1, 1);
x_48 = lean_ctor_get(x_1, 7);
x_49 = lean_ctor_get(x_45, 6);
x_50 = lean_ctor_get_uint8(x_45, sizeof(void*)*26 + 2);
lean_inc_ref(x_49);
x_51 = l_System_FilePath_normalize(x_49);
lean_inc_ref(x_47);
x_52 = l_Lake_joinRelative(x_47, x_51);
lean_dec_ref(x_51);
x_53 = l_System_FilePath_pathExists(x_52, x_44);
lean_dec_ref(x_52);
if (x_42 == 0)
{
lean_object* x_54; 
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec_ref(x_53);
x_9 = x_54;
x_10 = x_43;
x_11 = x_42;
goto block_18;
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
if (x_50 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_53, 1);
lean_inc(x_57);
lean_dec_ref(x_53);
x_58 = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__2;
x_59 = lean_string_dec_eq(x_48, x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__3;
x_61 = lean_string_dec_eq(x_48, x_60);
lean_inc_ref(x_41);
lean_inc(x_46);
x_28 = x_57;
x_29 = x_46;
x_30 = x_50;
x_31 = x_41;
x_32 = x_43;
x_33 = x_61;
goto block_37;
}
else
{
lean_inc_ref(x_41);
lean_inc(x_46);
x_28 = x_57;
x_29 = x_46;
x_30 = x_50;
x_31 = x_41;
x_32 = x_43;
x_33 = x_59;
goto block_37;
}
}
else
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_53, 1);
lean_inc(x_62);
lean_dec_ref(x_53);
lean_inc(x_46);
x_19 = x_62;
x_20 = x_46;
x_21 = x_43;
goto block_27;
}
}
else
{
lean_object* x_63; uint8_t x_64; 
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_63 = lean_ctor_get(x_53, 1);
lean_inc(x_63);
lean_dec_ref(x_53);
x_64 = 0;
x_9 = x_63;
x_10 = x_43;
x_11 = x_64;
goto block_18;
}
}
}
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" (run with '-v' for details)", 28, 28);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" (see '", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' for details)", 14, 14);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 3);
x_8 = 2;
x_9 = l_Lake_instDecidableEqVerbosity(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_10 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_5);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec_ref(x_1);
x_14 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1;
x_15 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_13, x_9);
x_16 = lean_string_append(x_14, x_15);
lean_dec_ref(x_15);
x_17 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = l_Lake_Name_eraseHead(x_2);
x_20 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_19, x_9);
x_21 = lean_string_append(x_18, x_20);
lean_dec_ref(x_20);
x_22 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_4);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_5);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*1 + 3);
x_12 = 2;
x_13 = l_Lake_instDecidableEqVerbosity(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_14 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec_ref(x_1);
x_18 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1;
x_19 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_17, x_13);
x_20 = lean_string_append(x_18, x_19);
lean_dec_ref(x_19);
x_21 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_Lake_Name_eraseHead(x_2);
x_24 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_23, x_13);
x_25 = lean_string_append(x_22, x_24);
lean_dec_ref(x_24);
x_26 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_9);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_get_set_stdout(x_1, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_box(0);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec_ref(x_20);
lean_inc(x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_26 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__0___redArg___lam__0(x_17, x_22, x_25, x_24, x_21);
lean_dec_ref(x_25);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_23);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_26, 0, x_32);
return x_26;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_20, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
lean_dec_ref(x_20);
x_41 = lean_box(0);
x_42 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__0___redArg___lam__0(x_17, x_22, x_41, x_40, x_21);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_10 = x_39;
x_11 = x_45;
x_12 = x_44;
goto block_15;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_get_set_stdin(x_1, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_box(0);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec_ref(x_20);
lean_inc(x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_26 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__1___redArg___lam__0(x_17, x_22, x_25, x_24, x_21);
lean_dec_ref(x_25);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_23);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_26, 0, x_32);
return x_26;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_20, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
lean_dec_ref(x_20);
x_41 = lean_box(0);
x_42 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__1___redArg___lam__0(x_17, x_22, x_41, x_40, x_21);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_10 = x_39;
x_11 = x_45;
x_12 = x_44;
goto block_15;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_get_set_stderr(x_1, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_box(0);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec_ref(x_20);
lean_inc(x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_26 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__2___redArg___lam__0(x_17, x_22, x_25, x_24, x_21);
lean_dec_ref(x_25);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_23);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_26, 0, x_32);
return x_26;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_20, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
lean_dec_ref(x_20);
x_41 = lean_box(0);
x_42 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__2___redArg___lam__0(x_17, x_22, x_41, x_40, x_21);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_10 = x_39;
x_11 = x_45;
x_12 = x_44;
goto block_15;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__0;
x_19 = lean_st_mk_ref(x_18, x_9);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_st_mk_ref(x_18, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = l_IO_FS_Stream_ofBuffer(x_20);
lean_inc(x_23);
x_26 = l_IO_FS_Stream_ofBuffer(x_23);
if (x_2 == 0)
{
x_27 = x_1;
goto block_54;
}
else
{
lean_object* x_55; 
lean_inc_ref(x_26);
x_55 = lean_alloc_closure((void*)(l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__2), 10, 3);
lean_closure_set(x_55, 0, lean_box(0));
lean_closure_set(x_55, 1, x_26);
lean_closure_set(x_55, 2, x_1);
x_27 = x_55;
goto block_54;
}
block_17:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
block_54:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_closure((void*)(l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__0), 10, 3);
lean_closure_set(x_28, 0, lean_box(0));
lean_closure_set(x_28, 1, x_26);
lean_closure_set(x_28, 2, x_27);
x_29 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__1___redArg(x_25, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec_ref(x_30);
x_34 = lean_st_ref_get(x_23, x_31);
lean_dec(x_23);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc_ref(x_37);
lean_dec(x_35);
x_38 = lean_string_validate_utf8(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec_ref(x_37);
x_39 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__4;
x_40 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__5(x_39);
x_10 = x_36;
x_11 = x_33;
x_12 = x_32;
x_13 = x_40;
goto block_17;
}
else
{
lean_object* x_41; 
x_41 = lean_string_from_utf8_unchecked(x_37);
lean_dec_ref(x_37);
x_10 = x_36;
x_11 = x_33;
x_12 = x_32;
x_13 = x_41;
goto block_17;
}
}
else
{
uint8_t x_42; 
lean_dec(x_23);
x_42 = !lean_is_exclusive(x_29);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_29, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_30);
if (x_44 == 0)
{
return x_29;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_30, 0);
x_46 = lean_ctor_get(x_30, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_30);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_29, 0, x_47);
return x_29;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_29, 1);
lean_inc(x_48);
lean_dec(x_29);
x_49 = lean_ctor_get(x_30, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_30, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_51 = x_30;
} else {
 lean_dec_ref(x_30);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec_ref(x_8);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_Lake_BuildTrace_mix(x_1, x_13);
x_15 = lean_apply_1(x_2, x_11);
x_16 = 1;
lean_ctor_set(x_10, 1, x_14);
x_17 = l_IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0___redArg(x_15, x_16, x_3, x_4, x_5, x_6, x_7, x_10, x_9);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_21 = x_17;
} else {
 lean_dec_ref(x_17);
 x_21 = lean_box(0);
}
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_23 = x_18;
} else {
 lean_dec_ref(x_18);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_31 = lean_string_utf8_byte_size(x_24);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_eq(x_31, x_32);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_22);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_22, 0);
x_36 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__2;
x_37 = l_Substring_takeWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__8(x_24, x_31, x_32);
x_38 = l_Substring_takeRightWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__9(x_24, x_37, x_31);
x_39 = lean_string_utf8_extract(x_24, x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_24);
x_40 = lean_string_append(x_36, x_39);
lean_dec_ref(x_39);
x_41 = 1;
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = lean_array_push(x_35, x_42);
lean_ctor_set(x_22, 0, x_43);
x_26 = x_22;
x_27 = x_20;
goto block_30;
}
else
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_44 = lean_ctor_get(x_22, 0);
x_45 = lean_ctor_get_uint8(x_22, sizeof(void*)*3);
x_46 = lean_ctor_get(x_22, 1);
x_47 = lean_ctor_get(x_22, 2);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_44);
lean_dec(x_22);
x_48 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__2;
x_49 = l_Substring_takeWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__8(x_24, x_31, x_32);
x_50 = l_Substring_takeRightWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__9(x_24, x_49, x_31);
x_51 = lean_string_utf8_extract(x_24, x_49, x_50);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_24);
x_52 = lean_string_append(x_48, x_51);
lean_dec_ref(x_51);
x_53 = 1;
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_53);
x_55 = lean_array_push(x_44, x_54);
x_56 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_46);
lean_ctor_set(x_56, 2, x_47);
lean_ctor_set_uint8(x_56, sizeof(void*)*3, x_45);
x_26 = x_56;
x_27 = x_20;
goto block_30;
}
}
else
{
lean_dec(x_31);
lean_dec(x_24);
x_26 = x_22;
x_27 = x_20;
goto block_30;
}
block_30:
{
lean_object* x_28; lean_object* x_29; 
if (lean_is_scalar(x_23)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_23;
}
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_26);
if (lean_is_scalar(x_21)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_21;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_17);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_17, 0);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_18);
if (x_59 == 0)
{
return x_17;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_18, 0);
x_61 = lean_ctor_get(x_18, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_18);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_17, 0, x_62);
return x_17;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_17, 1);
lean_inc(x_63);
lean_dec(x_17);
x_64 = lean_ctor_get(x_18, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_18, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_66 = x_18;
} else {
 lean_dec_ref(x_18);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_63);
return x_68;
}
}
}
else
{
lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_69 = lean_ctor_get(x_10, 0);
x_70 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_71 = lean_ctor_get(x_10, 1);
x_72 = lean_ctor_get(x_10, 2);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_69);
lean_dec(x_10);
x_73 = l_Lake_BuildTrace_mix(x_1, x_71);
x_74 = lean_apply_1(x_2, x_11);
x_75 = 1;
x_76 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_76, 0, x_69);
lean_ctor_set(x_76, 1, x_73);
lean_ctor_set(x_76, 2, x_72);
lean_ctor_set_uint8(x_76, sizeof(void*)*3, x_70);
x_77 = l_IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0___redArg(x_74, x_75, x_3, x_4, x_5, x_6, x_7, x_76, x_9);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_81 = x_77;
} else {
 lean_dec_ref(x_77);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_83 = x_78;
} else {
 lean_dec_ref(x_78);
 x_83 = lean_box(0);
}
x_84 = lean_ctor_get(x_79, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_79, 1);
lean_inc(x_85);
lean_dec(x_79);
x_91 = lean_string_utf8_byte_size(x_84);
x_92 = lean_unsigned_to_nat(0u);
x_93 = lean_nat_dec_eq(x_91, x_92);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_94 = lean_ctor_get(x_82, 0);
lean_inc_ref(x_94);
x_95 = lean_ctor_get_uint8(x_82, sizeof(void*)*3);
x_96 = lean_ctor_get(x_82, 1);
lean_inc_ref(x_96);
x_97 = lean_ctor_get(x_82, 2);
lean_inc(x_97);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 lean_ctor_release(x_82, 2);
 x_98 = x_82;
} else {
 lean_dec_ref(x_82);
 x_98 = lean_box(0);
}
x_99 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__2;
x_100 = l_Substring_takeWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__8(x_84, x_91, x_92);
x_101 = l_Substring_takeRightWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__9(x_84, x_100, x_91);
x_102 = lean_string_utf8_extract(x_84, x_100, x_101);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_84);
x_103 = lean_string_append(x_99, x_102);
lean_dec_ref(x_102);
x_104 = 1;
x_105 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set_uint8(x_105, sizeof(void*)*1, x_104);
x_106 = lean_array_push(x_94, x_105);
if (lean_is_scalar(x_98)) {
 x_107 = lean_alloc_ctor(0, 3, 1);
} else {
 x_107 = x_98;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_96);
lean_ctor_set(x_107, 2, x_97);
lean_ctor_set_uint8(x_107, sizeof(void*)*3, x_95);
x_86 = x_107;
x_87 = x_80;
goto block_90;
}
else
{
lean_dec(x_91);
lean_dec(x_84);
x_86 = x_82;
x_87 = x_80;
goto block_90;
}
block_90:
{
lean_object* x_88; lean_object* x_89; 
if (lean_is_scalar(x_83)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_83;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
if (lean_is_scalar(x_81)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_81;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_108 = lean_ctor_get(x_77, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_109 = x_77;
} else {
 lean_dec_ref(x_77);
 x_109 = lean_box(0);
}
x_110 = lean_ctor_get(x_78, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_78, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_112 = x_78;
} else {
 lean_dec_ref(x_78);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
if (lean_is_scalar(x_109)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_109;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_108);
return x_114;
}
}
}
else
{
uint8_t x_115; 
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_115 = !lean_is_exclusive(x_8);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_8);
lean_ctor_set(x_116, 1, x_9);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_8, 0);
x_118 = lean_ctor_get(x_8, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_8);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_9);
return x_120;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_dec(x_14);
x_15 = lean_alloc_closure((void*)(l_Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg___lam__0), 9, 7);
lean_closure_set(x_15, 0, x_10);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_5);
lean_closure_set(x_15, 3, x_6);
lean_closure_set(x_15, 4, x_7);
lean_closure_set(x_15, 5, x_8);
lean_closure_set(x_15, 6, x_9);
x_16 = lean_io_map_task(x_15, x_13, x_3, x_4, x_11);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = l_Lake_instDataKindUnit;
lean_ctor_set(x_1, 1, x_19);
lean_ctor_set(x_1, 0, x_18);
lean_ctor_set(x_16, 0, x_1);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = l_Lake_instDataKindUnit;
lean_ctor_set(x_1, 1, x_22);
lean_ctor_set(x_1, 0, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 2);
x_26 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_1);
x_27 = lean_alloc_closure((void*)(l_Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg___lam__0), 9, 7);
lean_closure_set(x_27, 0, x_10);
lean_closure_set(x_27, 1, x_2);
lean_closure_set(x_27, 2, x_5);
lean_closure_set(x_27, 3, x_6);
lean_closure_set(x_27, 4, x_7);
lean_closure_set(x_27, 5, x_8);
lean_closure_set(x_27, 6, x_9);
x_28 = lean_io_map_task(x_27, x_24, x_3, x_4, x_11);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
x_32 = l_Lake_instDataKindUnit;
x_33 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_25);
lean_ctor_set_uint8(x_33, sizeof(void*)*3, x_26);
if (lean_is_scalar(x_31)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_31;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("building from source; failed to fetch Reservoir build", 53, 53);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("building from source; failed to fetch GitHub release", 52, 52);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_optReservoirBarrelFacet;
x_2 = l_Lake_Name_eraseHead(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_optGitHubReleaseFacet;
x_2 = l_Lake_Name_eraseHead(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
if (x_2 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_1, 3);
x_65 = lean_ctor_get_uint8(x_64, sizeof(void*)*26 + 2);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_7, 0);
x_67 = lean_ctor_get(x_1, 0);
lean_inc(x_67);
lean_dec_ref(x_1);
x_68 = lean_ctor_get_uint8(x_66, sizeof(void*)*1 + 3);
x_69 = 2;
x_70 = l_Lake_instDecidableEqVerbosity(x_68, x_69);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_67);
x_71 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0;
x_10 = x_71;
x_11 = x_8;
x_12 = x_9;
goto block_36;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_72 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1;
x_73 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_67, x_70);
x_74 = lean_string_append(x_72, x_73);
lean_dec_ref(x_73);
x_75 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_76 = lean_string_append(x_74, x_75);
x_77 = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2;
x_78 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_77, x_70);
x_79 = lean_string_append(x_76, x_78);
lean_dec_ref(x_78);
x_80 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3;
x_81 = lean_string_append(x_79, x_80);
x_10 = x_81;
x_11 = x_8;
x_12 = x_9;
goto block_36;
}
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; 
x_82 = lean_ctor_get(x_7, 0);
x_83 = lean_ctor_get(x_1, 0);
lean_inc(x_83);
lean_dec_ref(x_1);
x_84 = lean_ctor_get_uint8(x_82, sizeof(void*)*1 + 3);
x_85 = 2;
x_86 = l_Lake_instDecidableEqVerbosity(x_84, x_85);
if (x_86 == 0)
{
lean_object* x_87; 
lean_dec(x_83);
x_87 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0;
x_37 = x_87;
x_38 = x_8;
x_39 = x_9;
goto block_63;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_88 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1;
x_89 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_83, x_86);
x_90 = lean_string_append(x_88, x_89);
lean_dec_ref(x_89);
x_91 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_92 = lean_string_append(x_90, x_91);
x_93 = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3;
x_94 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_93, x_86);
x_95 = lean_string_append(x_92, x_94);
lean_dec_ref(x_94);
x_96 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3;
x_97 = lean_string_append(x_95, x_96);
x_37 = x_97;
x_38 = x_8;
x_39 = x_9;
goto block_63;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec_ref(x_1);
x_98 = lean_box(0);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_8);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_9);
return x_100;
}
block_36:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__0;
x_16 = lean_string_append(x_15, x_10);
lean_dec_ref(x_10);
x_17 = 0;
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = lean_box(0);
x_20 = lean_array_push(x_14, x_18);
lean_ctor_set(x_11, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_11);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_12);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_25 = lean_ctor_get(x_11, 1);
x_26 = lean_ctor_get(x_11, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_23);
lean_dec(x_11);
x_27 = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__0;
x_28 = lean_string_append(x_27, x_10);
lean_dec_ref(x_10);
x_29 = 0;
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_29);
x_31 = lean_box(0);
x_32 = lean_array_push(x_23, x_30);
x_33 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_25);
lean_ctor_set(x_33, 2, x_26);
lean_ctor_set_uint8(x_33, sizeof(void*)*3, x_24);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_12);
return x_35;
}
}
block_63:
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_38, 0);
x_42 = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__1;
x_43 = lean_string_append(x_42, x_37);
lean_dec_ref(x_37);
x_44 = 2;
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_44);
x_46 = lean_box(0);
x_47 = lean_array_push(x_41, x_45);
lean_ctor_set(x_38, 0, x_47);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_38);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_39);
return x_49;
}
else
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_50 = lean_ctor_get(x_38, 0);
x_51 = lean_ctor_get_uint8(x_38, sizeof(void*)*3);
x_52 = lean_ctor_get(x_38, 1);
x_53 = lean_ctor_get(x_38, 2);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_50);
lean_dec(x_38);
x_54 = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__1;
x_55 = lean_string_append(x_54, x_37);
lean_dec_ref(x_37);
x_56 = 2;
x_57 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_56);
x_58 = lean_box(0);
x_59 = lean_array_push(x_50, x_57);
x_60 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_52);
lean_ctor_set(x_60, 2, x_53);
lean_ctor_set_uint8(x_60, sizeof(void*)*3, x_51);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_39);
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_9 = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed), 9, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = 0;
x_17 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__1;
x_18 = l_Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg(x_13, x_14, x_15, x_16, x_2, x_3, x_4, x_5, x_6, x_17, x_11);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_ctor_set(x_10, 0, x_20);
lean_ctor_set(x_18, 0, x_10);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_18);
lean_ctor_set(x_10, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_26 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed), 9, 1);
lean_closure_set(x_26, 0, x_1);
x_27 = lean_unsigned_to_nat(0u);
x_28 = 0;
x_29 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__1;
x_30 = l_Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg(x_24, x_26, x_27, x_28, x_2, x_3, x_4, x_5, x_6, x_29, x_11);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_25);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_36 = !lean_is_exclusive(x_9);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_9, 0);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_10);
if (x_38 == 0)
{
return x_9;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_10, 0);
x_40 = lean_ctor_get(x_10, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_10);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_9, 0, x_41);
return x_9;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_9, 1);
lean_inc(x_42);
lean_dec(x_9);
x_43 = lean_ctor_get(x_10, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_10, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_45 = x_10;
} else {
 lean_dec_ref(x_10);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_42);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0_spec__2___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0___redArg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
x_13 = l_Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
x_14 = l_Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_array_uget(x_2, x_4);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_1);
x_17 = l_Lake_Package_fetchTargetJob(x_1, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec_ref(x_18);
x_22 = l_Lake_Job_mix___redArg(x_5, x_20);
x_23 = 1;
x_24 = lean_usize_add(x_4, x_23);
x_4 = x_24;
x_5 = x_22;
x_11 = x_21;
x_12 = x_19;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_17, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
return x_17;
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
lean_ctor_set(x_17, 0, x_31);
return x_17;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_dec(x_17);
x_33 = lean_ctor_get(x_18, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_35 = x_18;
} else {
 lean_dec_ref(x_18);
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
LEAN_EXPORT lean_object* l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_JobResult_prependLog___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__1___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_33; 
x_9 = 1;
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_14 = l_Lake_instDataKindUnit;
x_15 = lean_array_get_size(x_7);
lean_dec_ref(x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_13);
x_91 = lean_ctor_get(x_11, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_11, 1);
lean_inc(x_92);
lean_dec_ref(x_11);
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec(x_91);
x_95 = lean_string_utf8_byte_size(x_93);
x_96 = lean_unsigned_to_nat(0u);
x_97 = lean_nat_dec_eq(x_95, x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_98 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__2;
x_99 = l_Substring_takeWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__8(x_93, x_95, x_96);
x_100 = l_Substring_takeRightWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__9(x_93, x_99, x_95);
x_101 = lean_string_utf8_extract(x_93, x_99, x_100);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_93);
x_102 = lean_string_append(x_98, x_101);
lean_dec_ref(x_101);
x_103 = 1;
x_104 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set_uint8(x_104, sizeof(void*)*1, x_103);
x_105 = lean_box(0);
x_106 = lean_array_push(x_92, x_104);
x_107 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__1___lam__1(x_94, x_105, x_2, x_3, x_4, x_5, x_6, x_106, x_12);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_33 = x_107;
goto block_90;
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_95);
lean_dec(x_93);
x_108 = lean_box(0);
x_109 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__1___lam__1(x_94, x_108, x_2, x_3, x_4, x_5, x_6, x_92, x_12);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_33 = x_109;
goto block_90;
}
}
else
{
lean_object* x_110; 
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_110 = lean_ctor_get(x_11, 1);
lean_inc(x_110);
lean_dec_ref(x_11);
x_16 = x_110;
x_17 = x_12;
goto block_32;
}
block_32:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_inc_ref(x_16);
x_18 = l_Array_shrink___redArg(x_16, x_15);
x_19 = lean_array_get_size(x_16);
x_20 = l_Array_extract___redArg(x_16, x_15, x_19);
lean_dec_ref(x_16);
x_21 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__5___closed__0;
x_22 = lean_unsigned_to_nat(0u);
x_23 = 0;
x_24 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__1;
x_25 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*3, x_23);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_task_pure(x_26);
x_28 = 0;
x_29 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_14);
lean_ctor_set(x_29, 2, x_21);
lean_ctor_set_uint8(x_29, sizeof(void*)*3, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_18);
if (lean_is_scalar(x_13)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_13;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_17);
return x_31;
}
block_90:
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_33, 1);
x_37 = lean_ctor_get(x_34, 0);
x_38 = lean_ctor_get(x_34, 1);
x_39 = lean_array_get_size(x_38);
x_40 = lean_nat_dec_lt(x_15, x_39);
if (x_40 == 0)
{
lean_dec(x_39);
lean_free_object(x_34);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_15);
return x_33;
}
else
{
uint8_t x_41; 
lean_inc(x_36);
x_41 = !lean_is_exclusive(x_33);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_33, 1);
lean_dec(x_42);
x_43 = lean_ctor_get(x_33, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_37, 0);
x_46 = lean_ctor_get(x_37, 1);
lean_dec(x_46);
lean_inc(x_38);
x_47 = l_Array_shrink___redArg(x_38, x_15);
x_48 = l_Array_extract___redArg(x_38, x_15, x_39);
lean_dec(x_38);
x_49 = lean_alloc_closure((void*)(l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__1___lam__0), 2, 1);
lean_closure_set(x_49, 0, x_48);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_task_map(x_49, x_45, x_50, x_9);
lean_ctor_set(x_37, 1, x_14);
lean_ctor_set(x_37, 0, x_51);
lean_ctor_set(x_34, 1, x_47);
return x_33;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_37, 0);
x_53 = lean_ctor_get(x_37, 2);
x_54 = lean_ctor_get_uint8(x_37, sizeof(void*)*3);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_37);
lean_inc(x_38);
x_55 = l_Array_shrink___redArg(x_38, x_15);
x_56 = l_Array_extract___redArg(x_38, x_15, x_39);
lean_dec(x_38);
x_57 = lean_alloc_closure((void*)(l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__1___lam__0), 2, 1);
lean_closure_set(x_57, 0, x_56);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_task_map(x_57, x_52, x_58, x_9);
x_60 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_14);
lean_ctor_set(x_60, 2, x_53);
lean_ctor_set_uint8(x_60, sizeof(void*)*3, x_54);
lean_ctor_set(x_34, 1, x_55);
lean_ctor_set(x_34, 0, x_60);
return x_33;
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_33);
x_61 = lean_ctor_get(x_37, 0);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_37, 2);
lean_inc_ref(x_62);
x_63 = lean_ctor_get_uint8(x_37, sizeof(void*)*3);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 x_64 = x_37;
} else {
 lean_dec_ref(x_37);
 x_64 = lean_box(0);
}
lean_inc(x_38);
x_65 = l_Array_shrink___redArg(x_38, x_15);
x_66 = l_Array_extract___redArg(x_38, x_15, x_39);
lean_dec(x_38);
x_67 = lean_alloc_closure((void*)(l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__1___lam__0), 2, 1);
lean_closure_set(x_67, 0, x_66);
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_task_map(x_67, x_61, x_68, x_9);
if (lean_is_scalar(x_64)) {
 x_70 = lean_alloc_ctor(0, 3, 1);
} else {
 x_70 = x_64;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_14);
lean_ctor_set(x_70, 2, x_62);
lean_ctor_set_uint8(x_70, sizeof(void*)*3, x_63);
lean_ctor_set(x_34, 1, x_65);
lean_ctor_set(x_34, 0, x_70);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_34);
lean_ctor_set(x_71, 1, x_36);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_72 = lean_ctor_get(x_33, 1);
x_73 = lean_ctor_get(x_34, 0);
x_74 = lean_ctor_get(x_34, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_34);
x_75 = lean_array_get_size(x_74);
x_76 = lean_nat_dec_lt(x_15, x_75);
if (x_76 == 0)
{
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_15);
return x_33;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_inc(x_72);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_77 = x_33;
} else {
 lean_dec_ref(x_33);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_73, 0);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_73, 2);
lean_inc_ref(x_79);
x_80 = lean_ctor_get_uint8(x_73, sizeof(void*)*3);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 x_81 = x_73;
} else {
 lean_dec_ref(x_73);
 x_81 = lean_box(0);
}
lean_inc(x_74);
x_82 = l_Array_shrink___redArg(x_74, x_15);
x_83 = l_Array_extract___redArg(x_74, x_15, x_75);
lean_dec(x_74);
x_84 = lean_alloc_closure((void*)(l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__1___lam__0), 2, 1);
lean_closure_set(x_84, 0, x_83);
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_task_map(x_84, x_78, x_85, x_9);
if (lean_is_scalar(x_81)) {
 x_87 = lean_alloc_ctor(0, 3, 1);
} else {
 x_87 = x_81;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_14);
lean_ctor_set(x_87, 2, x_79);
lean_ctor_set_uint8(x_87, sizeof(void*)*3, x_80);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_82);
if (lean_is_scalar(x_77)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_77;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_72);
return x_89;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_9, 1);
x_26 = lean_ctor_get(x_25, 0);
x_27 = lean_ctor_get(x_26, 0);
x_28 = lean_name_eq(x_3, x_27);
x_29 = l_instDecidableNot___redArg(x_28);
if (x_29 == 0)
{
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
x_16 = x_8;
x_17 = x_9;
x_18 = x_10;
x_19 = x_11;
goto block_24;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_2);
x_30 = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec_ref(x_31);
x_35 = l_Lake_Job_add___redArg(x_4, x_33);
x_12 = x_35;
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
x_16 = x_8;
x_17 = x_9;
x_18 = x_34;
x_19 = x_32;
goto block_24;
}
else
{
lean_dec_ref(x_31);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
return x_30;
}
}
block_24:
{
lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 3);
x_21 = lean_array_size(x_20);
x_22 = 0;
x_23 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(x_2, x_20, x_21, x_22, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_23;
}
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":extraDep", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_10);
x_11 = 1;
lean_inc(x_9);
x_12 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_9, x_11);
x_13 = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__0;
x_14 = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__1;
x_15 = lean_string_append(x_14, x_12);
x_16 = lean_string_append(x_15, x_13);
x_17 = lean_box(0);
x_18 = lean_box(0);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__0;
x_21 = 0;
x_22 = l_Lake_BuildTrace_nil(x_16);
x_23 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_19);
lean_ctor_set_uint8(x_23, sizeof(void*)*3, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_task_pure(x_24);
x_26 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__5___closed__0;
x_27 = 0;
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_18);
lean_ctor_set(x_28, 2, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_27);
x_29 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed), 11, 4);
lean_closure_set(x_29, 0, x_10);
lean_closure_set(x_29, 1, x_1);
lean_closure_set(x_29, 2, x_9);
lean_closure_set(x_29, 3, x_28);
lean_inc_ref(x_6);
x_30 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__1(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec_ref(x_30);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_37 = lean_ctor_get(x_32, 2);
lean_dec(x_37);
x_38 = lean_ctor_get(x_6, 3);
lean_inc(x_38);
lean_dec_ref(x_6);
x_39 = lean_st_ref_take(x_38, x_33);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = lean_string_append(x_12, x_13);
lean_ctor_set(x_32, 2, x_42);
lean_ctor_set_uint8(x_32, sizeof(void*)*3, x_27);
lean_inc_ref(x_32);
x_43 = l_Lake_Job_toOpaque___redArg(x_32);
x_44 = lean_array_push(x_40, x_43);
x_45 = lean_st_ref_set(x_38, x_44, x_41);
lean_dec(x_38);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
x_48 = l_Lake_Job_renew___redArg(x_32);
lean_ctor_set(x_31, 0, x_48);
lean_ctor_set(x_45, 0, x_31);
return x_45;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
x_50 = l_Lake_Job_renew___redArg(x_32);
lean_ctor_set(x_31, 0, x_50);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_31);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_52 = lean_ctor_get(x_32, 0);
x_53 = lean_ctor_get(x_32, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_32);
x_54 = lean_ctor_get(x_6, 3);
lean_inc(x_54);
lean_dec_ref(x_6);
x_55 = lean_st_ref_take(x_54, x_33);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec_ref(x_55);
x_58 = lean_string_append(x_12, x_13);
x_59 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_59, 0, x_52);
lean_ctor_set(x_59, 1, x_53);
lean_ctor_set(x_59, 2, x_58);
lean_ctor_set_uint8(x_59, sizeof(void*)*3, x_27);
lean_inc_ref(x_59);
x_60 = l_Lake_Job_toOpaque___redArg(x_59);
x_61 = lean_array_push(x_56, x_60);
x_62 = lean_st_ref_set(x_54, x_61, x_57);
lean_dec(x_54);
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
x_65 = l_Lake_Job_renew___redArg(x_59);
lean_ctor_set(x_31, 0, x_65);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_31);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_67 = lean_ctor_get(x_31, 1);
lean_inc(x_67);
lean_dec(x_31);
x_68 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_32, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 x_70 = x_32;
} else {
 lean_dec_ref(x_32);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get(x_6, 3);
lean_inc(x_71);
lean_dec_ref(x_6);
x_72 = lean_st_ref_take(x_71, x_33);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec_ref(x_72);
x_75 = lean_string_append(x_12, x_13);
if (lean_is_scalar(x_70)) {
 x_76 = lean_alloc_ctor(0, 3, 1);
} else {
 x_76 = x_70;
}
lean_ctor_set(x_76, 0, x_68);
lean_ctor_set(x_76, 1, x_69);
lean_ctor_set(x_76, 2, x_75);
lean_ctor_set_uint8(x_76, sizeof(void*)*3, x_27);
lean_inc_ref(x_76);
x_77 = l_Lake_Job_toOpaque___redArg(x_76);
x_78 = lean_array_push(x_73, x_77);
x_79 = lean_st_ref_set(x_71, x_78, x_74);
lean_dec(x_71);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_81 = x_79;
} else {
 lean_dec_ref(x_79);
 x_81 = lean_box(0);
}
x_82 = l_Lake_Job_renew___redArg(x_76);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_67);
if (lean_is_scalar(x_81)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_81;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_80);
return x_84;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__1___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__1___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_12;
}
}
static lean_object* _init_l_Lake_formatQuery___at___Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Json_compress(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___Lake_Package_extraDepFacetConfig_spec__0___redArg(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__5___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lake_formatQuery___at___Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___Lake_Package_extraDepFacetConfig_spec__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_formatQuery___at___Lake_Package_extraDepFacetConfig_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_formatQuery___at___Lake_Package_extraDepFacetConfig_spec__0___redArg(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_extraDepFacetConfig___lam__0___boxed), 2, 0);
x_2 = l_Lake_instDataKindUnit;
x_3 = l_Lake_Package_keyword;
x_4 = l_Lake_Package_extraDepFacetConfig___closed__0;
x_5 = 1;
x_6 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*4 + 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___Lake_Package_extraDepFacetConfig_spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_formatQuery___at___Lake_Package_extraDepFacetConfig_spec__0___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___Lake_Package_extraDepFacetConfig_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lake_formatQuery___at___Lake_Package_extraDepFacetConfig_spec__0(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lake_Package_extraDepFacetConfig___lam__0(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HEAD", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to resolve HEAD revision", 31, 31);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__1;
x_2 = 3;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/barrel\?rev=", 12, 12);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("&toolchain=", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean toolchain not known; Reservoir only hosts builds for known toolchains", 74, 74);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__6() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__5;
x_2 = 3;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("package has no Reservoir scope", 30, 30);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__8() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__7;
x_2 = 3;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = lean_string_utf8_byte_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0;
x_12 = l_Lake_GitRepo_resolveRevision_x3f(x_11, x_6, x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_2);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__2;
x_19 = lean_array_get_size(x_17);
x_20 = lean_array_push(x_17, x_18);
lean_ctor_set(x_3, 0, x_20);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_3);
lean_ctor_set(x_12, 0, x_21);
return x_12;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_24 = lean_ctor_get(x_3, 1);
x_25 = lean_ctor_get(x_3, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_22);
lean_dec(x_3);
x_26 = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__2;
x_27 = lean_array_get_size(x_22);
x_28 = lean_array_push(x_22, x_26);
x_29 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_25);
lean_ctor_set_uint8(x_29, sizeof(void*)*3, x_23);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_12, 0, x_30);
return x_12;
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_31 = lean_ctor_get(x_12, 1);
lean_inc(x_31);
lean_dec(x_12);
x_32 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_32);
x_33 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_34 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_34);
x_35 = lean_ctor_get(x_3, 2);
lean_inc(x_35);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_36 = x_3;
} else {
 lean_dec_ref(x_3);
 x_36 = lean_box(0);
}
x_37 = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__2;
x_38 = lean_array_get_size(x_32);
x_39 = lean_array_push(x_32, x_37);
if (lean_is_scalar(x_36)) {
 x_40 = lean_alloc_ctor(0, 3, 1);
} else {
 x_40 = x_36;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_34);
lean_ctor_set(x_40, 2, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*3, x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_31);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_2, 1);
lean_inc(x_43);
lean_dec_ref(x_2);
x_44 = lean_ctor_get(x_43, 1);
lean_inc_ref(x_44);
lean_dec(x_43);
x_45 = !lean_is_exclusive(x_12);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_46 = lean_ctor_get(x_12, 0);
lean_dec(x_46);
x_47 = lean_ctor_get(x_3, 0);
x_48 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_49 = lean_ctor_get(x_3, 1);
x_50 = lean_ctor_get(x_3, 2);
x_51 = lean_ctor_get(x_13, 0);
lean_inc(x_51);
lean_dec_ref(x_13);
x_52 = lean_ctor_get(x_44, 12);
lean_inc_ref(x_52);
x_53 = lean_string_utf8_byte_size(x_52);
x_54 = lean_nat_dec_eq(x_53, x_9);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_55 = l_Lean_Name_toString(x_5, x_10);
x_56 = l_Lake_Reservoir_pkgApiUrl(x_44, x_7, x_55);
lean_dec_ref(x_55);
lean_dec_ref(x_7);
x_57 = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__3;
x_58 = lean_string_append(x_56, x_57);
x_59 = lean_string_append(x_58, x_51);
lean_dec(x_51);
x_60 = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__4;
x_61 = lean_string_append(x_59, x_60);
x_62 = l_Lake_uriEncode(x_52);
lean_dec_ref(x_52);
x_63 = lean_string_append(x_61, x_62);
lean_dec_ref(x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_3);
lean_ctor_set(x_12, 0, x_64);
return x_12;
}
else
{
uint8_t x_65; 
lean_dec_ref(x_52);
lean_dec(x_51);
lean_inc(x_50);
lean_inc_ref(x_49);
lean_inc_ref(x_47);
lean_dec_ref(x_44);
lean_dec_ref(x_7);
lean_dec(x_5);
x_65 = !lean_is_exclusive(x_3);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_66 = lean_ctor_get(x_3, 2);
lean_dec(x_66);
x_67 = lean_ctor_get(x_3, 1);
lean_dec(x_67);
x_68 = lean_ctor_get(x_3, 0);
lean_dec(x_68);
x_69 = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__6;
x_70 = lean_array_get_size(x_47);
x_71 = lean_array_push(x_47, x_69);
lean_ctor_set(x_3, 0, x_71);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_3);
lean_ctor_set(x_12, 0, x_72);
return x_12;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_3);
x_73 = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__6;
x_74 = lean_array_get_size(x_47);
x_75 = lean_array_push(x_47, x_73);
x_76 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_49);
lean_ctor_set(x_76, 2, x_50);
lean_ctor_set_uint8(x_76, sizeof(void*)*3, x_48);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_12, 0, x_77);
return x_12;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_78 = lean_ctor_get(x_12, 1);
lean_inc(x_78);
lean_dec(x_12);
x_79 = lean_ctor_get(x_3, 0);
x_80 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_81 = lean_ctor_get(x_3, 1);
x_82 = lean_ctor_get(x_3, 2);
x_83 = lean_ctor_get(x_13, 0);
lean_inc(x_83);
lean_dec_ref(x_13);
x_84 = lean_ctor_get(x_44, 12);
lean_inc_ref(x_84);
x_85 = lean_string_utf8_byte_size(x_84);
x_86 = lean_nat_dec_eq(x_85, x_9);
lean_dec(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_87 = l_Lean_Name_toString(x_5, x_10);
x_88 = l_Lake_Reservoir_pkgApiUrl(x_44, x_7, x_87);
lean_dec_ref(x_87);
lean_dec_ref(x_7);
x_89 = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__3;
x_90 = lean_string_append(x_88, x_89);
x_91 = lean_string_append(x_90, x_83);
lean_dec(x_83);
x_92 = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__4;
x_93 = lean_string_append(x_91, x_92);
x_94 = l_Lake_uriEncode(x_84);
lean_dec_ref(x_84);
x_95 = lean_string_append(x_93, x_94);
lean_dec_ref(x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_3);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_78);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec_ref(x_84);
lean_dec(x_83);
lean_inc(x_82);
lean_inc_ref(x_81);
lean_inc_ref(x_79);
lean_dec_ref(x_44);
lean_dec_ref(x_7);
lean_dec(x_5);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_98 = x_3;
} else {
 lean_dec_ref(x_3);
 x_98 = lean_box(0);
}
x_99 = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__6;
x_100 = lean_array_get_size(x_79);
x_101 = lean_array_push(x_79, x_99);
if (lean_is_scalar(x_98)) {
 x_102 = lean_alloc_ctor(0, 3, 1);
} else {
 x_102 = x_98;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_81);
lean_ctor_set(x_102, 2, x_82);
lean_ctor_set_uint8(x_102, sizeof(void*)*3, x_80);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_78);
return x_104;
}
}
}
}
else
{
uint8_t x_105; 
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_105 = !lean_is_exclusive(x_3);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_3, 0);
x_107 = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__8;
x_108 = lean_array_get_size(x_106);
x_109 = lean_array_push(x_106, x_107);
lean_ctor_set(x_3, 0, x_109);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_3);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_4);
return x_111;
}
else
{
lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_112 = lean_ctor_get(x_3, 0);
x_113 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_114 = lean_ctor_get(x_3, 1);
x_115 = lean_ctor_get(x_3, 2);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_112);
lean_dec(x_3);
x_116 = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__8;
x_117 = lean_array_get_size(x_112);
x_118 = lean_array_push(x_112, x_116);
x_119 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_114);
lean_ctor_set(x_119, 2, x_115);
lean_ctor_set_uint8(x_119, sizeof(void*)*3, x_113);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_4);
return x_121;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(x_1, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no release tag found for revision", 33, 33);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" '", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/releases/download/", 19, 19);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Git_defaultRemote;
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("release repository URL not known; the package may need to set 'releaseRepo'", 75, 75);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__7() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__6;
x_2 = 3;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_67; lean_object* x_113; 
x_20 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_1, 8);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_1, 16);
lean_inc_ref(x_23);
lean_dec_ref(x_1);
x_113 = lean_ctor_get(x_21, 11);
lean_inc(x_113);
lean_dec_ref(x_21);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_string_utf8_byte_size(x_22);
x_115 = lean_unsigned_to_nat(0u);
x_116 = lean_nat_dec_eq(x_114, x_115);
lean_dec(x_114);
if (x_116 == 0)
{
lean_dec_ref(x_22);
x_67 = x_113;
goto block_112;
}
else
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_22);
x_67 = x_117;
goto block_112;
}
}
else
{
lean_dec_ref(x_22);
x_67 = x_113;
goto block_112;
}
block_19:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__0;
x_11 = lean_string_append(x_10, x_4);
lean_dec_ref(x_4);
x_12 = 3;
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_12);
x_14 = lean_array_get_size(x_5);
x_15 = lean_array_push(x_5, x_13);
x_16 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
lean_ctor_set(x_16, 2, x_8);
lean_ctor_set_uint8(x_16, sizeof(void*)*3, x_6);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
block_66:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0;
lean_inc_ref(x_20);
x_31 = l_Lake_GitRepo_findTag_x3f(x_30, x_20, x_24);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec_ref(x_29);
lean_dec_ref(x_23);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
x_34 = l_Lake_GitRepo_resolveRevision_x3f(x_30, x_20, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__5___closed__0;
x_4 = x_37;
x_5 = x_26;
x_6 = x_28;
x_7 = x_27;
x_8 = x_25;
x_9 = x_36;
goto block_19;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec_ref(x_34);
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
lean_dec_ref(x_35);
x_40 = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__1;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_42 = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__2;
x_43 = lean_string_append(x_41, x_42);
x_4 = x_43;
x_5 = x_26;
x_6 = x_28;
x_7 = x_27;
x_8 = x_25;
x_9 = x_38;
goto block_19;
}
}
else
{
uint8_t x_44; 
lean_dec_ref(x_20);
x_44 = !lean_is_exclusive(x_31);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_45 = lean_ctor_get(x_31, 0);
lean_dec(x_45);
x_46 = lean_ctor_get(x_32, 0);
lean_inc(x_46);
lean_dec_ref(x_32);
x_47 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_47, 0, x_26);
lean_ctor_set(x_47, 1, x_27);
lean_ctor_set(x_47, 2, x_25);
lean_ctor_set_uint8(x_47, sizeof(void*)*3, x_28);
x_48 = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__3;
x_49 = lean_string_append(x_29, x_48);
x_50 = lean_string_append(x_49, x_46);
lean_dec(x_46);
x_51 = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__4;
x_52 = lean_string_append(x_50, x_51);
x_53 = lean_string_append(x_52, x_23);
lean_dec_ref(x_23);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_47);
lean_ctor_set(x_31, 0, x_54);
return x_31;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_55 = lean_ctor_get(x_31, 1);
lean_inc(x_55);
lean_dec(x_31);
x_56 = lean_ctor_get(x_32, 0);
lean_inc(x_56);
lean_dec_ref(x_32);
x_57 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_57, 0, x_26);
lean_ctor_set(x_57, 1, x_27);
lean_ctor_set(x_57, 2, x_25);
lean_ctor_set_uint8(x_57, sizeof(void*)*3, x_28);
x_58 = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__3;
x_59 = lean_string_append(x_29, x_58);
x_60 = lean_string_append(x_59, x_56);
lean_dec(x_56);
x_61 = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__4;
x_62 = lean_string_append(x_60, x_61);
x_63 = lean_string_append(x_62, x_23);
lean_dec_ref(x_23);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_57);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_55);
return x_65;
}
}
}
block_112:
{
lean_object* x_68; lean_object* x_69; 
x_68 = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__5;
lean_inc_ref(x_20);
x_69 = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(x_68, x_20, x_3);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
lean_dec_ref(x_23);
lean_dec_ref(x_20);
x_71 = !lean_is_exclusive(x_69);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_69, 0);
lean_dec(x_72);
x_73 = !lean_is_exclusive(x_2);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_2, 0);
x_75 = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__7;
x_76 = lean_array_get_size(x_74);
x_77 = lean_array_push(x_74, x_75);
lean_ctor_set(x_2, 0, x_77);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_2);
lean_ctor_set(x_69, 0, x_78);
return x_69;
}
else
{
lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_79 = lean_ctor_get(x_2, 0);
x_80 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_81 = lean_ctor_get(x_2, 1);
x_82 = lean_ctor_get(x_2, 2);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_79);
lean_dec(x_2);
x_83 = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__7;
x_84 = lean_array_get_size(x_79);
x_85 = lean_array_push(x_79, x_83);
x_86 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_81);
lean_ctor_set(x_86, 2, x_82);
lean_ctor_set_uint8(x_86, sizeof(void*)*3, x_80);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_69, 0, x_87);
return x_69;
}
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_88 = lean_ctor_get(x_69, 1);
lean_inc(x_88);
lean_dec(x_69);
x_89 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_89);
x_90 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_91 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_91);
x_92 = lean_ctor_get(x_2, 2);
lean_inc(x_92);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_93 = x_2;
} else {
 lean_dec_ref(x_2);
 x_93 = lean_box(0);
}
x_94 = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__7;
x_95 = lean_array_get_size(x_89);
x_96 = lean_array_push(x_89, x_94);
if (lean_is_scalar(x_93)) {
 x_97 = lean_alloc_ctor(0, 3, 1);
} else {
 x_97 = x_93;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_91);
lean_ctor_set(x_97, 2, x_92);
lean_ctor_set_uint8(x_97, sizeof(void*)*3, x_90);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_88);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_100 = lean_ctor_get(x_69, 1);
lean_inc(x_100);
lean_dec_ref(x_69);
x_101 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_101);
x_102 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_103 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_103);
x_104 = lean_ctor_get(x_2, 2);
lean_inc(x_104);
lean_dec_ref(x_2);
x_105 = lean_ctor_get(x_70, 0);
lean_inc(x_105);
lean_dec_ref(x_70);
x_24 = x_100;
x_25 = x_104;
x_26 = x_101;
x_27 = x_103;
x_28 = x_102;
x_29 = x_105;
goto block_66;
}
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_69, 1);
lean_inc(x_106);
lean_dec_ref(x_69);
x_107 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_107);
x_108 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_109 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_2, 2);
lean_inc(x_110);
lean_dec_ref(x_2);
x_111 = lean_ctor_get(x_67, 0);
lean_inc(x_111);
lean_dec_ref(x_67);
x_24 = x_106;
x_25 = x_110;
x_26 = x_107;
x_27 = x_109;
x_28 = x_108;
x_29 = x_111;
goto block_66;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(x_1, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_metadata(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_IO_FS_ordSystemTime____x40_Init_System_IO_1242411632____hygCtx___hyg_51_(x_2, x_7);
lean_dec_ref(x_7);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; 
x_9 = 1;
x_10 = lean_box(x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
uint8_t x_11; lean_object* x_12; 
x_11 = 0;
x_12 = lean_box(x_11);
lean_ctor_set(x_4, 0, x_12);
return x_4;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_15);
lean_dec(x_13);
x_16 = l_IO_FS_ordSystemTime____x40_Init_System_IO_1242411632____hygCtx___hyg_51_(x_2, x_15);
lean_dec_ref(x_15);
if (x_16 == 0)
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_17 = 1;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
return x_19;
}
else
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_20 = 0;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_14);
return x_22;
}
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_4);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_4, 0);
lean_dec(x_24);
x_25 = 0;
x_26 = lean_box(x_25);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_26);
return x_4;
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_4, 1);
lean_inc(x_27);
lean_dec(x_4);
x_28 = 0;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_array_uget(x_1, x_2);
x_11 = lean_box(0);
x_12 = lean_array_push(x_9, x_10);
lean_ctor_set(x_5, 0, x_12);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_18 = lean_ctor_get(x_5, 1);
x_19 = lean_ctor_get(x_5, 2);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_16);
lean_dec(x_5);
x_20 = lean_array_uget(x_1, x_2);
x_21 = lean_box(0);
x_22 = lean_array_push(x_16, x_20);
x_23 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_19);
lean_ctor_set_uint8(x_23, sizeof(void*)*3, x_17);
x_24 = 1;
x_25 = lean_usize_add(x_2, x_24);
x_2 = x_25;
x_4 = x_21;
x_5 = x_23;
goto _start;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_5);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_6);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_unbox_uint64(x_6);
x_9 = lean_unbox_uint64(x_7);
x_10 = lean_uint64_dec_eq(x_8, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_3, 2);
x_27 = l_Lake_MTime_checkUpToDate___at___Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(x_2, x_26, x_11);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_10);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_10);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
case 1:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_44; uint8_t x_45; 
x_35 = l_Lake_MTime_checkUpToDate___at___Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(x_2, x_5, x_11);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
x_44 = lean_ctor_get(x_9, 0);
x_45 = lean_ctor_get_uint8(x_44, sizeof(void*)*1);
if (x_45 == 0)
{
lean_dec(x_36);
x_39 = x_45;
goto block_43;
}
else
{
uint8_t x_46; 
x_46 = lean_unbox(x_36);
lean_dec(x_36);
x_39 = x_46;
goto block_43;
}
block_43:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_box(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_10);
if (lean_is_scalar(x_38)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_38;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
}
default: 
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_4);
if (x_47 == 0)
{
lean_object* x_48; uint64_t x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; uint64_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_48 = lean_ctor_get(x_4, 0);
x_49 = lean_ctor_get_uint64(x_48, sizeof(void*)*3);
x_50 = lean_ctor_get(x_48, 2);
lean_inc_ref(x_50);
lean_dec_ref(x_48);
x_88 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_89 = lean_box_uint64(x_49);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_89);
x_90 = lean_box_uint64(x_88);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__2(x_91, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_91);
if (x_92 == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_9, 0);
x_94 = lean_ctor_get_uint8(x_93, sizeof(void*)*1);
if (x_94 == 0)
{
lean_dec_ref(x_50);
x_12 = x_94;
x_13 = x_10;
x_14 = x_11;
goto block_18;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_95 = l_Lake_MTime_checkUpToDate___at___Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(x_2, x_5, x_11);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec_ref(x_95);
x_98 = lean_unbox(x_96);
lean_dec(x_96);
x_51 = x_98;
x_52 = x_10;
x_53 = x_97;
goto block_87;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_99 = l_System_FilePath_pathExists(x_2, x_11);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec_ref(x_99);
x_102 = lean_unbox(x_100);
lean_dec(x_100);
x_51 = x_102;
x_52 = x_10;
x_53 = x_101;
goto block_87;
}
block_87:
{
if (x_51 == 0)
{
lean_dec_ref(x_50);
x_12 = x_51;
x_13 = x_52;
x_14 = x_53;
goto block_18;
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
uint8_t x_55; uint8_t x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_55 = lean_ctor_get_uint8(x_52, sizeof(void*)*3);
x_56 = 1;
x_57 = l_Lake_JobAction_merge(x_55, x_56);
lean_ctor_set_uint8(x_52, sizeof(void*)*3, x_57);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_array_get_size(x_50);
x_60 = lean_nat_dec_lt(x_58, x_59);
if (x_60 == 0)
{
lean_dec(x_59);
lean_dec_ref(x_50);
x_19 = x_51;
x_20 = x_52;
x_21 = x_53;
goto block_25;
}
else
{
uint8_t x_61; 
x_61 = lean_nat_dec_le(x_59, x_59);
if (x_61 == 0)
{
lean_dec(x_59);
lean_dec_ref(x_50);
x_19 = x_51;
x_20 = x_52;
x_21 = x_53;
goto block_25;
}
else
{
lean_object* x_62; size_t x_63; size_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_box(0);
x_63 = 0;
x_64 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_65 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1___redArg(x_50, x_63, x_64, x_62, x_52, x_53);
lean_dec_ref(x_50);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec_ref(x_65);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_19 = x_51;
x_20 = x_68;
x_21 = x_67;
goto block_25;
}
}
}
else
{
lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_69 = lean_ctor_get(x_52, 0);
x_70 = lean_ctor_get_uint8(x_52, sizeof(void*)*3);
x_71 = lean_ctor_get(x_52, 1);
x_72 = lean_ctor_get(x_52, 2);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_69);
lean_dec(x_52);
x_73 = 1;
x_74 = l_Lake_JobAction_merge(x_70, x_73);
x_75 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_75, 0, x_69);
lean_ctor_set(x_75, 1, x_71);
lean_ctor_set(x_75, 2, x_72);
lean_ctor_set_uint8(x_75, sizeof(void*)*3, x_74);
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_array_get_size(x_50);
x_78 = lean_nat_dec_lt(x_76, x_77);
if (x_78 == 0)
{
lean_dec(x_77);
lean_dec_ref(x_50);
x_19 = x_51;
x_20 = x_75;
x_21 = x_53;
goto block_25;
}
else
{
uint8_t x_79; 
x_79 = lean_nat_dec_le(x_77, x_77);
if (x_79 == 0)
{
lean_dec(x_77);
lean_dec_ref(x_50);
x_19 = x_51;
x_20 = x_75;
x_21 = x_53;
goto block_25;
}
else
{
lean_object* x_80; size_t x_81; size_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_80 = lean_box(0);
x_81 = 0;
x_82 = lean_usize_of_nat(x_77);
lean_dec(x_77);
x_83 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1___redArg(x_50, x_81, x_82, x_80, x_75, x_53);
lean_dec_ref(x_50);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec_ref(x_83);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_19 = x_51;
x_20 = x_86;
x_21 = x_85;
goto block_25;
}
}
}
}
}
}
else
{
lean_object* x_103; uint64_t x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; uint64_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_103 = lean_ctor_get(x_4, 0);
lean_inc(x_103);
lean_dec(x_4);
x_104 = lean_ctor_get_uint64(x_103, sizeof(void*)*3);
x_105 = lean_ctor_get(x_103, 2);
lean_inc_ref(x_105);
lean_dec_ref(x_103);
x_129 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_130 = lean_box_uint64(x_104);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_132 = lean_box_uint64(x_129);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_134 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__2(x_133, x_131);
lean_dec_ref(x_131);
lean_dec_ref(x_133);
if (x_134 == 0)
{
lean_object* x_135; uint8_t x_136; 
x_135 = lean_ctor_get(x_9, 0);
x_136 = lean_ctor_get_uint8(x_135, sizeof(void*)*1);
if (x_136 == 0)
{
lean_dec_ref(x_105);
x_12 = x_136;
x_13 = x_10;
x_14 = x_11;
goto block_18;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_137 = l_Lake_MTime_checkUpToDate___at___Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(x_2, x_5, x_11);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec_ref(x_137);
x_140 = lean_unbox(x_138);
lean_dec(x_138);
x_106 = x_140;
x_107 = x_10;
x_108 = x_139;
goto block_128;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_141 = l_System_FilePath_pathExists(x_2, x_11);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec_ref(x_141);
x_144 = lean_unbox(x_142);
lean_dec(x_142);
x_106 = x_144;
x_107 = x_10;
x_108 = x_143;
goto block_128;
}
block_128:
{
if (x_106 == 0)
{
lean_dec_ref(x_105);
x_12 = x_106;
x_13 = x_107;
x_14 = x_108;
goto block_18;
}
else
{
lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_109 = lean_ctor_get(x_107, 0);
lean_inc_ref(x_109);
x_110 = lean_ctor_get_uint8(x_107, sizeof(void*)*3);
x_111 = lean_ctor_get(x_107, 1);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_107, 2);
lean_inc(x_112);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 lean_ctor_release(x_107, 2);
 x_113 = x_107;
} else {
 lean_dec_ref(x_107);
 x_113 = lean_box(0);
}
x_114 = 1;
x_115 = l_Lake_JobAction_merge(x_110, x_114);
if (lean_is_scalar(x_113)) {
 x_116 = lean_alloc_ctor(0, 3, 1);
} else {
 x_116 = x_113;
}
lean_ctor_set(x_116, 0, x_109);
lean_ctor_set(x_116, 1, x_111);
lean_ctor_set(x_116, 2, x_112);
lean_ctor_set_uint8(x_116, sizeof(void*)*3, x_115);
x_117 = lean_unsigned_to_nat(0u);
x_118 = lean_array_get_size(x_105);
x_119 = lean_nat_dec_lt(x_117, x_118);
if (x_119 == 0)
{
lean_dec(x_118);
lean_dec_ref(x_105);
x_19 = x_106;
x_20 = x_116;
x_21 = x_108;
goto block_25;
}
else
{
uint8_t x_120; 
x_120 = lean_nat_dec_le(x_118, x_118);
if (x_120 == 0)
{
lean_dec(x_118);
lean_dec_ref(x_105);
x_19 = x_106;
x_20 = x_116;
x_21 = x_108;
goto block_25;
}
else
{
lean_object* x_121; size_t x_122; size_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_121 = lean_box(0);
x_122 = 0;
x_123 = lean_usize_of_nat(x_118);
lean_dec(x_118);
x_124 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1___redArg(x_105, x_122, x_123, x_121, x_116, x_108);
lean_dec_ref(x_105);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec_ref(x_124);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_19 = x_106;
x_20 = x_127;
x_21 = x_126;
goto block_25;
}
}
}
}
}
}
}
block_18:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_box(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
block_25:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_box(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_io_mono_ms_now(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_3, 2);
x_10 = lean_nat_sub(x_8, x_1);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = lean_nat_add(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
lean_ctor_set(x_3, 2, x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_3);
lean_ctor_set(x_5, 0, x_13);
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get(x_3, 2);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_dec(x_3);
x_19 = lean_nat_sub(x_14, x_1);
lean_dec(x_14);
x_20 = lean_box(0);
x_21 = lean_nat_add(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 2, x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_5, 0, x_23);
return x_5;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_5, 0);
x_25 = lean_ctor_get(x_5, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_5);
x_26 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_26);
x_27 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_28 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_3, 2);
lean_inc(x_29);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_30 = x_3;
} else {
 lean_dec_ref(x_3);
 x_30 = lean_box(0);
}
x_31 = lean_nat_sub(x_24, x_1);
lean_dec(x_24);
x_32 = lean_box(0);
x_33 = lean_nat_add(x_29, x_31);
lean_dec(x_31);
lean_dec(x_29);
if (lean_is_scalar(x_30)) {
 x_34 = lean_alloc_ctor(0, 3, 1);
} else {
 x_34 = x_30;
}
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_28);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*3, x_27);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_25);
return x_36;
}
}
}
static lean_object* _init_l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("target is out-of-date and needs to be rebuilt", 45, 45);
return x_1;
}
}
static lean_object* _init_l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg___closed__0;
x_2 = 3;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get_uint8(x_16, sizeof(void*)*1 + 2);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_36; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_21 = lean_io_mono_ms_now(x_9);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
lean_inc_ref(x_19);
x_24 = l_Lake_download(x_1, x_2, x_3, x_19, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_36 = l_Lake_JobAction_merge(x_20, x_6);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_25, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_25, 1);
lean_inc(x_38);
lean_dec_ref(x_25);
x_39 = lean_array_get_size(x_19);
lean_dec_ref(x_19);
x_40 = lean_array_get_size(x_38);
lean_inc(x_40);
x_41 = l_Array_extract___redArg(x_38, x_39, x_40);
x_42 = lean_box(0);
x_43 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_4, x_42, x_41);
x_44 = l_Lake_BuildMetadata_writeFile(x_5, x_43, x_26);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
lean_dec(x_40);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_46 = lean_ctor_get(x_44, 1);
x_47 = lean_ctor_get(x_44, 0);
lean_dec(x_47);
lean_ctor_set(x_8, 0, x_38);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_36);
x_48 = lean_box(0);
lean_inc(x_37);
lean_ctor_set_tag(x_44, 1);
lean_ctor_set(x_44, 1, x_48);
lean_ctor_set(x_44, 0, x_37);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_44);
x_50 = l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg___lam__0(x_22, x_49, x_8, x_46);
lean_dec_ref(x_49);
lean_dec(x_22);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
lean_ctor_set(x_52, 0, x_37);
return x_50;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_37);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_50, 0, x_56);
return x_50;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_50, 0);
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_50);
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
lean_ctor_set(x_61, 0, x_37);
lean_ctor_set(x_61, 1, x_59);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_58);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_63 = lean_ctor_get(x_44, 1);
lean_inc(x_63);
lean_dec(x_44);
lean_ctor_set(x_8, 0, x_38);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_36);
x_64 = lean_box(0);
lean_inc(x_37);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_37);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg___lam__0(x_22, x_66, x_8, x_63);
lean_dec_ref(x_66);
lean_dec(x_22);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_70 = x_67;
} else {
 lean_dec_ref(x_67);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_72 = x_68;
} else {
 lean_dec_ref(x_68);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_37);
lean_ctor_set(x_73, 1, x_71);
if (lean_is_scalar(x_70)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_70;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_69);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_37);
x_75 = lean_ctor_get(x_44, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_44, 1);
lean_inc(x_76);
lean_dec_ref(x_44);
x_77 = lean_io_error_to_string(x_75);
x_78 = 3;
x_79 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_78);
x_80 = lean_array_push(x_38, x_79);
lean_ctor_set(x_8, 0, x_80);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_36);
x_27 = x_40;
x_28 = x_8;
x_29 = x_76;
goto block_35;
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec_ref(x_19);
x_81 = lean_ctor_get(x_25, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_25, 1);
lean_inc(x_82);
lean_dec_ref(x_25);
lean_ctor_set(x_8, 0, x_82);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_36);
x_27 = x_81;
x_28 = x_8;
x_29 = x_26;
goto block_35;
}
block_35:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_box(0);
x_31 = l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg___lam__0(x_22, x_30, x_28, x_29);
lean_dec(x_22);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_10 = x_27;
x_11 = x_34;
x_12 = x_33;
goto block_15;
}
}
else
{
lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_102; 
x_83 = lean_ctor_get(x_8, 0);
x_84 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_85 = lean_ctor_get(x_8, 1);
x_86 = lean_ctor_get(x_8, 2);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_83);
lean_dec(x_8);
x_87 = lean_io_mono_ms_now(x_9);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec_ref(x_87);
lean_inc_ref(x_83);
x_90 = l_Lake_download(x_1, x_2, x_3, x_83, x_89);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec_ref(x_90);
x_102 = l_Lake_JobAction_merge(x_84, x_6);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_103 = lean_ctor_get(x_91, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_91, 1);
lean_inc(x_104);
lean_dec_ref(x_91);
x_105 = lean_array_get_size(x_83);
lean_dec_ref(x_83);
x_106 = lean_array_get_size(x_104);
lean_inc(x_106);
x_107 = l_Array_extract___redArg(x_104, x_105, x_106);
x_108 = lean_box(0);
x_109 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_4, x_108, x_107);
x_110 = l_Lake_BuildMetadata_writeFile(x_5, x_109, x_92);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_106);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_112 = x_110;
} else {
 lean_dec_ref(x_110);
 x_112 = lean_box(0);
}
x_113 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_113, 0, x_104);
lean_ctor_set(x_113, 1, x_85);
lean_ctor_set(x_113, 2, x_86);
lean_ctor_set_uint8(x_113, sizeof(void*)*3, x_102);
x_114 = lean_box(0);
lean_inc(x_103);
if (lean_is_scalar(x_112)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_112;
 lean_ctor_set_tag(x_115, 1);
}
lean_ctor_set(x_115, 0, x_103);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_117 = l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg___lam__0(x_88, x_116, x_113, x_111);
lean_dec_ref(x_116);
lean_dec(x_88);
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
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_122 = x_118;
} else {
 lean_dec_ref(x_118);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_103);
lean_ctor_set(x_123, 1, x_121);
if (lean_is_scalar(x_120)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_120;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_119);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_103);
x_125 = lean_ctor_get(x_110, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_110, 1);
lean_inc(x_126);
lean_dec_ref(x_110);
x_127 = lean_io_error_to_string(x_125);
x_128 = 3;
x_129 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set_uint8(x_129, sizeof(void*)*1, x_128);
x_130 = lean_array_push(x_104, x_129);
x_131 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_85);
lean_ctor_set(x_131, 2, x_86);
lean_ctor_set_uint8(x_131, sizeof(void*)*3, x_102);
x_93 = x_106;
x_94 = x_131;
x_95 = x_126;
goto block_101;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec_ref(x_83);
x_132 = lean_ctor_get(x_91, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_91, 1);
lean_inc(x_133);
lean_dec_ref(x_91);
x_134 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_85);
lean_ctor_set(x_134, 2, x_86);
lean_ctor_set_uint8(x_134, sizeof(void*)*3, x_102);
x_93 = x_132;
x_94 = x_134;
x_95 = x_92;
goto block_101;
}
block_101:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_box(0);
x_97 = l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg___lam__0(x_88, x_96, x_94, x_95);
lean_dec(x_88);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec_ref(x_97);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_10 = x_93;
x_11 = x_100;
x_12 = x_99;
goto block_15;
}
}
}
else
{
uint8_t x_135; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_135 = !lean_is_exclusive(x_8);
if (x_135 == 0)
{
lean_object* x_136; uint8_t x_137; uint8_t x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_136 = lean_ctor_get(x_8, 0);
x_137 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_138 = 3;
x_139 = l_Lake_JobAction_merge(x_137, x_138);
x_140 = l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg___closed__1;
x_141 = lean_array_get_size(x_136);
x_142 = lean_array_push(x_136, x_140);
lean_ctor_set(x_8, 0, x_142);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_139);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_8);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_9);
return x_144;
}
else
{
lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_145 = lean_ctor_get(x_8, 0);
x_146 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_147 = lean_ctor_get(x_8, 1);
x_148 = lean_ctor_get(x_8, 2);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_145);
lean_dec(x_8);
x_149 = 3;
x_150 = l_Lake_JobAction_merge(x_146, x_149);
x_151 = l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg___closed__1;
x_152 = lean_array_get_size(x_145);
x_153 = lean_array_push(x_145, x_151);
x_154 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_147);
lean_ctor_set(x_154, 2, x_148);
lean_ctor_set_uint8(x_154, sizeof(void*)*3, x_150);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_9);
return x_156;
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_11, x_12, x_13);
return x_14;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
static uint64_t _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__1() {
_start:
{
uint64_t x_1; 
x_1 = l_Lake_Hash_nil;
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<hash>", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__5() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4;
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__0;
lean_inc_ref(x_3);
x_21 = l_System_FilePath_addExtension(x_3, x_20);
lean_inc_ref(x_21);
x_22 = l_Lake_readTraceFile(x_21, x_19, x_11);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_110; lean_object* x_117; uint8_t x_118; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_27 = x_23;
} else {
 lean_dec_ref(x_23);
 x_27 = lean_box(0);
}
x_28 = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__1;
x_29 = lean_string_hash(x_2);
x_30 = lean_uint64_mix_hash(x_28, x_29);
x_31 = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__2;
x_32 = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3;
x_33 = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__5;
x_34 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set_uint64(x_34, sizeof(void*)*3, x_30);
lean_ctor_set(x_10, 0, x_26);
x_35 = l_Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(x_5, x_3, x_34, x_25, x_33, x_6, x_7, x_8, x_9, x_10, x_24);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
x_38 = 2;
x_117 = lean_ctor_get(x_36, 0);
lean_inc(x_117);
x_118 = lean_unbox(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec_ref(x_35);
x_119 = lean_ctor_get(x_36, 1);
lean_inc(x_119);
lean_dec(x_36);
lean_inc_ref(x_3);
x_120 = l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg(x_2, x_3, x_4, x_34, x_21, x_38, x_9, x_119, x_37);
lean_dec_ref(x_21);
lean_dec_ref(x_34);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec_ref(x_120);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec_ref(x_121);
x_124 = lean_unbox(x_117);
lean_dec(x_117);
x_80 = x_124;
x_81 = x_123;
x_82 = x_122;
goto block_109;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_117);
lean_dec(x_27);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_125 = lean_ctor_get(x_120, 1);
lean_inc(x_125);
lean_dec_ref(x_120);
x_126 = lean_ctor_get(x_121, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_121, 1);
lean_inc(x_127);
lean_dec_ref(x_121);
x_12 = x_126;
x_13 = x_127;
x_14 = x_125;
goto block_17;
}
}
else
{
lean_dec(x_117);
lean_dec(x_37);
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec_ref(x_21);
lean_dec_ref(x_2);
x_110 = x_35;
goto block_116;
}
block_79:
{
uint8_t x_45; lean_object* x_46; uint8_t x_47; 
x_45 = 1;
x_46 = l_Lake_untar(x_3, x_42, x_45, x_43, x_40);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = l_Lake_JobAction_merge(x_39, x_38);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_48, 1);
x_52 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_44);
lean_ctor_set(x_52, 2, x_41);
lean_ctor_set_uint8(x_52, sizeof(void*)*3, x_49);
lean_ctor_set(x_48, 1, x_52);
return x_46;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_48, 0);
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_48);
x_55 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_44);
lean_ctor_set(x_55, 2, x_41);
lean_ctor_set_uint8(x_55, sizeof(void*)*3, x_49);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_46, 0, x_56);
return x_46;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_48);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_48, 1);
x_59 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_44);
lean_ctor_set(x_59, 2, x_41);
lean_ctor_set_uint8(x_59, sizeof(void*)*3, x_49);
lean_ctor_set(x_48, 1, x_59);
return x_46;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_48, 0);
x_61 = lean_ctor_get(x_48, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_48);
x_62 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_44);
lean_ctor_set(x_62, 2, x_41);
lean_ctor_set_uint8(x_62, sizeof(void*)*3, x_49);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_46, 0, x_63);
return x_46;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_ctor_get(x_46, 0);
x_65 = lean_ctor_get(x_46, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_46);
x_66 = l_Lake_JobAction_merge(x_39, x_38);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_64, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_69 = x_64;
} else {
 lean_dec_ref(x_64);
 x_69 = lean_box(0);
}
x_70 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_44);
lean_ctor_set(x_70, 2, x_41);
lean_ctor_set_uint8(x_70, sizeof(void*)*3, x_66);
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_69;
}
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_65);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_64, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_64, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_75 = x_64;
} else {
 lean_dec_ref(x_64);
 x_75 = lean_box(0);
}
x_76 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_44);
lean_ctor_set(x_76, 2, x_41);
lean_ctor_set_uint8(x_76, sizeof(void*)*3, x_66);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_73);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_65);
return x_78;
}
}
}
block_109:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_84);
lean_dec_ref(x_1);
x_85 = lean_ctor_get(x_83, 6);
lean_inc_ref(x_85);
lean_dec_ref(x_83);
x_86 = l_System_FilePath_normalize(x_85);
x_87 = l_Lake_joinRelative(x_84, x_86);
lean_dec_ref(x_86);
x_88 = l_System_FilePath_pathExists(x_87, x_82);
if (x_80 == 0)
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_27);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec_ref(x_88);
x_90 = lean_ctor_get(x_81, 0);
lean_inc_ref(x_90);
x_91 = lean_ctor_get_uint8(x_81, sizeof(void*)*3);
x_92 = lean_ctor_get(x_81, 1);
lean_inc_ref(x_92);
x_93 = lean_ctor_get(x_81, 2);
lean_inc(x_93);
lean_dec_ref(x_81);
x_39 = x_91;
x_40 = x_89;
x_41 = x_93;
x_42 = x_87;
x_43 = x_90;
x_44 = x_92;
goto block_79;
}
else
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_88, 0);
lean_inc(x_94);
x_95 = lean_unbox(x_94);
lean_dec(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_27);
x_96 = lean_ctor_get(x_88, 1);
lean_inc(x_96);
lean_dec_ref(x_88);
x_97 = lean_ctor_get(x_81, 0);
lean_inc_ref(x_97);
x_98 = lean_ctor_get_uint8(x_81, sizeof(void*)*3);
x_99 = lean_ctor_get(x_81, 1);
lean_inc_ref(x_99);
x_100 = lean_ctor_get(x_81, 2);
lean_inc(x_100);
lean_dec_ref(x_81);
x_39 = x_98;
x_40 = x_96;
x_41 = x_100;
x_42 = x_87;
x_43 = x_97;
x_44 = x_99;
goto block_79;
}
else
{
uint8_t x_101; 
lean_dec_ref(x_87);
lean_dec_ref(x_3);
x_101 = !lean_is_exclusive(x_88);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_88, 0);
lean_dec(x_102);
x_103 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_27;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_81);
lean_ctor_set(x_88, 0, x_104);
return x_88;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_88, 1);
lean_inc(x_105);
lean_dec(x_88);
x_106 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_27;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_81);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_105);
return x_108;
}
}
}
}
block_116:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec_ref(x_110);
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
lean_dec(x_111);
x_115 = lean_unbox(x_113);
lean_dec(x_113);
x_80 = x_115;
x_81 = x_114;
x_82 = x_112;
goto block_109;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec_ref(x_21);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_128 = lean_ctor_get(x_22, 1);
lean_inc(x_128);
lean_dec_ref(x_22);
x_129 = lean_ctor_get(x_23, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_23, 1);
lean_inc(x_130);
lean_dec_ref(x_23);
lean_ctor_set(x_10, 0, x_130);
x_12 = x_129;
x_13 = x_10;
x_14 = x_128;
goto block_17;
}
}
else
{
lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_131 = lean_ctor_get(x_10, 0);
x_132 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_133 = lean_ctor_get(x_10, 1);
x_134 = lean_ctor_get(x_10, 2);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_131);
lean_dec(x_10);
x_135 = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__0;
lean_inc_ref(x_3);
x_136 = l_System_FilePath_addExtension(x_3, x_135);
lean_inc_ref(x_136);
x_137 = l_Lake_readTraceFile(x_136, x_131, x_11);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint64_t x_143; uint64_t x_144; uint64_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_207; lean_object* x_214; uint8_t x_215; 
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec_ref(x_137);
x_140 = lean_ctor_get(x_138, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_142 = x_138;
} else {
 lean_dec_ref(x_138);
 x_142 = lean_box(0);
}
x_143 = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__1;
x_144 = lean_string_hash(x_2);
x_145 = lean_uint64_mix_hash(x_143, x_144);
x_146 = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__2;
x_147 = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3;
x_148 = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__5;
x_149 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
lean_ctor_set(x_149, 2, x_148);
lean_ctor_set_uint64(x_149, sizeof(void*)*3, x_145);
x_150 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_150, 0, x_141);
lean_ctor_set(x_150, 1, x_133);
lean_ctor_set(x_150, 2, x_134);
lean_ctor_set_uint8(x_150, sizeof(void*)*3, x_132);
x_151 = l_Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(x_5, x_3, x_149, x_140, x_148, x_6, x_7, x_8, x_9, x_150, x_139);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
x_154 = 2;
x_214 = lean_ctor_get(x_152, 0);
lean_inc(x_214);
x_215 = lean_unbox(x_214);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec_ref(x_151);
x_216 = lean_ctor_get(x_152, 1);
lean_inc(x_216);
lean_dec(x_152);
lean_inc_ref(x_3);
x_217 = l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg(x_2, x_3, x_4, x_149, x_136, x_154, x_9, x_216, x_153);
lean_dec_ref(x_136);
lean_dec_ref(x_149);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec_ref(x_217);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec_ref(x_218);
x_221 = lean_unbox(x_214);
lean_dec(x_214);
x_180 = x_221;
x_181 = x_220;
x_182 = x_219;
goto block_206;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_214);
lean_dec(x_142);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_222 = lean_ctor_get(x_217, 1);
lean_inc(x_222);
lean_dec_ref(x_217);
x_223 = lean_ctor_get(x_218, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_218, 1);
lean_inc(x_224);
lean_dec_ref(x_218);
x_12 = x_223;
x_13 = x_224;
x_14 = x_222;
goto block_17;
}
}
else
{
lean_dec(x_214);
lean_dec(x_153);
lean_dec(x_152);
lean_dec_ref(x_149);
lean_dec_ref(x_136);
lean_dec_ref(x_2);
x_207 = x_151;
goto block_213;
}
block_179:
{
uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_161 = 1;
x_162 = l_Lake_untar(x_3, x_158, x_161, x_159, x_156);
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
x_166 = l_Lake_JobAction_merge(x_155, x_154);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_167 = lean_ctor_get(x_163, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_163, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_169 = x_163;
} else {
 lean_dec_ref(x_163);
 x_169 = lean_box(0);
}
x_170 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_160);
lean_ctor_set(x_170, 2, x_157);
lean_ctor_set_uint8(x_170, sizeof(void*)*3, x_166);
if (lean_is_scalar(x_169)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_169;
}
lean_ctor_set(x_171, 0, x_167);
lean_ctor_set(x_171, 1, x_170);
if (lean_is_scalar(x_165)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_165;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_164);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_173 = lean_ctor_get(x_163, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_163, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_175 = x_163;
} else {
 lean_dec_ref(x_163);
 x_175 = lean_box(0);
}
x_176 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_160);
lean_ctor_set(x_176, 2, x_157);
lean_ctor_set_uint8(x_176, sizeof(void*)*3, x_166);
if (lean_is_scalar(x_175)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_175;
}
lean_ctor_set(x_177, 0, x_173);
lean_ctor_set(x_177, 1, x_176);
if (lean_is_scalar(x_165)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_165;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_164);
return x_178;
}
}
block_206:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_183 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_183);
x_184 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_184);
lean_dec_ref(x_1);
x_185 = lean_ctor_get(x_183, 6);
lean_inc_ref(x_185);
lean_dec_ref(x_183);
x_186 = l_System_FilePath_normalize(x_185);
x_187 = l_Lake_joinRelative(x_184, x_186);
lean_dec_ref(x_186);
x_188 = l_System_FilePath_pathExists(x_187, x_182);
if (x_180 == 0)
{
lean_object* x_189; lean_object* x_190; uint8_t x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_142);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
lean_dec_ref(x_188);
x_190 = lean_ctor_get(x_181, 0);
lean_inc_ref(x_190);
x_191 = lean_ctor_get_uint8(x_181, sizeof(void*)*3);
x_192 = lean_ctor_get(x_181, 1);
lean_inc_ref(x_192);
x_193 = lean_ctor_get(x_181, 2);
lean_inc(x_193);
lean_dec_ref(x_181);
x_155 = x_191;
x_156 = x_189;
x_157 = x_193;
x_158 = x_187;
x_159 = x_190;
x_160 = x_192;
goto block_179;
}
else
{
lean_object* x_194; uint8_t x_195; 
x_194 = lean_ctor_get(x_188, 0);
lean_inc(x_194);
x_195 = lean_unbox(x_194);
lean_dec(x_194);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_142);
x_196 = lean_ctor_get(x_188, 1);
lean_inc(x_196);
lean_dec_ref(x_188);
x_197 = lean_ctor_get(x_181, 0);
lean_inc_ref(x_197);
x_198 = lean_ctor_get_uint8(x_181, sizeof(void*)*3);
x_199 = lean_ctor_get(x_181, 1);
lean_inc_ref(x_199);
x_200 = lean_ctor_get(x_181, 2);
lean_inc(x_200);
lean_dec_ref(x_181);
x_155 = x_198;
x_156 = x_196;
x_157 = x_200;
x_158 = x_187;
x_159 = x_197;
x_160 = x_199;
goto block_179;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec_ref(x_187);
lean_dec_ref(x_3);
x_201 = lean_ctor_get(x_188, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_202 = x_188;
} else {
 lean_dec_ref(x_188);
 x_202 = lean_box(0);
}
x_203 = lean_box(0);
if (lean_is_scalar(x_142)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_142;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_181);
if (lean_is_scalar(x_202)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_202;
}
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_201);
return x_205;
}
}
}
block_213:
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec_ref(x_207);
x_210 = lean_ctor_get(x_208, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_208, 1);
lean_inc(x_211);
lean_dec(x_208);
x_212 = lean_unbox(x_210);
lean_dec(x_210);
x_180 = x_212;
x_181 = x_211;
x_182 = x_209;
goto block_206;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec_ref(x_136);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_225 = lean_ctor_get(x_137, 1);
lean_inc(x_225);
lean_dec_ref(x_137);
x_226 = lean_ctor_get(x_138, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_138, 1);
lean_inc(x_227);
lean_dec_ref(x_138);
x_228 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_133);
lean_ctor_set(x_228, 2, x_134);
lean_ctor_set_uint8(x_228, sizeof(void*)*3, x_132);
x_12 = x_226;
x_13 = x_228;
x_14 = x_225;
goto block_17;
}
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_MTime_checkUpToDate___at___Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1___redArg(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_SavedTrace_replayIfUpToDate___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_6);
x_11 = l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_10, x_7, x_8, x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_7);
x_15 = l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_14, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_34; lean_object* x_35; 
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_2);
x_34 = lean_apply_8(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec_ref(x_35);
lean_inc_ref(x_2);
x_39 = lean_apply_1(x_3, x_2);
x_40 = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(x_2, x_37, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_38, x_36);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_40, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 0);
lean_dec(x_45);
x_46 = 1;
x_47 = lean_box(x_46);
lean_ctor_set(x_41, 0, x_47);
return x_40;
}
else
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_49 = 1;
x_50 = lean_box(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
lean_ctor_set(x_40, 0, x_51);
return x_40;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_40, 1);
lean_inc(x_52);
lean_dec(x_40);
x_53 = lean_ctor_get(x_41, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_54 = x_41;
} else {
 lean_dec_ref(x_41);
 x_54 = lean_box(0);
}
x_55 = 1;
x_56 = lean_box(x_55);
if (lean_is_scalar(x_54)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_54;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_52);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_40, 1);
lean_inc(x_59);
lean_dec_ref(x_40);
x_60 = lean_ctor_get(x_41, 1);
lean_inc(x_60);
lean_dec_ref(x_41);
x_12 = x_60;
x_13 = x_59;
goto block_33;
}
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_61 = lean_ctor_get(x_34, 1);
lean_inc(x_61);
lean_dec_ref(x_34);
x_62 = lean_ctor_get(x_35, 1);
lean_inc(x_62);
lean_dec_ref(x_35);
x_12 = x_62;
x_13 = x_61;
goto block_33;
}
block_33:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
x_16 = 2;
x_17 = l_Lake_JobAction_merge(x_15, x_16);
lean_ctor_set_uint8(x_12, sizeof(void*)*3, x_17);
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_12);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_13);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
x_24 = lean_ctor_get(x_12, 1);
x_25 = lean_ctor_get(x_12, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_22);
lean_dec(x_12);
x_26 = 2;
x_27 = l_Lake_JobAction_merge(x_23, x_26);
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_27);
x_29 = 0;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_13);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc_ref(x_6);
x_14 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed), 11, 4);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_6);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_3);
x_15 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__5___closed__0;
x_16 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_17 = lean_alloc_closure((void*)(l_Lake_Job_async___boxed), 12, 5);
lean_closure_set(x_17, 0, lean_box(0));
lean_closure_set(x_17, 1, x_4);
lean_closure_set(x_17, 2, x_14);
lean_closure_set(x_17, 3, x_16);
lean_closure_set(x_17, 4, x_15);
x_18 = lean_alloc_closure((void*)(l_Lake_JobM_runSpawnM), 9, 2);
lean_closure_set(x_18, 0, lean_box(0));
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lake_FetchM_runJobM), 9, 2);
lean_closure_set(x_19, 0, lean_box(0));
lean_closure_set(x_19, 1, x_18);
lean_inc_ref(x_11);
x_20 = l_Lake_ensureJob___redArg(x_4, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec_ref(x_20);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_27 = lean_ctor_get(x_22, 2);
lean_dec(x_27);
x_28 = lean_ctor_get(x_11, 3);
lean_inc(x_28);
lean_dec_ref(x_11);
x_29 = lean_st_ref_take(x_28, x_23);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = lean_ctor_get(x_6, 0);
lean_inc(x_32);
lean_dec_ref(x_6);
x_33 = 1;
x_34 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_32, x_33);
x_35 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_36 = lean_string_append(x_34, x_35);
x_37 = l_Lake_Name_eraseHead(x_5);
x_38 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_37, x_33);
x_39 = lean_string_append(x_36, x_38);
lean_dec_ref(x_38);
lean_ctor_set(x_22, 2, x_39);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_33);
lean_inc_ref(x_22);
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
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_49 = lean_ctor_get(x_22, 0);
x_50 = lean_ctor_get(x_22, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_22);
x_51 = lean_ctor_get(x_11, 3);
lean_inc(x_51);
lean_dec_ref(x_11);
x_52 = lean_st_ref_take(x_51, x_23);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec_ref(x_52);
x_55 = lean_ctor_get(x_6, 0);
lean_inc(x_55);
lean_dec_ref(x_6);
x_56 = 1;
x_57 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_55, x_56);
x_58 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_59 = lean_string_append(x_57, x_58);
x_60 = l_Lake_Name_eraseHead(x_5);
x_61 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_60, x_56);
x_62 = lean_string_append(x_59, x_61);
lean_dec_ref(x_61);
x_63 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_63, 0, x_49);
lean_ctor_set(x_63, 1, x_50);
lean_ctor_set(x_63, 2, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*3, x_56);
lean_inc_ref(x_63);
x_64 = l_Lake_Job_toOpaque___redArg(x_63);
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
x_69 = l_Lake_Job_renew___redArg(x_63);
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
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_71 = lean_ctor_get(x_21, 1);
lean_inc(x_71);
lean_dec(x_21);
x_72 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_72);
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
x_75 = lean_ctor_get(x_11, 3);
lean_inc(x_75);
lean_dec_ref(x_11);
x_76 = lean_st_ref_take(x_75, x_23);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec_ref(x_76);
x_79 = lean_ctor_get(x_6, 0);
lean_inc(x_79);
lean_dec_ref(x_6);
x_80 = 1;
x_81 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_79, x_80);
x_82 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_83 = lean_string_append(x_81, x_82);
x_84 = l_Lake_Name_eraseHead(x_5);
x_85 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_84, x_80);
x_86 = lean_string_append(x_83, x_85);
lean_dec_ref(x_85);
if (lean_is_scalar(x_74)) {
 x_87 = lean_alloc_ctor(0, 3, 1);
} else {
 x_87 = x_74;
}
lean_ctor_set(x_87, 0, x_72);
lean_ctor_set(x_87, 1, x_73);
lean_ctor_set(x_87, 2, x_86);
lean_ctor_set_uint8(x_87, sizeof(void*)*3, x_80);
lean_inc_ref(x_87);
x_88 = l_Lake_Job_toOpaque___redArg(x_87);
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
x_93 = l_Lake_Job_renew___redArg(x_87);
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
else
{
lean_dec_ref(x_21);
lean_dec_ref(x_11);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_20;
}
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringBool___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instToJsonBool___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__1;
x_2 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lake_formatQuery___boxed), 4, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lake_instDataKindBool;
x_6 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1), 13, 5);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_4);
lean_closure_set(x_6, 3, x_5);
lean_closure_set(x_6, 4, x_1);
x_7 = l_Lake_Package_keyword;
x_8 = 1;
x_9 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3;
x_10 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_5);
lean_ctor_set(x_10, 3, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*4, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*4 + 1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_6 = l_Lake_instDataKindBool;
x_7 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1), 13, 5);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_4);
lean_closure_set(x_7, 3, x_6);
lean_closure_set(x_7, 4, x_1);
x_8 = l_Lake_Package_keyword;
x_9 = 1;
x_10 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3;
x_11 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 3, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*4, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*4 + 1, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
return x_12;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to fetch ", 16, 16);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
if (x_4 == 0)
{
lean_object* x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_9, 0);
x_42 = lean_ctor_get_uint8(x_41, sizeof(void*)*1 + 3);
x_43 = 2;
x_44 = l_Lake_instDecidableEqVerbosity(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_3);
lean_dec(x_2);
x_45 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0;
x_12 = x_45;
x_13 = x_10;
x_14 = x_11;
goto block_40;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_46 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1;
x_47 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_2, x_44);
x_48 = lean_string_append(x_46, x_47);
lean_dec_ref(x_47);
x_49 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_50 = lean_string_append(x_48, x_49);
x_51 = l_Lake_Name_eraseHead(x_3);
x_52 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_51, x_44);
x_53 = lean_string_append(x_50, x_52);
lean_dec_ref(x_52);
x_54 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3;
x_55 = lean_string_append(x_53, x_54);
x_12 = x_55;
x_13 = x_10;
x_14 = x_11;
goto block_40;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_3);
lean_dec(x_2);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_10);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_11);
return x_58;
}
block_40:
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___closed__0;
x_18 = lean_string_append(x_17, x_1);
x_19 = lean_string_append(x_18, x_12);
lean_dec_ref(x_12);
x_20 = 3;
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = lean_array_get_size(x_16);
x_23 = lean_array_push(x_16, x_21);
lean_ctor_set(x_13, 0, x_23);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_13);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_14);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get_uint8(x_13, sizeof(void*)*3);
x_28 = lean_ctor_get(x_13, 1);
x_29 = lean_ctor_get(x_13, 2);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_26);
lean_dec(x_13);
x_30 = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___closed__0;
x_31 = lean_string_append(x_30, x_1);
x_32 = lean_string_append(x_31, x_12);
lean_dec_ref(x_12);
x_33 = 3;
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
x_35 = lean_array_get_size(x_26);
x_36 = lean_array_push(x_26, x_34);
x_37 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_28);
lean_ctor_set(x_37, 2, x_29);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_27);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_14);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_inc_ref(x_4);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_11 = lean_apply_7(x_4, x_1, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_unsigned_to_nat(0u);
x_17 = 0;
x_18 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__1;
x_19 = l_Lake_Job_mapM___redArg(x_2, x_15, x_3, x_16, x_17, x_4, x_5, x_6, x_7, x_8, x_18, x_13);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_ctor_set(x_12, 0, x_21);
lean_ctor_set(x_19, 0, x_12);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_19);
lean_ctor_set(x_12, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = lean_unsigned_to_nat(0u);
x_28 = 0;
x_29 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__1;
x_30 = l_Lake_Job_mapM___redArg(x_2, x_25, x_3, x_27, x_28, x_4, x_5, x_6, x_7, x_8, x_29, x_13);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_26);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_11);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_11, 0);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_12);
if (x_38 == 0)
{
return x_11;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_12, 0);
x_40 = lean_ctor_get(x_12, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_12);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_11, 0, x_41);
return x_11;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_11, 1);
lean_inc(x_42);
lean_dec(x_11);
x_43 = lean_ctor_get(x_12, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_12, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_45 = x_12;
} else {
 lean_dec_ref(x_12);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_42);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_inc(x_2);
lean_inc(x_13);
x_14 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___boxed), 11, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_2);
lean_inc(x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = l_Lake_Package_keyword;
x_17 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_5);
lean_ctor_set(x_17, 3, x_2);
lean_inc(x_3);
x_18 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1), 10, 3);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_3);
lean_closure_set(x_18, 2, x_14);
lean_inc_ref(x_10);
x_19 = l_Lake_ensureJob___redArg(x_3, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec_ref(x_19);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_26 = lean_ctor_get(x_21, 2);
lean_dec(x_26);
x_27 = lean_ctor_get(x_10, 3);
lean_inc(x_27);
lean_dec_ref(x_10);
x_28 = lean_st_ref_take(x_27, x_22);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = 1;
x_32 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_13, x_31);
x_33 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_34 = lean_string_append(x_32, x_33);
x_35 = l_Lake_Name_eraseHead(x_4);
x_36 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_35, x_31);
x_37 = lean_string_append(x_34, x_36);
lean_dec_ref(x_36);
x_38 = 0;
lean_ctor_set(x_21, 2, x_37);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_38);
lean_inc_ref(x_21);
x_39 = l_Lake_Job_toOpaque___redArg(x_21);
x_40 = lean_array_push(x_29, x_39);
x_41 = lean_st_ref_set(x_27, x_40, x_30);
lean_dec(x_27);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
x_44 = l_Lake_Job_renew___redArg(x_21);
lean_ctor_set(x_20, 0, x_44);
lean_ctor_set(x_41, 0, x_20);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = l_Lake_Job_renew___redArg(x_21);
lean_ctor_set(x_20, 0, x_46);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_20);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_48 = lean_ctor_get(x_21, 0);
x_49 = lean_ctor_get(x_21, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_21);
x_50 = lean_ctor_get(x_10, 3);
lean_inc(x_50);
lean_dec_ref(x_10);
x_51 = lean_st_ref_take(x_50, x_22);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec_ref(x_51);
x_54 = 1;
x_55 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_13, x_54);
x_56 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_57 = lean_string_append(x_55, x_56);
x_58 = l_Lake_Name_eraseHead(x_4);
x_59 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_58, x_54);
x_60 = lean_string_append(x_57, x_59);
lean_dec_ref(x_59);
x_61 = 0;
x_62 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_62, 0, x_48);
lean_ctor_set(x_62, 1, x_49);
lean_ctor_set(x_62, 2, x_60);
lean_ctor_set_uint8(x_62, sizeof(void*)*3, x_61);
lean_inc_ref(x_62);
x_63 = l_Lake_Job_toOpaque___redArg(x_62);
x_64 = lean_array_push(x_52, x_63);
x_65 = lean_st_ref_set(x_50, x_64, x_53);
lean_dec(x_50);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = l_Lake_Job_renew___redArg(x_62);
lean_ctor_set(x_20, 0, x_68);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_20);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_70 = lean_ctor_get(x_20, 1);
lean_inc(x_70);
lean_dec(x_20);
x_71 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_21, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 x_73 = x_21;
} else {
 lean_dec_ref(x_21);
 x_73 = lean_box(0);
}
x_74 = lean_ctor_get(x_10, 3);
lean_inc(x_74);
lean_dec_ref(x_10);
x_75 = lean_st_ref_take(x_74, x_22);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec_ref(x_75);
x_78 = 1;
x_79 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_13, x_78);
x_80 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_81 = lean_string_append(x_79, x_80);
x_82 = l_Lake_Name_eraseHead(x_4);
x_83 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_82, x_78);
x_84 = lean_string_append(x_81, x_83);
lean_dec_ref(x_83);
x_85 = 0;
if (lean_is_scalar(x_73)) {
 x_86 = lean_alloc_ctor(0, 3, 1);
} else {
 x_86 = x_73;
}
lean_ctor_set(x_86, 0, x_71);
lean_ctor_set(x_86, 1, x_72);
lean_ctor_set(x_86, 2, x_84);
lean_ctor_set_uint8(x_86, sizeof(void*)*3, x_85);
lean_inc_ref(x_86);
x_87 = l_Lake_Job_toOpaque___redArg(x_86);
x_88 = lean_array_push(x_76, x_87);
x_89 = lean_st_ref_set(x_74, x_88, x_77);
lean_dec(x_74);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_91 = x_89;
} else {
 lean_dec_ref(x_89);
 x_91 = lean_box(0);
}
x_92 = l_Lake_Job_renew___redArg(x_86);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_70);
if (lean_is_scalar(x_91)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_91;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_90);
return x_94;
}
}
else
{
lean_dec_ref(x_20);
lean_dec(x_13);
lean_dec_ref(x_10);
lean_dec(x_4);
return x_19;
}
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instQueryTextUnit___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instQueryJsonUnit___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__1;
x_2 = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lake_formatQuery___boxed), 4, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_Lake_instDataKindUnit;
x_5 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2), 12, 4);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
lean_closure_set(x_5, 3, x_1);
x_6 = l_Lake_Package_keyword;
x_7 = 1;
x_8 = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3;
x_9 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_4);
lean_ctor_set(x_9, 3, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*4 + 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_6 = l_Lake_instDataKindUnit;
x_7 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2), 12, 4);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_6);
lean_closure_set(x_7, 3, x_1);
x_8 = l_Lake_Package_keyword;
x_9 = 1;
x_10 = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3;
x_11 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 3, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*4, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*4 + 1, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
x_13 = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_13;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to fetch build cache", 27, 27);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
if (x_3 == 0)
{
lean_object* x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_8, 0);
x_39 = lean_ctor_get_uint8(x_38, sizeof(void*)*1 + 3);
x_40 = 2;
x_41 = l_Lake_instDecidableEqVerbosity(x_39, x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_2);
lean_dec(x_1);
x_42 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0;
x_11 = x_42;
x_12 = x_9;
x_13 = x_10;
goto block_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_43 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1;
x_44 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_1, x_41);
x_45 = lean_string_append(x_43, x_44);
lean_dec_ref(x_44);
x_46 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_47 = lean_string_append(x_45, x_46);
x_48 = l_Lake_Name_eraseHead(x_2);
x_49 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_48, x_41);
x_50 = lean_string_append(x_47, x_49);
lean_dec_ref(x_49);
x_51 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3;
x_52 = lean_string_append(x_50, x_51);
x_11 = x_52;
x_12 = x_9;
x_13 = x_10;
goto block_37;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_9);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_10);
return x_55;
}
block_37:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = l_Lake_Package_buildCacheFacetConfig___lam__1___closed__0;
x_17 = lean_string_append(x_16, x_11);
lean_dec_ref(x_11);
x_18 = 3;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
x_20 = lean_array_get_size(x_15);
x_21 = lean_array_push(x_15, x_19);
lean_ctor_set(x_12, 0, x_21);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_12);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_13);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
x_26 = lean_ctor_get(x_12, 1);
x_27 = lean_ctor_get(x_12, 2);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_24);
lean_dec(x_12);
x_28 = l_Lake_Package_buildCacheFacetConfig___lam__1___closed__0;
x_29 = lean_string_append(x_28, x_11);
lean_dec_ref(x_11);
x_30 = 3;
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
x_32 = lean_array_get_size(x_24);
x_33 = lean_array_push(x_24, x_31);
x_34 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_26);
lean_ctor_set(x_34, 2, x_27);
lean_ctor_set_uint8(x_34, sizeof(void*)*3, x_25);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_13);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc_ref(x_3);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = lean_apply_7(x_3, x_1, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_unsigned_to_nat(0u);
x_16 = 0;
x_17 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__1;
x_18 = l_Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg(x_14, x_2, x_15, x_16, x_3, x_4, x_5, x_6, x_7, x_17, x_12);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_ctor_set(x_11, 0, x_20);
lean_ctor_set(x_18, 0, x_11);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_18);
lean_ctor_set(x_11, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_26 = lean_unsigned_to_nat(0u);
x_27 = 0;
x_28 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__1;
x_29 = l_Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg(x_24, x_2, x_26, x_27, x_3, x_4, x_5, x_6, x_7, x_28, x_12);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_25);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_35 = !lean_is_exclusive(x_10);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_10, 0);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_11);
if (x_37 == 0)
{
return x_10;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_11, 0);
x_39 = lean_ctor_get(x_11, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_11);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_10, 0, x_40);
return x_10;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_10, 1);
lean_inc(x_41);
lean_dec(x_10);
x_42 = lean_ctor_get(x_11, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_11, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_44 = x_11;
} else {
 lean_dec_ref(x_11);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_inc(x_1);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_1);
lean_inc(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = l_Lake_Package_keyword;
x_15 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_3);
lean_ctor_set(x_15, 3, x_1);
x_16 = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__0), 9, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_12);
lean_inc_ref(x_8);
x_17 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__1(x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec_ref(x_17);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_24 = lean_ctor_get(x_19, 2);
lean_dec(x_24);
x_25 = lean_ctor_get(x_8, 3);
lean_inc(x_25);
lean_dec_ref(x_8);
x_26 = lean_st_ref_take(x_25, x_20);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = 1;
x_30 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_11, x_29);
x_31 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_32 = lean_string_append(x_30, x_31);
x_33 = l_Lake_Name_eraseHead(x_2);
x_34 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_33, x_29);
x_35 = lean_string_append(x_32, x_34);
lean_dec_ref(x_34);
x_36 = 0;
lean_ctor_set(x_19, 2, x_35);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_36);
lean_inc_ref(x_19);
x_37 = l_Lake_Job_toOpaque___redArg(x_19);
x_38 = lean_array_push(x_27, x_37);
x_39 = lean_st_ref_set(x_25, x_38, x_28);
lean_dec(x_25);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = l_Lake_Job_renew___redArg(x_19);
lean_ctor_set(x_18, 0, x_42);
lean_ctor_set(x_39, 0, x_18);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = l_Lake_Job_renew___redArg(x_19);
lean_ctor_set(x_18, 0, x_44);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_18);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_46 = lean_ctor_get(x_19, 0);
x_47 = lean_ctor_get(x_19, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_19);
x_48 = lean_ctor_get(x_8, 3);
lean_inc(x_48);
lean_dec_ref(x_8);
x_49 = lean_st_ref_take(x_48, x_20);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec_ref(x_49);
x_52 = 1;
x_53 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_11, x_52);
x_54 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_55 = lean_string_append(x_53, x_54);
x_56 = l_Lake_Name_eraseHead(x_2);
x_57 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_56, x_52);
x_58 = lean_string_append(x_55, x_57);
lean_dec_ref(x_57);
x_59 = 0;
x_60 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_60, 0, x_46);
lean_ctor_set(x_60, 1, x_47);
lean_ctor_set(x_60, 2, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*3, x_59);
lean_inc_ref(x_60);
x_61 = l_Lake_Job_toOpaque___redArg(x_60);
x_62 = lean_array_push(x_50, x_61);
x_63 = lean_st_ref_set(x_48, x_62, x_51);
lean_dec(x_48);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
x_66 = l_Lake_Job_renew___redArg(x_60);
lean_ctor_set(x_18, 0, x_66);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_18);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_68 = lean_ctor_get(x_18, 1);
lean_inc(x_68);
lean_dec(x_18);
x_69 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_19, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 x_71 = x_19;
} else {
 lean_dec_ref(x_19);
 x_71 = lean_box(0);
}
x_72 = lean_ctor_get(x_8, 3);
lean_inc(x_72);
lean_dec_ref(x_8);
x_73 = lean_st_ref_take(x_72, x_20);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec_ref(x_73);
x_76 = 1;
x_77 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_11, x_76);
x_78 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_79 = lean_string_append(x_77, x_78);
x_80 = l_Lake_Name_eraseHead(x_2);
x_81 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_80, x_76);
x_82 = lean_string_append(x_79, x_81);
lean_dec_ref(x_81);
x_83 = 0;
if (lean_is_scalar(x_71)) {
 x_84 = lean_alloc_ctor(0, 3, 1);
} else {
 x_84 = x_71;
}
lean_ctor_set(x_84, 0, x_69);
lean_ctor_set(x_84, 1, x_70);
lean_ctor_set(x_84, 2, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*3, x_83);
lean_inc_ref(x_84);
x_85 = l_Lake_Job_toOpaque___redArg(x_84);
x_86 = lean_array_push(x_74, x_85);
x_87 = lean_st_ref_set(x_72, x_86, x_75);
lean_dec(x_72);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = l_Lake_Job_renew___redArg(x_84);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_68);
if (lean_is_scalar(x_89)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_89;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_88);
return x_92;
}
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_extraDepFacetConfig___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_1 = l_Lake_Package_buildCacheFacetConfig___closed__0;
x_2 = l_Lake_Package_buildCacheFacet;
x_3 = l_Lake_Package_optBuildCacheFacet;
x_4 = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__2), 10, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
x_5 = l_Lake_instDataKindUnit;
x_6 = l_Lake_Package_keyword;
x_7 = 1;
x_8 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*4 + 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_Lake_Package_buildCacheFacetConfig___lam__1(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_JobResult_prependLog___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_33; 
x_9 = 1;
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_14 = l_Lake_instDataKindBool;
x_15 = lean_array_get_size(x_7);
lean_dec_ref(x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_13);
x_91 = lean_ctor_get(x_11, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_11, 1);
lean_inc(x_92);
lean_dec_ref(x_11);
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec(x_91);
x_95 = lean_string_utf8_byte_size(x_93);
x_96 = lean_unsigned_to_nat(0u);
x_97 = lean_nat_dec_eq(x_95, x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_98 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__2;
x_99 = l_Substring_takeWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__8(x_93, x_95, x_96);
x_100 = l_Substring_takeRightWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__9(x_93, x_99, x_95);
x_101 = lean_string_utf8_extract(x_93, x_99, x_100);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_93);
x_102 = lean_string_append(x_98, x_101);
lean_dec_ref(x_101);
x_103 = 1;
x_104 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set_uint8(x_104, sizeof(void*)*1, x_103);
x_105 = lean_box(0);
x_106 = lean_array_push(x_92, x_104);
x_107 = l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__1(x_94, x_105, x_2, x_3, x_4, x_5, x_6, x_106, x_12);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_33 = x_107;
goto block_90;
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_95);
lean_dec(x_93);
x_108 = lean_box(0);
x_109 = l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__1(x_94, x_108, x_2, x_3, x_4, x_5, x_6, x_92, x_12);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_33 = x_109;
goto block_90;
}
}
else
{
lean_object* x_110; 
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_110 = lean_ctor_get(x_11, 1);
lean_inc(x_110);
lean_dec_ref(x_11);
x_16 = x_110;
x_17 = x_12;
goto block_32;
}
block_32:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_inc_ref(x_16);
x_18 = l_Array_shrink___redArg(x_16, x_15);
x_19 = lean_array_get_size(x_16);
x_20 = l_Array_extract___redArg(x_16, x_15, x_19);
lean_dec_ref(x_16);
x_21 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__5___closed__0;
x_22 = lean_unsigned_to_nat(0u);
x_23 = 0;
x_24 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__1;
x_25 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*3, x_23);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_task_pure(x_26);
x_28 = 0;
x_29 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_14);
lean_ctor_set(x_29, 2, x_21);
lean_ctor_set_uint8(x_29, sizeof(void*)*3, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_18);
if (lean_is_scalar(x_13)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_13;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_17);
return x_31;
}
block_90:
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_33, 1);
x_37 = lean_ctor_get(x_34, 0);
x_38 = lean_ctor_get(x_34, 1);
x_39 = lean_array_get_size(x_38);
x_40 = lean_nat_dec_lt(x_15, x_39);
if (x_40 == 0)
{
lean_dec(x_39);
lean_free_object(x_34);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_15);
return x_33;
}
else
{
uint8_t x_41; 
lean_inc(x_36);
x_41 = !lean_is_exclusive(x_33);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_33, 1);
lean_dec(x_42);
x_43 = lean_ctor_get(x_33, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_37, 0);
x_46 = lean_ctor_get(x_37, 1);
lean_dec(x_46);
lean_inc(x_38);
x_47 = l_Array_shrink___redArg(x_38, x_15);
x_48 = l_Array_extract___redArg(x_38, x_15, x_39);
lean_dec(x_38);
x_49 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__0), 2, 1);
lean_closure_set(x_49, 0, x_48);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_task_map(x_49, x_45, x_50, x_9);
lean_ctor_set(x_37, 1, x_14);
lean_ctor_set(x_37, 0, x_51);
lean_ctor_set(x_34, 1, x_47);
return x_33;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_37, 0);
x_53 = lean_ctor_get(x_37, 2);
x_54 = lean_ctor_get_uint8(x_37, sizeof(void*)*3);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_37);
lean_inc(x_38);
x_55 = l_Array_shrink___redArg(x_38, x_15);
x_56 = l_Array_extract___redArg(x_38, x_15, x_39);
lean_dec(x_38);
x_57 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__0), 2, 1);
lean_closure_set(x_57, 0, x_56);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_task_map(x_57, x_52, x_58, x_9);
x_60 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_14);
lean_ctor_set(x_60, 2, x_53);
lean_ctor_set_uint8(x_60, sizeof(void*)*3, x_54);
lean_ctor_set(x_34, 1, x_55);
lean_ctor_set(x_34, 0, x_60);
return x_33;
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_33);
x_61 = lean_ctor_get(x_37, 0);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_37, 2);
lean_inc_ref(x_62);
x_63 = lean_ctor_get_uint8(x_37, sizeof(void*)*3);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 x_64 = x_37;
} else {
 lean_dec_ref(x_37);
 x_64 = lean_box(0);
}
lean_inc(x_38);
x_65 = l_Array_shrink___redArg(x_38, x_15);
x_66 = l_Array_extract___redArg(x_38, x_15, x_39);
lean_dec(x_38);
x_67 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__0), 2, 1);
lean_closure_set(x_67, 0, x_66);
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_task_map(x_67, x_61, x_68, x_9);
if (lean_is_scalar(x_64)) {
 x_70 = lean_alloc_ctor(0, 3, 1);
} else {
 x_70 = x_64;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_14);
lean_ctor_set(x_70, 2, x_62);
lean_ctor_set_uint8(x_70, sizeof(void*)*3, x_63);
lean_ctor_set(x_34, 1, x_65);
lean_ctor_set(x_34, 0, x_70);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_34);
lean_ctor_set(x_71, 1, x_36);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_72 = lean_ctor_get(x_33, 1);
x_73 = lean_ctor_get(x_34, 0);
x_74 = lean_ctor_get(x_34, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_34);
x_75 = lean_array_get_size(x_74);
x_76 = lean_nat_dec_lt(x_15, x_75);
if (x_76 == 0)
{
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_15);
return x_33;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_inc(x_72);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_77 = x_33;
} else {
 lean_dec_ref(x_33);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_73, 0);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_73, 2);
lean_inc_ref(x_79);
x_80 = lean_ctor_get_uint8(x_73, sizeof(void*)*3);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 x_81 = x_73;
} else {
 lean_dec_ref(x_73);
 x_81 = lean_box(0);
}
lean_inc(x_74);
x_82 = l_Array_shrink___redArg(x_74, x_15);
x_83 = l_Array_extract___redArg(x_74, x_15, x_75);
lean_dec(x_74);
x_84 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__0), 2, 1);
lean_closure_set(x_84, 0, x_83);
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_task_map(x_84, x_78, x_85, x_9);
if (lean_is_scalar(x_81)) {
 x_87 = lean_alloc_ctor(0, 3, 1);
} else {
 x_87 = x_81;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_14);
lean_ctor_set(x_87, 2, x_79);
lean_ctor_set_uint8(x_87, sizeof(void*)*3, x_80);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_82);
if (lean_is_scalar(x_77)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_77;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_72);
return x_89;
}
}
}
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultLakeDir;
return x_1;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___lam__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("build.barrel", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_32; lean_object* x_33; 
lean_inc_ref(x_7);
lean_inc_ref(x_1);
x_32 = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(x_1, x_7, x_8, x_9);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec_ref(x_33);
x_37 = lean_ctor_get(x_1, 1);
x_38 = l_Lake_Package_optBarrelFacetConfig___lam__1___closed__0;
lean_inc_ref(x_37);
x_39 = l_Lake_joinRelative(x_37, x_38);
x_40 = l_Lake_Package_optBarrelFacetConfig___lam__1___closed__1;
x_41 = l_Lake_joinRelative(x_39, x_40);
x_42 = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(x_1, x_35, x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_36, x_34);
lean_dec_ref(x_7);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_42, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 0);
lean_dec(x_47);
x_48 = 1;
x_49 = lean_box(x_48);
lean_ctor_set(x_43, 0, x_49);
return x_42;
}
else
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_dec(x_43);
x_51 = 1;
x_52 = lean_box(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
lean_ctor_set(x_42, 0, x_53);
return x_42;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_42, 1);
lean_inc(x_54);
lean_dec(x_42);
x_55 = lean_ctor_get(x_43, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_56 = x_43;
} else {
 lean_dec_ref(x_43);
 x_56 = lean_box(0);
}
x_57 = 1;
x_58 = lean_box(x_57);
if (lean_is_scalar(x_56)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_56;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_55);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_54);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_42, 1);
lean_inc(x_61);
lean_dec_ref(x_42);
x_62 = lean_ctor_get(x_43, 1);
lean_inc(x_62);
lean_dec_ref(x_43);
x_10 = x_62;
x_11 = x_61;
goto block_31;
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_63 = lean_ctor_get(x_32, 1);
lean_inc(x_63);
lean_dec_ref(x_32);
x_64 = lean_ctor_get(x_33, 1);
lean_inc(x_64);
lean_dec_ref(x_33);
x_10 = x_64;
x_11 = x_63;
goto block_31;
}
block_31:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_14 = 2;
x_15 = l_Lake_JobAction_merge(x_13, x_14);
lean_ctor_set_uint8(x_10, sizeof(void*)*3, x_15);
x_16 = 0;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_11);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_22 = lean_ctor_get(x_10, 1);
x_23 = lean_ctor_get(x_10, 2);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_dec(x_10);
x_24 = 2;
x_25 = l_Lake_JobAction_merge(x_21, x_24);
x_26 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_26, 2, x_23);
lean_ctor_set_uint8(x_26, sizeof(void*)*3, x_25);
x_27 = 0;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_11);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_25; uint8_t x_26; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_15 = x_11;
} else {
 lean_dec_ref(x_11);
 x_15 = lean_box(0);
}
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_17 = x_12;
} else {
 lean_dec_ref(x_12);
 x_17 = lean_box(0);
}
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_25 = lean_string_utf8_byte_size(x_18);
x_26 = lean_nat_dec_eq(x_25, x_9);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__2;
x_30 = l_Substring_takeWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__8(x_18, x_25, x_9);
x_31 = l_Substring_takeRightWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__9(x_18, x_30, x_25);
x_32 = lean_string_utf8_extract(x_18, x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_18);
x_33 = lean_string_append(x_29, x_32);
lean_dec_ref(x_32);
x_34 = 1;
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = lean_array_push(x_28, x_35);
lean_ctor_set(x_16, 0, x_36);
x_20 = x_16;
x_21 = x_14;
goto block_24;
}
else
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_37 = lean_ctor_get(x_16, 0);
x_38 = lean_ctor_get_uint8(x_16, sizeof(void*)*3);
x_39 = lean_ctor_get(x_16, 1);
x_40 = lean_ctor_get(x_16, 2);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_37);
lean_dec(x_16);
x_41 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__2;
x_42 = l_Substring_takeWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__8(x_18, x_25, x_9);
x_43 = l_Substring_takeRightWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__9(x_18, x_42, x_25);
x_44 = lean_string_utf8_extract(x_18, x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_18);
x_45 = lean_string_append(x_41, x_44);
lean_dec_ref(x_44);
x_46 = 1;
x_47 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_46);
x_48 = lean_array_push(x_37, x_47);
x_49 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_39);
lean_ctor_set(x_49, 2, x_40);
lean_ctor_set_uint8(x_49, sizeof(void*)*3, x_38);
x_20 = x_49;
x_21 = x_14;
goto block_24;
}
}
else
{
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_9);
x_20 = x_16;
x_21 = x_14;
goto block_24;
}
block_24:
{
lean_object* x_22; lean_object* x_23; 
if (lean_is_scalar(x_17)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_17;
}
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
if (lean_is_scalar(x_15)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_15;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_50; 
lean_dec(x_9);
x_50 = !lean_is_exclusive(x_11);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_11, 0);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_12);
if (x_52 == 0)
{
return x_11;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_12, 0);
x_54 = lean_ctor_get(x_12, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_12);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_11, 0, x_55);
return x_11;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_11, 1);
lean_inc(x_56);
lean_dec(x_11);
x_57 = lean_ctor_get(x_12, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_12, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_59 = x_12;
} else {
 lean_dec_ref(x_12);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_56);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = 1;
x_13 = lean_mk_empty_array_with_capacity(x_1);
x_14 = 0;
x_15 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__1;
lean_inc(x_1);
x_16 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_1);
lean_ctor_set_uint8(x_16, sizeof(void*)*3, x_14);
x_17 = lean_box(x_12);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__0___boxed), 10, 9);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_5);
lean_closure_set(x_18, 3, x_6);
lean_closure_set(x_18, 4, x_7);
lean_closure_set(x_18, 5, x_8);
lean_closure_set(x_18, 6, x_9);
lean_closure_set(x_18, 7, x_16);
lean_closure_set(x_18, 8, x_1);
x_19 = lean_io_as_task(x_18, x_1, x_11);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = 0;
x_23 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_3);
lean_ctor_set(x_23, 2, x_4);
lean_ctor_set_uint8(x_23, sizeof(void*)*3, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_10);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = 0;
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_3);
lean_ctor_set(x_28, 2, x_4);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_inc_ref(x_4);
x_12 = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__1___boxed), 9, 2);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_1);
x_13 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__5___closed__0;
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__2), 11, 4);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_12);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_13);
lean_inc_ref(x_9);
x_16 = l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec_ref(x_16);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_23 = lean_ctor_get(x_18, 2);
lean_dec(x_23);
x_24 = lean_ctor_get(x_9, 3);
lean_inc(x_24);
lean_dec_ref(x_9);
x_25 = lean_st_ref_take(x_24, x_19);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = lean_ctor_get(x_4, 0);
lean_inc(x_28);
lean_dec_ref(x_4);
x_29 = 1;
x_30 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_28, x_29);
x_31 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_32 = lean_string_append(x_30, x_31);
x_33 = l_Lake_Name_eraseHead(x_3);
x_34 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_33, x_29);
x_35 = lean_string_append(x_32, x_34);
lean_dec_ref(x_34);
lean_ctor_set(x_18, 2, x_35);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_29);
lean_inc_ref(x_18);
x_36 = l_Lake_Job_toOpaque___redArg(x_18);
x_37 = lean_array_push(x_26, x_36);
x_38 = lean_st_ref_set(x_24, x_37, x_27);
lean_dec(x_24);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = l_Lake_Job_renew___redArg(x_18);
lean_ctor_set(x_17, 0, x_41);
lean_ctor_set(x_38, 0, x_17);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = l_Lake_Job_renew___redArg(x_18);
lean_ctor_set(x_17, 0, x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_17);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_45 = lean_ctor_get(x_18, 0);
x_46 = lean_ctor_get(x_18, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_18);
x_47 = lean_ctor_get(x_9, 3);
lean_inc(x_47);
lean_dec_ref(x_9);
x_48 = lean_st_ref_take(x_47, x_19);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec_ref(x_48);
x_51 = lean_ctor_get(x_4, 0);
lean_inc(x_51);
lean_dec_ref(x_4);
x_52 = 1;
x_53 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_51, x_52);
x_54 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_55 = lean_string_append(x_53, x_54);
x_56 = l_Lake_Name_eraseHead(x_3);
x_57 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_56, x_52);
x_58 = lean_string_append(x_55, x_57);
lean_dec_ref(x_57);
x_59 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_59, 0, x_45);
lean_ctor_set(x_59, 1, x_46);
lean_ctor_set(x_59, 2, x_58);
lean_ctor_set_uint8(x_59, sizeof(void*)*3, x_52);
lean_inc_ref(x_59);
x_60 = l_Lake_Job_toOpaque___redArg(x_59);
x_61 = lean_array_push(x_49, x_60);
x_62 = lean_st_ref_set(x_47, x_61, x_50);
lean_dec(x_47);
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
x_65 = l_Lake_Job_renew___redArg(x_59);
lean_ctor_set(x_17, 0, x_65);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_17);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_67 = lean_ctor_get(x_17, 1);
lean_inc(x_67);
lean_dec(x_17);
x_68 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_18, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 x_70 = x_18;
} else {
 lean_dec_ref(x_18);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get(x_9, 3);
lean_inc(x_71);
lean_dec_ref(x_9);
x_72 = lean_st_ref_take(x_71, x_19);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec_ref(x_72);
x_75 = lean_ctor_get(x_4, 0);
lean_inc(x_75);
lean_dec_ref(x_4);
x_76 = 1;
x_77 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_75, x_76);
x_78 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_79 = lean_string_append(x_77, x_78);
x_80 = l_Lake_Name_eraseHead(x_3);
x_81 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_80, x_76);
x_82 = lean_string_append(x_79, x_81);
lean_dec_ref(x_81);
if (lean_is_scalar(x_70)) {
 x_83 = lean_alloc_ctor(0, 3, 1);
} else {
 x_83 = x_70;
}
lean_ctor_set(x_83, 0, x_68);
lean_ctor_set(x_83, 1, x_69);
lean_ctor_set(x_83, 2, x_82);
lean_ctor_set_uint8(x_83, sizeof(void*)*3, x_76);
lean_inc_ref(x_83);
x_84 = l_Lake_Job_toOpaque___redArg(x_83);
x_85 = lean_array_push(x_73, x_84);
x_86 = lean_st_ref_set(x_71, x_85, x_74);
lean_dec(x_71);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
x_89 = l_Lake_Job_renew___redArg(x_83);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_67);
if (lean_is_scalar(x_88)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_88;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_87);
return x_91;
}
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_optBuildCacheFacetConfig___lam__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Reservoir_lakeHeaders;
return x_1;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_1 = l_Lake_Package_optBarrelFacetConfig___closed__0;
x_2 = l_Lake_Package_optReservoirBarrelFacet;
x_3 = l_Lake_Package_optBarrelFacetConfig___closed__1;
x_4 = l_Lake_instDataKindBool;
x_5 = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__3), 11, 3);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
lean_closure_set(x_5, 2, x_2);
x_6 = l_Lake_Package_keyword;
x_7 = 1;
x_8 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_4);
lean_ctor_set(x_8, 3, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*4 + 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Package_optBarrelFacetConfig___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l_Lake_Package_optBarrelFacetConfig___lam__0(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to fetch Reservoir build", 31, 31);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
if (x_3 == 0)
{
lean_object* x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_8, 0);
x_39 = lean_ctor_get_uint8(x_38, sizeof(void*)*1 + 3);
x_40 = 2;
x_41 = l_Lake_instDecidableEqVerbosity(x_39, x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_2);
lean_dec(x_1);
x_42 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0;
x_11 = x_42;
x_12 = x_9;
x_13 = x_10;
goto block_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_43 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1;
x_44 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_1, x_41);
x_45 = lean_string_append(x_43, x_44);
lean_dec_ref(x_44);
x_46 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_47 = lean_string_append(x_45, x_46);
x_48 = l_Lake_Name_eraseHead(x_2);
x_49 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_48, x_41);
x_50 = lean_string_append(x_47, x_49);
lean_dec_ref(x_49);
x_51 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3;
x_52 = lean_string_append(x_50, x_51);
x_11 = x_52;
x_12 = x_9;
x_13 = x_10;
goto block_37;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_9);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_10);
return x_55;
}
block_37:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = l_Lake_Package_barrelFacetConfig___lam__1___closed__0;
x_17 = lean_string_append(x_16, x_11);
lean_dec_ref(x_11);
x_18 = 3;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
x_20 = lean_array_get_size(x_15);
x_21 = lean_array_push(x_15, x_19);
lean_ctor_set(x_12, 0, x_21);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_12);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_13);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
x_26 = lean_ctor_get(x_12, 1);
x_27 = lean_ctor_get(x_12, 2);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_24);
lean_dec(x_12);
x_28 = l_Lake_Package_barrelFacetConfig___lam__1___closed__0;
x_29 = lean_string_append(x_28, x_11);
lean_dec_ref(x_11);
x_30 = 3;
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
x_32 = lean_array_get_size(x_24);
x_33 = lean_array_push(x_24, x_31);
x_34 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_26);
lean_ctor_set(x_34, 2, x_27);
lean_ctor_set_uint8(x_34, sizeof(void*)*3, x_25);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_13);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_inc(x_1);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_1);
lean_inc(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = l_Lake_Package_keyword;
x_15 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_3);
lean_ctor_set(x_15, 3, x_1);
x_16 = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__0), 9, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_12);
lean_inc_ref(x_8);
x_17 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__1(x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec_ref(x_17);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_24 = lean_ctor_get(x_19, 2);
lean_dec(x_24);
x_25 = lean_ctor_get(x_8, 3);
lean_inc(x_25);
lean_dec_ref(x_8);
x_26 = lean_st_ref_take(x_25, x_20);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = 1;
x_30 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_11, x_29);
x_31 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_32 = lean_string_append(x_30, x_31);
x_33 = l_Lake_Name_eraseHead(x_2);
x_34 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_33, x_29);
x_35 = lean_string_append(x_32, x_34);
lean_dec_ref(x_34);
x_36 = 0;
lean_ctor_set(x_19, 2, x_35);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_36);
lean_inc_ref(x_19);
x_37 = l_Lake_Job_toOpaque___redArg(x_19);
x_38 = lean_array_push(x_27, x_37);
x_39 = lean_st_ref_set(x_25, x_38, x_28);
lean_dec(x_25);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = l_Lake_Job_renew___redArg(x_19);
lean_ctor_set(x_18, 0, x_42);
lean_ctor_set(x_39, 0, x_18);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = l_Lake_Job_renew___redArg(x_19);
lean_ctor_set(x_18, 0, x_44);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_18);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_46 = lean_ctor_get(x_19, 0);
x_47 = lean_ctor_get(x_19, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_19);
x_48 = lean_ctor_get(x_8, 3);
lean_inc(x_48);
lean_dec_ref(x_8);
x_49 = lean_st_ref_take(x_48, x_20);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec_ref(x_49);
x_52 = 1;
x_53 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_11, x_52);
x_54 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_55 = lean_string_append(x_53, x_54);
x_56 = l_Lake_Name_eraseHead(x_2);
x_57 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_56, x_52);
x_58 = lean_string_append(x_55, x_57);
lean_dec_ref(x_57);
x_59 = 0;
x_60 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_60, 0, x_46);
lean_ctor_set(x_60, 1, x_47);
lean_ctor_set(x_60, 2, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*3, x_59);
lean_inc_ref(x_60);
x_61 = l_Lake_Job_toOpaque___redArg(x_60);
x_62 = lean_array_push(x_50, x_61);
x_63 = lean_st_ref_set(x_48, x_62, x_51);
lean_dec(x_48);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
x_66 = l_Lake_Job_renew___redArg(x_60);
lean_ctor_set(x_18, 0, x_66);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_18);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_68 = lean_ctor_get(x_18, 1);
lean_inc(x_68);
lean_dec(x_18);
x_69 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_19, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 x_71 = x_19;
} else {
 lean_dec_ref(x_19);
 x_71 = lean_box(0);
}
x_72 = lean_ctor_get(x_8, 3);
lean_inc(x_72);
lean_dec_ref(x_8);
x_73 = lean_st_ref_take(x_72, x_20);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec_ref(x_73);
x_76 = 1;
x_77 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_11, x_76);
x_78 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_79 = lean_string_append(x_77, x_78);
x_80 = l_Lake_Name_eraseHead(x_2);
x_81 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_80, x_76);
x_82 = lean_string_append(x_79, x_81);
lean_dec_ref(x_81);
x_83 = 0;
if (lean_is_scalar(x_71)) {
 x_84 = lean_alloc_ctor(0, 3, 1);
} else {
 x_84 = x_71;
}
lean_ctor_set(x_84, 0, x_69);
lean_ctor_set(x_84, 1, x_70);
lean_ctor_set(x_84, 2, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*3, x_83);
lean_inc_ref(x_84);
x_85 = l_Lake_Job_toOpaque___redArg(x_84);
x_86 = lean_array_push(x_74, x_85);
x_87 = lean_st_ref_set(x_72, x_86, x_75);
lean_dec(x_72);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = l_Lake_Job_renew___redArg(x_84);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_68);
if (lean_is_scalar(x_89)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_89;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_88);
return x_92;
}
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_1 = l_Lake_Package_buildCacheFacetConfig___closed__0;
x_2 = l_Lake_Package_reservoirBarrelFacet;
x_3 = l_Lake_Package_optReservoirBarrelFacet;
x_4 = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__2), 10, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
x_5 = l_Lake_instDataKindUnit;
x_6 = l_Lake_Package_keyword;
x_7 = 1;
x_8 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*4 + 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_Lake_Package_barrelFacetConfig___lam__1(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_32; lean_object* x_33; 
lean_inc_ref(x_1);
x_32 = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(x_1, x_8, x_9);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec_ref(x_33);
x_37 = lean_ctor_get(x_1, 1);
x_38 = lean_ctor_get(x_1, 16);
x_39 = l_Lake_Package_optBarrelFacetConfig___lam__1___closed__0;
lean_inc_ref(x_37);
x_40 = l_Lake_joinRelative(x_37, x_39);
x_41 = l_Lake_joinRelative(x_40, x_38);
x_42 = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(x_1, x_35, x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_36, x_34);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_42, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 0);
lean_dec(x_47);
x_48 = 1;
x_49 = lean_box(x_48);
lean_ctor_set(x_43, 0, x_49);
return x_42;
}
else
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_dec(x_43);
x_51 = 1;
x_52 = lean_box(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
lean_ctor_set(x_42, 0, x_53);
return x_42;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_42, 1);
lean_inc(x_54);
lean_dec(x_42);
x_55 = lean_ctor_get(x_43, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_56 = x_43;
} else {
 lean_dec_ref(x_43);
 x_56 = lean_box(0);
}
x_57 = 1;
x_58 = lean_box(x_57);
if (lean_is_scalar(x_56)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_56;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_55);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_54);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_42, 1);
lean_inc(x_61);
lean_dec_ref(x_42);
x_62 = lean_ctor_get(x_43, 1);
lean_inc(x_62);
lean_dec_ref(x_43);
x_10 = x_62;
x_11 = x_61;
goto block_31;
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec_ref(x_1);
x_63 = lean_ctor_get(x_32, 1);
lean_inc(x_63);
lean_dec_ref(x_32);
x_64 = lean_ctor_get(x_33, 1);
lean_inc(x_64);
lean_dec_ref(x_33);
x_10 = x_64;
x_11 = x_63;
goto block_31;
}
block_31:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_14 = 2;
x_15 = l_Lake_JobAction_merge(x_13, x_14);
lean_ctor_set_uint8(x_10, sizeof(void*)*3, x_15);
x_16 = 0;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_11);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_22 = lean_ctor_get(x_10, 1);
x_23 = lean_ctor_get(x_10, 2);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_dec(x_10);
x_24 = 2;
x_25 = l_Lake_JobAction_merge(x_21, x_24);
x_26 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_26, 2, x_23);
lean_ctor_set_uint8(x_26, sizeof(void*)*3, x_25);
x_27 = 0;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_11);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_inc_ref(x_5);
x_13 = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__1___boxed), 9, 2);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_1);
x_14 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__5___closed__0;
x_15 = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__2), 11, 4);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_14);
lean_inc_ref(x_10);
x_16 = l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0(x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec_ref(x_16);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_23 = lean_ctor_get(x_18, 2);
lean_dec(x_23);
x_24 = lean_ctor_get(x_10, 3);
lean_inc(x_24);
lean_dec_ref(x_10);
x_25 = lean_st_ref_take(x_24, x_19);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = lean_ctor_get(x_5, 0);
lean_inc(x_28);
lean_dec_ref(x_5);
x_29 = 1;
x_30 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_28, x_29);
x_31 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_32 = lean_string_append(x_30, x_31);
x_33 = l_Lake_Name_eraseHead(x_4);
x_34 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_33, x_29);
x_35 = lean_string_append(x_32, x_34);
lean_dec_ref(x_34);
lean_ctor_set(x_18, 2, x_35);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_29);
lean_inc_ref(x_18);
x_36 = l_Lake_Job_toOpaque___redArg(x_18);
x_37 = lean_array_push(x_26, x_36);
x_38 = lean_st_ref_set(x_24, x_37, x_27);
lean_dec(x_24);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = l_Lake_Job_renew___redArg(x_18);
lean_ctor_set(x_17, 0, x_41);
lean_ctor_set(x_38, 0, x_17);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = l_Lake_Job_renew___redArg(x_18);
lean_ctor_set(x_17, 0, x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_17);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_45 = lean_ctor_get(x_18, 0);
x_46 = lean_ctor_get(x_18, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_18);
x_47 = lean_ctor_get(x_10, 3);
lean_inc(x_47);
lean_dec_ref(x_10);
x_48 = lean_st_ref_take(x_47, x_19);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec_ref(x_48);
x_51 = lean_ctor_get(x_5, 0);
lean_inc(x_51);
lean_dec_ref(x_5);
x_52 = 1;
x_53 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_51, x_52);
x_54 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_55 = lean_string_append(x_53, x_54);
x_56 = l_Lake_Name_eraseHead(x_4);
x_57 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_56, x_52);
x_58 = lean_string_append(x_55, x_57);
lean_dec_ref(x_57);
x_59 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_59, 0, x_45);
lean_ctor_set(x_59, 1, x_46);
lean_ctor_set(x_59, 2, x_58);
lean_ctor_set_uint8(x_59, sizeof(void*)*3, x_52);
lean_inc_ref(x_59);
x_60 = l_Lake_Job_toOpaque___redArg(x_59);
x_61 = lean_array_push(x_49, x_60);
x_62 = lean_st_ref_set(x_47, x_61, x_50);
lean_dec(x_47);
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
x_65 = l_Lake_Job_renew___redArg(x_59);
lean_ctor_set(x_17, 0, x_65);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_17);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_67 = lean_ctor_get(x_17, 1);
lean_inc(x_67);
lean_dec(x_17);
x_68 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_18, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 x_70 = x_18;
} else {
 lean_dec_ref(x_18);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get(x_10, 3);
lean_inc(x_71);
lean_dec_ref(x_10);
x_72 = lean_st_ref_take(x_71, x_19);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec_ref(x_72);
x_75 = lean_ctor_get(x_5, 0);
lean_inc(x_75);
lean_dec_ref(x_5);
x_76 = 1;
x_77 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_75, x_76);
x_78 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_79 = lean_string_append(x_77, x_78);
x_80 = l_Lake_Name_eraseHead(x_4);
x_81 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_80, x_76);
x_82 = lean_string_append(x_79, x_81);
lean_dec_ref(x_81);
if (lean_is_scalar(x_70)) {
 x_83 = lean_alloc_ctor(0, 3, 1);
} else {
 x_83 = x_70;
}
lean_ctor_set(x_83, 0, x_68);
lean_ctor_set(x_83, 1, x_69);
lean_ctor_set(x_83, 2, x_82);
lean_ctor_set_uint8(x_83, sizeof(void*)*3, x_76);
lean_inc_ref(x_83);
x_84 = l_Lake_Job_toOpaque___redArg(x_83);
x_85 = lean_array_push(x_73, x_84);
x_86 = lean_st_ref_set(x_71, x_85, x_74);
lean_dec(x_71);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
x_89 = l_Lake_Job_renew___redArg(x_83);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_67);
if (lean_is_scalar(x_88)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_88;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_87);
return x_91;
}
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_1 = l_Lake_Package_optBarrelFacetConfig___closed__0;
x_2 = l_Lake_Package_optGitHubReleaseFacet;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lake_Package_optGitHubReleaseFacetConfig___closed__0;
x_5 = l_Lake_instDataKindBool;
x_6 = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__3), 12, 4);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_3);
lean_closure_set(x_6, 2, x_5);
lean_closure_set(x_6, 3, x_2);
x_7 = l_Lake_Package_keyword;
x_8 = 1;
x_9 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_5);
lean_ctor_set(x_9, 3, x_1);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*4 + 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Package_optGitHubReleaseFacetConfig___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to fetch GitHub release", 30, 30);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
if (x_3 == 0)
{
lean_object* x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_8, 0);
x_39 = lean_ctor_get_uint8(x_38, sizeof(void*)*1 + 3);
x_40 = 2;
x_41 = l_Lake_instDecidableEqVerbosity(x_39, x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_2);
lean_dec(x_1);
x_42 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0;
x_11 = x_42;
x_12 = x_9;
x_13 = x_10;
goto block_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_43 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1;
x_44 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_1, x_41);
x_45 = lean_string_append(x_43, x_44);
lean_dec_ref(x_44);
x_46 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_47 = lean_string_append(x_45, x_46);
x_48 = l_Lake_Name_eraseHead(x_2);
x_49 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_48, x_41);
x_50 = lean_string_append(x_47, x_49);
lean_dec_ref(x_49);
x_51 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3;
x_52 = lean_string_append(x_50, x_51);
x_11 = x_52;
x_12 = x_9;
x_13 = x_10;
goto block_37;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_9);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_10);
return x_55;
}
block_37:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = l_Lake_Package_gitHubReleaseFacetConfig___lam__1___closed__0;
x_17 = lean_string_append(x_16, x_11);
lean_dec_ref(x_11);
x_18 = 3;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
x_20 = lean_array_get_size(x_15);
x_21 = lean_array_push(x_15, x_19);
lean_ctor_set(x_12, 0, x_21);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_12);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_13);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
x_26 = lean_ctor_get(x_12, 1);
x_27 = lean_ctor_get(x_12, 2);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_24);
lean_dec(x_12);
x_28 = l_Lake_Package_gitHubReleaseFacetConfig___lam__1___closed__0;
x_29 = lean_string_append(x_28, x_11);
lean_dec_ref(x_11);
x_30 = 3;
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
x_32 = lean_array_get_size(x_24);
x_33 = lean_array_push(x_24, x_31);
x_34 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_26);
lean_ctor_set(x_34, 2, x_27);
lean_ctor_set_uint8(x_34, sizeof(void*)*3, x_25);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_13);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_inc(x_1);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_1);
lean_inc(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = l_Lake_Package_keyword;
x_15 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_3);
lean_ctor_set(x_15, 3, x_1);
x_16 = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__0), 9, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_12);
lean_inc_ref(x_8);
x_17 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__1(x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec_ref(x_17);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_24 = lean_ctor_get(x_19, 2);
lean_dec(x_24);
x_25 = lean_ctor_get(x_8, 3);
lean_inc(x_25);
lean_dec_ref(x_8);
x_26 = lean_st_ref_take(x_25, x_20);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = 1;
x_30 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_11, x_29);
x_31 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_32 = lean_string_append(x_30, x_31);
x_33 = l_Lake_Name_eraseHead(x_2);
x_34 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_33, x_29);
x_35 = lean_string_append(x_32, x_34);
lean_dec_ref(x_34);
x_36 = 0;
lean_ctor_set(x_19, 2, x_35);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_36);
lean_inc_ref(x_19);
x_37 = l_Lake_Job_toOpaque___redArg(x_19);
x_38 = lean_array_push(x_27, x_37);
x_39 = lean_st_ref_set(x_25, x_38, x_28);
lean_dec(x_25);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = l_Lake_Job_renew___redArg(x_19);
lean_ctor_set(x_18, 0, x_42);
lean_ctor_set(x_39, 0, x_18);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = l_Lake_Job_renew___redArg(x_19);
lean_ctor_set(x_18, 0, x_44);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_18);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_46 = lean_ctor_get(x_19, 0);
x_47 = lean_ctor_get(x_19, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_19);
x_48 = lean_ctor_get(x_8, 3);
lean_inc(x_48);
lean_dec_ref(x_8);
x_49 = lean_st_ref_take(x_48, x_20);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec_ref(x_49);
x_52 = 1;
x_53 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_11, x_52);
x_54 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_55 = lean_string_append(x_53, x_54);
x_56 = l_Lake_Name_eraseHead(x_2);
x_57 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_56, x_52);
x_58 = lean_string_append(x_55, x_57);
lean_dec_ref(x_57);
x_59 = 0;
x_60 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_60, 0, x_46);
lean_ctor_set(x_60, 1, x_47);
lean_ctor_set(x_60, 2, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*3, x_59);
lean_inc_ref(x_60);
x_61 = l_Lake_Job_toOpaque___redArg(x_60);
x_62 = lean_array_push(x_50, x_61);
x_63 = lean_st_ref_set(x_48, x_62, x_51);
lean_dec(x_48);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
x_66 = l_Lake_Job_renew___redArg(x_60);
lean_ctor_set(x_18, 0, x_66);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_18);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_68 = lean_ctor_get(x_18, 1);
lean_inc(x_68);
lean_dec(x_18);
x_69 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_19, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 x_71 = x_19;
} else {
 lean_dec_ref(x_19);
 x_71 = lean_box(0);
}
x_72 = lean_ctor_get(x_8, 3);
lean_inc(x_72);
lean_dec_ref(x_8);
x_73 = lean_st_ref_take(x_72, x_20);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec_ref(x_73);
x_76 = 1;
x_77 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_11, x_76);
x_78 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_79 = lean_string_append(x_77, x_78);
x_80 = l_Lake_Name_eraseHead(x_2);
x_81 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_80, x_76);
x_82 = lean_string_append(x_79, x_81);
lean_dec_ref(x_81);
x_83 = 0;
if (lean_is_scalar(x_71)) {
 x_84 = lean_alloc_ctor(0, 3, 1);
} else {
 x_84 = x_71;
}
lean_ctor_set(x_84, 0, x_69);
lean_ctor_set(x_84, 1, x_70);
lean_ctor_set(x_84, 2, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*3, x_83);
lean_inc_ref(x_84);
x_85 = l_Lake_Job_toOpaque___redArg(x_84);
x_86 = lean_array_push(x_74, x_85);
x_87 = lean_st_ref_set(x_72, x_86, x_75);
lean_dec(x_72);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = l_Lake_Job_renew___redArg(x_84);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_68);
if (lean_is_scalar(x_89)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_89;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_88);
return x_92;
}
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_1 = l_Lake_Package_buildCacheFacetConfig___closed__0;
x_2 = l_Lake_Package_gitHubReleaseFacet;
x_3 = l_Lake_Package_optGitHubReleaseFacet;
x_4 = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__2), 10, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
x_5 = l_Lake_instDataKindUnit;
x_6 = l_Lake_Package_keyword;
x_7 = 1;
x_8 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*4 + 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_Lake_Package_gitHubReleaseFacetConfig___lam__1(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lake_JobState_merge(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_4, 0);
lean_dec(x_11);
lean_ctor_set(x_4, 2, x_8);
lean_ctor_set(x_4, 0, x_6);
lean_ctor_set_uint8(x_4, sizeof(void*)*3, x_7);
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_8);
lean_ctor_set_uint8(x_13, sizeof(void*)*3, x_7);
lean_ctor_set(x_2, 1, x_13);
return x_2;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
lean_inc(x_15);
x_16 = l_Lake_JobState_merge(x_1, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_17);
x_18 = lean_ctor_get_uint8(x_16, sizeof(void*)*3);
x_19 = lean_ctor_get(x_16, 2);
lean_inc(x_19);
lean_dec_ref(x_16);
x_20 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_20);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 x_21 = x_15;
} else {
 lean_dec_ref(x_15);
 x_21 = lean_box(0);
}
if (lean_is_scalar(x_21)) {
 x_22 = lean_alloc_ctor(0, 3, 1);
} else {
 x_22 = x_21;
}
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_2);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; uint8_t x_32; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_27);
lean_inc(x_26);
x_28 = l_Lake_JobState_merge(x_1, x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc_ref(x_29);
x_30 = lean_ctor_get_uint8(x_28, sizeof(void*)*3);
x_31 = lean_ctor_get(x_28, 2);
lean_inc(x_31);
lean_dec_ref(x_28);
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_26, 2);
lean_dec(x_33);
x_34 = lean_ctor_get(x_26, 0);
lean_dec(x_34);
x_35 = lean_array_get_size(x_27);
lean_dec_ref(x_27);
x_36 = lean_nat_add(x_35, x_25);
lean_dec(x_25);
lean_dec(x_35);
lean_ctor_set(x_26, 2, x_31);
lean_ctor_set(x_26, 0, x_29);
lean_ctor_set_uint8(x_26, sizeof(void*)*3, x_30);
lean_ctor_set(x_2, 0, x_36);
return x_2;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_26, 1);
lean_inc(x_37);
lean_dec(x_26);
x_38 = lean_array_get_size(x_27);
lean_dec_ref(x_27);
x_39 = lean_nat_add(x_38, x_25);
lean_dec(x_25);
lean_dec(x_38);
x_40 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_40, 0, x_29);
lean_ctor_set(x_40, 1, x_37);
lean_ctor_set(x_40, 2, x_31);
lean_ctor_set_uint8(x_40, sizeof(void*)*3, x_30);
lean_ctor_set(x_2, 1, x_40);
lean_ctor_set(x_2, 0, x_39);
return x_2;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_41 = lean_ctor_get(x_2, 0);
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_2);
x_43 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_43);
lean_inc(x_42);
x_44 = l_Lake_JobState_merge(x_1, x_42);
x_45 = lean_ctor_get(x_44, 0);
lean_inc_ref(x_45);
x_46 = lean_ctor_get_uint8(x_44, sizeof(void*)*3);
x_47 = lean_ctor_get(x_44, 2);
lean_inc(x_47);
lean_dec_ref(x_44);
x_48 = lean_ctor_get(x_42, 1);
lean_inc_ref(x_48);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 x_49 = x_42;
} else {
 lean_dec_ref(x_42);
 x_49 = lean_box(0);
}
x_50 = lean_array_get_size(x_43);
lean_dec_ref(x_43);
x_51 = lean_nat_add(x_50, x_41);
lean_dec(x_41);
lean_dec(x_50);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 3, 1);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_45);
lean_ctor_set(x_52, 1, x_48);
lean_ctor_set(x_52, 2, x_47);
lean_ctor_set_uint8(x_52, sizeof(void*)*3, x_46);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_18; 
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_9, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_9, 0);
lean_inc(x_37);
lean_dec_ref(x_9);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_36, 1);
x_40 = l_Lake_BuildTrace_mix(x_1, x_39);
x_41 = lean_apply_1(x_2, x_37);
x_42 = 1;
lean_ctor_set(x_36, 1, x_40);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_43 = l_IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0___redArg(x_41, x_42, x_3, x_4, x_5, x_6, x_7, x_36, x_10);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec_ref(x_43);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec_ref(x_44);
x_48 = lean_ctor_get(x_45, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
x_50 = lean_string_utf8_byte_size(x_48);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_nat_dec_eq(x_50, x_51);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_47);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_54 = lean_ctor_get(x_47, 0);
x_55 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__2;
x_56 = l_Substring_takeWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__8(x_48, x_50, x_51);
x_57 = l_Substring_takeRightWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__9(x_48, x_56, x_50);
x_58 = lean_string_utf8_extract(x_48, x_56, x_57);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_48);
x_59 = lean_string_append(x_55, x_58);
lean_dec_ref(x_58);
x_60 = 1;
x_61 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_60);
x_62 = lean_box(0);
x_63 = lean_array_push(x_54, x_61);
lean_ctor_set(x_47, 0, x_63);
x_64 = l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__1(x_49, x_62, x_3, x_4, x_5, x_6, x_7, x_47, x_46);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_18 = x_64;
goto block_35;
}
else
{
lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_65 = lean_ctor_get(x_47, 0);
x_66 = lean_ctor_get_uint8(x_47, sizeof(void*)*3);
x_67 = lean_ctor_get(x_47, 1);
x_68 = lean_ctor_get(x_47, 2);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_65);
lean_dec(x_47);
x_69 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__2;
x_70 = l_Substring_takeWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__8(x_48, x_50, x_51);
x_71 = l_Substring_takeRightWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__9(x_48, x_70, x_50);
x_72 = lean_string_utf8_extract(x_48, x_70, x_71);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_48);
x_73 = lean_string_append(x_69, x_72);
lean_dec_ref(x_72);
x_74 = 1;
x_75 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_74);
x_76 = lean_box(0);
x_77 = lean_array_push(x_65, x_75);
x_78 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_67);
lean_ctor_set(x_78, 2, x_68);
lean_ctor_set_uint8(x_78, sizeof(void*)*3, x_66);
x_79 = l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__1(x_49, x_76, x_3, x_4, x_5, x_6, x_7, x_78, x_46);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_18 = x_79;
goto block_35;
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_50);
lean_dec(x_48);
x_80 = lean_box(0);
x_81 = l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__1(x_49, x_80, x_3, x_4, x_5, x_6, x_7, x_47, x_46);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_18 = x_81;
goto block_35;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_82 = lean_ctor_get(x_43, 1);
lean_inc(x_82);
lean_dec_ref(x_43);
x_83 = lean_ctor_get(x_44, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_44, 1);
lean_inc(x_84);
lean_dec_ref(x_44);
x_11 = x_83;
x_12 = x_84;
x_13 = x_82;
goto block_17;
}
}
else
{
lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_85 = lean_ctor_get(x_36, 0);
x_86 = lean_ctor_get_uint8(x_36, sizeof(void*)*3);
x_87 = lean_ctor_get(x_36, 1);
x_88 = lean_ctor_get(x_36, 2);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_85);
lean_dec(x_36);
x_89 = l_Lake_BuildTrace_mix(x_1, x_87);
x_90 = lean_apply_1(x_2, x_37);
x_91 = 1;
x_92 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_92, 0, x_85);
lean_ctor_set(x_92, 1, x_89);
lean_ctor_set(x_92, 2, x_88);
lean_ctor_set_uint8(x_92, sizeof(void*)*3, x_86);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_93 = l_IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0___redArg(x_90, x_91, x_3, x_4, x_5, x_6, x_7, x_92, x_10);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec_ref(x_93);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec_ref(x_94);
x_98 = lean_ctor_get(x_95, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_95, 1);
lean_inc(x_99);
lean_dec(x_95);
x_100 = lean_string_utf8_byte_size(x_98);
x_101 = lean_unsigned_to_nat(0u);
x_102 = lean_nat_dec_eq(x_100, x_101);
if (x_102 == 0)
{
lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_103 = lean_ctor_get(x_97, 0);
lean_inc_ref(x_103);
x_104 = lean_ctor_get_uint8(x_97, sizeof(void*)*3);
x_105 = lean_ctor_get(x_97, 1);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_97, 2);
lean_inc(x_106);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 lean_ctor_release(x_97, 2);
 x_107 = x_97;
} else {
 lean_dec_ref(x_97);
 x_107 = lean_box(0);
}
x_108 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__2;
x_109 = l_Substring_takeWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__8(x_98, x_100, x_101);
x_110 = l_Substring_takeRightWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__9(x_98, x_109, x_100);
x_111 = lean_string_utf8_extract(x_98, x_109, x_110);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_98);
x_112 = lean_string_append(x_108, x_111);
lean_dec_ref(x_111);
x_113 = 1;
x_114 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set_uint8(x_114, sizeof(void*)*1, x_113);
x_115 = lean_box(0);
x_116 = lean_array_push(x_103, x_114);
if (lean_is_scalar(x_107)) {
 x_117 = lean_alloc_ctor(0, 3, 1);
} else {
 x_117 = x_107;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_105);
lean_ctor_set(x_117, 2, x_106);
lean_ctor_set_uint8(x_117, sizeof(void*)*3, x_104);
x_118 = l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__1(x_99, x_115, x_3, x_4, x_5, x_6, x_7, x_117, x_96);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_18 = x_118;
goto block_35;
}
else
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_100);
lean_dec(x_98);
x_119 = lean_box(0);
x_120 = l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__1(x_99, x_119, x_3, x_4, x_5, x_6, x_7, x_97, x_96);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_18 = x_120;
goto block_35;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_121 = lean_ctor_get(x_93, 1);
lean_inc(x_121);
lean_dec_ref(x_93);
x_122 = lean_ctor_get(x_94, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_94, 1);
lean_inc(x_123);
lean_dec_ref(x_94);
x_11 = x_122;
x_12 = x_123;
x_13 = x_121;
goto block_17;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_124 = !lean_is_exclusive(x_9);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_task_pure(x_9);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_10);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_127 = lean_ctor_get(x_9, 0);
x_128 = lean_ctor_get(x_9, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_9);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_task_pure(x_129);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_10);
return x_131;
}
}
block_17:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_task_pure(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
block_35:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_24);
lean_dec(x_20);
x_25 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(x_25, 0, x_23);
x_26 = 1;
x_27 = lean_task_map(x_25, x_24, x_8, x_26);
lean_ctor_set(x_18, 0, x_27);
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_30);
lean_dec(x_20);
x_31 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(x_31, 0, x_29);
x_32 = 1;
x_33 = lean_task_map(x_31, x_30, x_8, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_28);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_dec(x_14);
lean_inc(x_3);
x_15 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__2), 10, 8);
lean_closure_set(x_15, 0, x_10);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_5);
lean_closure_set(x_15, 3, x_6);
lean_closure_set(x_15, 4, x_7);
lean_closure_set(x_15, 5, x_8);
lean_closure_set(x_15, 6, x_9);
lean_closure_set(x_15, 7, x_3);
x_16 = lean_io_bind_task(x_13, x_15, x_3, x_4, x_11);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_box(0);
lean_ctor_set(x_1, 1, x_19);
lean_ctor_set(x_1, 0, x_18);
lean_ctor_set(x_16, 0, x_1);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_box(0);
lean_ctor_set(x_1, 1, x_22);
lean_ctor_set(x_1, 0, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 2);
x_26 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_1);
lean_inc(x_3);
x_27 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__2), 10, 8);
lean_closure_set(x_27, 0, x_10);
lean_closure_set(x_27, 1, x_2);
lean_closure_set(x_27, 2, x_5);
lean_closure_set(x_27, 3, x_6);
lean_closure_set(x_27, 4, x_7);
lean_closure_set(x_27, 5, x_8);
lean_closure_set(x_27, 6, x_9);
lean_closure_set(x_27, 7, x_3);
x_28 = lean_io_bind_task(x_24, x_27, x_3, x_4, x_11);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_25);
lean_ctor_set_uint8(x_33, sizeof(void*)*3, x_26);
if (lean_is_scalar(x_31)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_31;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 1);
lean_dec(x_11);
x_12 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__1;
lean_ctor_set(x_8, 1, x_12);
x_13 = lean_apply_7(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_16 = lean_ctor_get(x_8, 2);
lean_inc(x_16);
lean_inc(x_14);
lean_dec(x_8);
x_17 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__1;
x_18 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_15);
x_19 = lean_apply_7(x_1, x_3, x_4, x_5, x_6, x_7, x_18, x_9);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_10, 0);
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_name_eq(x_12, x_13);
x_15 = l_instDecidableNot___redArg(x_14);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_1);
x_16 = 0;
x_17 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__1;
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_16);
x_20 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_19, x_9);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_21, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_27);
lean_dec(x_22);
lean_ctor_set(x_21, 1, x_27);
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
x_29 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_29);
lean_dec(x_22);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_20, 0, x_30);
return x_20;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_dec(x_20);
x_32 = lean_ctor_get(x_21, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_33 = x_21;
} else {
 lean_dec_ref(x_21);
 x_33 = lean_box(0);
}
x_34 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_34);
lean_dec(x_22);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
return x_36;
}
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
x_38 = !lean_is_exclusive(x_20);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_20, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_21);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_21, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_37, 0);
lean_inc_ref(x_42);
lean_dec(x_37);
lean_ctor_set(x_21, 1, x_42);
return x_20;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_21, 0);
lean_inc(x_43);
lean_dec(x_21);
x_44 = lean_ctor_get(x_37, 0);
lean_inc_ref(x_44);
lean_dec(x_37);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_20, 0, x_45);
return x_20;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_20, 1);
lean_inc(x_46);
lean_dec(x_20);
x_47 = lean_ctor_get(x_21, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_48 = x_21;
} else {
 lean_dec_ref(x_21);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_37, 0);
lean_inc_ref(x_49);
lean_dec(x_37);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_46);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_52 = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec_ref(x_52);
x_55 = !lean_is_exclusive(x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_56 = lean_ctor_get(x_53, 0);
x_57 = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed), 9, 1);
lean_closure_set(x_57, 0, x_2);
x_58 = lean_unsigned_to_nat(0u);
x_59 = 0;
x_60 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__1;
x_61 = l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg(x_56, x_57, x_58, x_59, x_3, x_4, x_5, x_6, x_7, x_60, x_54);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 0);
lean_ctor_set(x_53, 0, x_63);
lean_ctor_set(x_61, 0, x_53);
return x_61;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_61, 0);
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_61);
lean_ctor_set(x_53, 0, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_53);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_67 = lean_ctor_get(x_53, 0);
x_68 = lean_ctor_get(x_53, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_53);
x_69 = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed), 9, 1);
lean_closure_set(x_69, 0, x_2);
x_70 = lean_unsigned_to_nat(0u);
x_71 = 0;
x_72 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__1;
x_73 = l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg(x_67, x_69, x_70, x_71, x_3, x_4, x_5, x_6, x_7, x_72, x_54);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_76 = x_73;
} else {
 lean_dec_ref(x_73);
 x_76 = lean_box(0);
}
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_68);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
}
else
{
uint8_t x_79; 
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_79 = !lean_is_exclusive(x_52);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_52, 0);
lean_dec(x_80);
x_81 = !lean_is_exclusive(x_53);
if (x_81 == 0)
{
return x_52;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_53, 0);
x_83 = lean_ctor_get(x_53, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_53);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_52, 0, x_84);
return x_52;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_85 = lean_ctor_get(x_52, 1);
lean_inc(x_85);
lean_dec(x_52);
x_86 = lean_ctor_get(x_53, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_53, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_88 = x_53;
} else {
 lean_dec_ref(x_53);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_85);
return x_90;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_Package_afterBuildCacheAsync___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
x_13 = l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
x_15 = l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec_ref(x_8);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_Lake_BuildTrace_mix(x_1, x_13);
x_15 = lean_apply_1(x_2, x_11);
x_16 = 1;
lean_ctor_set(x_10, 1, x_14);
x_17 = l_IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0___redArg(x_15, x_16, x_3, x_4, x_5, x_6, x_7, x_10, x_9);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_21 = x_17;
} else {
 lean_dec_ref(x_17);
 x_21 = lean_box(0);
}
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_23 = x_18;
} else {
 lean_dec_ref(x_18);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_31 = lean_string_utf8_byte_size(x_24);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_eq(x_31, x_32);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_22);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_22, 0);
x_36 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__2;
x_37 = l_Substring_takeWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__8(x_24, x_31, x_32);
x_38 = l_Substring_takeRightWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__9(x_24, x_37, x_31);
x_39 = lean_string_utf8_extract(x_24, x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_24);
x_40 = lean_string_append(x_36, x_39);
lean_dec_ref(x_39);
x_41 = 1;
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = lean_array_push(x_35, x_42);
lean_ctor_set(x_22, 0, x_43);
x_26 = x_22;
x_27 = x_20;
goto block_30;
}
else
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_44 = lean_ctor_get(x_22, 0);
x_45 = lean_ctor_get_uint8(x_22, sizeof(void*)*3);
x_46 = lean_ctor_get(x_22, 1);
x_47 = lean_ctor_get(x_22, 2);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_44);
lean_dec(x_22);
x_48 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__2;
x_49 = l_Substring_takeWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__8(x_24, x_31, x_32);
x_50 = l_Substring_takeRightWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__9(x_24, x_49, x_31);
x_51 = lean_string_utf8_extract(x_24, x_49, x_50);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_24);
x_52 = lean_string_append(x_48, x_51);
lean_dec_ref(x_51);
x_53 = 1;
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_53);
x_55 = lean_array_push(x_44, x_54);
x_56 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_46);
lean_ctor_set(x_56, 2, x_47);
lean_ctor_set_uint8(x_56, sizeof(void*)*3, x_45);
x_26 = x_56;
x_27 = x_20;
goto block_30;
}
}
else
{
lean_dec(x_31);
lean_dec(x_24);
x_26 = x_22;
x_27 = x_20;
goto block_30;
}
block_30:
{
lean_object* x_28; lean_object* x_29; 
if (lean_is_scalar(x_23)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_23;
}
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_26);
if (lean_is_scalar(x_21)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_21;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_17);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_17, 0);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_18);
if (x_59 == 0)
{
return x_17;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_18, 0);
x_61 = lean_ctor_get(x_18, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_18);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_17, 0, x_62);
return x_17;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_17, 1);
lean_inc(x_63);
lean_dec(x_17);
x_64 = lean_ctor_get(x_18, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_18, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_66 = x_18;
} else {
 lean_dec_ref(x_18);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_63);
return x_68;
}
}
}
else
{
lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_69 = lean_ctor_get(x_10, 0);
x_70 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_71 = lean_ctor_get(x_10, 1);
x_72 = lean_ctor_get(x_10, 2);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_69);
lean_dec(x_10);
x_73 = l_Lake_BuildTrace_mix(x_1, x_71);
x_74 = lean_apply_1(x_2, x_11);
x_75 = 1;
x_76 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_76, 0, x_69);
lean_ctor_set(x_76, 1, x_73);
lean_ctor_set(x_76, 2, x_72);
lean_ctor_set_uint8(x_76, sizeof(void*)*3, x_70);
x_77 = l_IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0___redArg(x_74, x_75, x_3, x_4, x_5, x_6, x_7, x_76, x_9);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_81 = x_77;
} else {
 lean_dec_ref(x_77);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_83 = x_78;
} else {
 lean_dec_ref(x_78);
 x_83 = lean_box(0);
}
x_84 = lean_ctor_get(x_79, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_79, 1);
lean_inc(x_85);
lean_dec(x_79);
x_91 = lean_string_utf8_byte_size(x_84);
x_92 = lean_unsigned_to_nat(0u);
x_93 = lean_nat_dec_eq(x_91, x_92);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_94 = lean_ctor_get(x_82, 0);
lean_inc_ref(x_94);
x_95 = lean_ctor_get_uint8(x_82, sizeof(void*)*3);
x_96 = lean_ctor_get(x_82, 1);
lean_inc_ref(x_96);
x_97 = lean_ctor_get(x_82, 2);
lean_inc(x_97);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 lean_ctor_release(x_82, 2);
 x_98 = x_82;
} else {
 lean_dec_ref(x_82);
 x_98 = lean_box(0);
}
x_99 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__2;
x_100 = l_Substring_takeWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__8(x_84, x_91, x_92);
x_101 = l_Substring_takeRightWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__9(x_84, x_100, x_91);
x_102 = lean_string_utf8_extract(x_84, x_100, x_101);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_84);
x_103 = lean_string_append(x_99, x_102);
lean_dec_ref(x_102);
x_104 = 1;
x_105 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set_uint8(x_105, sizeof(void*)*1, x_104);
x_106 = lean_array_push(x_94, x_105);
if (lean_is_scalar(x_98)) {
 x_107 = lean_alloc_ctor(0, 3, 1);
} else {
 x_107 = x_98;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_96);
lean_ctor_set(x_107, 2, x_97);
lean_ctor_set_uint8(x_107, sizeof(void*)*3, x_95);
x_86 = x_107;
x_87 = x_80;
goto block_90;
}
else
{
lean_dec(x_91);
lean_dec(x_84);
x_86 = x_82;
x_87 = x_80;
goto block_90;
}
block_90:
{
lean_object* x_88; lean_object* x_89; 
if (lean_is_scalar(x_83)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_83;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
if (lean_is_scalar(x_81)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_81;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_108 = lean_ctor_get(x_77, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_109 = x_77;
} else {
 lean_dec_ref(x_77);
 x_109 = lean_box(0);
}
x_110 = lean_ctor_get(x_78, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_78, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_112 = x_78;
} else {
 lean_dec_ref(x_78);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
if (lean_is_scalar(x_109)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_109;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_108);
return x_114;
}
}
}
else
{
uint8_t x_115; 
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_115 = !lean_is_exclusive(x_8);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_8);
lean_ctor_set(x_116, 1, x_9);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_8, 0);
x_118 = lean_ctor_get(x_8, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_8);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_9);
return x_120;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_dec(x_14);
x_15 = lean_alloc_closure((void*)(l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg___lam__0), 9, 7);
lean_closure_set(x_15, 0, x_10);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_5);
lean_closure_set(x_15, 3, x_6);
lean_closure_set(x_15, 4, x_7);
lean_closure_set(x_15, 5, x_8);
lean_closure_set(x_15, 6, x_9);
x_16 = lean_io_map_task(x_15, x_13, x_3, x_4, x_11);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_box(0);
lean_ctor_set(x_1, 1, x_19);
lean_ctor_set(x_1, 0, x_18);
lean_ctor_set(x_16, 0, x_1);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_box(0);
lean_ctor_set(x_1, 1, x_22);
lean_ctor_set(x_1, 0, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 2);
x_26 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_1);
x_27 = lean_alloc_closure((void*)(l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg___lam__0), 9, 7);
lean_closure_set(x_27, 0, x_10);
lean_closure_set(x_27, 1, x_2);
lean_closure_set(x_27, 2, x_5);
lean_closure_set(x_27, 3, x_6);
lean_closure_set(x_27, 4, x_7);
lean_closure_set(x_27, 5, x_8);
lean_closure_set(x_27, 6, x_9);
x_28 = lean_io_map_task(x_27, x_24, x_3, x_4, x_11);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_25);
lean_ctor_set_uint8(x_33, sizeof(void*)*3, x_26);
if (lean_is_scalar(x_31)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_31;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_Job_mapM___at_____private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_25; uint8_t x_26; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_15 = x_11;
} else {
 lean_dec_ref(x_11);
 x_15 = lean_box(0);
}
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_17 = x_12;
} else {
 lean_dec_ref(x_12);
 x_17 = lean_box(0);
}
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_25 = lean_string_utf8_byte_size(x_18);
x_26 = lean_nat_dec_eq(x_25, x_9);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__2;
x_30 = l_Substring_takeWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__8(x_18, x_25, x_9);
x_31 = l_Substring_takeRightWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__9(x_18, x_30, x_25);
x_32 = lean_string_utf8_extract(x_18, x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_18);
x_33 = lean_string_append(x_29, x_32);
lean_dec_ref(x_32);
x_34 = 1;
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = lean_array_push(x_28, x_35);
lean_ctor_set(x_16, 0, x_36);
x_20 = x_16;
x_21 = x_14;
goto block_24;
}
else
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_37 = lean_ctor_get(x_16, 0);
x_38 = lean_ctor_get_uint8(x_16, sizeof(void*)*3);
x_39 = lean_ctor_get(x_16, 1);
x_40 = lean_ctor_get(x_16, 2);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_37);
lean_dec(x_16);
x_41 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__2;
x_42 = l_Substring_takeWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__8(x_18, x_25, x_9);
x_43 = l_Substring_takeRightWhileAux___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__9(x_18, x_42, x_25);
x_44 = lean_string_utf8_extract(x_18, x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_18);
x_45 = lean_string_append(x_41, x_44);
lean_dec_ref(x_44);
x_46 = 1;
x_47 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_46);
x_48 = lean_array_push(x_37, x_47);
x_49 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_39);
lean_ctor_set(x_49, 2, x_40);
lean_ctor_set_uint8(x_49, sizeof(void*)*3, x_38);
x_20 = x_49;
x_21 = x_14;
goto block_24;
}
}
else
{
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_9);
x_20 = x_16;
x_21 = x_14;
goto block_24;
}
block_24:
{
lean_object* x_22; lean_object* x_23; 
if (lean_is_scalar(x_17)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_17;
}
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
if (lean_is_scalar(x_15)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_15;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_50; 
lean_dec(x_9);
x_50 = !lean_is_exclusive(x_11);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_11, 0);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_12);
if (x_52 == 0)
{
return x_11;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_12, 0);
x_54 = lean_ctor_get(x_12, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_12);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_11, 0, x_55);
return x_11;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_11, 1);
lean_inc(x_56);
lean_dec(x_11);
x_57 = lean_ctor_get(x_12, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_12, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_59 = x_12;
} else {
 lean_dec_ref(x_12);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_56);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 1);
lean_dec(x_11);
x_12 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__1;
lean_ctor_set(x_8, 1, x_12);
x_13 = lean_apply_7(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_16 = lean_ctor_get(x_8, 2);
lean_inc(x_16);
lean_inc(x_14);
lean_dec(x_8);
x_17 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__1;
x_18 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_15);
x_19 = lean_apply_7(x_1, x_3, x_4, x_5, x_6, x_7, x_18, x_9);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_10, 0);
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_name_eq(x_12, x_13);
x_15 = l_instDecidableNot___redArg(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec_ref(x_1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = 1;
x_18 = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__1;
x_19 = lean_box(x_17);
x_20 = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed), 10, 9);
lean_closure_set(x_20, 0, x_2);
lean_closure_set(x_20, 1, x_19);
lean_closure_set(x_20, 2, x_3);
lean_closure_set(x_20, 3, x_4);
lean_closure_set(x_20, 4, x_5);
lean_closure_set(x_20, 5, x_6);
lean_closure_set(x_20, 6, x_7);
lean_closure_set(x_20, 7, x_18);
lean_closure_set(x_20, 8, x_16);
x_21 = lean_io_as_task(x_20, x_16, x_9);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_box(0);
x_25 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__5___closed__0;
x_26 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*3, x_15);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_8);
lean_ctor_set(x_21, 0, x_27);
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
x_30 = lean_box(0);
x_31 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__5___closed__0;
x_32 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*3, x_15);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_8);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_35 = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_39 = lean_ctor_get(x_36, 0);
x_40 = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheSync___redArg___lam__1___boxed), 9, 1);
lean_closure_set(x_40, 0, x_2);
x_41 = lean_unsigned_to_nat(0u);
x_42 = 0;
x_43 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__1;
x_44 = l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg(x_39, x_40, x_41, x_42, x_3, x_4, x_5, x_6, x_7, x_43, x_37);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_ctor_set(x_36, 0, x_46);
lean_ctor_set(x_44, 0, x_36);
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_44, 0);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_44);
lean_ctor_set(x_36, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_36);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_50 = lean_ctor_get(x_36, 0);
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_36);
x_52 = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheSync___redArg___lam__1___boxed), 9, 1);
lean_closure_set(x_52, 0, x_2);
x_53 = lean_unsigned_to_nat(0u);
x_54 = 0;
x_55 = l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__1;
x_56 = l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg(x_50, x_52, x_53, x_54, x_3, x_4, x_5, x_6, x_7, x_55, x_37);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_59 = x_56;
} else {
 lean_dec_ref(x_56);
 x_59 = lean_box(0);
}
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_51);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_62 = !lean_is_exclusive(x_35);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_35, 0);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_36);
if (x_64 == 0)
{
return x_35;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_36, 0);
x_66 = lean_ctor_get(x_36, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_36);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_35, 0, x_67);
return x_35;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_35, 1);
lean_inc(x_68);
lean_dec(x_35);
x_69 = lean_ctor_get(x_36, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_36, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_71 = x_36;
} else {
 lean_dec_ref(x_36);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_68);
return x_73;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_Package_afterBuildCacheSync___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
x_13 = l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
x_15 = l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l_Lake_Package_afterBuildCacheSync___redArg___lam__0(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Lake_Package_afterBuildCacheSync___redArg___lam__1(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lake_Package_initFacetConfigs_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 4);
lean_inc(x_8);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 x_9 = x_3;
} else {
 lean_dec_ref(x_3);
 x_9 = lean_box(0);
}
x_10 = l_Lean_Name_quickCmp(x_1, x_5);
switch (x_10) {
case 0:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_11 = l_Std_DTreeMap_Internal_Impl_insert___at___Lake_Package_initFacetConfigs_spec__0___redArg(x_1, x_2, x_7);
x_12 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_11, 4);
lean_inc(x_18);
x_19 = lean_unsigned_to_nat(3u);
x_20 = lean_nat_mul(x_19, x_13);
x_21 = lean_nat_dec_lt(x_20, x_14);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_22 = lean_nat_add(x_12, x_14);
lean_dec(x_14);
x_23 = lean_nat_add(x_22, x_13);
lean_dec(x_22);
if (lean_is_scalar(x_9)) {
 x_24 = lean_alloc_ctor(0, 5, 0);
} else {
 x_24 = x_9;
}
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
lean_ctor_set(x_24, 2, x_6);
lean_ctor_set(x_24, 3, x_11);
lean_ctor_set(x_24, 4, x_8);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 x_25 = x_11;
} else {
 lean_dec_ref(x_11);
 x_25 = lean_box(0);
}
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
x_29 = lean_ctor_get(x_18, 2);
x_30 = lean_ctor_get(x_18, 3);
x_31 = lean_ctor_get(x_18, 4);
x_32 = lean_unsigned_to_nat(2u);
x_33 = lean_nat_mul(x_32, x_26);
x_34 = lean_nat_dec_lt(x_27, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_45; lean_object* x_46; 
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 x_35 = x_18;
} else {
 lean_dec_ref(x_18);
 x_35 = lean_box(0);
}
x_36 = lean_nat_add(x_12, x_14);
lean_dec(x_14);
x_37 = lean_nat_add(x_36, x_13);
lean_dec(x_36);
x_45 = lean_nat_add(x_12, x_26);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_30, 0);
lean_inc(x_53);
x_46 = x_53;
goto block_52;
}
else
{
lean_object* x_54; 
x_54 = lean_unsigned_to_nat(0u);
x_46 = x_54;
goto block_52;
}
block_44:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_nat_add(x_39, x_40);
lean_dec(x_40);
lean_dec(x_39);
if (lean_is_scalar(x_35)) {
 x_42 = lean_alloc_ctor(0, 5, 0);
} else {
 x_42 = x_35;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_5);
lean_ctor_set(x_42, 2, x_6);
lean_ctor_set(x_42, 3, x_31);
lean_ctor_set(x_42, 4, x_8);
if (lean_is_scalar(x_25)) {
 x_43 = lean_alloc_ctor(0, 5, 0);
} else {
 x_43 = x_25;
}
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_28);
lean_ctor_set(x_43, 2, x_29);
lean_ctor_set(x_43, 3, x_38);
lean_ctor_set(x_43, 4, x_42);
return x_43;
}
block_52:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_nat_add(x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
if (lean_is_scalar(x_9)) {
 x_48 = lean_alloc_ctor(0, 5, 0);
} else {
 x_48 = x_9;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_15);
lean_ctor_set(x_48, 2, x_16);
lean_ctor_set(x_48, 3, x_17);
lean_ctor_set(x_48, 4, x_30);
x_49 = lean_nat_add(x_12, x_13);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_31, 0);
lean_inc(x_50);
x_38 = x_48;
x_39 = x_49;
x_40 = x_50;
goto block_44;
}
else
{
lean_object* x_51; 
x_51 = lean_unsigned_to_nat(0u);
x_38 = x_48;
x_39 = x_49;
x_40 = x_51;
goto block_44;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_9);
x_55 = lean_nat_add(x_12, x_14);
lean_dec(x_14);
x_56 = lean_nat_add(x_55, x_13);
lean_dec(x_55);
x_57 = lean_nat_add(x_12, x_13);
x_58 = lean_nat_add(x_57, x_27);
lean_dec(x_57);
lean_inc_ref(x_8);
if (lean_is_scalar(x_25)) {
 x_59 = lean_alloc_ctor(0, 5, 0);
} else {
 x_59 = x_25;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_5);
lean_ctor_set(x_59, 2, x_6);
lean_ctor_set(x_59, 3, x_18);
lean_ctor_set(x_59, 4, x_8);
x_60 = !lean_is_exclusive(x_8);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_8, 4);
lean_dec(x_61);
x_62 = lean_ctor_get(x_8, 3);
lean_dec(x_62);
x_63 = lean_ctor_get(x_8, 2);
lean_dec(x_63);
x_64 = lean_ctor_get(x_8, 1);
lean_dec(x_64);
x_65 = lean_ctor_get(x_8, 0);
lean_dec(x_65);
lean_ctor_set(x_8, 4, x_59);
lean_ctor_set(x_8, 3, x_17);
lean_ctor_set(x_8, 2, x_16);
lean_ctor_set(x_8, 1, x_15);
lean_ctor_set(x_8, 0, x_56);
return x_8;
}
else
{
lean_object* x_66; 
lean_dec(x_8);
x_66 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_66, 0, x_56);
lean_ctor_set(x_66, 1, x_15);
lean_ctor_set(x_66, 2, x_16);
lean_ctor_set(x_66, 3, x_17);
lean_ctor_set(x_66, 4, x_59);
return x_66;
}
}
}
}
else
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_11, 3);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_11);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_ctor_get(x_11, 4);
x_70 = lean_ctor_get(x_11, 1);
x_71 = lean_ctor_get(x_11, 2);
x_72 = lean_ctor_get(x_11, 3);
lean_dec(x_72);
x_73 = lean_ctor_get(x_11, 0);
lean_dec(x_73);
x_74 = lean_unsigned_to_nat(3u);
lean_inc(x_69);
lean_ctor_set(x_11, 3, x_69);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 0, x_12);
if (lean_is_scalar(x_9)) {
 x_75 = lean_alloc_ctor(0, 5, 0);
} else {
 x_75 = x_9;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_70);
lean_ctor_set(x_75, 2, x_71);
lean_ctor_set(x_75, 3, x_67);
lean_ctor_set(x_75, 4, x_11);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_11, 4);
x_77 = lean_ctor_get(x_11, 1);
x_78 = lean_ctor_get(x_11, 2);
lean_inc(x_76);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_11);
x_79 = lean_unsigned_to_nat(3u);
lean_inc(x_76);
x_80 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_80, 0, x_12);
lean_ctor_set(x_80, 1, x_5);
lean_ctor_set(x_80, 2, x_6);
lean_ctor_set(x_80, 3, x_76);
lean_ctor_set(x_80, 4, x_76);
if (lean_is_scalar(x_9)) {
 x_81 = lean_alloc_ctor(0, 5, 0);
} else {
 x_81 = x_9;
}
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_77);
lean_ctor_set(x_81, 2, x_78);
lean_ctor_set(x_81, 3, x_67);
lean_ctor_set(x_81, 4, x_80);
return x_81;
}
}
else
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_11, 4);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_11);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_84 = lean_ctor_get(x_11, 1);
x_85 = lean_ctor_get(x_11, 2);
x_86 = lean_ctor_get(x_11, 4);
lean_dec(x_86);
x_87 = lean_ctor_get(x_11, 3);
lean_dec(x_87);
x_88 = lean_ctor_get(x_11, 0);
lean_dec(x_88);
x_89 = !lean_is_exclusive(x_82);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_90 = lean_ctor_get(x_82, 1);
x_91 = lean_ctor_get(x_82, 2);
x_92 = lean_ctor_get(x_82, 4);
lean_dec(x_92);
x_93 = lean_ctor_get(x_82, 3);
lean_dec(x_93);
x_94 = lean_ctor_get(x_82, 0);
lean_dec(x_94);
x_95 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_82, 4, x_67);
lean_ctor_set(x_82, 3, x_67);
lean_ctor_set(x_82, 2, x_85);
lean_ctor_set(x_82, 1, x_84);
lean_ctor_set(x_82, 0, x_12);
lean_ctor_set(x_11, 4, x_67);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 0, x_12);
if (lean_is_scalar(x_9)) {
 x_96 = lean_alloc_ctor(0, 5, 0);
} else {
 x_96 = x_9;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_90);
lean_ctor_set(x_96, 2, x_91);
lean_ctor_set(x_96, 3, x_82);
lean_ctor_set(x_96, 4, x_11);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_82, 1);
x_98 = lean_ctor_get(x_82, 2);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_82);
x_99 = lean_unsigned_to_nat(3u);
x_100 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_100, 0, x_12);
lean_ctor_set(x_100, 1, x_84);
lean_ctor_set(x_100, 2, x_85);
lean_ctor_set(x_100, 3, x_67);
lean_ctor_set(x_100, 4, x_67);
lean_ctor_set(x_11, 4, x_67);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 0, x_12);
if (lean_is_scalar(x_9)) {
 x_101 = lean_alloc_ctor(0, 5, 0);
} else {
 x_101 = x_9;
}
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_97);
lean_ctor_set(x_101, 2, x_98);
lean_ctor_set(x_101, 3, x_100);
lean_ctor_set(x_101, 4, x_11);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_102 = lean_ctor_get(x_11, 1);
x_103 = lean_ctor_get(x_11, 2);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_11);
x_104 = lean_ctor_get(x_82, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_82, 2);
lean_inc(x_105);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 lean_ctor_release(x_82, 2);
 lean_ctor_release(x_82, 3);
 lean_ctor_release(x_82, 4);
 x_106 = x_82;
} else {
 lean_dec_ref(x_82);
 x_106 = lean_box(0);
}
x_107 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(0, 5, 0);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_12);
lean_ctor_set(x_108, 1, x_102);
lean_ctor_set(x_108, 2, x_103);
lean_ctor_set(x_108, 3, x_67);
lean_ctor_set(x_108, 4, x_67);
x_109 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_109, 0, x_12);
lean_ctor_set(x_109, 1, x_5);
lean_ctor_set(x_109, 2, x_6);
lean_ctor_set(x_109, 3, x_67);
lean_ctor_set(x_109, 4, x_67);
if (lean_is_scalar(x_9)) {
 x_110 = lean_alloc_ctor(0, 5, 0);
} else {
 x_110 = x_9;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_104);
lean_ctor_set(x_110, 2, x_105);
lean_ctor_set(x_110, 3, x_108);
lean_ctor_set(x_110, 4, x_109);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_9)) {
 x_112 = lean_alloc_ctor(0, 5, 0);
} else {
 x_112 = x_9;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_5);
lean_ctor_set(x_112, 2, x_6);
lean_ctor_set(x_112, 3, x_11);
lean_ctor_set(x_112, 4, x_82);
return x_112;
}
}
}
}
case 1:
{
lean_object* x_113; 
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_9)) {
 x_113 = lean_alloc_ctor(0, 5, 0);
} else {
 x_113 = x_9;
}
lean_ctor_set(x_113, 0, x_4);
lean_ctor_set(x_113, 1, x_1);
lean_ctor_set(x_113, 2, x_2);
lean_ctor_set(x_113, 3, x_7);
lean_ctor_set(x_113, 4, x_8);
return x_113;
}
default: 
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_4);
x_114 = l_Std_DTreeMap_Internal_Impl_insert___at___Lake_Package_initFacetConfigs_spec__0___redArg(x_1, x_2, x_8);
x_115 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_116 = lean_ctor_get(x_7, 0);
x_117 = lean_ctor_get(x_114, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_114, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_114, 3);
lean_inc(x_120);
x_121 = lean_ctor_get(x_114, 4);
lean_inc(x_121);
x_122 = lean_unsigned_to_nat(3u);
x_123 = lean_nat_mul(x_122, x_116);
x_124 = lean_nat_dec_lt(x_123, x_117);
lean_dec(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
x_125 = lean_nat_add(x_115, x_116);
x_126 = lean_nat_add(x_125, x_117);
lean_dec(x_117);
lean_dec(x_125);
if (lean_is_scalar(x_9)) {
 x_127 = lean_alloc_ctor(0, 5, 0);
} else {
 x_127 = x_9;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_5);
lean_ctor_set(x_127, 2, x_6);
lean_ctor_set(x_127, 3, x_7);
lean_ctor_set(x_127, 4, x_114);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 lean_ctor_release(x_114, 2);
 lean_ctor_release(x_114, 3);
 lean_ctor_release(x_114, 4);
 x_128 = x_114;
} else {
 lean_dec_ref(x_114);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_120, 0);
x_130 = lean_ctor_get(x_120, 1);
x_131 = lean_ctor_get(x_120, 2);
x_132 = lean_ctor_get(x_120, 3);
x_133 = lean_ctor_get(x_120, 4);
x_134 = lean_ctor_get(x_121, 0);
x_135 = lean_unsigned_to_nat(2u);
x_136 = lean_nat_mul(x_135, x_134);
x_137 = lean_nat_dec_lt(x_129, x_136);
lean_dec(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_148; 
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 lean_ctor_release(x_120, 2);
 lean_ctor_release(x_120, 3);
 lean_ctor_release(x_120, 4);
 x_138 = x_120;
} else {
 lean_dec_ref(x_120);
 x_138 = lean_box(0);
}
x_139 = lean_nat_add(x_115, x_116);
x_140 = lean_nat_add(x_139, x_117);
lean_dec(x_117);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_155; 
x_155 = lean_ctor_get(x_132, 0);
lean_inc(x_155);
x_148 = x_155;
goto block_154;
}
else
{
lean_object* x_156; 
x_156 = lean_unsigned_to_nat(0u);
x_148 = x_156;
goto block_154;
}
block_147:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_nat_add(x_142, x_143);
lean_dec(x_143);
lean_dec(x_142);
if (lean_is_scalar(x_138)) {
 x_145 = lean_alloc_ctor(0, 5, 0);
} else {
 x_145 = x_138;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_118);
lean_ctor_set(x_145, 2, x_119);
lean_ctor_set(x_145, 3, x_133);
lean_ctor_set(x_145, 4, x_121);
if (lean_is_scalar(x_128)) {
 x_146 = lean_alloc_ctor(0, 5, 0);
} else {
 x_146 = x_128;
}
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_130);
lean_ctor_set(x_146, 2, x_131);
lean_ctor_set(x_146, 3, x_141);
lean_ctor_set(x_146, 4, x_145);
return x_146;
}
block_154:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_nat_add(x_139, x_148);
lean_dec(x_148);
lean_dec(x_139);
if (lean_is_scalar(x_9)) {
 x_150 = lean_alloc_ctor(0, 5, 0);
} else {
 x_150 = x_9;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_5);
lean_ctor_set(x_150, 2, x_6);
lean_ctor_set(x_150, 3, x_7);
lean_ctor_set(x_150, 4, x_132);
x_151 = lean_nat_add(x_115, x_134);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_133, 0);
lean_inc(x_152);
x_141 = x_150;
x_142 = x_151;
x_143 = x_152;
goto block_147;
}
else
{
lean_object* x_153; 
x_153 = lean_unsigned_to_nat(0u);
x_141 = x_150;
x_142 = x_151;
x_143 = x_153;
goto block_147;
}
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
lean_dec(x_9);
x_157 = lean_nat_add(x_115, x_116);
x_158 = lean_nat_add(x_157, x_117);
lean_dec(x_117);
x_159 = lean_nat_add(x_157, x_129);
lean_dec(x_157);
lean_inc_ref(x_7);
if (lean_is_scalar(x_128)) {
 x_160 = lean_alloc_ctor(0, 5, 0);
} else {
 x_160 = x_128;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_5);
lean_ctor_set(x_160, 2, x_6);
lean_ctor_set(x_160, 3, x_7);
lean_ctor_set(x_160, 4, x_120);
x_161 = !lean_is_exclusive(x_7);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_162 = lean_ctor_get(x_7, 4);
lean_dec(x_162);
x_163 = lean_ctor_get(x_7, 3);
lean_dec(x_163);
x_164 = lean_ctor_get(x_7, 2);
lean_dec(x_164);
x_165 = lean_ctor_get(x_7, 1);
lean_dec(x_165);
x_166 = lean_ctor_get(x_7, 0);
lean_dec(x_166);
lean_ctor_set(x_7, 4, x_121);
lean_ctor_set(x_7, 3, x_160);
lean_ctor_set(x_7, 2, x_119);
lean_ctor_set(x_7, 1, x_118);
lean_ctor_set(x_7, 0, x_158);
return x_7;
}
else
{
lean_object* x_167; 
lean_dec(x_7);
x_167 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_167, 0, x_158);
lean_ctor_set(x_167, 1, x_118);
lean_ctor_set(x_167, 2, x_119);
lean_ctor_set(x_167, 3, x_160);
lean_ctor_set(x_167, 4, x_121);
return x_167;
}
}
}
}
else
{
lean_object* x_168; 
x_168 = lean_ctor_get(x_114, 3);
lean_inc(x_168);
if (lean_obj_tag(x_168) == 0)
{
uint8_t x_169; 
x_169 = !lean_is_exclusive(x_114);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_170 = lean_ctor_get(x_114, 4);
x_171 = lean_ctor_get(x_114, 3);
lean_dec(x_171);
x_172 = lean_ctor_get(x_114, 0);
lean_dec(x_172);
x_173 = !lean_is_exclusive(x_168);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_174 = lean_ctor_get(x_168, 1);
x_175 = lean_ctor_get(x_168, 2);
x_176 = lean_ctor_get(x_168, 4);
lean_dec(x_176);
x_177 = lean_ctor_get(x_168, 3);
lean_dec(x_177);
x_178 = lean_ctor_get(x_168, 0);
lean_dec(x_178);
x_179 = lean_unsigned_to_nat(3u);
lean_inc_n(x_170, 2);
lean_ctor_set(x_168, 4, x_170);
lean_ctor_set(x_168, 3, x_170);
lean_ctor_set(x_168, 2, x_6);
lean_ctor_set(x_168, 1, x_5);
lean_ctor_set(x_168, 0, x_115);
lean_inc(x_170);
lean_ctor_set(x_114, 3, x_170);
lean_ctor_set(x_114, 0, x_115);
if (lean_is_scalar(x_9)) {
 x_180 = lean_alloc_ctor(0, 5, 0);
} else {
 x_180 = x_9;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_174);
lean_ctor_set(x_180, 2, x_175);
lean_ctor_set(x_180, 3, x_168);
lean_ctor_set(x_180, 4, x_114);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_181 = lean_ctor_get(x_168, 1);
x_182 = lean_ctor_get(x_168, 2);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_168);
x_183 = lean_unsigned_to_nat(3u);
lean_inc_n(x_170, 2);
x_184 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_184, 0, x_115);
lean_ctor_set(x_184, 1, x_5);
lean_ctor_set(x_184, 2, x_6);
lean_ctor_set(x_184, 3, x_170);
lean_ctor_set(x_184, 4, x_170);
lean_inc(x_170);
lean_ctor_set(x_114, 3, x_170);
lean_ctor_set(x_114, 0, x_115);
if (lean_is_scalar(x_9)) {
 x_185 = lean_alloc_ctor(0, 5, 0);
} else {
 x_185 = x_9;
}
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_181);
lean_ctor_set(x_185, 2, x_182);
lean_ctor_set(x_185, 3, x_184);
lean_ctor_set(x_185, 4, x_114);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_186 = lean_ctor_get(x_114, 4);
x_187 = lean_ctor_get(x_114, 1);
x_188 = lean_ctor_get(x_114, 2);
lean_inc(x_186);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_114);
x_189 = lean_ctor_get(x_168, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_168, 2);
lean_inc(x_190);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 lean_ctor_release(x_168, 2);
 lean_ctor_release(x_168, 3);
 lean_ctor_release(x_168, 4);
 x_191 = x_168;
} else {
 lean_dec_ref(x_168);
 x_191 = lean_box(0);
}
x_192 = lean_unsigned_to_nat(3u);
lean_inc_n(x_186, 2);
if (lean_is_scalar(x_191)) {
 x_193 = lean_alloc_ctor(0, 5, 0);
} else {
 x_193 = x_191;
}
lean_ctor_set(x_193, 0, x_115);
lean_ctor_set(x_193, 1, x_5);
lean_ctor_set(x_193, 2, x_6);
lean_ctor_set(x_193, 3, x_186);
lean_ctor_set(x_193, 4, x_186);
lean_inc(x_186);
x_194 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_194, 0, x_115);
lean_ctor_set(x_194, 1, x_187);
lean_ctor_set(x_194, 2, x_188);
lean_ctor_set(x_194, 3, x_186);
lean_ctor_set(x_194, 4, x_186);
if (lean_is_scalar(x_9)) {
 x_195 = lean_alloc_ctor(0, 5, 0);
} else {
 x_195 = x_9;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_189);
lean_ctor_set(x_195, 2, x_190);
lean_ctor_set(x_195, 3, x_193);
lean_ctor_set(x_195, 4, x_194);
return x_195;
}
}
else
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_114, 4);
lean_inc(x_196);
if (lean_obj_tag(x_196) == 0)
{
uint8_t x_197; 
x_197 = !lean_is_exclusive(x_114);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_198 = lean_ctor_get(x_114, 1);
x_199 = lean_ctor_get(x_114, 2);
x_200 = lean_ctor_get(x_114, 4);
lean_dec(x_200);
x_201 = lean_ctor_get(x_114, 3);
lean_dec(x_201);
x_202 = lean_ctor_get(x_114, 0);
lean_dec(x_202);
x_203 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_114, 4, x_168);
lean_ctor_set(x_114, 2, x_6);
lean_ctor_set(x_114, 1, x_5);
lean_ctor_set(x_114, 0, x_115);
if (lean_is_scalar(x_9)) {
 x_204 = lean_alloc_ctor(0, 5, 0);
} else {
 x_204 = x_9;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_198);
lean_ctor_set(x_204, 2, x_199);
lean_ctor_set(x_204, 3, x_114);
lean_ctor_set(x_204, 4, x_196);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_205 = lean_ctor_get(x_114, 1);
x_206 = lean_ctor_get(x_114, 2);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_114);
x_207 = lean_unsigned_to_nat(3u);
x_208 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_208, 0, x_115);
lean_ctor_set(x_208, 1, x_5);
lean_ctor_set(x_208, 2, x_6);
lean_ctor_set(x_208, 3, x_168);
lean_ctor_set(x_208, 4, x_168);
if (lean_is_scalar(x_9)) {
 x_209 = lean_alloc_ctor(0, 5, 0);
} else {
 x_209 = x_9;
}
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_205);
lean_ctor_set(x_209, 2, x_206);
lean_ctor_set(x_209, 3, x_208);
lean_ctor_set(x_209, 4, x_196);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_9)) {
 x_211 = lean_alloc_ctor(0, 5, 0);
} else {
 x_211 = x_9;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_5);
lean_ctor_set(x_211, 2, x_6);
lean_ctor_set(x_211, 3, x_196);
lean_ctor_set(x_211, 4, x_114);
return x_211;
}
}
}
}
}
}
else
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_unsigned_to_nat(1u);
x_213 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_1);
lean_ctor_set(x_213, 2, x_2);
lean_ctor_set(x_213, 3, x_3);
lean_ctor_set(x_213, 4, x_3);
return x_213;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lake_Package_initFacetConfigs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_insert___at___Lake_Package_initFacetConfigs_spec__0___redArg(x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_1 = lean_box(1);
x_2 = l_Lake_Package_depsFacet;
x_3 = l_Lake_Package_depsFacetConfig;
x_4 = l_Std_DTreeMap_Internal_Impl_insert___at___Lake_Package_initFacetConfigs_spec__0___redArg(x_2, x_3, x_1);
x_5 = l_Lake_Package_transDepsFacet;
x_6 = l_Lake_Package_transDepsFacetConfig;
x_7 = l_Std_DTreeMap_Internal_Impl_insert___at___Lake_Package_initFacetConfigs_spec__0___redArg(x_5, x_6, x_4);
x_8 = l_Lake_Package_extraDepFacet;
x_9 = l_Lake_Package_extraDepFacetConfig;
x_10 = l_Std_DTreeMap_Internal_Impl_insert___at___Lake_Package_initFacetConfigs_spec__0___redArg(x_8, x_9, x_7);
x_11 = l_Lake_Package_optBuildCacheFacet;
x_12 = l_Lake_Package_optBuildCacheFacetConfig;
x_13 = l_Std_DTreeMap_Internal_Impl_insert___at___Lake_Package_initFacetConfigs_spec__0___redArg(x_11, x_12, x_10);
x_14 = l_Lake_Package_buildCacheFacet;
x_15 = l_Lake_Package_buildCacheFacetConfig;
x_16 = l_Std_DTreeMap_Internal_Impl_insert___at___Lake_Package_initFacetConfigs_spec__0___redArg(x_14, x_15, x_13);
x_17 = l_Lake_Package_optReservoirBarrelFacet;
x_18 = l_Lake_Package_optBarrelFacetConfig;
x_19 = l_Std_DTreeMap_Internal_Impl_insert___at___Lake_Package_initFacetConfigs_spec__0___redArg(x_17, x_18, x_16);
x_20 = l_Lake_Package_reservoirBarrelFacet;
x_21 = l_Lake_Package_barrelFacetConfig;
x_22 = l_Std_DTreeMap_Internal_Impl_insert___at___Lake_Package_initFacetConfigs_spec__0___redArg(x_20, x_21, x_19);
x_23 = l_Lake_Package_optGitHubReleaseFacet;
x_24 = l_Lake_Package_optGitHubReleaseFacetConfig;
x_25 = l_Std_DTreeMap_Internal_Impl_insert___at___Lake_Package_initFacetConfigs_spec__0___redArg(x_23, x_24, x_22);
x_26 = l_Lake_Package_gitHubReleaseFacet;
x_27 = l_Lake_Package_gitHubReleaseFacetConfig;
x_28 = l_Std_DTreeMap_Internal_Impl_insert___at___Lake_Package_initFacetConfigs_spec__0___redArg(x_26, x_27, x_25);
return x_28;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_initFacetConfigs;
return x_1;
}
}
lean_object* initialize_Lake_Util_Name(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_FacetConfig(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Job_Monad(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Infos(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Git(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Proc(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Actions(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Common(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Targets(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Topological(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Job_Register(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Reservoir(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Package(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Name(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_FacetConfig(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job_Monad(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Infos(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Git(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Proc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Actions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Common(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Targets(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Topological(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job_Register(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Reservoir(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1_spec__1___redArg___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1_spec__1___redArg___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1_spec__1___redArg___closed__0);
l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1_spec__1___redArg___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1_spec__1___redArg___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1_spec__1___redArg___closed__1);
l_panic___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__5___closed__0 = _init_l_panic___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__5___closed__0();
lean_mark_persistent(l_panic___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3_spec__5___closed__0);
l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__0 = _init_l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__0();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__0);
l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__1 = _init_l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__1();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__1);
l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__2 = _init_l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__2();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__2);
l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__3 = _init_l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__3();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__3);
l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__4 = _init_l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__4();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3_spec__3___redArg___closed__4);
l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__0 = _init_l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__0();
lean_mark_persistent(l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__0);
l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__1 = _init_l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__1();
lean_mark_persistent(l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__1);
l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__2 = _init_l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__2();
lean_mark_persistent(l_Lake_ensureJob___at_____private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__3___closed__2);
l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__0 = _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__0();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__0);
l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__1 = _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__1();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__1);
l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_formatQuery___at___Lake_Package_depsFacetConfig_spec__0_spec__0___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_formatQuery___at___Lake_Package_depsFacetConfig_spec__0_spec__0___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_formatQuery___at___Lake_Package_depsFacetConfig_spec__0_spec__0___closed__0);
l_Lake_Package_depsFacetConfig___closed__0 = _init_l_Lake_Package_depsFacetConfig___closed__0();
lean_mark_persistent(l_Lake_Package_depsFacetConfig___closed__0);
l_Lake_Package_depsFacetConfig = _init_l_Lake_Package_depsFacetConfig();
lean_mark_persistent(l_Lake_Package_depsFacetConfig);
l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__0 = _init_l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__0();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__0);
l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__1 = _init_l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__1();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__1);
l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__2 = _init_l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__2();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__2);
l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__3 = _init_l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__3();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__3);
l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__4 = _init_l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__4();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__4);
l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__5 = _init_l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__5();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__5);
l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__6 = _init_l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__6();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9___closed__6);
l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9 = _init_l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at_____private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__9);
l_Lake_Package_transDepsFacetConfig___closed__0 = _init_l_Lake_Package_transDepsFacetConfig___closed__0();
lean_mark_persistent(l_Lake_Package_transDepsFacetConfig___closed__0);
l_Lake_Package_transDepsFacetConfig___closed__1 = _init_l_Lake_Package_transDepsFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Package_transDepsFacetConfig___closed__1);
l_Lake_Package_transDepsFacetConfig___closed__2 = _init_l_Lake_Package_transDepsFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Package_transDepsFacetConfig___closed__2);
l_Lake_Package_transDepsFacetConfig = _init_l_Lake_Package_transDepsFacetConfig();
lean_mark_persistent(l_Lake_Package_transDepsFacetConfig);
l_Lake_formatQuery___at___Lake_Package_optBuildCacheFacetConfig_spec__0___closed__0 = _init_l_Lake_formatQuery___at___Lake_Package_optBuildCacheFacetConfig_spec__0___closed__0();
lean_mark_persistent(l_Lake_formatQuery___at___Lake_Package_optBuildCacheFacetConfig_spec__0___closed__0);
l_Lake_formatQuery___at___Lake_Package_optBuildCacheFacetConfig_spec__0___closed__1 = _init_l_Lake_formatQuery___at___Lake_Package_optBuildCacheFacetConfig_spec__0___closed__1();
lean_mark_persistent(l_Lake_formatQuery___at___Lake_Package_optBuildCacheFacetConfig_spec__0___closed__1);
l_Lake_Package_optBuildCacheFacetConfig = _init_l_Lake_Package_optBuildCacheFacetConfig();
lean_mark_persistent(l_Lake_Package_optBuildCacheFacetConfig);
l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__0 = _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__0();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__0);
l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__1 = _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__1();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__1);
l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__2 = _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__2();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__2);
l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__3 = _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__3();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__3);
l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0 = _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1 = _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1);
l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2 = _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2);
l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3 = _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3);
l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__0 = _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__0();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__0);
l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__1 = _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__1();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__1);
l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2 = _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2);
l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3 = _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3);
l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__0 = _init_l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__0();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__0);
l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__1 = _init_l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__1();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__1);
l_Lake_formatQuery___at___Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0 = _init_l_Lake_formatQuery___at___Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lake_formatQuery___at___Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0);
l_Lake_Package_extraDepFacetConfig___closed__0 = _init_l_Lake_Package_extraDepFacetConfig___closed__0();
lean_mark_persistent(l_Lake_Package_extraDepFacetConfig___closed__0);
l_Lake_Package_extraDepFacetConfig = _init_l_Lake_Package_extraDepFacetConfig();
lean_mark_persistent(l_Lake_Package_extraDepFacetConfig);
l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0 = _init_l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0);
l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__1 = _init_l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__1();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__1);
l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__2 = _init_l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__2();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__2);
l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__3 = _init_l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__3();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__3);
l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__4 = _init_l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__4();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__4);
l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__5 = _init_l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__5();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__5);
l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__6 = _init_l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__6();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__6);
l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__7 = _init_l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__7();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__7);
l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__8 = _init_l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__8();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__8);
l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__0 = _init_l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__0();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__0);
l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__1 = _init_l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__1();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__1);
l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__2 = _init_l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__2();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__2);
l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__3 = _init_l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__3();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__3);
l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__4 = _init_l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__4();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__4);
l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__5 = _init_l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__5();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__5);
l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__6 = _init_l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__6();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__6);
l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__7 = _init_l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__7();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__7);
l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg___closed__0 = _init_l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg___closed__0();
lean_mark_persistent(l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg___closed__0);
l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg___closed__1 = _init_l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg___closed__1();
lean_mark_persistent(l_Lake_buildAction___at_____private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__4___redArg___closed__1);
l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__0 = _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__0();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__0);
l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__1 = _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__1();
l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__2 = _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__2();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__2);
l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3 = _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3);
l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4 = _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4);
l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__5 = _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__5();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__5);
l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__0 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__0();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__0);
l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__1 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__1();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__1);
l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__2 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__2();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__2);
l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3);
l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___closed__0 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___closed__0();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___closed__0);
l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__0 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__0();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__0);
l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__1 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__1();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__1);
l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__2 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__2();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__2);
l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3);
l_Lake_Package_buildCacheFacetConfig___lam__1___closed__0 = _init_l_Lake_Package_buildCacheFacetConfig___lam__1___closed__0();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig___lam__1___closed__0);
l_Lake_Package_buildCacheFacetConfig___closed__0 = _init_l_Lake_Package_buildCacheFacetConfig___closed__0();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig___closed__0);
l_Lake_Package_buildCacheFacetConfig = _init_l_Lake_Package_buildCacheFacetConfig();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig);
l_Lake_Package_optBarrelFacetConfig___lam__1___closed__0 = _init_l_Lake_Package_optBarrelFacetConfig___lam__1___closed__0();
lean_mark_persistent(l_Lake_Package_optBarrelFacetConfig___lam__1___closed__0);
l_Lake_Package_optBarrelFacetConfig___lam__1___closed__1 = _init_l_Lake_Package_optBarrelFacetConfig___lam__1___closed__1();
lean_mark_persistent(l_Lake_Package_optBarrelFacetConfig___lam__1___closed__1);
l_Lake_Package_optBarrelFacetConfig___closed__0 = _init_l_Lake_Package_optBarrelFacetConfig___closed__0();
lean_mark_persistent(l_Lake_Package_optBarrelFacetConfig___closed__0);
l_Lake_Package_optBarrelFacetConfig___closed__1 = _init_l_Lake_Package_optBarrelFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Package_optBarrelFacetConfig___closed__1);
l_Lake_Package_optBarrelFacetConfig = _init_l_Lake_Package_optBarrelFacetConfig();
lean_mark_persistent(l_Lake_Package_optBarrelFacetConfig);
l_Lake_Package_barrelFacetConfig___lam__1___closed__0 = _init_l_Lake_Package_barrelFacetConfig___lam__1___closed__0();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig___lam__1___closed__0);
l_Lake_Package_barrelFacetConfig = _init_l_Lake_Package_barrelFacetConfig();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig);
l_Lake_Package_optGitHubReleaseFacetConfig___closed__0 = _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__0();
lean_mark_persistent(l_Lake_Package_optGitHubReleaseFacetConfig___closed__0);
l_Lake_Package_optGitHubReleaseFacetConfig = _init_l_Lake_Package_optGitHubReleaseFacetConfig();
lean_mark_persistent(l_Lake_Package_optGitHubReleaseFacetConfig);
l_Lake_Package_gitHubReleaseFacetConfig___lam__1___closed__0 = _init_l_Lake_Package_gitHubReleaseFacetConfig___lam__1___closed__0();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig___lam__1___closed__0);
l_Lake_Package_gitHubReleaseFacetConfig = _init_l_Lake_Package_gitHubReleaseFacetConfig();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig);
l_Lake_Package_initFacetConfigs = _init_l_Lake_Package_initFacetConfigs();
lean_mark_persistent(l_Lake_Package_initFacetConfigs);
l_Lake_initPackageFacetConfigs = _init_l_Lake_initPackageFacetConfigs();
lean_mark_persistent(l_Lake_initPackageFacetConfigs);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

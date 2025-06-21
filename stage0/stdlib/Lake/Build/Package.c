// Lean compiler output
// Module: Lake.Build.Package
// Imports: Lake.Util.Git Lake.Util.Sugar Lake.Build.Common Lake.Build.Targets Lake.Build.Topological Lake.Reservoir
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
LEAN_EXPORT lean_object* l_Lake_Package_getReleaseUrl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_recBuildExtraDepTargets___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig___lam__1(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_fetchTargetJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_ensureJob___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JobResult_prependLog___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_initFacetConfigs___closed__3;
lean_object* l_Lean_Json_compress(lean_object*);
static lean_object* l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__5;
LEAN_EXPORT lean_object* l_Lake_initPackageFacetConfigs;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getReleaseUrl___redArg___closed__13;
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__3;
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig;
static lean_object* l_Lake_Package_getReleaseUrl___redArg___closed__9;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__7;
static lean_object* l_Lake_Package_getBarrelUrl___redArg___closed__19;
lean_object* l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_recFetchDeps___lam__1___closed__0;
lean_object* l_System_FilePath_normalize(lean_object*);
static lean_object* l_Lake_Package_fetchBuildArchive___closed__2;
extern lean_object* l_Lake_Package_depsFacet;
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig___lam__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Package_fetchBuildArchive___closed__4;
static lean_object* l_Lake_Package_getReleaseUrl___redArg___closed__2;
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___closed__2;
static lean_object* l_Lake_Package_depsFacetConfig___closed__0;
LEAN_EXPORT lean_object* l_Lake_Package_getReleaseUrl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_mapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__0(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_transDepsFacetConfig___closed__2;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recFetchDeps___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCache___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig;
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_download(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lake_buildUnlessUpToDate_x3f_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_initFacetConfigs___closed__5;
extern lean_object* l_Lake_Package_keyword;
static lean_object* l_Lake_Package_initFacetConfigs___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__3___boxed(lean_object**);
static lean_object* l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__3;
lean_object* l_Lake_EStateT_instPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Reservoir_lakeHeaders;
static lean_object* l_Lake_Package_initFacetConfigs___closed__6;
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at___Lake_Package_fetchBuildArchive_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___redArg___closed__8;
lean_object* l_Lake_EStateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recFetchDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___Lake_buildUnlessUpToDate_x3f___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getReleaseUrl___redArg___closed__11;
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__8(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig;
lean_object* l_Lake_readTraceFile_x3f(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___closed__3;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
extern lean_object* l_Lake_Package_gitHubReleaseFacet;
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___closed__1;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__4;
static lean_object* l_Lake_Package_getBarrelUrl___redArg___closed__18;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCache___closed__3;
LEAN_EXPORT lean_object* l_Lake_Package_fetchBuildArchive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__13;
static lean_object* l_Lake_Package_getReleaseUrl___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl___redArg___lam__0___boxed(lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindBool;
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___redArg___closed__2;
lean_object* l_Lake_Job_mix___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___closed__2;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lake_Package_getReleaseUrl___redArg___closed__4;
lean_object* l_Lake_captureProc_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Package_recFetchDeps___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_transDepsFacetConfig;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instFunctor___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1___lam__0(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lake_nullFormat___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2___closed__0;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
static lean_object* l_Lake_stdFormat___at___Lake_Package_optBuildCacheFacetConfig_spec__0___closed__0;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__0;
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___redArg___closed__9;
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__5;
extern lean_object* l_Lake_instDataKindUnit;
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Package_recBuildExtraDepTargets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___lam__0(lean_object*, lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lake_Package_recComputeTransDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___redArg___closed__14;
static lean_object* l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___redArg___closed__13;
extern lean_object* l_Lake_Package_transDepsFacet;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__12;
static lean_object* l_Lake_Package_initFacetConfigs___closed__8;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___redArg___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JobState_merge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___redArg___closed__10;
static lean_object* l_Lake_Package_getBarrelUrl___redArg___closed__16;
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lake_Package_recBuildExtraDepTargets___closed__0;
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
static lean_object* l_Lake_Package_transDepsFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_getReleaseUrl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___closed__1;
static lean_object* l_Lake_Package_getBarrelUrl___redArg___closed__7;
static lean_object* l_Lake_Package_initFacetConfigs___closed__1;
static lean_object* l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__6;
static lean_object* l_Lake_Package_recFetchDeps___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__4;
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
lean_object* l_Lake_Name_eraseHead(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_renew___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__8_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7;
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
static lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instToJsonBool___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_initFacetConfigs;
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_barrelFacetConfig___lam__2___closed__0;
static lean_object* l_Lake_Package_optBarrelFacetConfig___closed__0;
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Package_buildCacheFacet;
lean_object* lean_string_from_utf8_unchecked(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___closed__3;
static lean_object* l_Lake_Package_getBarrelUrl___redArg___closed__11;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__1;
lean_object* l_Lake_untar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonadExceptOfOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getReleaseUrl___redArg___closed__10;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0;
static lean_object* l_Lake_Package_getReleaseUrl___redArg___closed__14;
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Package_recBuildExtraDepTargets_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0(uint8_t, lean_object*);
static lean_object* l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__0;
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig;
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
static lean_object* l_Lake_Package_maybeFetchBuildCache___closed__0;
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0___lam__0(uint8_t, lean_object*);
static lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JobM_runSpawnM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_depsFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___redArg___closed__12;
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at___Lake_Package_fetchBuildArchive_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getReleaseUrl___redArg___closed__7;
static lean_object* l_Lake_Package_maybeFetchBuildCache___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Package_extraDepFacet;
lean_object* l_panic___at___Lean_Name_getString_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getReleaseUrl___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recComputeTransDeps___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_Job_async___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_MTime_checkUpToDate___at___Lake_buildUnlessUpToDate_x3f___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getReleaseUrl___redArg___closed__12;
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___closed__0;
static lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg___closed__0;
static lean_object* l_Lake_Package_extraDepFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Package_optGitHubReleaseFacet;
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getReleaseUrl___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lake_EquipT_tryCatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
static lean_object* l_Lake_Package_getReleaseUrl___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_recComputeTransDeps___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_stdFormat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_prevn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Lake_uriEncode(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig;
static lean_object* l_Lake_Package_getBarrelUrl___redArg___closed__15;
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_fetchBuildArchive___closed__3;
uint8_t l_instDecidableNot___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at___Lake_Package_fetchBuildArchive_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___closed__0;
static lean_object* l_Lake_Package_fetchBuildArchive___closed__0;
static lean_object* l_Lake_Package_fetchBuildArchive___closed__1;
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_JobAction_merge(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_Package_optBuildCacheFacetConfig_spec__0(uint8_t, uint8_t);
static lean_object* l_Lake_Package_getBarrelUrl___redArg___closed__17;
LEAN_EXPORT uint8_t l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__1(uint8_t, lean_object*);
lean_object* l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lake_Job_add___redArg(lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_FetchM_runJobM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__2;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__11;
lean_object* l_Lake_Env_toolchain(lean_object*);
static lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2___closed__0;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___closed__0;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Package_reservoirBarrelFacet;
extern lean_object* l_Lake_Package_optBuildCacheFacet;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_stdFormat___at___Lake_Package_optBuildCacheFacetConfig_spec__0___closed__1;
lean_object* l_Lake_EStateT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recFetchDeps___lam__0___boxed(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0___closed__0;
lean_object* lean_io_wait(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___redArg___closed__5;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lake_checkHashUpToDate___at___Lake_buildUnlessUpToDate_x3f___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__0;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__8_spec__8(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_extraDepFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_depsFacetConfig___lam__0___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_Package_recFetchDeps___lam__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_Package_recFetchDeps___boxed__const__1;
lean_object* l_Lake_EquipT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___redArg___closed__1;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__10;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_depsFacetConfig___lam__0(uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instToStringBool___lam__0___boxed(lean_object*);
static lean_object* l_Lake_Package_extraDepFacetConfig___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lake_BuildInfo_fetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_Package_optBuildCacheFacetConfig_spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Package_initFacetConfigs___closed__0;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getReleaseUrl___redArg___closed__8;
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__8;
static lean_object* l_Lake_Package_transDepsFacetConfig___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at___Lake_Package_fetchBuildArchive_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lake_Package_initFacetConfigs___closed__4;
static lean_object* l_Lake_Package_initFacetConfigs___closed__7;
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___redArg___closed__6;
static lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg___closed__1;
static lean_object* l_Lake_Package_getBarrelUrl___redArg___closed__4;
LEAN_EXPORT uint8_t l_Lake_Package_getBarrelUrl___redArg___lam__0(uint8_t, lean_object*);
lean_object* l_Lake_Reservoir_pkgApiUrl(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Package_optReservoirBarrelFacet;
static lean_object* l_Lake_Package_getReleaseUrl___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": package not found for dependency '", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' (this is likely a bug in Lake)", 32, 32);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_4, x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_6, 1);
x_13 = lean_ctor_get(x_12, 4);
x_14 = lean_array_uget(x_5, x_4);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_13, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_5);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
lean_inc(x_2);
x_18 = l_Lean_Name_toString(x_17, x_9, x_2);
x_19 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg___closed__0;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Lean_Name_toString(x_15, x_9, x_2);
x_22 = lean_string_append(x_20, x_21);
lean_dec(x_21);
x_23 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_box(3);
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_27);
x_28 = lean_array_get_size(x_7);
x_29 = lean_array_push(x_7, x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_8);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; 
lean_dec(x_15);
x_32 = lean_ctor_get(x_16, 0);
lean_inc(x_32);
lean_dec(x_16);
x_33 = lean_box(0);
x_34 = lean_array_uset(x_5, x_4, x_33);
x_35 = 1;
x_36 = lean_usize_add(x_4, x_35);
x_37 = lean_array_uset(x_34, x_4, x_32);
x_4 = x_36;
x_5 = x_37;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_9, 1);
x_16 = lean_ctor_get(x_15, 4);
x_17 = lean_array_uget(x_5, x_4);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_16, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_5);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
lean_inc(x_2);
x_21 = l_Lean_Name_toString(x_20, x_12, x_2);
x_22 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg___closed__0;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Lean_Name_toString(x_18, x_12, x_2);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
x_26 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg___closed__1;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_box(3);
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
x_30 = lean_unbox(x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_30);
x_31 = lean_array_get_size(x_10);
x_32 = lean_array_push(x_10, x_29);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_11);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_18);
x_35 = lean_ctor_get(x_19, 0);
lean_inc(x_35);
lean_dec(x_19);
x_36 = lean_box(0);
x_37 = lean_array_uset(x_5, x_4, x_36);
x_38 = 1;
x_39 = lean_usize_add(x_4, x_38);
x_40 = lean_array_uset(x_37, x_4, x_35);
x_41 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg(x_1, x_2, x_3, x_39, x_40, x_9, x_10, x_11);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_25 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__2___redArg___lam__0(x_16, x_21, x_24, x_23, x_20);
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
x_41 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__2___redArg___lam__0(x_16, x_21, x_40, x_39, x_20);
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
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_25 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__3___redArg___lam__0(x_16, x_21, x_24, x_23, x_20);
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
x_41 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__3___redArg___lam__0(x_16, x_21, x_40, x_39, x_20);
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
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__4___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_25 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__4___redArg___lam__0(x_16, x_21, x_24, x_23, x_20);
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
x_41 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__4___redArg___lam__0(x_16, x_21, x_40, x_39, x_20);
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
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__4___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___closed__0() {
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
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.String.Extra", 22, 22);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String.fromUTF8!", 16, 16);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid UTF-8 string", 20, 20);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___closed__3;
x_2 = lean_unsigned_to_nat(47u);
x_3 = lean_unsigned_to_nat(129u);
x_4 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___closed__2;
x_5 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___closed__1;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___closed__0;
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
x_54 = lean_alloc_closure((void*)(l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__4), 9, 3);
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
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
block_53:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_alloc_closure((void*)(l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__2), 9, 3);
lean_closure_set(x_27, 0, lean_box(0));
lean_closure_set(x_27, 1, x_25);
lean_closure_set(x_27, 2, x_26);
x_28 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__3___redArg(x_24, x_27, x_3, x_4, x_5, x_6, x_7, x_23);
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
x_38 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___closed__4;
x_39 = l_panic___at___Lean_Name_getString_x21_spec__0(x_38);
x_9 = x_35;
x_10 = x_32;
x_11 = x_31;
x_12 = x_39;
goto block_16;
}
else
{
lean_object* x_40; 
x_40 = lean_string_from_utf8_unchecked(x_36);
lean_dec(x_36);
x_9 = x_35;
x_10 = x_32;
x_11 = x_31;
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
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_JobResult_prependLog___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
static lean_object* _init_l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<nil>", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__1;
x_2 = l_Lake_BuildTrace_nil(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
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
x_103 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__3;
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
x_113 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___lam__1(x_99, x_111, x_2, x_3, x_4, x_5, x_112, x_12);
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
x_115 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___lam__1(x_99, x_114, x_2, x_3, x_4, x_5, x_97, x_12);
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
x_21 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__0;
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_box(0);
x_24 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__2;
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
x_51 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___lam__0), 2, 1);
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
x_60 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___lam__0), 2, 1);
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
x_71 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___lam__0), 2, 1);
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
x_88 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___lam__0), 2, 1);
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
LEAN_EXPORT uint8_t l_Lake_Package_recFetchDeps___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_recFetchDeps___lam__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_recFetchDeps___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_1 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__2;
x_2 = lean_box(0);
x_3 = l_Lake_Package_recFetchDeps___lam__1___closed__0;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
x_5 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_5);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recFetchDeps___lam__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_box(0);
x_19 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__0;
x_20 = l_Lake_Package_recFetchDeps___lam__1___closed__1;
lean_ctor_set(x_13, 1, x_20);
x_21 = lean_task_pure(x_13);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_19);
x_24 = lean_unbox(x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*3, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_17);
lean_ctor_set(x_12, 0, x_25);
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_28 = lean_box(0);
x_29 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__0;
x_30 = l_Lake_Package_recFetchDeps___lam__1___closed__1;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_task_pure(x_31);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_28);
lean_ctor_set(x_34, 2, x_29);
x_35 = lean_unbox(x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*3, x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_27);
lean_ctor_set(x_12, 0, x_36);
return x_12;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_37 = lean_ctor_get(x_12, 1);
lean_inc(x_37);
lean_dec(x_12);
x_38 = lean_ctor_get(x_13, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_13, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_40 = x_13;
} else {
 lean_dec_ref(x_13);
 x_40 = lean_box(0);
}
x_41 = lean_box(0);
x_42 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__0;
x_43 = l_Lake_Package_recFetchDeps___lam__1___closed__1;
if (lean_is_scalar(x_40)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_40;
}
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_task_pure(x_44);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_41);
lean_ctor_set(x_47, 2, x_42);
x_48 = lean_unbox(x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*3, x_48);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_39);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_37);
return x_50;
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_12);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_12, 0);
lean_dec(x_52);
x_53 = !lean_is_exclusive(x_13);
if (x_53 == 0)
{
return x_12;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_13, 0);
x_55 = lean_ctor_get(x_13, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_13);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_12, 0, x_56);
return x_12;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_12, 1);
lean_inc(x_57);
lean_dec(x_12);
x_58 = lean_ctor_get(x_13, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_13, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_60 = x_13;
} else {
 lean_dec_ref(x_13);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
return x_62;
}
}
}
}
static lean_object* _init_l_Lake_Package_recFetchDeps___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recFetchDeps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 9);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lake_Package_recFetchDeps___lam__0___boxed), 1, 0);
x_10 = lean_array_size(x_8);
x_11 = lean_box_usize(x_10);
x_12 = l_Lake_Package_recFetchDeps___boxed__const__1;
x_13 = lean_alloc_closure((void*)(l_Lake_Package_recFetchDeps___lam__1___boxed), 11, 5);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_9);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
lean_closure_set(x_13, 4, x_8);
x_14 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2(x_13, x_2, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__2___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__3___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__4___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__4___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recFetchDeps___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Package_recFetchDeps___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recFetchDeps___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Lake_Package_recFetchDeps___lam__1(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(x_5);
x_9 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_Name_toString(x_7, x_11, x_9);
x_13 = lean_string_append(x_4, x_12);
lean_dec(x_12);
x_14 = l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0___closed__0;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
x_7 = lean_ctor_get(x_6, 0);
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
static lean_object* _init_l_Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_recFetchDeps___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1___closed__0;
x_3 = lean_array_size(x_1);
x_4 = 0;
x_5 = l_Array_mapMUnsafe_map___at___Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1_spec__1(x_2, x_3, x_4, x_1);
x_6 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
if (x_1 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__0;
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
x_18 = l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0(x_2, x_16, x_17, x_11);
lean_dec(x_2);
x_3 = x_18;
goto block_10;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1(x_2);
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
LEAN_EXPORT lean_object* l_Lake_Package_depsFacetConfig___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_depsFacetConfig___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_recFetchDeps), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_depsFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_depsFacetConfig___lam__0___boxed), 2, 0);
x_2 = lean_box(0);
x_3 = l_Lake_Package_keyword;
x_4 = l_Lake_Package_depsFacetConfig___closed__0;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1_spec__1(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_depsFacetConfig___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Package_depsFacetConfig___lam__0(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_1, 0);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
x_26 = lean_ctor_get(x_23, 0);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__1_spec__1___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0(lean_object* x_1, lean_object* x_2) {
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
x_11 = lean_ctor_get(x_2, 0);
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
x_26 = l_Std_DHashMap_Internal_AssocList_contains___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(x_2, x_25);
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
x_41 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(x_34);
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
x_53 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(x_46);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0(x_4, x_6);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static lean_object* _init_l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__5;
x_2 = l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__6;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__8_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_19; 
x_19 = lean_usize_dec_eq(x_4, x_5);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 4);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_array_uget(x_3, x_4);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_21, x_23);
lean_dec(x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_box(1);
x_27 = lean_unbox(x_26);
lean_inc(x_2);
x_28 = l_Lean_Name_toString(x_25, x_27, x_2);
x_29 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg___closed__0;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_unbox(x_26);
x_32 = l_Lean_Name_toString(x_23, x_31, x_2);
x_33 = lean_string_append(x_30, x_32);
lean_dec(x_32);
x_34 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg___closed__1;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_box(3);
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_35);
x_38 = lean_unbox(x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_38);
x_39 = lean_array_get_size(x_11);
x_40 = lean_array_push(x_11, x_37);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_12);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_23);
x_43 = !lean_is_exclusive(x_24);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_44 = lean_ctor_get(x_24, 0);
x_64 = lean_ctor_get(x_44, 0);
lean_inc(x_64);
x_65 = l_Lake_Package_transDepsFacet;
lean_ctor_set(x_24, 0, x_64);
x_66 = l_Lake_Package_keyword;
lean_inc(x_44);
x_67 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_67, 0, x_24);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_67, 2, x_44);
lean_ctor_set(x_67, 3, x_65);
lean_inc(x_7);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_68 = lean_apply_6(x_7, x_67, x_8, x_9, x_10, x_11, x_12);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = lean_ctor_get(x_70, 0);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_io_wait(x_73, x_71);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_ctor_get(x_75, 0);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_ctor_get(x_76, 0);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_unsigned_to_nat(0u);
x_81 = lean_array_get_size(x_79);
x_82 = lean_nat_dec_lt(x_80, x_81);
if (x_82 == 0)
{
lean_dec(x_81);
lean_dec(x_79);
x_53 = x_78;
x_54 = x_72;
x_55 = x_77;
goto block_63;
}
else
{
uint8_t x_83; 
x_83 = lean_nat_dec_le(x_81, x_81);
if (x_83 == 0)
{
lean_dec(x_81);
lean_dec(x_79);
x_53 = x_78;
x_54 = x_72;
x_55 = x_77;
goto block_63;
}
else
{
lean_object* x_84; size_t x_85; size_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_84 = lean_box(0);
x_85 = 0;
x_86 = lean_usize_of_nat(x_81);
lean_dec(x_81);
x_87 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__6(x_79, x_85, x_86, x_84, x_72, x_77);
lean_dec(x_79);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_53 = x_78;
x_54 = x_90;
x_55 = x_89;
goto block_63;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_44);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_91 = lean_ctor_get(x_75, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_74, 1);
lean_inc(x_92);
lean_dec(x_74);
x_93 = lean_ctor_get(x_75, 0);
lean_inc(x_93);
lean_dec(x_75);
x_94 = lean_ctor_get(x_91, 0);
lean_inc(x_94);
lean_dec(x_91);
x_95 = lean_unsigned_to_nat(0u);
x_96 = lean_array_get_size(x_94);
x_97 = lean_nat_dec_lt(x_95, x_96);
if (x_97 == 0)
{
lean_dec(x_96);
lean_dec(x_94);
x_13 = x_93;
x_14 = x_72;
x_15 = x_92;
goto block_18;
}
else
{
uint8_t x_98; 
x_98 = lean_nat_dec_le(x_96, x_96);
if (x_98 == 0)
{
lean_dec(x_96);
lean_dec(x_94);
x_13 = x_93;
x_14 = x_72;
x_15 = x_92;
goto block_18;
}
else
{
lean_object* x_99; size_t x_100; size_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_99 = lean_box(0);
x_100 = 0;
x_101 = lean_usize_of_nat(x_96);
lean_dec(x_96);
x_102 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__6(x_94, x_100, x_101, x_99, x_72, x_92);
lean_dec(x_94);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_13 = x_93;
x_14 = x_105;
x_15 = x_104;
goto block_18;
}
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_44);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_68);
if (x_106 == 0)
{
lean_object* x_107; uint8_t x_108; 
x_107 = lean_ctor_get(x_68, 0);
lean_dec(x_107);
x_108 = !lean_is_exclusive(x_69);
if (x_108 == 0)
{
return x_68;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_69, 0);
x_110 = lean_ctor_get(x_69, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_69);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
lean_ctor_set(x_68, 0, x_111);
return x_68;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_112 = lean_ctor_get(x_68, 1);
lean_inc(x_112);
lean_dec(x_68);
x_113 = lean_ctor_get(x_69, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_69, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_115 = x_69;
} else {
 lean_dec_ref(x_69);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_112);
return x_117;
}
}
block_52:
{
lean_object* x_48; size_t x_49; size_t x_50; 
x_48 = l_Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0(x_47, x_44);
x_49 = 1;
x_50 = lean_usize_add(x_4, x_49);
x_4 = x_50;
x_6 = x_48;
x_11 = x_45;
x_12 = x_46;
goto _start;
}
block_63:
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_array_get_size(x_53);
x_58 = lean_nat_dec_lt(x_56, x_57);
if (x_58 == 0)
{
lean_dec(x_57);
lean_dec(x_53);
x_45 = x_54;
x_46 = x_55;
x_47 = x_6;
goto block_52;
}
else
{
uint8_t x_59; 
x_59 = lean_nat_dec_le(x_57, x_57);
if (x_59 == 0)
{
lean_dec(x_57);
lean_dec(x_53);
x_45 = x_54;
x_46 = x_55;
x_47 = x_6;
goto block_52;
}
else
{
size_t x_60; size_t x_61; lean_object* x_62; 
x_60 = 0;
x_61 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_62 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__5(x_53, x_60, x_61, x_6);
lean_dec(x_53);
x_45 = x_54;
x_46 = x_55;
x_47 = x_62;
goto block_52;
}
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_118 = lean_ctor_get(x_24, 0);
lean_inc(x_118);
lean_dec(x_24);
x_138 = lean_ctor_get(x_118, 0);
lean_inc(x_138);
x_139 = l_Lake_Package_transDepsFacet;
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_138);
x_141 = l_Lake_Package_keyword;
lean_inc(x_118);
x_142 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set(x_142, 2, x_118);
lean_ctor_set(x_142, 3, x_139);
lean_inc(x_7);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_143 = lean_apply_6(x_7, x_142, x_8, x_9, x_10, x_11, x_12);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
lean_dec(x_143);
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_dec(x_144);
x_148 = lean_ctor_get(x_145, 0);
lean_inc(x_148);
lean_dec(x_145);
x_149 = lean_io_wait(x_148, x_146);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
lean_dec(x_149);
x_153 = lean_ctor_get(x_150, 0);
lean_inc(x_153);
lean_dec(x_150);
x_154 = lean_ctor_get(x_151, 0);
lean_inc(x_154);
lean_dec(x_151);
x_155 = lean_unsigned_to_nat(0u);
x_156 = lean_array_get_size(x_154);
x_157 = lean_nat_dec_lt(x_155, x_156);
if (x_157 == 0)
{
lean_dec(x_156);
lean_dec(x_154);
x_127 = x_153;
x_128 = x_147;
x_129 = x_152;
goto block_137;
}
else
{
uint8_t x_158; 
x_158 = lean_nat_dec_le(x_156, x_156);
if (x_158 == 0)
{
lean_dec(x_156);
lean_dec(x_154);
x_127 = x_153;
x_128 = x_147;
x_129 = x_152;
goto block_137;
}
else
{
lean_object* x_159; size_t x_160; size_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_159 = lean_box(0);
x_160 = 0;
x_161 = lean_usize_of_nat(x_156);
lean_dec(x_156);
x_162 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__6(x_154, x_160, x_161, x_159, x_147, x_152);
lean_dec(x_154);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_127 = x_153;
x_128 = x_165;
x_129 = x_164;
goto block_137;
}
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
lean_dec(x_118);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_166 = lean_ctor_get(x_150, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_149, 1);
lean_inc(x_167);
lean_dec(x_149);
x_168 = lean_ctor_get(x_150, 0);
lean_inc(x_168);
lean_dec(x_150);
x_169 = lean_ctor_get(x_166, 0);
lean_inc(x_169);
lean_dec(x_166);
x_170 = lean_unsigned_to_nat(0u);
x_171 = lean_array_get_size(x_169);
x_172 = lean_nat_dec_lt(x_170, x_171);
if (x_172 == 0)
{
lean_dec(x_171);
lean_dec(x_169);
x_13 = x_168;
x_14 = x_147;
x_15 = x_167;
goto block_18;
}
else
{
uint8_t x_173; 
x_173 = lean_nat_dec_le(x_171, x_171);
if (x_173 == 0)
{
lean_dec(x_171);
lean_dec(x_169);
x_13 = x_168;
x_14 = x_147;
x_15 = x_167;
goto block_18;
}
else
{
lean_object* x_174; size_t x_175; size_t x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_174 = lean_box(0);
x_175 = 0;
x_176 = lean_usize_of_nat(x_171);
lean_dec(x_171);
x_177 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__6(x_169, x_175, x_176, x_174, x_147, x_167);
lean_dec(x_169);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_13 = x_168;
x_14 = x_180;
x_15 = x_179;
goto block_18;
}
}
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_118);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_181 = lean_ctor_get(x_143, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_182 = x_143;
} else {
 lean_dec_ref(x_143);
 x_182 = lean_box(0);
}
x_183 = lean_ctor_get(x_144, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_144, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_185 = x_144;
} else {
 lean_dec_ref(x_144);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_184);
if (lean_is_scalar(x_182)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_182;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_181);
return x_187;
}
block_126:
{
lean_object* x_122; size_t x_123; size_t x_124; 
x_122 = l_Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0(x_121, x_118);
x_123 = 1;
x_124 = lean_usize_add(x_4, x_123);
x_4 = x_124;
x_6 = x_122;
x_11 = x_119;
x_12 = x_120;
goto _start;
}
block_137:
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_130 = lean_unsigned_to_nat(0u);
x_131 = lean_array_get_size(x_127);
x_132 = lean_nat_dec_lt(x_130, x_131);
if (x_132 == 0)
{
lean_dec(x_131);
lean_dec(x_127);
x_119 = x_128;
x_120 = x_129;
x_121 = x_6;
goto block_126;
}
else
{
uint8_t x_133; 
x_133 = lean_nat_dec_le(x_131, x_131);
if (x_133 == 0)
{
lean_dec(x_131);
lean_dec(x_127);
x_119 = x_128;
x_120 = x_129;
x_121 = x_6;
goto block_126;
}
else
{
size_t x_134; size_t x_135; lean_object* x_136; 
x_134 = 0;
x_135 = lean_usize_of_nat(x_131);
lean_dec(x_131);
x_136 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__5(x_127, x_134, x_135, x_6);
lean_dec(x_127);
x_119 = x_128;
x_120 = x_129;
x_121 = x_136;
goto block_126;
}
}
}
}
}
}
else
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_6);
lean_ctor_set(x_188, 1, x_11);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_12);
return x_189;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_19; 
x_19 = lean_usize_dec_eq(x_4, x_5);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 4);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_array_uget(x_3, x_4);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_21, x_23);
lean_dec(x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_box(1);
x_27 = lean_unbox(x_26);
lean_inc(x_2);
x_28 = l_Lean_Name_toString(x_25, x_27, x_2);
x_29 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg___closed__0;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_unbox(x_26);
x_32 = l_Lean_Name_toString(x_23, x_31, x_2);
x_33 = lean_string_append(x_30, x_32);
lean_dec(x_32);
x_34 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg___closed__1;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_box(3);
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_35);
x_38 = lean_unbox(x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_38);
x_39 = lean_array_get_size(x_11);
x_40 = lean_array_push(x_11, x_37);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_12);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_23);
x_43 = !lean_is_exclusive(x_24);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_44 = lean_ctor_get(x_24, 0);
x_64 = lean_ctor_get(x_44, 0);
lean_inc(x_64);
x_65 = l_Lake_Package_transDepsFacet;
lean_ctor_set(x_24, 0, x_64);
x_66 = l_Lake_Package_keyword;
lean_inc(x_44);
x_67 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_67, 0, x_24);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_67, 2, x_44);
lean_ctor_set(x_67, 3, x_65);
lean_inc(x_7);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_68 = lean_apply_6(x_7, x_67, x_8, x_9, x_10, x_11, x_12);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = lean_ctor_get(x_70, 0);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_io_wait(x_73, x_71);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_ctor_get(x_75, 0);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_ctor_get(x_76, 0);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_unsigned_to_nat(0u);
x_81 = lean_array_get_size(x_79);
x_82 = lean_nat_dec_lt(x_80, x_81);
if (x_82 == 0)
{
lean_dec(x_81);
lean_dec(x_79);
x_53 = x_78;
x_54 = x_72;
x_55 = x_77;
goto block_63;
}
else
{
uint8_t x_83; 
x_83 = lean_nat_dec_le(x_81, x_81);
if (x_83 == 0)
{
lean_dec(x_81);
lean_dec(x_79);
x_53 = x_78;
x_54 = x_72;
x_55 = x_77;
goto block_63;
}
else
{
lean_object* x_84; size_t x_85; size_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_84 = lean_box(0);
x_85 = 0;
x_86 = lean_usize_of_nat(x_81);
lean_dec(x_81);
x_87 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__6(x_79, x_85, x_86, x_84, x_72, x_77);
lean_dec(x_79);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_53 = x_78;
x_54 = x_90;
x_55 = x_89;
goto block_63;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_44);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_91 = lean_ctor_get(x_75, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_74, 1);
lean_inc(x_92);
lean_dec(x_74);
x_93 = lean_ctor_get(x_75, 0);
lean_inc(x_93);
lean_dec(x_75);
x_94 = lean_ctor_get(x_91, 0);
lean_inc(x_94);
lean_dec(x_91);
x_95 = lean_unsigned_to_nat(0u);
x_96 = lean_array_get_size(x_94);
x_97 = lean_nat_dec_lt(x_95, x_96);
if (x_97 == 0)
{
lean_dec(x_96);
lean_dec(x_94);
x_13 = x_93;
x_14 = x_72;
x_15 = x_92;
goto block_18;
}
else
{
uint8_t x_98; 
x_98 = lean_nat_dec_le(x_96, x_96);
if (x_98 == 0)
{
lean_dec(x_96);
lean_dec(x_94);
x_13 = x_93;
x_14 = x_72;
x_15 = x_92;
goto block_18;
}
else
{
lean_object* x_99; size_t x_100; size_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_99 = lean_box(0);
x_100 = 0;
x_101 = lean_usize_of_nat(x_96);
lean_dec(x_96);
x_102 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__6(x_94, x_100, x_101, x_99, x_72, x_92);
lean_dec(x_94);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_13 = x_93;
x_14 = x_105;
x_15 = x_104;
goto block_18;
}
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_44);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_68);
if (x_106 == 0)
{
lean_object* x_107; uint8_t x_108; 
x_107 = lean_ctor_get(x_68, 0);
lean_dec(x_107);
x_108 = !lean_is_exclusive(x_69);
if (x_108 == 0)
{
return x_68;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_69, 0);
x_110 = lean_ctor_get(x_69, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_69);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
lean_ctor_set(x_68, 0, x_111);
return x_68;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_112 = lean_ctor_get(x_68, 1);
lean_inc(x_112);
lean_dec(x_68);
x_113 = lean_ctor_get(x_69, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_69, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_115 = x_69;
} else {
 lean_dec_ref(x_69);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_112);
return x_117;
}
}
block_52:
{
lean_object* x_48; size_t x_49; size_t x_50; lean_object* x_51; 
x_48 = l_Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0(x_47, x_44);
x_49 = 1;
x_50 = lean_usize_add(x_4, x_49);
x_51 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__8_spec__8(x_1, x_2, x_3, x_50, x_5, x_48, x_7, x_8, x_9, x_10, x_46, x_45);
return x_51;
}
block_63:
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_array_get_size(x_53);
x_58 = lean_nat_dec_lt(x_56, x_57);
if (x_58 == 0)
{
lean_dec(x_57);
lean_dec(x_53);
x_45 = x_55;
x_46 = x_54;
x_47 = x_6;
goto block_52;
}
else
{
uint8_t x_59; 
x_59 = lean_nat_dec_le(x_57, x_57);
if (x_59 == 0)
{
lean_dec(x_57);
lean_dec(x_53);
x_45 = x_55;
x_46 = x_54;
x_47 = x_6;
goto block_52;
}
else
{
size_t x_60; size_t x_61; lean_object* x_62; 
x_60 = 0;
x_61 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_62 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__5(x_53, x_60, x_61, x_6);
lean_dec(x_53);
x_45 = x_55;
x_46 = x_54;
x_47 = x_62;
goto block_52;
}
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_118 = lean_ctor_get(x_24, 0);
lean_inc(x_118);
lean_dec(x_24);
x_138 = lean_ctor_get(x_118, 0);
lean_inc(x_138);
x_139 = l_Lake_Package_transDepsFacet;
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_138);
x_141 = l_Lake_Package_keyword;
lean_inc(x_118);
x_142 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set(x_142, 2, x_118);
lean_ctor_set(x_142, 3, x_139);
lean_inc(x_7);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_143 = lean_apply_6(x_7, x_142, x_8, x_9, x_10, x_11, x_12);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
lean_dec(x_143);
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_dec(x_144);
x_148 = lean_ctor_get(x_145, 0);
lean_inc(x_148);
lean_dec(x_145);
x_149 = lean_io_wait(x_148, x_146);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
lean_dec(x_149);
x_153 = lean_ctor_get(x_150, 0);
lean_inc(x_153);
lean_dec(x_150);
x_154 = lean_ctor_get(x_151, 0);
lean_inc(x_154);
lean_dec(x_151);
x_155 = lean_unsigned_to_nat(0u);
x_156 = lean_array_get_size(x_154);
x_157 = lean_nat_dec_lt(x_155, x_156);
if (x_157 == 0)
{
lean_dec(x_156);
lean_dec(x_154);
x_127 = x_153;
x_128 = x_147;
x_129 = x_152;
goto block_137;
}
else
{
uint8_t x_158; 
x_158 = lean_nat_dec_le(x_156, x_156);
if (x_158 == 0)
{
lean_dec(x_156);
lean_dec(x_154);
x_127 = x_153;
x_128 = x_147;
x_129 = x_152;
goto block_137;
}
else
{
lean_object* x_159; size_t x_160; size_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_159 = lean_box(0);
x_160 = 0;
x_161 = lean_usize_of_nat(x_156);
lean_dec(x_156);
x_162 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__6(x_154, x_160, x_161, x_159, x_147, x_152);
lean_dec(x_154);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_127 = x_153;
x_128 = x_165;
x_129 = x_164;
goto block_137;
}
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
lean_dec(x_118);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_166 = lean_ctor_get(x_150, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_149, 1);
lean_inc(x_167);
lean_dec(x_149);
x_168 = lean_ctor_get(x_150, 0);
lean_inc(x_168);
lean_dec(x_150);
x_169 = lean_ctor_get(x_166, 0);
lean_inc(x_169);
lean_dec(x_166);
x_170 = lean_unsigned_to_nat(0u);
x_171 = lean_array_get_size(x_169);
x_172 = lean_nat_dec_lt(x_170, x_171);
if (x_172 == 0)
{
lean_dec(x_171);
lean_dec(x_169);
x_13 = x_168;
x_14 = x_147;
x_15 = x_167;
goto block_18;
}
else
{
uint8_t x_173; 
x_173 = lean_nat_dec_le(x_171, x_171);
if (x_173 == 0)
{
lean_dec(x_171);
lean_dec(x_169);
x_13 = x_168;
x_14 = x_147;
x_15 = x_167;
goto block_18;
}
else
{
lean_object* x_174; size_t x_175; size_t x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_174 = lean_box(0);
x_175 = 0;
x_176 = lean_usize_of_nat(x_171);
lean_dec(x_171);
x_177 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__6(x_169, x_175, x_176, x_174, x_147, x_167);
lean_dec(x_169);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_13 = x_168;
x_14 = x_180;
x_15 = x_179;
goto block_18;
}
}
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_118);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_181 = lean_ctor_get(x_143, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_182 = x_143;
} else {
 lean_dec_ref(x_143);
 x_182 = lean_box(0);
}
x_183 = lean_ctor_get(x_144, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_144, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_185 = x_144;
} else {
 lean_dec_ref(x_144);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_184);
if (lean_is_scalar(x_182)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_182;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_181);
return x_187;
}
block_126:
{
lean_object* x_122; size_t x_123; size_t x_124; lean_object* x_125; 
x_122 = l_Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0(x_121, x_118);
x_123 = 1;
x_124 = lean_usize_add(x_4, x_123);
x_125 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__8_spec__8(x_1, x_2, x_3, x_124, x_5, x_122, x_7, x_8, x_9, x_10, x_120, x_119);
return x_125;
}
block_137:
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_130 = lean_unsigned_to_nat(0u);
x_131 = lean_array_get_size(x_127);
x_132 = lean_nat_dec_lt(x_130, x_131);
if (x_132 == 0)
{
lean_dec(x_131);
lean_dec(x_127);
x_119 = x_129;
x_120 = x_128;
x_121 = x_6;
goto block_126;
}
else
{
uint8_t x_133; 
x_133 = lean_nat_dec_le(x_131, x_131);
if (x_133 == 0)
{
lean_dec(x_131);
lean_dec(x_127);
x_119 = x_129;
x_120 = x_128;
x_121 = x_6;
goto block_126;
}
else
{
size_t x_134; size_t x_135; lean_object* x_136; 
x_134 = 0;
x_135 = lean_usize_of_nat(x_131);
lean_dec(x_131);
x_136 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__5(x_127, x_134, x_135, x_6);
lean_dec(x_127);
x_119 = x_129;
x_120 = x_128;
x_121 = x_136;
goto block_126;
}
}
}
}
}
}
else
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_6);
lean_ctor_set(x_188, 1, x_11);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_12);
return x_189;
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
LEAN_EXPORT lean_object* l_Lake_Package_recComputeTransDeps___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_48; 
x_48 = lean_nat_dec_lt(x_1, x_2);
if (x_48 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_13 = x_3;
x_14 = x_11;
x_15 = x_12;
goto block_47;
}
else
{
uint8_t x_49; 
x_49 = lean_nat_dec_le(x_2, x_2);
if (x_49 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_13 = x_3;
x_14 = x_11;
x_15 = x_12;
goto block_47;
}
else
{
size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; 
x_50 = 0;
x_51 = lean_usize_of_nat(x_2);
x_52 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__8(x_4, x_5, x_6, x_50, x_51, x_3, x_7, x_8, x_9, x_10, x_11, x_12);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_13 = x_55;
x_14 = x_56;
x_15 = x_54;
goto block_47;
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_52, 0);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_53);
if (x_59 == 0)
{
return x_52;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_53, 0);
x_61 = lean_ctor_get(x_53, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_53);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_52, 0, x_62);
return x_52;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_52, 1);
lean_inc(x_63);
lean_dec(x_52);
x_64 = lean_ctor_get(x_53, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_53, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_66 = x_53;
} else {
 lean_dec_ref(x_53);
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
}
block_47:
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
x_19 = lean_box(0);
x_20 = lean_mk_empty_array_with_capacity(x_1);
x_21 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__0;
x_22 = lean_box(0);
x_23 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__2;
x_24 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_unbox(x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_25);
lean_ctor_set(x_13, 1, x_24);
lean_ctor_set(x_13, 0, x_17);
x_26 = lean_task_pure(x_13);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_19);
lean_ctor_set(x_28, 2, x_21);
x_29 = lean_unbox(x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_29);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_14);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_15);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_32 = lean_ctor_get(x_13, 1);
lean_inc(x_32);
lean_dec(x_13);
x_33 = lean_box(0);
x_34 = lean_mk_empty_array_with_capacity(x_1);
x_35 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__0;
x_36 = lean_box(0);
x_37 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__2;
x_38 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_unbox(x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_39);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_32);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_task_pure(x_40);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_33);
lean_ctor_set(x_43, 2, x_35);
x_44 = lean_unbox(x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*3, x_44);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_14);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_15);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recComputeTransDeps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 9);
lean_inc(x_8);
x_9 = l_Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1___closed__0;
x_10 = l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7;
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get_size(x_8);
x_13 = lean_alloc_closure((void*)(l_Lake_Package_recComputeTransDeps___lam__1___boxed), 12, 6);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_10);
lean_closure_set(x_13, 3, x_1);
lean_closure_set(x_13, 4, x_9);
lean_closure_set(x_13, 5, x_8);
x_14 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2(x_13, x_2, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__5(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__6(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__8_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__8_spec__8(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__8(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recComputeTransDeps___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_Package_recComputeTransDeps___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
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
x_1 = lean_alloc_closure((void*)(l_Lake_Package_recComputeTransDeps), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_transDepsFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_1 = lean_box(1);
x_2 = l_Lake_Package_transDepsFacetConfig___closed__0;
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = l_Lake_Package_transDepsFacetConfig___closed__1;
x_6 = l_Lake_Package_keyword;
x_7 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_2);
x_8 = lean_unbox(x_3);
lean_ctor_set_uint8(x_7, sizeof(void*)*4, x_8);
x_9 = lean_unbox(x_1);
lean_ctor_set_uint8(x_7, sizeof(void*)*4 + 1, x_9);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*25 + 2);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = l_Lake_Package_optReservoirBarrelFacet;
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_10);
x_13 = l_Lake_Package_keyword;
x_14 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_1);
lean_ctor_set(x_14, 3, x_11);
x_15 = lean_apply_6(x_2, x_14, x_3, x_4, x_5, x_6, x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = l_Lake_Package_optGitHubReleaseFacet;
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_16);
x_19 = l_Lake_Package_keyword;
x_20 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_1);
lean_ctor_set(x_20, 3, x_17);
x_21 = lean_apply_6(x_2, x_20, x_3, x_4, x_5, x_6, x_7);
return x_21;
}
}
}
static lean_object* _init_l_Lake_stdFormat___at___Lake_Package_optBuildCacheFacetConfig_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_stdFormat___at___Lake_Package_optBuildCacheFacetConfig_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_Package_optBuildCacheFacetConfig_spec__0(uint8_t x_1, uint8_t x_2) {
_start:
{
if (x_1 == 0)
{
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at___Lake_Package_optBuildCacheFacetConfig_spec__0___closed__0;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = l_Lake_stdFormat___at___Lake_Package_optBuildCacheFacetConfig_spec__0___closed__1;
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
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig___lam__1(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at___Lake_Package_optBuildCacheFacetConfig_spec__0(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_optBuildCacheFacetConfig___lam__0), 7, 0);
x_2 = lean_alloc_closure((void*)(l_Lake_Package_optBuildCacheFacetConfig___lam__1___boxed), 2, 0);
x_3 = l_Lake_instDataKindBool;
x_4 = l_Lake_Package_keyword;
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
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_Package_optBuildCacheFacetConfig_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_stdFormat___at___Lake_Package_optBuildCacheFacetConfig_spec__0(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_Package_optBuildCacheFacetConfig___lam__1(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_Package_maybeFetchBuildCache___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_recFetchDeps___lam__1___closed__1;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_maybeFetchBuildCache___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_maybeFetchBuildCache___closed__0;
x_2 = lean_task_pure(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_maybeFetchBuildCache___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("leanprover", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_maybeFetchBuildCache___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("leanprover-community", 20, 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; uint8_t x_32; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; uint8_t x_65; 
x_37 = lean_ctor_get(x_5, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_65 = lean_ctor_get_uint8(x_38, sizeof(void*)*11);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_box(1);
x_67 = lean_unbox(x_66);
x_39 = x_67;
x_40 = x_6;
x_41 = x_7;
goto block_64;
}
else
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_box(0);
x_69 = lean_unbox(x_68);
x_39 = x_69;
x_40 = x_6;
x_41 = x_7;
goto block_64;
}
block_17:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_box(0);
x_12 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__0;
x_13 = l_Lake_Package_maybeFetchBuildCache___closed__1;
x_14 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_8);
return x_16;
}
block_26:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = l_Lake_Package_optBuildCacheFacet;
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_18);
x_23 = l_Lake_Package_keyword;
x_24 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_1);
lean_ctor_set(x_24, 3, x_21);
x_25 = lean_apply_6(x_2, x_24, x_3, x_4, x_5, x_20, x_19);
return x_25;
}
block_36:
{
if (x_32 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = x_29;
x_9 = x_31;
x_10 = x_32;
goto block_17;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_string_utf8_byte_size(x_28);
lean_dec(x_28);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_eq(x_33, x_34);
lean_dec(x_33);
if (x_35 == 0)
{
x_18 = x_27;
x_19 = x_29;
x_20 = x_31;
goto block_26;
}
else
{
if (x_30 == 0)
{
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = x_29;
x_9 = x_31;
x_10 = x_30;
goto block_17;
}
else
{
x_18 = x_27;
x_19 = x_29;
x_20 = x_31;
goto block_26;
}
}
}
}
block_64:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_1, 3);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 7);
lean_inc(x_45);
x_46 = lean_ctor_get(x_42, 6);
lean_inc(x_46);
x_47 = lean_ctor_get_uint8(x_42, sizeof(void*)*25 + 2);
lean_dec(x_42);
x_48 = l_System_FilePath_normalize(x_46);
x_49 = l_Lake_joinRelative(x_44, x_48);
lean_dec(x_48);
x_50 = l_System_FilePath_pathExists(x_49, x_41);
lean_dec(x_49);
if (x_39 == 0)
{
lean_object* x_51; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_38);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_8 = x_51;
x_9 = x_40;
x_10 = x_39;
goto block_17;
}
else
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
if (x_47 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = l_Lake_Env_toolchain(x_38);
lean_dec(x_38);
x_56 = l_Lake_Package_maybeFetchBuildCache___closed__2;
x_57 = lean_string_dec_eq(x_45, x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = l_Lake_Package_maybeFetchBuildCache___closed__3;
x_59 = lean_string_dec_eq(x_45, x_58);
lean_dec(x_45);
x_27 = x_43;
x_28 = x_55;
x_29 = x_54;
x_30 = x_47;
x_31 = x_40;
x_32 = x_59;
goto block_36;
}
else
{
lean_dec(x_45);
x_27 = x_43;
x_28 = x_55;
x_29 = x_54;
x_30 = x_47;
x_31 = x_40;
x_32 = x_57;
goto block_36;
}
}
else
{
lean_object* x_60; 
lean_dec(x_45);
lean_dec(x_38);
x_60 = lean_ctor_get(x_50, 1);
lean_inc(x_60);
lean_dec(x_50);
x_18 = x_43;
x_19 = x_60;
x_20 = x_40;
goto block_26;
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_38);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = lean_ctor_get(x_50, 1);
lean_inc(x_61);
lean_dec(x_50);
x_62 = lean_box(0);
x_63 = lean_unbox(x_62);
x_8 = x_61;
x_9 = x_40;
x_10 = x_63;
goto block_17;
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
lean_object* x_6; uint8_t x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 3);
x_8 = lean_box(2);
x_9 = lean_unbox(x_8);
x_10 = l_Lake_instDecidableEqVerbosity(x_7, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1___closed__0;
x_16 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1;
x_17 = l_Lean_Name_toString(x_14, x_10, x_15);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Lake_Name_eraseHead(x_2);
x_22 = l_Lean_Name_toString(x_21, x_10, x_15);
x_23 = lean_string_append(x_20, x_22);
lean_dec(x_22);
x_24 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_4);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_5);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get_uint8(x_9, sizeof(void*)*1 + 3);
x_11 = lean_box(2);
x_12 = lean_unbox(x_11);
x_13 = l_Lake_instDecidableEqVerbosity(x_10, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_8);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1___closed__0;
x_19 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1;
x_20 = l_Lean_Name_toString(x_17, x_13, x_18);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Lake_Name_eraseHead(x_2);
x_25 = l_Lean_Name_toString(x_24, x_13, x_18);
x_26 = lean_string_append(x_23, x_25);
lean_dec(x_25);
x_27 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_7);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_8);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Lake_BuildTrace_mix(x_1, x_12);
x_14 = lean_apply_1(x_2, x_10);
lean_ctor_set(x_9, 1, x_13);
x_15 = lean_box(1);
x_16 = lean_unbox(x_15);
x_17 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_14, x_16, x_3, x_4, x_5, x_6, x_9, x_8);
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_35 = lean_ctor_get(x_22, 0);
x_36 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__3;
x_37 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_24, x_31, x_32);
x_38 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_24, x_37, x_31);
x_39 = lean_string_utf8_extract(x_24, x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_24);
x_40 = lean_string_append(x_36, x_39);
lean_dec(x_39);
x_41 = lean_box(1);
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_40);
x_43 = lean_unbox(x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_43);
x_44 = lean_array_push(x_35, x_42);
lean_ctor_set(x_22, 0, x_44);
x_26 = x_22;
x_27 = x_20;
goto block_30;
}
else
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_45 = lean_ctor_get(x_22, 0);
x_46 = lean_ctor_get_uint8(x_22, sizeof(void*)*2);
x_47 = lean_ctor_get(x_22, 1);
lean_inc(x_47);
lean_inc(x_45);
lean_dec(x_22);
x_48 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__3;
x_49 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_24, x_31, x_32);
x_50 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_24, x_49, x_31);
x_51 = lean_string_utf8_extract(x_24, x_49, x_50);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_24);
x_52 = lean_string_append(x_48, x_51);
lean_dec(x_51);
x_53 = lean_box(1);
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_52);
x_55 = lean_unbox(x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_55);
x_56 = lean_array_push(x_45, x_54);
x_57 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_47);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_46);
x_26 = x_57;
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
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_17);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_17, 0);
lean_dec(x_59);
x_60 = !lean_is_exclusive(x_18);
if (x_60 == 0)
{
return x_17;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_18, 0);
x_62 = lean_ctor_get(x_18, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_18);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_17, 0, x_63);
return x_17;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_17, 1);
lean_inc(x_64);
lean_dec(x_17);
x_65 = lean_ctor_get(x_18, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_18, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_67 = x_18;
} else {
 lean_dec_ref(x_18);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_64);
return x_69;
}
}
}
else
{
lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; 
x_70 = lean_ctor_get(x_9, 0);
x_71 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_72 = lean_ctor_get(x_9, 1);
lean_inc(x_72);
lean_inc(x_70);
lean_dec(x_9);
x_73 = l_Lake_BuildTrace_mix(x_1, x_72);
x_74 = lean_apply_1(x_2, x_10);
x_75 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_73);
lean_ctor_set_uint8(x_75, sizeof(void*)*2, x_71);
x_76 = lean_box(1);
x_77 = lean_unbox(x_76);
x_78 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_74, x_77, x_3, x_4, x_5, x_6, x_75, x_8);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
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
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_84 = x_79;
} else {
 lean_dec_ref(x_79);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_80, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_80, 1);
lean_inc(x_86);
lean_dec(x_80);
x_92 = lean_string_utf8_byte_size(x_85);
x_93 = lean_unsigned_to_nat(0u);
x_94 = lean_nat_dec_eq(x_92, x_93);
if (x_94 == 0)
{
lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; 
x_95 = lean_ctor_get(x_83, 0);
lean_inc(x_95);
x_96 = lean_ctor_get_uint8(x_83, sizeof(void*)*2);
x_97 = lean_ctor_get(x_83, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_98 = x_83;
} else {
 lean_dec_ref(x_83);
 x_98 = lean_box(0);
}
x_99 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__3;
x_100 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_85, x_92, x_93);
x_101 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_85, x_100, x_92);
x_102 = lean_string_utf8_extract(x_85, x_100, x_101);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_85);
x_103 = lean_string_append(x_99, x_102);
lean_dec(x_102);
x_104 = lean_box(1);
x_105 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_105, 0, x_103);
x_106 = lean_unbox(x_104);
lean_ctor_set_uint8(x_105, sizeof(void*)*1, x_106);
x_107 = lean_array_push(x_95, x_105);
if (lean_is_scalar(x_98)) {
 x_108 = lean_alloc_ctor(0, 2, 1);
} else {
 x_108 = x_98;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_97);
lean_ctor_set_uint8(x_108, sizeof(void*)*2, x_96);
x_87 = x_108;
x_88 = x_81;
goto block_91;
}
else
{
lean_dec(x_92);
lean_dec(x_85);
x_87 = x_83;
x_88 = x_81;
goto block_91;
}
block_91:
{
lean_object* x_89; lean_object* x_90; 
if (lean_is_scalar(x_84)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_84;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
if (lean_is_scalar(x_82)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_82;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_109 = lean_ctor_get(x_78, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_110 = x_78;
} else {
 lean_dec_ref(x_78);
 x_110 = lean_box(0);
}
x_111 = lean_ctor_get(x_79, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_79, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_113 = x_79;
} else {
 lean_dec_ref(x_79);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
if (lean_is_scalar(x_110)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_110;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_109);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_7);
if (x_116 == 0)
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_7);
lean_ctor_set(x_117, 1, x_8);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_7, 0);
x_119 = lean_ctor_get(x_7, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_7);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_8);
return x_121;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_dec(x_13);
x_14 = lean_alloc_closure((void*)(l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg___lam__0), 8, 6);
lean_closure_set(x_14, 0, x_9);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_5);
lean_closure_set(x_14, 3, x_6);
lean_closure_set(x_14, 4, x_7);
lean_closure_set(x_14, 5, x_8);
x_15 = lean_io_map_task(x_14, x_12, x_3, x_4, x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l_Lake_instDataKindUnit;
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_17);
lean_ctor_set(x_15, 0, x_1);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = l_Lake_instDataKindUnit;
lean_ctor_set(x_1, 1, x_21);
lean_ctor_set(x_1, 0, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 2);
x_25 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
x_26 = lean_alloc_closure((void*)(l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg___lam__0), 8, 6);
lean_closure_set(x_26, 0, x_9);
lean_closure_set(x_26, 1, x_2);
lean_closure_set(x_26, 2, x_5);
lean_closure_set(x_26, 3, x_6);
lean_closure_set(x_26, 4, x_7);
lean_closure_set(x_26, 5, x_8);
x_27 = lean_io_map_task(x_26, x_23, x_3, x_4, x_10);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = l_Lake_instDataKindUnit;
x_32 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_24);
lean_ctor_set_uint8(x_32, sizeof(void*)*3, x_25);
if (lean_is_scalar(x_30)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_30;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
static lean_object* _init_l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("building from source; failed to fetch Reservoir build", 53, 53);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("building from source; failed to fetch GitHub release", 52, 52);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_optReservoirBarrelFacet;
x_2 = l_Lake_Name_eraseHead(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_optGitHubReleaseFacet;
x_2 = l_Lake_Name_eraseHead(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
if (x_2 == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_1, 3);
lean_inc(x_65);
x_66 = lean_ctor_get_uint8(x_65, sizeof(void*)*25 + 2);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; 
x_67 = lean_ctor_get(x_6, 0);
x_68 = lean_ctor_get(x_1, 0);
lean_inc(x_68);
lean_dec(x_1);
x_69 = lean_ctor_get_uint8(x_67, sizeof(void*)*1 + 3);
x_70 = lean_box(2);
x_71 = lean_unbox(x_70);
x_72 = l_Lake_instDecidableEqVerbosity(x_69, x_71);
if (x_72 == 0)
{
lean_object* x_73; 
lean_dec(x_68);
x_73 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0;
x_9 = x_73;
x_10 = x_7;
x_11 = x_8;
goto block_36;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_74 = lean_box(x_66);
x_75 = lean_alloc_closure((void*)(l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed), 2, 1);
lean_closure_set(x_75, 0, x_74);
x_76 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1;
lean_inc(x_75);
x_77 = l_Lean_Name_toString(x_68, x_72, x_75);
x_78 = lean_string_append(x_76, x_77);
lean_dec(x_77);
x_79 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_80 = lean_string_append(x_78, x_79);
x_81 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___closed__2;
x_82 = l_Lean_Name_toString(x_81, x_72, x_75);
x_83 = lean_string_append(x_80, x_82);
lean_dec(x_82);
x_84 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3;
x_85 = lean_string_append(x_83, x_84);
x_9 = x_85;
x_10 = x_7;
x_11 = x_8;
goto block_36;
}
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; uint8_t x_90; uint8_t x_91; 
x_86 = lean_ctor_get(x_6, 0);
x_87 = lean_ctor_get(x_1, 0);
lean_inc(x_87);
lean_dec(x_1);
x_88 = lean_ctor_get_uint8(x_86, sizeof(void*)*1 + 3);
x_89 = lean_box(2);
x_90 = lean_unbox(x_89);
x_91 = l_Lake_instDecidableEqVerbosity(x_88, x_90);
if (x_91 == 0)
{
lean_object* x_92; 
lean_dec(x_87);
x_92 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0;
x_37 = x_92;
x_38 = x_7;
x_39 = x_8;
goto block_64;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_93 = lean_box(x_2);
x_94 = lean_alloc_closure((void*)(l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__1___boxed), 2, 1);
lean_closure_set(x_94, 0, x_93);
x_95 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1;
lean_inc(x_94);
x_96 = l_Lean_Name_toString(x_87, x_91, x_94);
x_97 = lean_string_append(x_95, x_96);
lean_dec(x_96);
x_98 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_99 = lean_string_append(x_97, x_98);
x_100 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___closed__3;
x_101 = l_Lean_Name_toString(x_100, x_91, x_94);
x_102 = lean_string_append(x_99, x_101);
lean_dec(x_101);
x_103 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3;
x_104 = lean_string_append(x_102, x_103);
x_37 = x_104;
x_38 = x_7;
x_39 = x_8;
goto block_64;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_1);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_7);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_8);
return x_107;
}
block_36:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___closed__0;
x_15 = lean_string_append(x_14, x_9);
lean_dec(x_9);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_unbox(x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_18);
x_19 = lean_box(0);
x_20 = lean_array_push(x_13, x_17);
lean_ctor_set(x_10, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_10);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_11);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get_uint8(x_10, sizeof(void*)*2);
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_inc(x_23);
lean_dec(x_10);
x_26 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___closed__0;
x_27 = lean_string_append(x_26, x_9);
lean_dec(x_9);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
x_30 = lean_unbox(x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_30);
x_31 = lean_box(0);
x_32 = lean_array_push(x_23, x_29);
x_33 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_25);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_24);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_11);
return x_35;
}
}
block_64:
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_38, 0);
x_42 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___closed__1;
x_43 = lean_string_append(x_42, x_37);
lean_dec(x_37);
x_44 = lean_box(2);
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_43);
x_46 = lean_unbox(x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_46);
x_47 = lean_box(0);
x_48 = lean_array_push(x_41, x_45);
lean_ctor_set(x_38, 0, x_48);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_38);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_39);
return x_50;
}
else
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_51 = lean_ctor_get(x_38, 0);
x_52 = lean_ctor_get_uint8(x_38, sizeof(void*)*2);
x_53 = lean_ctor_get(x_38, 1);
lean_inc(x_53);
lean_inc(x_51);
lean_dec(x_38);
x_54 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___closed__1;
x_55 = lean_string_append(x_54, x_37);
lean_dec(x_37);
x_56 = lean_box(2);
x_57 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_57, 0, x_55);
x_58 = lean_unbox(x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_58);
x_59 = lean_box(0);
x_60 = lean_array_push(x_51, x_57);
x_61 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_53);
lean_ctor_set_uint8(x_61, sizeof(void*)*2, x_52);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_39);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Lake_Package_maybeFetchBuildCache(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_alloc_closure((void*)(l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___boxed), 8, 1);
lean_closure_set(x_13, 0, x_1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_box(0);
x_16 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__2;
x_17 = lean_unbox(x_15);
x_18 = l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg(x_12, x_13, x_14, x_17, x_2, x_3, x_4, x_5, x_16, x_10);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_ctor_set(x_9, 0, x_20);
lean_ctor_set(x_18, 0, x_9);
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
lean_ctor_set(x_9, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_9, 0);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_9);
x_26 = lean_alloc_closure((void*)(l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___boxed), 8, 1);
lean_closure_set(x_26, 0, x_1);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_box(0);
x_29 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__2;
x_30 = lean_unbox(x_28);
x_31 = l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg(x_24, x_26, x_27, x_30, x_2, x_3, x_4, x_5, x_29, x_10);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_25);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_8);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_8, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_9);
if (x_39 == 0)
{
return x_8;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_9, 0);
x_41 = lean_ctor_get(x_9, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_9);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_8, 0, x_42);
return x_8;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_8, 1);
lean_inc(x_43);
lean_dec(x_8);
x_44 = lean_ctor_get(x_9, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_9, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_46 = x_9;
} else {
 lean_dec_ref(x_9);
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
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Package_recBuildExtraDepTargets_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_JobResult_prependLog___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
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
x_103 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__3;
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
x_113 = l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1___lam__1(x_99, x_111, x_2, x_3, x_4, x_5, x_112, x_12);
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
x_115 = l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1___lam__1(x_99, x_114, x_2, x_3, x_4, x_5, x_97, x_12);
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
x_21 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__0;
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_box(0);
x_24 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__2;
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
x_51 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1___lam__0), 2, 1);
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
x_60 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1___lam__0), 2, 1);
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
x_71 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1___lam__0), 2, 1);
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
x_88 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1___lam__0), 2, 1);
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
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_name_eq(x_3, x_25);
lean_dec(x_25);
x_27 = l_instDecidableNot___redArg(x_26);
if (x_27 == 0)
{
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_9;
x_17 = x_10;
goto block_22;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_28 = l_Lake_Package_maybeFetchBuildCacheWithWarning(x_2, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_33 = l_Lake_Job_add___redArg(x_4, x_31);
x_11 = x_33;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_32;
x_17 = x_30;
goto block_22;
}
else
{
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_28;
}
}
block_22:
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_1, 3);
x_19 = lean_array_size(x_18);
x_20 = 0;
x_21 = l_Array_forIn_x27Unsafe_loop___at___Lake_Package_recBuildExtraDepTargets_spec__0(x_2, x_18, x_19, x_20, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_21;
}
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":extraDep", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
x_10 = l_Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1___closed__0;
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
lean_inc(x_8);
x_13 = l_Lean_Name_toString(x_8, x_12, x_10);
x_14 = l_Lake_Package_recBuildExtraDepTargets___closed__0;
x_15 = l_Lake_Package_recBuildExtraDepTargets___closed__1;
x_16 = lean_string_append(x_15, x_13);
x_17 = lean_string_append(x_16, x_14);
x_18 = lean_box(0);
x_19 = lean_box(0);
x_20 = l_Lake_Package_recFetchDeps___lam__1___closed__0;
x_21 = lean_box(0);
x_22 = l_Lake_BuildTrace_nil(x_17);
x_23 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_unbox(x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_task_pure(x_25);
x_27 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__0;
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_19);
lean_ctor_set(x_29, 2, x_27);
x_30 = lean_unbox(x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*3, x_30);
x_31 = lean_alloc_closure((void*)(l_Lake_Package_recBuildExtraDepTargets___lam__1___boxed), 10, 4);
lean_closure_set(x_31, 0, x_9);
lean_closure_set(x_31, 1, x_1);
lean_closure_set(x_31, 2, x_8);
lean_closure_set(x_31, 3, x_29);
lean_inc(x_5);
x_32 = l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1(x_31, x_2, x_3, x_4, x_5, x_6, x_7);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_33, 0);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_39 = lean_ctor_get(x_34, 2);
lean_dec(x_39);
x_40 = lean_ctor_get(x_5, 3);
lean_inc(x_40);
lean_dec(x_5);
x_41 = lean_st_ref_take(x_40, x_35);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_string_append(x_13, x_14);
lean_ctor_set(x_34, 2, x_44);
x_45 = lean_unbox(x_28);
lean_ctor_set_uint8(x_34, sizeof(void*)*3, x_45);
lean_inc(x_34);
x_46 = l_Lake_Job_toOpaque___redArg(x_34);
x_47 = lean_array_push(x_42, x_46);
x_48 = lean_st_ref_set(x_40, x_47, x_43);
lean_dec(x_40);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
x_51 = l_Lake_Job_renew___redArg(x_34);
lean_ctor_set(x_33, 0, x_51);
lean_ctor_set(x_48, 0, x_33);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = l_Lake_Job_renew___redArg(x_34);
lean_ctor_set(x_33, 0, x_53);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_33);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_55 = lean_ctor_get(x_34, 0);
x_56 = lean_ctor_get(x_34, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_34);
x_57 = lean_ctor_get(x_5, 3);
lean_inc(x_57);
lean_dec(x_5);
x_58 = lean_st_ref_take(x_57, x_35);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_string_append(x_13, x_14);
x_62 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_62, 0, x_55);
lean_ctor_set(x_62, 1, x_56);
lean_ctor_set(x_62, 2, x_61);
x_63 = lean_unbox(x_28);
lean_ctor_set_uint8(x_62, sizeof(void*)*3, x_63);
lean_inc(x_62);
x_64 = l_Lake_Job_toOpaque___redArg(x_62);
x_65 = lean_array_push(x_59, x_64);
x_66 = lean_st_ref_set(x_57, x_65, x_60);
lean_dec(x_57);
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
lean_ctor_set(x_33, 0, x_69);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_33);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_71 = lean_ctor_get(x_33, 1);
lean_inc(x_71);
lean_dec(x_33);
x_72 = lean_ctor_get(x_34, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_34, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 x_74 = x_34;
} else {
 lean_dec_ref(x_34);
 x_74 = lean_box(0);
}
x_75 = lean_ctor_get(x_5, 3);
lean_inc(x_75);
lean_dec(x_5);
x_76 = lean_st_ref_take(x_75, x_35);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_string_append(x_13, x_14);
if (lean_is_scalar(x_74)) {
 x_80 = lean_alloc_ctor(0, 3, 1);
} else {
 x_80 = x_74;
}
lean_ctor_set(x_80, 0, x_72);
lean_ctor_set(x_80, 1, x_73);
lean_ctor_set(x_80, 2, x_79);
x_81 = lean_unbox(x_28);
lean_ctor_set_uint8(x_80, sizeof(void*)*3, x_81);
lean_inc(x_80);
x_82 = l_Lake_Job_toOpaque___redArg(x_80);
x_83 = lean_array_push(x_77, x_82);
x_84 = lean_st_ref_set(x_75, x_83, x_78);
lean_dec(x_75);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
x_87 = l_Lake_Job_renew___redArg(x_80);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_71);
if (lean_is_scalar(x_86)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_86;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_85);
return x_89;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Package_recBuildExtraDepTargets_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lake_Package_recBuildExtraDepTargets_spec__0(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_Package_recBuildExtraDepTargets___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_recBuildExtraDepTargets), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_nullFormat___boxed), 3, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_1 = l_Lake_Package_extraDepFacetConfig___closed__1;
x_2 = lean_box(1);
x_3 = l_Lake_instDataKindUnit;
x_4 = l_Lake_Package_extraDepFacetConfig___closed__0;
x_5 = l_Lake_Package_keyword;
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
static lean_object* _init_l_Lake_Package_extraDepFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_extraDepFacetConfig___closed__2;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_getBarrelUrl___redArg___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HEAD", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rev-parse", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--verify", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--end-of-options", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_getBarrelUrl___redArg___closed__1;
x_2 = l_Lake_Package_getBarrelUrl___redArg___closed__4;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_getBarrelUrl___redArg___closed__2;
x_2 = l_Lake_Package_getBarrelUrl___redArg___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_getBarrelUrl___redArg___closed__3;
x_2 = l_Lake_Package_getBarrelUrl___redArg___closed__6;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_getBarrelUrl___redArg___closed__0;
x_2 = l_Lake_Package_getBarrelUrl___redArg___closed__7;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(0, 0, 3);
x_3 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 0, x_3);
x_4 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 1, x_4);
x_5 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 2, x_5);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___redArg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("git", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___redArg___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to resolve HEAD revision", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = l_Lake_Package_getBarrelUrl___redArg___closed__12;
x_2 = lean_box(3);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___redArg___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/barrel\?rev=", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___redArg___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("&toolchain=", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___redArg___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean toolchain not known; Reservoir only hosts builds for known toolchains", 74, 74);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___redArg___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = l_Lake_Package_getBarrelUrl___redArg___closed__16;
x_2 = lean_box(3);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___redArg___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("package has no Reservoir scope", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___redArg___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = l_Lake_Package_getBarrelUrl___redArg___closed__18;
x_2 = lean_box(3);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 7);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_string_utf8_byte_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_11 = l_Lake_Package_getBarrelUrl___redArg___closed__8;
x_12 = l_Lake_Package_getBarrelUrl___redArg___closed__9;
x_13 = l_Lake_Package_getBarrelUrl___redArg___closed__10;
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_6);
x_15 = l_Lake_Package_getBarrelUrl___redArg___closed__11;
x_16 = lean_box(1);
x_17 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_11);
lean_ctor_set(x_17, 3, x_14);
lean_ctor_set(x_17, 4, x_15);
x_18 = lean_unbox(x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*5, x_18);
lean_ctor_set_uint8(x_17, sizeof(void*)*5 + 1, x_10);
x_19 = l_Lake_captureProc_x3f(x_17, x_4);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = l_Lake_Package_getBarrelUrl___redArg___closed__13;
x_26 = lean_array_get_size(x_24);
x_27 = lean_array_push(x_24, x_25);
lean_ctor_set(x_3, 0, x_27);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_3);
lean_ctor_set(x_19, 0, x_28);
return x_19;
}
else
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_3, 0);
x_30 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_31 = lean_ctor_get(x_3, 1);
lean_inc(x_31);
lean_inc(x_29);
lean_dec(x_3);
x_32 = l_Lake_Package_getBarrelUrl___redArg___closed__13;
x_33 = lean_array_get_size(x_29);
x_34 = lean_array_push(x_29, x_32);
x_35 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_30);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_19, 0, x_36);
return x_19;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_37 = lean_ctor_get(x_19, 1);
lean_inc(x_37);
lean_dec(x_19);
x_38 = lean_ctor_get(x_3, 0);
lean_inc(x_38);
x_39 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_40 = lean_ctor_get(x_3, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_41 = x_3;
} else {
 lean_dec_ref(x_3);
 x_41 = lean_box(0);
}
x_42 = l_Lake_Package_getBarrelUrl___redArg___closed__13;
x_43 = lean_array_get_size(x_38);
x_44 = lean_array_push(x_38, x_42);
if (lean_is_scalar(x_41)) {
 x_45 = lean_alloc_ctor(0, 2, 1);
} else {
 x_45 = x_41;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
lean_ctor_set_uint8(x_45, sizeof(void*)*2, x_39);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_37);
return x_47;
}
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_2, 1);
lean_inc(x_48);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_19);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_50 = lean_ctor_get(x_19, 0);
lean_dec(x_50);
x_51 = lean_ctor_get(x_3, 0);
lean_inc(x_51);
x_52 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_53 = lean_ctor_get(x_3, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_20, 0);
lean_inc(x_54);
lean_dec(x_20);
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
lean_dec(x_48);
x_56 = l_Lake_Env_toolchain(x_55);
x_57 = lean_string_utf8_byte_size(x_56);
x_58 = lean_nat_dec_eq(x_57, x_9);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_53);
lean_dec(x_51);
x_59 = lean_box(x_10);
x_60 = lean_alloc_closure((void*)(l_Lake_Package_getBarrelUrl___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_60, 0, x_59);
x_61 = l_Lean_Name_toString(x_5, x_10, x_60);
x_62 = l_Lake_Reservoir_pkgApiUrl(x_55, x_7, x_61);
lean_dec(x_61);
lean_dec(x_7);
x_63 = l_Lake_Package_getBarrelUrl___redArg___closed__14;
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_string_append(x_64, x_54);
lean_dec(x_54);
x_66 = l_Lake_Package_getBarrelUrl___redArg___closed__15;
x_67 = lean_string_append(x_65, x_66);
x_68 = l_Lake_uriEncode(x_56);
lean_dec(x_56);
x_69 = lean_string_append(x_67, x_68);
lean_dec(x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_3);
lean_ctor_set(x_19, 0, x_70);
return x_19;
}
else
{
uint8_t x_71; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_7);
lean_dec(x_5);
x_71 = !lean_is_exclusive(x_3);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_3, 1);
lean_dec(x_72);
x_73 = lean_ctor_get(x_3, 0);
lean_dec(x_73);
x_74 = l_Lake_Package_getBarrelUrl___redArg___closed__17;
x_75 = lean_array_get_size(x_51);
x_76 = lean_array_push(x_51, x_74);
lean_ctor_set(x_3, 0, x_76);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_3);
lean_ctor_set(x_19, 0, x_77);
return x_19;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_3);
x_78 = l_Lake_Package_getBarrelUrl___redArg___closed__17;
x_79 = lean_array_get_size(x_51);
x_80 = lean_array_push(x_51, x_78);
x_81 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_53);
lean_ctor_set_uint8(x_81, sizeof(void*)*2, x_52);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_19, 0, x_82);
return x_19;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_83 = lean_ctor_get(x_19, 1);
lean_inc(x_83);
lean_dec(x_19);
x_84 = lean_ctor_get(x_3, 0);
lean_inc(x_84);
x_85 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_86 = lean_ctor_get(x_3, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_20, 0);
lean_inc(x_87);
lean_dec(x_20);
x_88 = lean_ctor_get(x_48, 1);
lean_inc(x_88);
lean_dec(x_48);
x_89 = l_Lake_Env_toolchain(x_88);
x_90 = lean_string_utf8_byte_size(x_89);
x_91 = lean_nat_dec_eq(x_90, x_9);
lean_dec(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_86);
lean_dec(x_84);
x_92 = lean_box(x_10);
x_93 = lean_alloc_closure((void*)(l_Lake_Package_getBarrelUrl___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_93, 0, x_92);
x_94 = l_Lean_Name_toString(x_5, x_10, x_93);
x_95 = l_Lake_Reservoir_pkgApiUrl(x_88, x_7, x_94);
lean_dec(x_94);
lean_dec(x_7);
x_96 = l_Lake_Package_getBarrelUrl___redArg___closed__14;
x_97 = lean_string_append(x_95, x_96);
x_98 = lean_string_append(x_97, x_87);
lean_dec(x_87);
x_99 = l_Lake_Package_getBarrelUrl___redArg___closed__15;
x_100 = lean_string_append(x_98, x_99);
x_101 = l_Lake_uriEncode(x_89);
lean_dec(x_89);
x_102 = lean_string_append(x_100, x_101);
lean_dec(x_101);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_3);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_83);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_7);
lean_dec(x_5);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_105 = x_3;
} else {
 lean_dec_ref(x_3);
 x_105 = lean_box(0);
}
x_106 = l_Lake_Package_getBarrelUrl___redArg___closed__17;
x_107 = lean_array_get_size(x_84);
x_108 = lean_array_push(x_84, x_106);
if (lean_is_scalar(x_105)) {
 x_109 = lean_alloc_ctor(0, 2, 1);
} else {
 x_109 = x_105;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_86);
lean_ctor_set_uint8(x_109, sizeof(void*)*2, x_85);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_83);
return x_111;
}
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_112 = !lean_is_exclusive(x_3);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_113 = lean_ctor_get(x_3, 0);
x_114 = l_Lake_Package_getBarrelUrl___redArg___closed__19;
x_115 = lean_array_get_size(x_113);
x_116 = lean_array_push(x_113, x_114);
lean_ctor_set(x_3, 0, x_116);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_3);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_4);
return x_118;
}
else
{
lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_119 = lean_ctor_get(x_3, 0);
x_120 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_121 = lean_ctor_get(x_3, 1);
lean_inc(x_121);
lean_inc(x_119);
lean_dec(x_3);
x_122 = l_Lake_Package_getBarrelUrl___redArg___closed__19;
x_123 = lean_array_get_size(x_119);
x_124 = lean_array_push(x_119, x_122);
x_125 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_121);
lean_ctor_set_uint8(x_125, sizeof(void*)*2, x_120);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_4);
return x_127;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Package_getBarrelUrl___redArg(x_1, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Package_getBarrelUrl___redArg___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Package_getBarrelUrl(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lake_Package_getReleaseUrl___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no release tag found for revision", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getReleaseUrl___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("describe", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getReleaseUrl___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--tags", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getReleaseUrl___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--exact-match", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getReleaseUrl___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_getReleaseUrl___redArg___closed__1;
x_2 = l_Lake_Package_getBarrelUrl___redArg___closed__4;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_getReleaseUrl___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_getReleaseUrl___redArg___closed__2;
x_2 = l_Lake_Package_getReleaseUrl___redArg___closed__4;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_getReleaseUrl___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_getReleaseUrl___redArg___closed__3;
x_2 = l_Lake_Package_getReleaseUrl___redArg___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_getReleaseUrl___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_getBarrelUrl___redArg___closed__0;
x_2 = l_Lake_Package_getReleaseUrl___redArg___closed__6;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_getReleaseUrl___redArg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" '", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getReleaseUrl___redArg___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getReleaseUrl___redArg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/releases/download/", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getReleaseUrl___redArg___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getReleaseUrl___redArg___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("origin", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getReleaseUrl___redArg___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("release repository URL not known; the package may need to set 'releaseRepo'", 75, 75);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getReleaseUrl___redArg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = l_Lake_Package_getReleaseUrl___redArg___closed__13;
x_2 = lean_box(3);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_getReleaseUrl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_79; lean_object* x_121; 
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 8);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 16);
lean_inc(x_23);
lean_dec(x_1);
x_121 = lean_ctor_get(x_21, 11);
lean_inc(x_121);
lean_dec(x_21);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_122 = lean_string_utf8_byte_size(x_22);
x_123 = lean_unsigned_to_nat(0u);
x_124 = lean_nat_dec_eq(x_122, x_123);
lean_dec(x_122);
if (x_124 == 0)
{
lean_dec(x_22);
x_79 = x_121;
goto block_120;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_22);
x_79 = x_125;
goto block_120;
}
}
else
{
lean_dec(x_22);
x_79 = x_121;
goto block_120;
}
block_19:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = l_Lake_Package_getReleaseUrl___redArg___closed__0;
x_10 = lean_string_append(x_9, x_4);
lean_dec(x_4);
x_11 = lean_box(3);
x_12 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_12, 0, x_10);
x_13 = lean_unbox(x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_13);
x_14 = lean_array_get_size(x_5);
x_15 = lean_array_push(x_5, x_12);
x_16 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_6);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
return x_18;
}
block_78:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_29 = l_Lake_Package_getReleaseUrl___redArg___closed__7;
x_30 = l_Lake_Package_getBarrelUrl___redArg___closed__9;
x_31 = l_Lake_Package_getBarrelUrl___redArg___closed__10;
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_20);
x_33 = l_Lake_Package_getBarrelUrl___redArg___closed__11;
x_34 = lean_box(1);
x_35 = lean_box(0);
lean_inc(x_32);
x_36 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_31);
lean_ctor_set(x_36, 2, x_29);
lean_ctor_set(x_36, 3, x_32);
lean_ctor_set(x_36, 4, x_33);
x_37 = lean_unbox(x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*5, x_37);
x_38 = lean_unbox(x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*5 + 1, x_38);
x_39 = l_Lake_captureProc_x3f(x_36, x_24);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_28);
lean_dec(x_23);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lake_Package_getBarrelUrl___redArg___closed__8;
x_43 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_43, 0, x_30);
lean_ctor_set(x_43, 1, x_31);
lean_ctor_set(x_43, 2, x_42);
lean_ctor_set(x_43, 3, x_32);
lean_ctor_set(x_43, 4, x_33);
x_44 = lean_unbox(x_34);
lean_ctor_set_uint8(x_43, sizeof(void*)*5, x_44);
x_45 = lean_unbox(x_35);
lean_ctor_set_uint8(x_43, sizeof(void*)*5 + 1, x_45);
x_46 = l_Lake_captureProc_x3f(x_43, x_41);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__0;
x_4 = x_49;
x_5 = x_25;
x_6 = x_27;
x_7 = x_26;
x_8 = x_48;
goto block_19;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_ctor_get(x_47, 0);
lean_inc(x_51);
lean_dec(x_47);
x_52 = l_Lake_Package_getReleaseUrl___redArg___closed__8;
x_53 = lean_string_append(x_52, x_51);
lean_dec(x_51);
x_54 = l_Lake_Package_getReleaseUrl___redArg___closed__9;
x_55 = lean_string_append(x_53, x_54);
x_4 = x_55;
x_5 = x_25;
x_6 = x_27;
x_7 = x_26;
x_8 = x_50;
goto block_19;
}
}
else
{
uint8_t x_56; 
lean_dec(x_32);
x_56 = !lean_is_exclusive(x_39);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_57 = lean_ctor_get(x_39, 0);
lean_dec(x_57);
x_58 = lean_ctor_get(x_40, 0);
lean_inc(x_58);
lean_dec(x_40);
x_59 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_59, 0, x_25);
lean_ctor_set(x_59, 1, x_26);
lean_ctor_set_uint8(x_59, sizeof(void*)*2, x_27);
x_60 = l_Lake_Package_getReleaseUrl___redArg___closed__10;
x_61 = lean_string_append(x_28, x_60);
x_62 = lean_string_append(x_61, x_58);
lean_dec(x_58);
x_63 = l_Lake_Package_getReleaseUrl___redArg___closed__11;
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_string_append(x_64, x_23);
lean_dec(x_23);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_59);
lean_ctor_set(x_39, 0, x_66);
return x_39;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_67 = lean_ctor_get(x_39, 1);
lean_inc(x_67);
lean_dec(x_39);
x_68 = lean_ctor_get(x_40, 0);
lean_inc(x_68);
lean_dec(x_40);
x_69 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_69, 0, x_25);
lean_ctor_set(x_69, 1, x_26);
lean_ctor_set_uint8(x_69, sizeof(void*)*2, x_27);
x_70 = l_Lake_Package_getReleaseUrl___redArg___closed__10;
x_71 = lean_string_append(x_28, x_70);
x_72 = lean_string_append(x_71, x_68);
lean_dec(x_68);
x_73 = l_Lake_Package_getReleaseUrl___redArg___closed__11;
x_74 = lean_string_append(x_72, x_73);
x_75 = lean_string_append(x_74, x_23);
lean_dec(x_23);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_69);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_67);
return x_77;
}
}
}
block_120:
{
lean_object* x_80; lean_object* x_81; 
x_80 = l_Lake_Package_getReleaseUrl___redArg___closed__12;
lean_inc(x_20);
x_81 = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(x_80, x_20, x_3);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
lean_dec(x_23);
lean_dec(x_20);
x_83 = !lean_is_exclusive(x_81);
if (x_83 == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_81, 0);
lean_dec(x_84);
x_85 = !lean_is_exclusive(x_2);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_2, 0);
x_87 = l_Lake_Package_getReleaseUrl___redArg___closed__14;
x_88 = lean_array_get_size(x_86);
x_89 = lean_array_push(x_86, x_87);
lean_ctor_set(x_2, 0, x_89);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_2);
lean_ctor_set(x_81, 0, x_90);
return x_81;
}
else
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_91 = lean_ctor_get(x_2, 0);
x_92 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_93 = lean_ctor_get(x_2, 1);
lean_inc(x_93);
lean_inc(x_91);
lean_dec(x_2);
x_94 = l_Lake_Package_getReleaseUrl___redArg___closed__14;
x_95 = lean_array_get_size(x_91);
x_96 = lean_array_push(x_91, x_94);
x_97 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_93);
lean_ctor_set_uint8(x_97, sizeof(void*)*2, x_92);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set(x_81, 0, x_98);
return x_81;
}
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_99 = lean_ctor_get(x_81, 1);
lean_inc(x_99);
lean_dec(x_81);
x_100 = lean_ctor_get(x_2, 0);
lean_inc(x_100);
x_101 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_102 = lean_ctor_get(x_2, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_103 = x_2;
} else {
 lean_dec_ref(x_2);
 x_103 = lean_box(0);
}
x_104 = l_Lake_Package_getReleaseUrl___redArg___closed__14;
x_105 = lean_array_get_size(x_100);
x_106 = lean_array_push(x_100, x_104);
if (lean_is_scalar(x_103)) {
 x_107 = lean_alloc_ctor(0, 2, 1);
} else {
 x_107 = x_103;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_102);
lean_ctor_set_uint8(x_107, sizeof(void*)*2, x_101);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_99);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; 
x_110 = lean_ctor_get(x_81, 1);
lean_inc(x_110);
lean_dec(x_81);
x_111 = lean_ctor_get(x_2, 0);
lean_inc(x_111);
x_112 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_113 = lean_ctor_get(x_2, 1);
lean_inc(x_113);
lean_dec(x_2);
x_114 = lean_ctor_get(x_82, 0);
lean_inc(x_114);
lean_dec(x_82);
x_24 = x_110;
x_25 = x_111;
x_26 = x_113;
x_27 = x_112;
x_28 = x_114;
goto block_78;
}
}
else
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; 
x_115 = lean_ctor_get(x_81, 1);
lean_inc(x_115);
lean_dec(x_81);
x_116 = lean_ctor_get(x_2, 0);
lean_inc(x_116);
x_117 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_118 = lean_ctor_get(x_2, 1);
lean_inc(x_118);
lean_dec(x_2);
x_119 = lean_ctor_get(x_79, 0);
lean_inc(x_119);
lean_dec(x_79);
x_24 = x_115;
x_25 = x_116;
x_26 = x_118;
x_27 = x_117;
x_28 = x_119;
goto block_78;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_getReleaseUrl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Package_getReleaseUrl___redArg(x_1, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_getReleaseUrl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Package_getReleaseUrl(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at___Lake_Package_fetchBuildArchive_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = l_Lake_download(x_1, x_2, x_3, x_11, x_9);
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
lean_object* x_17; 
x_17 = lean_ctor_get(x_13, 1);
lean_ctor_set(x_8, 0, x_17);
lean_ctor_set(x_13, 1, x_8);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
lean_ctor_set(x_8, 0, x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_8);
lean_ctor_set(x_12, 0, x_20);
return x_12;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_24 = x_13;
} else {
 lean_dec_ref(x_13);
 x_24 = lean_box(0);
}
lean_ctor_set(x_8, 0, x_23);
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_8);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_12);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_12, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_13, 1);
lean_ctor_set(x_8, 0, x_30);
lean_ctor_set(x_13, 1, x_8);
return x_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_13, 0);
x_32 = lean_ctor_get(x_13, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_13);
lean_ctor_set(x_8, 0, x_32);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_8);
lean_ctor_set(x_12, 0, x_33);
return x_12;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_12, 1);
lean_inc(x_34);
lean_dec(x_12);
x_35 = lean_ctor_get(x_13, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_37 = x_13;
} else {
 lean_dec_ref(x_13);
 x_37 = lean_box(0);
}
lean_ctor_set(x_8, 0, x_36);
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_8);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_34);
return x_39;
}
}
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_8, 0);
x_41 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_42 = lean_ctor_get(x_8, 1);
lean_inc(x_42);
lean_inc(x_40);
lean_dec(x_8);
x_43 = l_Lake_download(x_1, x_2, x_3, x_40, x_9);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_49 = x_44;
} else {
 lean_dec_ref(x_44);
 x_49 = lean_box(0);
}
x_50 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_42);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_41);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_50);
if (lean_is_scalar(x_46)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_46;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_45);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_43, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_54 = x_43;
} else {
 lean_dec_ref(x_43);
 x_54 = lean_box(0);
}
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
x_58 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_42);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_41);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_58);
if (lean_is_scalar(x_54)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_54;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_53);
return x_60;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at___Lake_Package_fetchBuildArchive_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_29; 
x_15 = l_System_FilePath_pathExists(x_7, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
x_22 = lean_alloc_closure((void*)(l_Lake_buildUnlessUpToDate_x3f___at___Lake_Package_fetchBuildArchive_spec__0___lam__0___boxed), 9, 3);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_2);
lean_closure_set(x_22, 2, x_3);
x_23 = lean_box(1);
x_29 = lean_unbox(x_16);
lean_dec(x_16);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
x_30 = lean_ctor_get(x_6, 3);
x_31 = l_Lake_MTime_checkUpToDate___at___Lake_buildUnlessUpToDate_x3f___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(x_5, x_30, x_17);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_22, x_8, x_4, x_10, x_11, x_12, x_13, x_34);
lean_dec(x_7);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_31, 0);
lean_dec(x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_23);
lean_ctor_set(x_38, 1, x_13);
lean_ctor_set(x_31, 0, x_38);
return x_31;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_23);
lean_ctor_set(x_40, 1, x_13);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_13);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_13, 1);
lean_dec(x_43);
x_44 = lean_ctor_get(x_13, 0);
lean_dec(x_44);
lean_inc(x_7);
x_45 = l_Lake_readTraceFile_x3f(x_7, x_19, x_17);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; uint8_t x_49; 
lean_dec(x_18);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_46, 1);
x_51 = lean_ctor_get(x_46, 0);
lean_dec(x_51);
x_52 = l_Lake_MTime_checkUpToDate___at___Lake_buildUnlessUpToDate_x3f___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(x_5, x_9, x_48);
x_53 = lean_ctor_get(x_12, 0);
lean_inc(x_53);
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_ctor_get(x_52, 0);
x_56 = lean_ctor_get(x_52, 1);
x_57 = lean_ctor_get_uint8(x_53, sizeof(void*)*1);
lean_dec(x_53);
lean_ctor_set(x_13, 0, x_50);
if (x_57 == 0)
{
lean_object* x_58; 
lean_free_object(x_52);
lean_dec(x_55);
lean_free_object(x_46);
x_58 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_22, x_8, x_4, x_10, x_11, x_12, x_13, x_56);
lean_dec(x_7);
return x_58;
}
else
{
uint8_t x_59; 
x_59 = lean_unbox(x_55);
lean_dec(x_55);
if (x_59 == 0)
{
lean_object* x_60; 
lean_free_object(x_52);
lean_free_object(x_46);
x_60 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_22, x_8, x_4, x_10, x_11, x_12, x_13, x_56);
lean_dec(x_7);
return x_60;
}
else
{
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_ctor_set(x_46, 1, x_13);
lean_ctor_set(x_46, 0, x_23);
lean_ctor_set(x_52, 0, x_46);
return x_52;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_52, 0);
x_62 = lean_ctor_get(x_52, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_52);
x_63 = lean_ctor_get_uint8(x_53, sizeof(void*)*1);
lean_dec(x_53);
lean_ctor_set(x_13, 0, x_50);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_61);
lean_free_object(x_46);
x_64 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_22, x_8, x_4, x_10, x_11, x_12, x_13, x_62);
lean_dec(x_7);
return x_64;
}
else
{
uint8_t x_65; 
x_65 = lean_unbox(x_61);
lean_dec(x_61);
if (x_65 == 0)
{
lean_object* x_66; 
lean_free_object(x_46);
x_66 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_22, x_8, x_4, x_10, x_11, x_12, x_13, x_62);
lean_dec(x_7);
return x_66;
}
else
{
lean_object* x_67; 
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_ctor_set(x_46, 1, x_13);
lean_ctor_set(x_46, 0, x_23);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_46);
lean_ctor_set(x_67, 1, x_62);
return x_67;
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_68 = lean_ctor_get(x_46, 1);
lean_inc(x_68);
lean_dec(x_46);
x_69 = l_Lake_MTime_checkUpToDate___at___Lake_buildUnlessUpToDate_x3f___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(x_5, x_9, x_48);
x_70 = lean_ctor_get(x_12, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
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
x_74 = lean_ctor_get_uint8(x_70, sizeof(void*)*1);
lean_dec(x_70);
lean_ctor_set(x_13, 0, x_68);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_73);
lean_dec(x_71);
x_75 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_22, x_8, x_4, x_10, x_11, x_12, x_13, x_72);
lean_dec(x_7);
return x_75;
}
else
{
uint8_t x_76; 
x_76 = lean_unbox(x_71);
lean_dec(x_71);
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec(x_73);
x_77 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_22, x_8, x_4, x_10, x_11, x_12, x_13, x_72);
lean_dec(x_7);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_23);
lean_ctor_set(x_78, 1, x_13);
if (lean_is_scalar(x_73)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_73;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_72);
return x_79;
}
}
}
}
else
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_47);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_81 = lean_ctor_get(x_47, 0);
x_82 = lean_ctor_get(x_45, 1);
lean_inc(x_82);
lean_dec(x_45);
x_83 = lean_ctor_get(x_46, 1);
lean_inc(x_83);
lean_dec(x_46);
x_84 = lean_ctor_get(x_81, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_81, 2);
lean_inc(x_85);
lean_dec(x_81);
lean_ctor_set(x_13, 0, x_83);
lean_ctor_set(x_47, 0, x_84);
x_86 = l_Lake_checkHashUpToDate___at___Lake_buildUnlessUpToDate_x3f___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___redArg(x_5, x_6, x_47, x_9, x_12, x_13, x_82);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_85);
lean_dec(x_18);
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_90);
lean_dec(x_86);
x_91 = lean_ctor_get(x_87, 1);
lean_inc(x_91);
lean_dec(x_87);
x_92 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_22, x_8, x_4, x_10, x_11, x_12, x_91, x_90);
lean_dec(x_7);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
x_93 = lean_ctor_get(x_87, 1);
lean_inc(x_93);
lean_dec(x_87);
x_94 = lean_ctor_get(x_86, 1);
lean_inc(x_94);
lean_dec(x_86);
x_95 = !lean_is_exclusive(x_93);
if (x_95 == 0)
{
uint8_t x_96; lean_object* x_97; uint8_t x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_96 = lean_ctor_get_uint8(x_93, sizeof(void*)*2);
x_97 = lean_box(1);
x_98 = lean_unbox(x_97);
x_99 = l_Lake_JobAction_merge(x_96, x_98);
lean_ctor_set_uint8(x_93, sizeof(void*)*2, x_99);
x_100 = lean_unsigned_to_nat(0u);
x_101 = lean_array_get_size(x_85);
x_102 = lean_nat_dec_lt(x_100, x_101);
if (x_102 == 0)
{
lean_dec(x_101);
lean_dec(x_85);
x_24 = x_93;
x_25 = x_94;
goto block_28;
}
else
{
uint8_t x_103; 
x_103 = lean_nat_dec_le(x_101, x_101);
if (x_103 == 0)
{
lean_dec(x_101);
lean_dec(x_85);
x_24 = x_93;
x_25 = x_94;
goto block_28;
}
else
{
lean_object* x_104; size_t x_105; size_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_104 = lean_box(0);
x_105 = 0;
x_106 = lean_usize_of_nat(x_101);
lean_dec(x_101);
x_107 = l_Array_foldlMUnsafe_fold___at___Lake_buildUnlessUpToDate_x3f___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__3___redArg(x_85, x_105, x_106, x_104, x_93, x_94);
lean_dec(x_85);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_24 = x_110;
x_25 = x_109;
goto block_28;
}
}
}
else
{
lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_111 = lean_ctor_get(x_93, 0);
x_112 = lean_ctor_get_uint8(x_93, sizeof(void*)*2);
x_113 = lean_ctor_get(x_93, 1);
lean_inc(x_113);
lean_inc(x_111);
lean_dec(x_93);
x_114 = lean_box(1);
x_115 = lean_unbox(x_114);
x_116 = l_Lake_JobAction_merge(x_112, x_115);
x_117 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_117, 0, x_111);
lean_ctor_set(x_117, 1, x_113);
lean_ctor_set_uint8(x_117, sizeof(void*)*2, x_116);
x_118 = lean_unsigned_to_nat(0u);
x_119 = lean_array_get_size(x_85);
x_120 = lean_nat_dec_lt(x_118, x_119);
if (x_120 == 0)
{
lean_dec(x_119);
lean_dec(x_85);
x_24 = x_117;
x_25 = x_94;
goto block_28;
}
else
{
uint8_t x_121; 
x_121 = lean_nat_dec_le(x_119, x_119);
if (x_121 == 0)
{
lean_dec(x_119);
lean_dec(x_85);
x_24 = x_117;
x_25 = x_94;
goto block_28;
}
else
{
lean_object* x_122; size_t x_123; size_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_122 = lean_box(0);
x_123 = 0;
x_124 = lean_usize_of_nat(x_119);
lean_dec(x_119);
x_125 = l_Array_foldlMUnsafe_fold___at___Lake_buildUnlessUpToDate_x3f___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__3___redArg(x_85, x_123, x_124, x_122, x_117, x_94);
lean_dec(x_85);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_24 = x_128;
x_25 = x_127;
goto block_28;
}
}
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_129 = lean_ctor_get(x_47, 0);
lean_inc(x_129);
lean_dec(x_47);
x_130 = lean_ctor_get(x_45, 1);
lean_inc(x_130);
lean_dec(x_45);
x_131 = lean_ctor_get(x_46, 1);
lean_inc(x_131);
lean_dec(x_46);
x_132 = lean_ctor_get(x_129, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_129, 2);
lean_inc(x_133);
lean_dec(x_129);
lean_ctor_set(x_13, 0, x_131);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_132);
x_135 = l_Lake_checkHashUpToDate___at___Lake_buildUnlessUpToDate_x3f___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___redArg(x_5, x_6, x_134, x_9, x_12, x_13, x_130);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_unbox(x_137);
lean_dec(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_133);
lean_dec(x_18);
x_139 = lean_ctor_get(x_135, 1);
lean_inc(x_139);
lean_dec(x_135);
x_140 = lean_ctor_get(x_136, 1);
lean_inc(x_140);
lean_dec(x_136);
x_141 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_22, x_8, x_4, x_10, x_11, x_12, x_140, x_139);
lean_dec(x_7);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
x_142 = lean_ctor_get(x_136, 1);
lean_inc(x_142);
lean_dec(x_136);
x_143 = lean_ctor_get(x_135, 1);
lean_inc(x_143);
lean_dec(x_135);
x_144 = lean_ctor_get(x_142, 0);
lean_inc(x_144);
x_145 = lean_ctor_get_uint8(x_142, sizeof(void*)*2);
x_146 = lean_ctor_get(x_142, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_147 = x_142;
} else {
 lean_dec_ref(x_142);
 x_147 = lean_box(0);
}
x_148 = lean_box(1);
x_149 = lean_unbox(x_148);
x_150 = l_Lake_JobAction_merge(x_145, x_149);
if (lean_is_scalar(x_147)) {
 x_151 = lean_alloc_ctor(0, 2, 1);
} else {
 x_151 = x_147;
}
lean_ctor_set(x_151, 0, x_144);
lean_ctor_set(x_151, 1, x_146);
lean_ctor_set_uint8(x_151, sizeof(void*)*2, x_150);
x_152 = lean_unsigned_to_nat(0u);
x_153 = lean_array_get_size(x_133);
x_154 = lean_nat_dec_lt(x_152, x_153);
if (x_154 == 0)
{
lean_dec(x_153);
lean_dec(x_133);
x_24 = x_151;
x_25 = x_143;
goto block_28;
}
else
{
uint8_t x_155; 
x_155 = lean_nat_dec_le(x_153, x_153);
if (x_155 == 0)
{
lean_dec(x_153);
lean_dec(x_133);
x_24 = x_151;
x_25 = x_143;
goto block_28;
}
else
{
lean_object* x_156; size_t x_157; size_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_156 = lean_box(0);
x_157 = 0;
x_158 = lean_usize_of_nat(x_153);
lean_dec(x_153);
x_159 = l_Array_foldlMUnsafe_fold___at___Lake_buildUnlessUpToDate_x3f___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__3___redArg(x_133, x_157, x_158, x_156, x_151, x_143);
lean_dec(x_133);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_24 = x_162;
x_25 = x_161;
goto block_28;
}
}
}
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_13);
lean_inc(x_7);
x_163 = l_Lake_readTraceFile_x3f(x_7, x_19, x_17);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; 
lean_dec(x_18);
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
lean_dec(x_163);
x_167 = lean_ctor_get(x_164, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_168 = x_164;
} else {
 lean_dec_ref(x_164);
 x_168 = lean_box(0);
}
x_169 = l_Lake_MTime_checkUpToDate___at___Lake_buildUnlessUpToDate_x3f___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(x_5, x_9, x_166);
x_170 = lean_ctor_get(x_12, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_173 = x_169;
} else {
 lean_dec_ref(x_169);
 x_173 = lean_box(0);
}
x_174 = lean_ctor_get_uint8(x_170, sizeof(void*)*1);
lean_dec(x_170);
x_175 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_175, 0, x_167);
lean_ctor_set(x_175, 1, x_21);
lean_ctor_set_uint8(x_175, sizeof(void*)*2, x_20);
if (x_174 == 0)
{
lean_object* x_176; 
lean_dec(x_173);
lean_dec(x_171);
lean_dec(x_168);
x_176 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_22, x_8, x_4, x_10, x_11, x_12, x_175, x_172);
lean_dec(x_7);
return x_176;
}
else
{
uint8_t x_177; 
x_177 = lean_unbox(x_171);
lean_dec(x_171);
if (x_177 == 0)
{
lean_object* x_178; 
lean_dec(x_173);
lean_dec(x_168);
x_178 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_22, x_8, x_4, x_10, x_11, x_12, x_175, x_172);
lean_dec(x_7);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; 
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
if (lean_is_scalar(x_168)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_168;
}
lean_ctor_set(x_179, 0, x_23);
lean_ctor_set(x_179, 1, x_175);
if (lean_is_scalar(x_173)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_173;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_172);
return x_180;
}
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_181 = lean_ctor_get(x_165, 0);
lean_inc(x_181);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 x_182 = x_165;
} else {
 lean_dec_ref(x_165);
 x_182 = lean_box(0);
}
x_183 = lean_ctor_get(x_163, 1);
lean_inc(x_183);
lean_dec(x_163);
x_184 = lean_ctor_get(x_164, 1);
lean_inc(x_184);
lean_dec(x_164);
x_185 = lean_ctor_get(x_181, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_181, 2);
lean_inc(x_186);
lean_dec(x_181);
x_187 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_21);
lean_ctor_set_uint8(x_187, sizeof(void*)*2, x_20);
if (lean_is_scalar(x_182)) {
 x_188 = lean_alloc_ctor(1, 1, 0);
} else {
 x_188 = x_182;
}
lean_ctor_set(x_188, 0, x_185);
x_189 = l_Lake_checkHashUpToDate___at___Lake_buildUnlessUpToDate_x3f___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___redArg(x_5, x_6, x_188, x_9, x_12, x_187, x_183);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_unbox(x_191);
lean_dec(x_191);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_186);
lean_dec(x_18);
x_193 = lean_ctor_get(x_189, 1);
lean_inc(x_193);
lean_dec(x_189);
x_194 = lean_ctor_get(x_190, 1);
lean_inc(x_194);
lean_dec(x_190);
x_195 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_22, x_8, x_4, x_10, x_11, x_12, x_194, x_193);
lean_dec(x_7);
return x_195;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
x_196 = lean_ctor_get(x_190, 1);
lean_inc(x_196);
lean_dec(x_190);
x_197 = lean_ctor_get(x_189, 1);
lean_inc(x_197);
lean_dec(x_189);
x_198 = lean_ctor_get(x_196, 0);
lean_inc(x_198);
x_199 = lean_ctor_get_uint8(x_196, sizeof(void*)*2);
x_200 = lean_ctor_get(x_196, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_201 = x_196;
} else {
 lean_dec_ref(x_196);
 x_201 = lean_box(0);
}
x_202 = lean_box(1);
x_203 = lean_unbox(x_202);
x_204 = l_Lake_JobAction_merge(x_199, x_203);
if (lean_is_scalar(x_201)) {
 x_205 = lean_alloc_ctor(0, 2, 1);
} else {
 x_205 = x_201;
}
lean_ctor_set(x_205, 0, x_198);
lean_ctor_set(x_205, 1, x_200);
lean_ctor_set_uint8(x_205, sizeof(void*)*2, x_204);
x_206 = lean_unsigned_to_nat(0u);
x_207 = lean_array_get_size(x_186);
x_208 = lean_nat_dec_lt(x_206, x_207);
if (x_208 == 0)
{
lean_dec(x_207);
lean_dec(x_186);
x_24 = x_205;
x_25 = x_197;
goto block_28;
}
else
{
uint8_t x_209; 
x_209 = lean_nat_dec_le(x_207, x_207);
if (x_209 == 0)
{
lean_dec(x_207);
lean_dec(x_186);
x_24 = x_205;
x_25 = x_197;
goto block_28;
}
else
{
lean_object* x_210; size_t x_211; size_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_210 = lean_box(0);
x_211 = 0;
x_212 = lean_usize_of_nat(x_207);
lean_dec(x_207);
x_213 = l_Array_foldlMUnsafe_fold___at___Lake_buildUnlessUpToDate_x3f___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__3___redArg(x_186, x_211, x_212, x_210, x_205, x_197);
lean_dec(x_186);
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_24 = x_216;
x_25 = x_215;
goto block_28;
}
}
}
}
}
}
block_28:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
if (lean_is_scalar(x_18)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_18;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
static lean_object* _init_l_Lake_Package_fetchBuildArchive___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchBuildArchive___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<hash>", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchBuildArchive___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_fetchBuildArchive___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_fetchBuildArchive___closed__4() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lake_Package_fetchBuildArchive___closed__3;
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_fetchBuildArchive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint64_t x_11; uint64_t x_12; uint64_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_11 = 1723;
x_12 = lean_string_hash(x_2);
x_13 = lean_uint64_mix_hash(x_11, x_12);
x_14 = l_Lake_Package_fetchBuildArchive___closed__0;
lean_inc(x_3);
x_15 = l_System_FilePath_addExtension(x_3, x_14);
x_16 = l_Lake_Package_fetchBuildArchive___closed__1;
x_17 = l_Lake_Package_fetchBuildArchive___closed__2;
x_18 = l_Lake_Package_fetchBuildArchive___closed__4;
x_19 = lean_box_uint64(x_13);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_20, 3, x_18);
x_21 = lean_box(2);
x_22 = lean_unbox(x_21);
lean_inc(x_3);
x_23 = l_Lake_buildUnlessUpToDate_x3f___at___Lake_Package_fetchBuildArchive_spec__0(x_2, x_3, x_4, x_5, x_3, x_20, x_15, x_22, x_18, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_1, 3);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
lean_dec(x_1);
x_31 = lean_ctor_get(x_25, 6);
lean_inc(x_31);
lean_dec(x_25);
x_32 = l_System_FilePath_normalize(x_31);
x_33 = l_Lake_joinRelative(x_30, x_32);
lean_dec(x_32);
x_34 = l_System_FilePath_pathExists(x_33, x_26);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; uint8_t x_79; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
x_39 = lean_ctor_get_uint8(x_29, sizeof(void*)*2);
x_40 = lean_ctor_get(x_29, 1);
lean_inc(x_40);
x_79 = lean_unbox(x_28);
lean_dec(x_28);
if (x_79 == 0)
{
lean_free_object(x_34);
lean_dec(x_36);
lean_free_object(x_24);
lean_dec(x_29);
goto block_78;
}
else
{
uint8_t x_80; 
x_80 = lean_unbox(x_36);
lean_dec(x_36);
if (x_80 == 0)
{
lean_free_object(x_34);
lean_free_object(x_24);
lean_dec(x_29);
goto block_78;
}
else
{
lean_object* x_81; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_33);
lean_dec(x_3);
x_81 = lean_box(0);
lean_ctor_set(x_24, 0, x_81);
lean_ctor_set(x_34, 0, x_24);
return x_34;
}
}
block_78:
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_box(1);
x_42 = lean_unbox(x_41);
x_43 = l_Lake_untar(x_3, x_33, x_42, x_38, x_37);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_unbox(x_21);
x_47 = l_Lake_JobAction_merge(x_39, x_46);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_45);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_45, 1);
x_50 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_40);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_47);
lean_ctor_set(x_45, 1, x_50);
return x_43;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_45, 0);
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_45);
x_53 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_40);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_47);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_43, 0, x_54);
return x_43;
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_45);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_45, 1);
x_57 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_40);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_47);
lean_ctor_set(x_45, 1, x_57);
return x_43;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_45, 0);
x_59 = lean_ctor_get(x_45, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_45);
x_60 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_40);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_47);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_43, 0, x_61);
return x_43;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; 
x_62 = lean_ctor_get(x_43, 0);
x_63 = lean_ctor_get(x_43, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_43);
x_64 = lean_unbox(x_21);
x_65 = l_Lake_JobAction_merge(x_39, x_64);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_62, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_62, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_68 = x_62;
} else {
 lean_dec_ref(x_62);
 x_68 = lean_box(0);
}
x_69 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_40);
lean_ctor_set_uint8(x_69, sizeof(void*)*2, x_65);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_63);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_62, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_62, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_74 = x_62;
} else {
 lean_dec_ref(x_62);
 x_74 = lean_box(0);
}
x_75 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_40);
lean_ctor_set_uint8(x_75, sizeof(void*)*2, x_65);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_63);
return x_77;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; uint8_t x_108; 
x_82 = lean_ctor_get(x_34, 0);
x_83 = lean_ctor_get(x_34, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_34);
x_84 = lean_ctor_get(x_29, 0);
lean_inc(x_84);
x_85 = lean_ctor_get_uint8(x_29, sizeof(void*)*2);
x_86 = lean_ctor_get(x_29, 1);
lean_inc(x_86);
x_108 = lean_unbox(x_28);
lean_dec(x_28);
if (x_108 == 0)
{
lean_dec(x_82);
lean_free_object(x_24);
lean_dec(x_29);
goto block_107;
}
else
{
uint8_t x_109; 
x_109 = lean_unbox(x_82);
lean_dec(x_82);
if (x_109 == 0)
{
lean_free_object(x_24);
lean_dec(x_29);
goto block_107;
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_86);
lean_dec(x_84);
lean_dec(x_33);
lean_dec(x_3);
x_110 = lean_box(0);
lean_ctor_set(x_24, 0, x_110);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_24);
lean_ctor_set(x_111, 1, x_83);
return x_111;
}
}
block_107:
{
lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; uint8_t x_94; 
x_87 = lean_box(1);
x_88 = lean_unbox(x_87);
x_89 = l_Lake_untar(x_3, x_33, x_88, x_84, x_83);
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
x_93 = lean_unbox(x_21);
x_94 = l_Lake_JobAction_merge(x_85, x_93);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_95 = lean_ctor_get(x_90, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_90, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_97 = x_90;
} else {
 lean_dec_ref(x_90);
 x_97 = lean_box(0);
}
x_98 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_86);
lean_ctor_set_uint8(x_98, sizeof(void*)*2, x_94);
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_97;
}
lean_ctor_set(x_99, 0, x_95);
lean_ctor_set(x_99, 1, x_98);
if (lean_is_scalar(x_92)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_92;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_91);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_101 = lean_ctor_get(x_90, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_90, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_103 = x_90;
} else {
 lean_dec_ref(x_90);
 x_103 = lean_box(0);
}
x_104 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_86);
lean_ctor_set_uint8(x_104, sizeof(void*)*2, x_94);
if (lean_is_scalar(x_103)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_103;
}
lean_ctor_set(x_105, 0, x_101);
lean_ctor_set(x_105, 1, x_104);
if (lean_is_scalar(x_92)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_92;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_91);
return x_106;
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; uint8_t x_146; 
x_112 = lean_ctor_get(x_24, 0);
x_113 = lean_ctor_get(x_24, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_24);
x_114 = lean_ctor_get(x_1, 1);
lean_inc(x_114);
lean_dec(x_1);
x_115 = lean_ctor_get(x_25, 6);
lean_inc(x_115);
lean_dec(x_25);
x_116 = l_System_FilePath_normalize(x_115);
x_117 = l_Lake_joinRelative(x_114, x_116);
lean_dec(x_116);
x_118 = l_System_FilePath_pathExists(x_117, x_26);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_121 = x_118;
} else {
 lean_dec_ref(x_118);
 x_121 = lean_box(0);
}
x_122 = lean_ctor_get(x_113, 0);
lean_inc(x_122);
x_123 = lean_ctor_get_uint8(x_113, sizeof(void*)*2);
x_124 = lean_ctor_get(x_113, 1);
lean_inc(x_124);
x_146 = lean_unbox(x_112);
lean_dec(x_112);
if (x_146 == 0)
{
lean_dec(x_121);
lean_dec(x_119);
lean_dec(x_113);
goto block_145;
}
else
{
uint8_t x_147; 
x_147 = lean_unbox(x_119);
lean_dec(x_119);
if (x_147 == 0)
{
lean_dec(x_121);
lean_dec(x_113);
goto block_145;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_124);
lean_dec(x_122);
lean_dec(x_117);
lean_dec(x_3);
x_148 = lean_box(0);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_113);
if (lean_is_scalar(x_121)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_121;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_120);
return x_150;
}
}
block_145:
{
lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; uint8_t x_132; 
x_125 = lean_box(1);
x_126 = lean_unbox(x_125);
x_127 = l_Lake_untar(x_3, x_117, x_126, x_122, x_120);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_130 = x_127;
} else {
 lean_dec_ref(x_127);
 x_130 = lean_box(0);
}
x_131 = lean_unbox(x_21);
x_132 = l_Lake_JobAction_merge(x_123, x_131);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_133 = lean_ctor_get(x_128, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_128, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_135 = x_128;
} else {
 lean_dec_ref(x_128);
 x_135 = lean_box(0);
}
x_136 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_124);
lean_ctor_set_uint8(x_136, sizeof(void*)*2, x_132);
if (lean_is_scalar(x_135)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_135;
}
lean_ctor_set(x_137, 0, x_133);
lean_ctor_set(x_137, 1, x_136);
if (lean_is_scalar(x_130)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_130;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_129);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_139 = lean_ctor_get(x_128, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_128, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_141 = x_128;
} else {
 lean_dec_ref(x_128);
 x_141 = lean_box(0);
}
x_142 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_124);
lean_ctor_set_uint8(x_142, sizeof(void*)*2, x_132);
if (lean_is_scalar(x_141)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_141;
}
lean_ctor_set(x_143, 0, x_139);
lean_ctor_set(x_143, 1, x_142);
if (lean_is_scalar(x_130)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_130;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_129);
return x_144;
}
}
}
}
else
{
uint8_t x_151; 
lean_dec(x_3);
lean_dec(x_1);
x_151 = !lean_is_exclusive(x_23);
if (x_151 == 0)
{
lean_object* x_152; uint8_t x_153; 
x_152 = lean_ctor_get(x_23, 0);
lean_dec(x_152);
x_153 = !lean_is_exclusive(x_24);
if (x_153 == 0)
{
return x_23;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_24, 0);
x_155 = lean_ctor_get(x_24, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_24);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
lean_ctor_set(x_23, 0, x_156);
return x_23;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_157 = lean_ctor_get(x_23, 1);
lean_inc(x_157);
lean_dec(x_23);
x_158 = lean_ctor_get(x_24, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_24, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_160 = x_24;
} else {
 lean_dec_ref(x_24);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_159);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_157);
return x_162;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at___Lake_Package_fetchBuildArchive_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_buildUnlessUpToDate_x3f___at___Lake_Package_fetchBuildArchive_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at___Lake_Package_fetchBuildArchive_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_8);
lean_dec(x_8);
x_16 = l_Lake_buildUnlessUpToDate_x3f___at___Lake_Package_fetchBuildArchive_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_15, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_10 = lean_box(2);
x_11 = lean_unbox(x_10);
x_12 = l_Lake_JobAction_merge(x_9, x_11);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_12);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_inc(x_16);
lean_dec(x_6);
x_19 = lean_box(2);
x_20 = lean_unbox(x_19);
x_21 = l_Lake_JobAction_merge(x_17, x_20);
x_22 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_21);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_7);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_2);
x_11 = lean_apply_1(x_1, x_2);
x_12 = l_Lake_Package_fetchBuildArchive(x_2, x_4, x_11, x_3, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = lean_box(1);
lean_ctor_set(x_13, 0, x_18);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_box(1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_12, 0, x_21);
return x_12;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_24 = x_13;
} else {
 lean_dec_ref(x_13);
 x_24 = lean_box(0);
}
x_25 = lean_box(1);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_12, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_13);
if (x_30 == 0)
{
return x_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_13, 0);
x_32 = lean_ctor_get(x_13, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_13);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_12, 0, x_33);
return x_12;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_12, 1);
lean_inc(x_34);
lean_dec(x_12);
x_35 = lean_ctor_get(x_13, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_37 = x_13;
} else {
 lean_dec_ref(x_13);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_34);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_inc(x_11);
x_18 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__2), 10, 3);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_11);
lean_closure_set(x_18, 2, x_2);
x_19 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__0;
lean_inc(x_11);
x_20 = lean_apply_1(x_3, x_11);
lean_inc(x_4);
x_21 = lean_alloc_closure((void*)(l_Lake_EquipT_bind), 8, 7);
lean_closure_set(x_21, 0, lean_box(0));
lean_closure_set(x_21, 1, lean_box(0));
lean_closure_set(x_21, 2, x_4);
lean_closure_set(x_21, 3, lean_box(0));
lean_closure_set(x_21, 4, lean_box(0));
lean_closure_set(x_21, 5, x_20);
lean_closure_set(x_21, 6, x_18);
x_22 = lean_alloc_closure((void*)(l_Lake_EquipT_tryCatch), 8, 7);
lean_closure_set(x_22, 0, lean_box(0));
lean_closure_set(x_22, 1, lean_box(0));
lean_closure_set(x_22, 2, lean_box(0));
lean_closure_set(x_22, 3, x_5);
lean_closure_set(x_22, 4, lean_box(0));
lean_closure_set(x_22, 5, x_21);
lean_closure_set(x_22, 6, x_6);
x_23 = lean_alloc_closure((void*)(l_Lake_EquipT_bind), 8, 7);
lean_closure_set(x_23, 0, lean_box(0));
lean_closure_set(x_23, 1, lean_box(0));
lean_closure_set(x_23, 2, x_4);
lean_closure_set(x_23, 3, lean_box(0));
lean_closure_set(x_23, 4, lean_box(0));
lean_closure_set(x_23, 5, x_22);
lean_closure_set(x_23, 6, x_7);
x_24 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
x_25 = lean_alloc_closure((void*)(l_Lake_Job_async___boxed), 11, 5);
lean_closure_set(x_25, 0, lean_box(0));
lean_closure_set(x_25, 1, x_8);
lean_closure_set(x_25, 2, x_23);
lean_closure_set(x_25, 3, x_24);
lean_closure_set(x_25, 4, x_19);
x_26 = lean_alloc_closure((void*)(l_Lake_JobM_runSpawnM), 8, 2);
lean_closure_set(x_26, 0, lean_box(0));
lean_closure_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l_Lake_FetchM_runJobM), 8, 2);
lean_closure_set(x_27, 0, lean_box(0));
lean_closure_set(x_27, 1, x_26);
lean_inc(x_15);
x_28 = l_Lake_ensureJob___redArg(x_8, x_27, x_12, x_13, x_14, x_15, x_16, x_17);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_29, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_35 = lean_ctor_get(x_30, 2);
lean_dec(x_35);
x_36 = lean_ctor_get(x_15, 3);
lean_inc(x_36);
lean_dec(x_15);
x_37 = lean_st_ref_take(x_36, x_31);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_11, 0);
lean_inc(x_40);
lean_dec(x_11);
x_41 = lean_box(1);
x_42 = lean_unbox(x_41);
lean_inc(x_9);
x_43 = l_Lean_Name_toString(x_40, x_42, x_9);
x_44 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_45 = lean_string_append(x_43, x_44);
x_46 = l_Lake_Name_eraseHead(x_10);
x_47 = lean_unbox(x_41);
x_48 = l_Lean_Name_toString(x_46, x_47, x_9);
x_49 = lean_string_append(x_45, x_48);
lean_dec(x_48);
lean_ctor_set(x_30, 2, x_49);
x_50 = lean_unbox(x_41);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_50);
lean_inc(x_30);
x_51 = l_Lake_Job_toOpaque___redArg(x_30);
x_52 = lean_array_push(x_38, x_51);
x_53 = lean_st_ref_set(x_36, x_52, x_39);
lean_dec(x_36);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
x_56 = l_Lake_Job_renew___redArg(x_30);
lean_ctor_set(x_29, 0, x_56);
lean_ctor_set(x_53, 0, x_29);
return x_53;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_53, 1);
lean_inc(x_57);
lean_dec(x_53);
x_58 = l_Lake_Job_renew___redArg(x_30);
lean_ctor_set(x_29, 0, x_58);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_29);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_60 = lean_ctor_get(x_30, 0);
x_61 = lean_ctor_get(x_30, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_30);
x_62 = lean_ctor_get(x_15, 3);
lean_inc(x_62);
lean_dec(x_15);
x_63 = lean_st_ref_take(x_62, x_31);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_11, 0);
lean_inc(x_66);
lean_dec(x_11);
x_67 = lean_box(1);
x_68 = lean_unbox(x_67);
lean_inc(x_9);
x_69 = l_Lean_Name_toString(x_66, x_68, x_9);
x_70 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_71 = lean_string_append(x_69, x_70);
x_72 = l_Lake_Name_eraseHead(x_10);
x_73 = lean_unbox(x_67);
x_74 = l_Lean_Name_toString(x_72, x_73, x_9);
x_75 = lean_string_append(x_71, x_74);
lean_dec(x_74);
x_76 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_76, 0, x_60);
lean_ctor_set(x_76, 1, x_61);
lean_ctor_set(x_76, 2, x_75);
x_77 = lean_unbox(x_67);
lean_ctor_set_uint8(x_76, sizeof(void*)*3, x_77);
lean_inc(x_76);
x_78 = l_Lake_Job_toOpaque___redArg(x_76);
x_79 = lean_array_push(x_64, x_78);
x_80 = lean_st_ref_set(x_62, x_79, x_65);
lean_dec(x_62);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_82 = x_80;
} else {
 lean_dec_ref(x_80);
 x_82 = lean_box(0);
}
x_83 = l_Lake_Job_renew___redArg(x_76);
lean_ctor_set(x_29, 0, x_83);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_29);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_85 = lean_ctor_get(x_29, 1);
lean_inc(x_85);
lean_dec(x_29);
x_86 = lean_ctor_get(x_30, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_30, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 x_88 = x_30;
} else {
 lean_dec_ref(x_30);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_15, 3);
lean_inc(x_89);
lean_dec(x_15);
x_90 = lean_st_ref_take(x_89, x_31);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_ctor_get(x_11, 0);
lean_inc(x_93);
lean_dec(x_11);
x_94 = lean_box(1);
x_95 = lean_unbox(x_94);
lean_inc(x_9);
x_96 = l_Lean_Name_toString(x_93, x_95, x_9);
x_97 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_98 = lean_string_append(x_96, x_97);
x_99 = l_Lake_Name_eraseHead(x_10);
x_100 = lean_unbox(x_94);
x_101 = l_Lean_Name_toString(x_99, x_100, x_9);
x_102 = lean_string_append(x_98, x_101);
lean_dec(x_101);
if (lean_is_scalar(x_88)) {
 x_103 = lean_alloc_ctor(0, 3, 1);
} else {
 x_103 = x_88;
}
lean_ctor_set(x_103, 0, x_86);
lean_ctor_set(x_103, 1, x_87);
lean_ctor_set(x_103, 2, x_102);
x_104 = lean_unbox(x_94);
lean_ctor_set_uint8(x_103, sizeof(void*)*3, x_104);
lean_inc(x_103);
x_105 = l_Lake_Job_toOpaque___redArg(x_103);
x_106 = lean_array_push(x_91, x_105);
x_107 = lean_st_ref_set(x_89, x_106, x_92);
lean_dec(x_89);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_109 = x_107;
} else {
 lean_dec_ref(x_107);
 x_109 = lean_box(0);
}
x_110 = l_Lake_Job_renew___redArg(x_103);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_85);
if (lean_is_scalar(x_109)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_109;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_108);
return x_112;
}
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringBool___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instToJsonBool___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__0;
x_2 = l_Lake_EStateT_instMonadExceptOfOfMonad___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3;
x_2 = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3;
x_2 = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__5;
x_2 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__6;
x_2 = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__6;
x_2 = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__8;
x_2 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__9;
x_2 = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__9;
x_2 = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__11;
x_2 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__10;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__2;
x_2 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__1;
x_3 = lean_alloc_closure((void*)(l_Lake_stdFormat___boxed), 5, 3);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
lean_closure_set(x_3, 2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__0;
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; 
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_ctor_get(x_7, 4);
lean_dec(x_12);
x_13 = lean_ctor_get(x_7, 3);
lean_dec(x_13);
x_14 = lean_ctor_get(x_7, 2);
lean_dec(x_14);
lean_inc(x_9);
lean_inc(x_11);
x_15 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_15, 0, x_11);
lean_closure_set(x_15, 1, x_9);
lean_inc(x_9);
lean_inc(x_11);
x_16 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_16, 0, x_11);
lean_closure_set(x_16, 1, x_9);
lean_inc(x_15);
lean_inc(x_11);
x_17 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_17, 0, x_11);
lean_closure_set(x_17, 1, x_15);
lean_inc(x_11);
lean_inc(x_10);
x_18 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_18, 0, x_10);
lean_closure_set(x_18, 1, x_11);
lean_closure_set(x_18, 2, x_9);
x_19 = l_Lake_EStateT_instFunctor___redArg(x_10);
x_20 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_20, 0, x_11);
lean_ctor_set(x_7, 4, x_16);
lean_ctor_set(x_7, 3, x_17);
lean_ctor_set(x_7, 2, x_18);
lean_ctor_set(x_7, 1, x_20);
lean_ctor_set(x_7, 0, x_19);
lean_ctor_set(x_5, 1, x_15);
x_21 = l_ReaderT_instMonad___redArg(x_5);
x_22 = l_ReaderT_instMonad___redArg(x_21);
x_23 = l_ReaderT_instMonad___redArg(x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1___closed__0;
x_26 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 7, 0);
x_27 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed), 7, 0);
x_28 = l_Lake_instDataKindBool;
x_29 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__12;
x_30 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__3___boxed), 17, 10);
lean_closure_set(x_30, 0, x_2);
lean_closure_set(x_30, 1, x_4);
lean_closure_set(x_30, 2, x_3);
lean_closure_set(x_30, 3, x_24);
lean_closure_set(x_30, 4, x_29);
lean_closure_set(x_30, 5, x_27);
lean_closure_set(x_30, 6, x_26);
lean_closure_set(x_30, 7, x_28);
lean_closure_set(x_30, 8, x_25);
lean_closure_set(x_30, 9, x_1);
x_31 = l_Lake_Package_keyword;
x_32 = lean_box(1);
x_33 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__13;
x_34 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set(x_34, 2, x_28);
lean_ctor_set(x_34, 3, x_33);
x_35 = lean_unbox(x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*4, x_35);
x_36 = lean_unbox(x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*4 + 1, x_36);
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_62; 
x_37 = lean_ctor_get(x_5, 1);
x_38 = lean_ctor_get(x_7, 0);
x_39 = lean_ctor_get(x_7, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_7);
lean_inc(x_37);
lean_inc(x_39);
x_40 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_40, 0, x_39);
lean_closure_set(x_40, 1, x_37);
lean_inc(x_37);
lean_inc(x_39);
x_41 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_41, 0, x_39);
lean_closure_set(x_41, 1, x_37);
lean_inc(x_40);
lean_inc(x_39);
x_42 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_42, 0, x_39);
lean_closure_set(x_42, 1, x_40);
lean_inc(x_39);
lean_inc(x_38);
x_43 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_43, 0, x_38);
lean_closure_set(x_43, 1, x_39);
lean_closure_set(x_43, 2, x_37);
x_44 = l_Lake_EStateT_instFunctor___redArg(x_38);
x_45 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_45, 0, x_39);
x_46 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_43);
lean_ctor_set(x_46, 3, x_42);
lean_ctor_set(x_46, 4, x_41);
lean_ctor_set(x_5, 1, x_40);
lean_ctor_set(x_5, 0, x_46);
x_47 = l_ReaderT_instMonad___redArg(x_5);
x_48 = l_ReaderT_instMonad___redArg(x_47);
x_49 = l_ReaderT_instMonad___redArg(x_48);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = l_Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1___closed__0;
x_52 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 7, 0);
x_53 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed), 7, 0);
x_54 = l_Lake_instDataKindBool;
x_55 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__12;
x_56 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__3___boxed), 17, 10);
lean_closure_set(x_56, 0, x_2);
lean_closure_set(x_56, 1, x_4);
lean_closure_set(x_56, 2, x_3);
lean_closure_set(x_56, 3, x_50);
lean_closure_set(x_56, 4, x_55);
lean_closure_set(x_56, 5, x_53);
lean_closure_set(x_56, 6, x_52);
lean_closure_set(x_56, 7, x_54);
lean_closure_set(x_56, 8, x_51);
lean_closure_set(x_56, 9, x_1);
x_57 = l_Lake_Package_keyword;
x_58 = lean_box(1);
x_59 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__13;
x_60 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_56);
lean_ctor_set(x_60, 2, x_54);
lean_ctor_set(x_60, 3, x_59);
x_61 = lean_unbox(x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*4, x_61);
x_62 = lean_unbox(x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*4 + 1, x_62);
return x_60;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_91; 
x_63 = lean_ctor_get(x_5, 0);
x_64 = lean_ctor_get(x_5, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_5);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 lean_ctor_release(x_63, 2);
 lean_ctor_release(x_63, 3);
 lean_ctor_release(x_63, 4);
 x_67 = x_63;
} else {
 lean_dec_ref(x_63);
 x_67 = lean_box(0);
}
lean_inc(x_64);
lean_inc(x_66);
x_68 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_68, 0, x_66);
lean_closure_set(x_68, 1, x_64);
lean_inc(x_64);
lean_inc(x_66);
x_69 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_69, 0, x_66);
lean_closure_set(x_69, 1, x_64);
lean_inc(x_68);
lean_inc(x_66);
x_70 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_70, 0, x_66);
lean_closure_set(x_70, 1, x_68);
lean_inc(x_66);
lean_inc(x_65);
x_71 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_71, 0, x_65);
lean_closure_set(x_71, 1, x_66);
lean_closure_set(x_71, 2, x_64);
x_72 = l_Lake_EStateT_instFunctor___redArg(x_65);
x_73 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_73, 0, x_66);
if (lean_is_scalar(x_67)) {
 x_74 = lean_alloc_ctor(0, 5, 0);
} else {
 x_74 = x_67;
}
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_74, 2, x_71);
lean_ctor_set(x_74, 3, x_70);
lean_ctor_set(x_74, 4, x_69);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_68);
x_76 = l_ReaderT_instMonad___redArg(x_75);
x_77 = l_ReaderT_instMonad___redArg(x_76);
x_78 = l_ReaderT_instMonad___redArg(x_77);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = l_Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1___closed__0;
x_81 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 7, 0);
x_82 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed), 7, 0);
x_83 = l_Lake_instDataKindBool;
x_84 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__12;
x_85 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__3___boxed), 17, 10);
lean_closure_set(x_85, 0, x_2);
lean_closure_set(x_85, 1, x_4);
lean_closure_set(x_85, 2, x_3);
lean_closure_set(x_85, 3, x_79);
lean_closure_set(x_85, 4, x_84);
lean_closure_set(x_85, 5, x_82);
lean_closure_set(x_85, 6, x_81);
lean_closure_set(x_85, 7, x_83);
lean_closure_set(x_85, 8, x_80);
lean_closure_set(x_85, 9, x_1);
x_86 = l_Lake_Package_keyword;
x_87 = lean_box(1);
x_88 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__13;
x_89 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_85);
lean_ctor_set(x_89, 2, x_83);
lean_ctor_set(x_89, 3, x_88);
x_90 = lean_unbox(x_87);
lean_ctor_set_uint8(x_89, sizeof(void*)*4, x_90);
x_91 = lean_unbox(x_87);
lean_ctor_set_uint8(x_89, sizeof(void*)*4 + 1, x_91);
return x_89;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__0;
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; 
x_10 = lean_ctor_get(x_6, 1);
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 1);
x_13 = lean_ctor_get(x_8, 4);
lean_dec(x_13);
x_14 = lean_ctor_get(x_8, 3);
lean_dec(x_14);
x_15 = lean_ctor_get(x_8, 2);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_12);
x_16 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_16, 0, x_12);
lean_closure_set(x_16, 1, x_10);
lean_inc(x_10);
lean_inc(x_12);
x_17 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_17, 0, x_12);
lean_closure_set(x_17, 1, x_10);
lean_inc(x_16);
lean_inc(x_12);
x_18 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_18, 0, x_12);
lean_closure_set(x_18, 1, x_16);
lean_inc(x_12);
lean_inc(x_11);
x_19 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_19, 0, x_11);
lean_closure_set(x_19, 1, x_12);
lean_closure_set(x_19, 2, x_10);
x_20 = l_Lake_EStateT_instFunctor___redArg(x_11);
x_21 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_21, 0, x_12);
lean_ctor_set(x_8, 4, x_17);
lean_ctor_set(x_8, 3, x_18);
lean_ctor_set(x_8, 2, x_19);
lean_ctor_set(x_8, 1, x_21);
lean_ctor_set(x_8, 0, x_20);
lean_ctor_set(x_6, 1, x_16);
x_22 = l_ReaderT_instMonad___redArg(x_6);
x_23 = l_ReaderT_instMonad___redArg(x_22);
x_24 = l_ReaderT_instMonad___redArg(x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1___closed__0;
x_27 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 7, 0);
x_28 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed), 7, 0);
x_29 = l_Lake_instDataKindBool;
x_30 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__12;
x_31 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__3___boxed), 17, 10);
lean_closure_set(x_31, 0, x_2);
lean_closure_set(x_31, 1, x_4);
lean_closure_set(x_31, 2, x_3);
lean_closure_set(x_31, 3, x_25);
lean_closure_set(x_31, 4, x_30);
lean_closure_set(x_31, 5, x_28);
lean_closure_set(x_31, 6, x_27);
lean_closure_set(x_31, 7, x_29);
lean_closure_set(x_31, 8, x_26);
lean_closure_set(x_31, 9, x_1);
x_32 = l_Lake_Package_keyword;
x_33 = lean_box(1);
x_34 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__13;
x_35 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set(x_35, 2, x_29);
lean_ctor_set(x_35, 3, x_34);
x_36 = lean_unbox(x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*4, x_36);
x_37 = lean_unbox(x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*4 + 1, x_37);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; 
x_38 = lean_ctor_get(x_6, 1);
x_39 = lean_ctor_get(x_8, 0);
x_40 = lean_ctor_get(x_8, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_8);
lean_inc(x_38);
lean_inc(x_40);
x_41 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_41, 0, x_40);
lean_closure_set(x_41, 1, x_38);
lean_inc(x_38);
lean_inc(x_40);
x_42 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_42, 0, x_40);
lean_closure_set(x_42, 1, x_38);
lean_inc(x_41);
lean_inc(x_40);
x_43 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_43, 0, x_40);
lean_closure_set(x_43, 1, x_41);
lean_inc(x_40);
lean_inc(x_39);
x_44 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_44, 0, x_39);
lean_closure_set(x_44, 1, x_40);
lean_closure_set(x_44, 2, x_38);
x_45 = l_Lake_EStateT_instFunctor___redArg(x_39);
x_46 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_46, 0, x_40);
x_47 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_47, 2, x_44);
lean_ctor_set(x_47, 3, x_43);
lean_ctor_set(x_47, 4, x_42);
lean_ctor_set(x_6, 1, x_41);
lean_ctor_set(x_6, 0, x_47);
x_48 = l_ReaderT_instMonad___redArg(x_6);
x_49 = l_ReaderT_instMonad___redArg(x_48);
x_50 = l_ReaderT_instMonad___redArg(x_49);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = l_Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1___closed__0;
x_53 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 7, 0);
x_54 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed), 7, 0);
x_55 = l_Lake_instDataKindBool;
x_56 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__12;
x_57 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__3___boxed), 17, 10);
lean_closure_set(x_57, 0, x_2);
lean_closure_set(x_57, 1, x_4);
lean_closure_set(x_57, 2, x_3);
lean_closure_set(x_57, 3, x_51);
lean_closure_set(x_57, 4, x_56);
lean_closure_set(x_57, 5, x_54);
lean_closure_set(x_57, 6, x_53);
lean_closure_set(x_57, 7, x_55);
lean_closure_set(x_57, 8, x_52);
lean_closure_set(x_57, 9, x_1);
x_58 = l_Lake_Package_keyword;
x_59 = lean_box(1);
x_60 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__13;
x_61 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_57);
lean_ctor_set(x_61, 2, x_55);
lean_ctor_set(x_61, 3, x_60);
x_62 = lean_unbox(x_59);
lean_ctor_set_uint8(x_61, sizeof(void*)*4, x_62);
x_63 = lean_unbox(x_59);
lean_ctor_set_uint8(x_61, sizeof(void*)*4 + 1, x_63);
return x_61;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_92; 
x_64 = lean_ctor_get(x_6, 0);
x_65 = lean_ctor_get(x_6, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_6);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 lean_ctor_release(x_64, 2);
 lean_ctor_release(x_64, 3);
 lean_ctor_release(x_64, 4);
 x_68 = x_64;
} else {
 lean_dec_ref(x_64);
 x_68 = lean_box(0);
}
lean_inc(x_65);
lean_inc(x_67);
x_69 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_69, 0, x_67);
lean_closure_set(x_69, 1, x_65);
lean_inc(x_65);
lean_inc(x_67);
x_70 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_70, 0, x_67);
lean_closure_set(x_70, 1, x_65);
lean_inc(x_69);
lean_inc(x_67);
x_71 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_71, 0, x_67);
lean_closure_set(x_71, 1, x_69);
lean_inc(x_67);
lean_inc(x_66);
x_72 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_72, 0, x_66);
lean_closure_set(x_72, 1, x_67);
lean_closure_set(x_72, 2, x_65);
x_73 = l_Lake_EStateT_instFunctor___redArg(x_66);
x_74 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_74, 0, x_67);
if (lean_is_scalar(x_68)) {
 x_75 = lean_alloc_ctor(0, 5, 0);
} else {
 x_75 = x_68;
}
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set(x_75, 2, x_72);
lean_ctor_set(x_75, 3, x_71);
lean_ctor_set(x_75, 4, x_70);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_69);
x_77 = l_ReaderT_instMonad___redArg(x_76);
x_78 = l_ReaderT_instMonad___redArg(x_77);
x_79 = l_ReaderT_instMonad___redArg(x_78);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = l_Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1___closed__0;
x_82 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 7, 0);
x_83 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed), 7, 0);
x_84 = l_Lake_instDataKindBool;
x_85 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__12;
x_86 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__3___boxed), 17, 10);
lean_closure_set(x_86, 0, x_2);
lean_closure_set(x_86, 1, x_4);
lean_closure_set(x_86, 2, x_3);
lean_closure_set(x_86, 3, x_80);
lean_closure_set(x_86, 4, x_85);
lean_closure_set(x_86, 5, x_83);
lean_closure_set(x_86, 6, x_82);
lean_closure_set(x_86, 7, x_84);
lean_closure_set(x_86, 8, x_81);
lean_closure_set(x_86, 9, x_1);
x_87 = l_Lake_Package_keyword;
x_88 = lean_box(1);
x_89 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__13;
x_90 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_86);
lean_ctor_set(x_90, 2, x_84);
lean_ctor_set(x_90, 3, x_89);
x_91 = lean_unbox(x_88);
lean_ctor_set_uint8(x_90, sizeof(void*)*4, x_91);
x_92 = lean_unbox(x_88);
lean_ctor_set_uint8(x_90, sizeof(void*)*4 + 1, x_92);
return x_90;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__3___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to fetch ", 16, 16);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
if (x_4 == 0)
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_8, 0);
x_42 = lean_ctor_get_uint8(x_41, sizeof(void*)*1 + 3);
x_43 = lean_box(2);
x_44 = lean_unbox(x_43);
x_45 = l_Lake_instDecidableEqVerbosity(x_42, x_44);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_3);
lean_dec(x_2);
x_46 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0;
x_11 = x_46;
x_12 = x_9;
x_13 = x_10;
goto block_40;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_47 = lean_box(x_4);
x_48 = lean_alloc_closure((void*)(l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__1___boxed), 2, 1);
lean_closure_set(x_48, 0, x_47);
x_49 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1;
lean_inc(x_48);
x_50 = l_Lean_Name_toString(x_2, x_45, x_48);
x_51 = lean_string_append(x_49, x_50);
lean_dec(x_50);
x_52 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_53 = lean_string_append(x_51, x_52);
x_54 = l_Lake_Name_eraseHead(x_3);
x_55 = l_Lean_Name_toString(x_54, x_45, x_48);
x_56 = lean_string_append(x_53, x_55);
lean_dec(x_55);
x_57 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3;
x_58 = lean_string_append(x_56, x_57);
x_11 = x_58;
x_12 = x_9;
x_13 = x_10;
goto block_40;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_3);
lean_dec(x_2);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_9);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_10);
return x_61;
}
block_40:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___closed__0;
x_17 = lean_string_append(x_16, x_1);
x_18 = lean_string_append(x_17, x_11);
lean_dec(x_11);
x_19 = lean_box(3);
x_20 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_20, 0, x_18);
x_21 = lean_unbox(x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_21);
x_22 = lean_array_get_size(x_15);
x_23 = lean_array_push(x_15, x_20);
lean_ctor_set(x_12, 0, x_23);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_12);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_13);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get_uint8(x_12, sizeof(void*)*2);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_26);
lean_dec(x_12);
x_29 = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___closed__0;
x_30 = lean_string_append(x_29, x_1);
x_31 = lean_string_append(x_30, x_11);
lean_dec(x_11);
x_32 = lean_box(3);
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_31);
x_34 = lean_unbox(x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_34);
x_35 = lean_array_get_size(x_26);
x_36 = lean_array_push(x_26, x_33);
x_37 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_28);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_27);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_13);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_box(0);
x_12 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__2;
x_13 = lean_unbox(x_11);
x_14 = l_Lake_Job_mapM___redArg(x_1, x_3, x_2, x_10, x_13, x_4, x_5, x_6, x_7, x_12, x_9);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_8);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_8);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_inc(x_2);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed), 10, 3);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_14);
lean_closure_set(x_15, 2, x_2);
lean_inc(x_3);
x_16 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0), 9, 2);
lean_closure_set(x_16, 0, x_3);
lean_closure_set(x_16, 1, x_15);
lean_inc(x_14);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_18 = l_Lake_Package_keyword;
x_19 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_7);
lean_ctor_set(x_19, 3, x_2);
x_20 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch), 9, 3);
lean_closure_set(x_20, 0, lean_box(0));
lean_closure_set(x_20, 1, x_19);
lean_closure_set(x_20, 2, lean_box(0));
x_21 = lean_alloc_closure((void*)(l_Lake_EquipT_bind), 8, 7);
lean_closure_set(x_21, 0, lean_box(0));
lean_closure_set(x_21, 1, lean_box(0));
lean_closure_set(x_21, 2, x_4);
lean_closure_set(x_21, 3, lean_box(0));
lean_closure_set(x_21, 4, lean_box(0));
lean_closure_set(x_21, 5, x_20);
lean_closure_set(x_21, 6, x_16);
lean_inc(x_11);
x_22 = l_Lake_ensureJob___redArg(x_3, x_21, x_8, x_9, x_10, x_11, x_12, x_13);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_23, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_29 = lean_ctor_get(x_24, 2);
lean_dec(x_29);
x_30 = lean_ctor_get(x_11, 3);
lean_inc(x_30);
lean_dec(x_11);
x_31 = lean_st_ref_take(x_30, x_25);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_box(1);
x_35 = lean_unbox(x_34);
lean_inc(x_5);
x_36 = l_Lean_Name_toString(x_14, x_35, x_5);
x_37 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_38 = lean_string_append(x_36, x_37);
x_39 = l_Lake_Name_eraseHead(x_6);
x_40 = lean_unbox(x_34);
x_41 = l_Lean_Name_toString(x_39, x_40, x_5);
x_42 = lean_string_append(x_38, x_41);
lean_dec(x_41);
x_43 = lean_box(0);
lean_ctor_set(x_24, 2, x_42);
x_44 = lean_unbox(x_43);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_44);
lean_inc(x_24);
x_45 = l_Lake_Job_toOpaque___redArg(x_24);
x_46 = lean_array_push(x_32, x_45);
x_47 = lean_st_ref_set(x_30, x_46, x_33);
lean_dec(x_30);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = l_Lake_Job_renew___redArg(x_24);
lean_ctor_set(x_23, 0, x_50);
lean_ctor_set(x_47, 0, x_23);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = l_Lake_Job_renew___redArg(x_24);
lean_ctor_set(x_23, 0, x_52);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_23);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_54 = lean_ctor_get(x_24, 0);
x_55 = lean_ctor_get(x_24, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_24);
x_56 = lean_ctor_get(x_11, 3);
lean_inc(x_56);
lean_dec(x_11);
x_57 = lean_st_ref_take(x_56, x_25);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_box(1);
x_61 = lean_unbox(x_60);
lean_inc(x_5);
x_62 = l_Lean_Name_toString(x_14, x_61, x_5);
x_63 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_64 = lean_string_append(x_62, x_63);
x_65 = l_Lake_Name_eraseHead(x_6);
x_66 = lean_unbox(x_60);
x_67 = l_Lean_Name_toString(x_65, x_66, x_5);
x_68 = lean_string_append(x_64, x_67);
lean_dec(x_67);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_70, 0, x_54);
lean_ctor_set(x_70, 1, x_55);
lean_ctor_set(x_70, 2, x_68);
x_71 = lean_unbox(x_69);
lean_ctor_set_uint8(x_70, sizeof(void*)*3, x_71);
lean_inc(x_70);
x_72 = l_Lake_Job_toOpaque___redArg(x_70);
x_73 = lean_array_push(x_58, x_72);
x_74 = lean_st_ref_set(x_56, x_73, x_59);
lean_dec(x_56);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
x_77 = l_Lake_Job_renew___redArg(x_70);
lean_ctor_set(x_23, 0, x_77);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_23);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_79 = lean_ctor_get(x_23, 1);
lean_inc(x_79);
lean_dec(x_23);
x_80 = lean_ctor_get(x_24, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_24, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 x_82 = x_24;
} else {
 lean_dec_ref(x_24);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_11, 3);
lean_inc(x_83);
lean_dec(x_11);
x_84 = lean_st_ref_take(x_83, x_25);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_box(1);
x_88 = lean_unbox(x_87);
lean_inc(x_5);
x_89 = l_Lean_Name_toString(x_14, x_88, x_5);
x_90 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_91 = lean_string_append(x_89, x_90);
x_92 = l_Lake_Name_eraseHead(x_6);
x_93 = lean_unbox(x_87);
x_94 = l_Lean_Name_toString(x_92, x_93, x_5);
x_95 = lean_string_append(x_91, x_94);
lean_dec(x_94);
x_96 = lean_box(0);
if (lean_is_scalar(x_82)) {
 x_97 = lean_alloc_ctor(0, 3, 1);
} else {
 x_97 = x_82;
}
lean_ctor_set(x_97, 0, x_80);
lean_ctor_set(x_97, 1, x_81);
lean_ctor_set(x_97, 2, x_95);
x_98 = lean_unbox(x_96);
lean_ctor_set_uint8(x_97, sizeof(void*)*3, x_98);
lean_inc(x_97);
x_99 = l_Lake_Job_toOpaque___redArg(x_97);
x_100 = lean_array_push(x_85, x_99);
x_101 = lean_st_ref_set(x_83, x_100, x_86);
lean_dec(x_83);
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
x_104 = l_Lake_Job_renew___redArg(x_97);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_79);
if (lean_is_scalar(x_103)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_103;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_102);
return x_106;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__0;
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; 
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
x_11 = lean_ctor_get(x_6, 4);
lean_dec(x_11);
x_12 = lean_ctor_get(x_6, 3);
lean_dec(x_12);
x_13 = lean_ctor_get(x_6, 2);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_10);
x_14 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_8);
lean_inc(x_8);
lean_inc(x_10);
x_15 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_15, 0, x_10);
lean_closure_set(x_15, 1, x_8);
lean_inc(x_14);
lean_inc(x_10);
x_16 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_16, 0, x_10);
lean_closure_set(x_16, 1, x_14);
lean_inc(x_10);
lean_inc(x_9);
x_17 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_17, 0, x_9);
lean_closure_set(x_17, 1, x_10);
lean_closure_set(x_17, 2, x_8);
x_18 = l_Lake_EStateT_instFunctor___redArg(x_9);
x_19 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_19, 0, x_10);
lean_ctor_set(x_6, 4, x_15);
lean_ctor_set(x_6, 3, x_16);
lean_ctor_set(x_6, 2, x_17);
lean_ctor_set(x_6, 1, x_19);
lean_ctor_set(x_6, 0, x_18);
lean_ctor_set(x_4, 1, x_14);
x_20 = l_ReaderT_instMonad___redArg(x_4);
x_21 = l_ReaderT_instMonad___redArg(x_20);
x_22 = l_ReaderT_instMonad___redArg(x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1___closed__0;
x_25 = l_Lake_instDataKindUnit;
x_26 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1), 13, 6);
lean_closure_set(x_26, 0, x_3);
lean_closure_set(x_26, 1, x_2);
lean_closure_set(x_26, 2, x_25);
lean_closure_set(x_26, 3, x_23);
lean_closure_set(x_26, 4, x_24);
lean_closure_set(x_26, 5, x_1);
x_27 = l_Lake_Package_keyword;
x_28 = lean_box(1);
x_29 = l_Lake_Package_extraDepFacetConfig___closed__1;
x_30 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_26);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 3, x_29);
x_31 = lean_unbox(x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_31);
x_32 = lean_unbox(x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*4 + 1, x_32);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; 
x_33 = lean_ctor_get(x_4, 1);
x_34 = lean_ctor_get(x_6, 0);
x_35 = lean_ctor_get(x_6, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_6);
lean_inc(x_33);
lean_inc(x_35);
x_36 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_36, 0, x_35);
lean_closure_set(x_36, 1, x_33);
lean_inc(x_33);
lean_inc(x_35);
x_37 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_37, 0, x_35);
lean_closure_set(x_37, 1, x_33);
lean_inc(x_36);
lean_inc(x_35);
x_38 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_38, 0, x_35);
lean_closure_set(x_38, 1, x_36);
lean_inc(x_35);
lean_inc(x_34);
x_39 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_39, 0, x_34);
lean_closure_set(x_39, 1, x_35);
lean_closure_set(x_39, 2, x_33);
x_40 = l_Lake_EStateT_instFunctor___redArg(x_34);
x_41 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_41, 0, x_35);
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_39);
lean_ctor_set(x_42, 3, x_38);
lean_ctor_set(x_42, 4, x_37);
lean_ctor_set(x_4, 1, x_36);
lean_ctor_set(x_4, 0, x_42);
x_43 = l_ReaderT_instMonad___redArg(x_4);
x_44 = l_ReaderT_instMonad___redArg(x_43);
x_45 = l_ReaderT_instMonad___redArg(x_44);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1___closed__0;
x_48 = l_Lake_instDataKindUnit;
x_49 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1), 13, 6);
lean_closure_set(x_49, 0, x_3);
lean_closure_set(x_49, 1, x_2);
lean_closure_set(x_49, 2, x_48);
lean_closure_set(x_49, 3, x_46);
lean_closure_set(x_49, 4, x_47);
lean_closure_set(x_49, 5, x_1);
x_50 = l_Lake_Package_keyword;
x_51 = lean_box(1);
x_52 = l_Lake_Package_extraDepFacetConfig___closed__1;
x_53 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_49);
lean_ctor_set(x_53, 2, x_48);
lean_ctor_set(x_53, 3, x_52);
x_54 = lean_unbox(x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_54);
x_55 = lean_unbox(x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*4 + 1, x_55);
return x_53;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_81; 
x_56 = lean_ctor_get(x_4, 0);
x_57 = lean_ctor_get(x_4, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_4);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 lean_ctor_release(x_56, 2);
 lean_ctor_release(x_56, 3);
 lean_ctor_release(x_56, 4);
 x_60 = x_56;
} else {
 lean_dec_ref(x_56);
 x_60 = lean_box(0);
}
lean_inc(x_57);
lean_inc(x_59);
x_61 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_61, 0, x_59);
lean_closure_set(x_61, 1, x_57);
lean_inc(x_57);
lean_inc(x_59);
x_62 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_62, 0, x_59);
lean_closure_set(x_62, 1, x_57);
lean_inc(x_61);
lean_inc(x_59);
x_63 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_63, 0, x_59);
lean_closure_set(x_63, 1, x_61);
lean_inc(x_59);
lean_inc(x_58);
x_64 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_64, 0, x_58);
lean_closure_set(x_64, 1, x_59);
lean_closure_set(x_64, 2, x_57);
x_65 = l_Lake_EStateT_instFunctor___redArg(x_58);
x_66 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_66, 0, x_59);
if (lean_is_scalar(x_60)) {
 x_67 = lean_alloc_ctor(0, 5, 0);
} else {
 x_67 = x_60;
}
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_67, 2, x_64);
lean_ctor_set(x_67, 3, x_63);
lean_ctor_set(x_67, 4, x_62);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_61);
x_69 = l_ReaderT_instMonad___redArg(x_68);
x_70 = l_ReaderT_instMonad___redArg(x_69);
x_71 = l_ReaderT_instMonad___redArg(x_70);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = l_Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1___closed__0;
x_74 = l_Lake_instDataKindUnit;
x_75 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1), 13, 6);
lean_closure_set(x_75, 0, x_3);
lean_closure_set(x_75, 1, x_2);
lean_closure_set(x_75, 2, x_74);
lean_closure_set(x_75, 3, x_72);
lean_closure_set(x_75, 4, x_73);
lean_closure_set(x_75, 5, x_1);
x_76 = l_Lake_Package_keyword;
x_77 = lean_box(1);
x_78 = l_Lake_Package_extraDepFacetConfig___closed__1;
x_79 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_75);
lean_ctor_set(x_79, 2, x_74);
lean_ctor_set(x_79, 3, x_78);
x_80 = lean_unbox(x_77);
lean_ctor_set_uint8(x_79, sizeof(void*)*4, x_80);
x_81 = lean_unbox(x_77);
lean_ctor_set_uint8(x_79, sizeof(void*)*4 + 1, x_81);
return x_79;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__0;
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; 
x_10 = lean_ctor_get(x_6, 1);
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 1);
x_13 = lean_ctor_get(x_8, 4);
lean_dec(x_13);
x_14 = lean_ctor_get(x_8, 3);
lean_dec(x_14);
x_15 = lean_ctor_get(x_8, 2);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_12);
x_16 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_16, 0, x_12);
lean_closure_set(x_16, 1, x_10);
lean_inc(x_10);
lean_inc(x_12);
x_17 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_17, 0, x_12);
lean_closure_set(x_17, 1, x_10);
lean_inc(x_16);
lean_inc(x_12);
x_18 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_18, 0, x_12);
lean_closure_set(x_18, 1, x_16);
lean_inc(x_12);
lean_inc(x_11);
x_19 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_19, 0, x_11);
lean_closure_set(x_19, 1, x_12);
lean_closure_set(x_19, 2, x_10);
x_20 = l_Lake_EStateT_instFunctor___redArg(x_11);
x_21 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_21, 0, x_12);
lean_ctor_set(x_8, 4, x_17);
lean_ctor_set(x_8, 3, x_18);
lean_ctor_set(x_8, 2, x_19);
lean_ctor_set(x_8, 1, x_21);
lean_ctor_set(x_8, 0, x_20);
lean_ctor_set(x_6, 1, x_16);
x_22 = l_ReaderT_instMonad___redArg(x_6);
x_23 = l_ReaderT_instMonad___redArg(x_22);
x_24 = l_ReaderT_instMonad___redArg(x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1___closed__0;
x_27 = l_Lake_instDataKindUnit;
x_28 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1), 13, 6);
lean_closure_set(x_28, 0, x_3);
lean_closure_set(x_28, 1, x_2);
lean_closure_set(x_28, 2, x_27);
lean_closure_set(x_28, 3, x_25);
lean_closure_set(x_28, 4, x_26);
lean_closure_set(x_28, 5, x_1);
x_29 = l_Lake_Package_keyword;
x_30 = lean_box(1);
x_31 = l_Lake_Package_extraDepFacetConfig___closed__1;
x_32 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_28);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 3, x_31);
x_33 = lean_unbox(x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*4, x_33);
x_34 = lean_unbox(x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*4 + 1, x_34);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_57; 
x_35 = lean_ctor_get(x_6, 1);
x_36 = lean_ctor_get(x_8, 0);
x_37 = lean_ctor_get(x_8, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_8);
lean_inc(x_35);
lean_inc(x_37);
x_38 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_38, 0, x_37);
lean_closure_set(x_38, 1, x_35);
lean_inc(x_35);
lean_inc(x_37);
x_39 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_39, 0, x_37);
lean_closure_set(x_39, 1, x_35);
lean_inc(x_38);
lean_inc(x_37);
x_40 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_40, 0, x_37);
lean_closure_set(x_40, 1, x_38);
lean_inc(x_37);
lean_inc(x_36);
x_41 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_41, 0, x_36);
lean_closure_set(x_41, 1, x_37);
lean_closure_set(x_41, 2, x_35);
x_42 = l_Lake_EStateT_instFunctor___redArg(x_36);
x_43 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_43, 0, x_37);
x_44 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_41);
lean_ctor_set(x_44, 3, x_40);
lean_ctor_set(x_44, 4, x_39);
lean_ctor_set(x_6, 1, x_38);
lean_ctor_set(x_6, 0, x_44);
x_45 = l_ReaderT_instMonad___redArg(x_6);
x_46 = l_ReaderT_instMonad___redArg(x_45);
x_47 = l_ReaderT_instMonad___redArg(x_46);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1___closed__0;
x_50 = l_Lake_instDataKindUnit;
x_51 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1), 13, 6);
lean_closure_set(x_51, 0, x_3);
lean_closure_set(x_51, 1, x_2);
lean_closure_set(x_51, 2, x_50);
lean_closure_set(x_51, 3, x_48);
lean_closure_set(x_51, 4, x_49);
lean_closure_set(x_51, 5, x_1);
x_52 = l_Lake_Package_keyword;
x_53 = lean_box(1);
x_54 = l_Lake_Package_extraDepFacetConfig___closed__1;
x_55 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_51);
lean_ctor_set(x_55, 2, x_50);
lean_ctor_set(x_55, 3, x_54);
x_56 = lean_unbox(x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*4, x_56);
x_57 = lean_unbox(x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*4 + 1, x_57);
return x_55;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_83; 
x_58 = lean_ctor_get(x_6, 0);
x_59 = lean_ctor_get(x_6, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_6);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 lean_ctor_release(x_58, 3);
 lean_ctor_release(x_58, 4);
 x_62 = x_58;
} else {
 lean_dec_ref(x_58);
 x_62 = lean_box(0);
}
lean_inc(x_59);
lean_inc(x_61);
x_63 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_63, 0, x_61);
lean_closure_set(x_63, 1, x_59);
lean_inc(x_59);
lean_inc(x_61);
x_64 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_64, 0, x_61);
lean_closure_set(x_64, 1, x_59);
lean_inc(x_63);
lean_inc(x_61);
x_65 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_65, 0, x_61);
lean_closure_set(x_65, 1, x_63);
lean_inc(x_61);
lean_inc(x_60);
x_66 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_66, 0, x_60);
lean_closure_set(x_66, 1, x_61);
lean_closure_set(x_66, 2, x_59);
x_67 = l_Lake_EStateT_instFunctor___redArg(x_60);
x_68 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_68, 0, x_61);
if (lean_is_scalar(x_62)) {
 x_69 = lean_alloc_ctor(0, 5, 0);
} else {
 x_69 = x_62;
}
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_69, 2, x_66);
lean_ctor_set(x_69, 3, x_65);
lean_ctor_set(x_69, 4, x_64);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_63);
x_71 = l_ReaderT_instMonad___redArg(x_70);
x_72 = l_ReaderT_instMonad___redArg(x_71);
x_73 = l_ReaderT_instMonad___redArg(x_72);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = l_Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1___closed__0;
x_76 = l_Lake_instDataKindUnit;
x_77 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1), 13, 6);
lean_closure_set(x_77, 0, x_3);
lean_closure_set(x_77, 1, x_2);
lean_closure_set(x_77, 2, x_76);
lean_closure_set(x_77, 3, x_74);
lean_closure_set(x_77, 4, x_75);
lean_closure_set(x_77, 5, x_1);
x_78 = l_Lake_Package_keyword;
x_79 = lean_box(1);
x_80 = l_Lake_Package_extraDepFacetConfig___closed__1;
x_81 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_77);
lean_ctor_set(x_81, 2, x_76);
lean_ctor_set(x_81, 3, x_80);
x_82 = lean_unbox(x_79);
lean_ctor_set_uint8(x_81, sizeof(void*)*4, x_82);
x_83 = lean_unbox(x_79);
lean_ctor_set_uint8(x_81, sizeof(void*)*4 + 1, x_83);
return x_81;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to fetch build cache", 27, 27);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
if (x_3 == 0)
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_7, 0);
x_39 = lean_ctor_get_uint8(x_38, sizeof(void*)*1 + 3);
x_40 = lean_box(2);
x_41 = lean_unbox(x_40);
x_42 = l_Lake_instDecidableEqVerbosity(x_39, x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_2);
lean_dec(x_1);
x_43 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0;
x_10 = x_43;
x_11 = x_8;
x_12 = x_9;
goto block_37;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_44 = lean_box(x_3);
x_45 = lean_alloc_closure((void*)(l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__1___boxed), 2, 1);
lean_closure_set(x_45, 0, x_44);
x_46 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1;
lean_inc(x_45);
x_47 = l_Lean_Name_toString(x_1, x_42, x_45);
x_48 = lean_string_append(x_46, x_47);
lean_dec(x_47);
x_49 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_50 = lean_string_append(x_48, x_49);
x_51 = l_Lake_Name_eraseHead(x_2);
x_52 = l_Lean_Name_toString(x_51, x_42, x_45);
x_53 = lean_string_append(x_50, x_52);
lean_dec(x_52);
x_54 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3;
x_55 = lean_string_append(x_53, x_54);
x_10 = x_55;
x_11 = x_8;
x_12 = x_9;
goto block_37;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_2);
lean_dec(x_1);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_8);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_9);
return x_58;
}
block_37:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = l_Lake_Package_buildCacheFacetConfig___lam__2___closed__0;
x_16 = lean_string_append(x_15, x_10);
lean_dec(x_10);
x_17 = lean_box(3);
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_unbox(x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_19);
x_20 = lean_array_get_size(x_14);
x_21 = lean_array_push(x_14, x_18);
lean_ctor_set(x_11, 0, x_21);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_11);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_12);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_inc(x_24);
lean_dec(x_11);
x_27 = l_Lake_Package_buildCacheFacetConfig___lam__2___closed__0;
x_28 = lean_string_append(x_27, x_10);
lean_dec(x_10);
x_29 = lean_box(3);
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_unbox(x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_31);
x_32 = lean_array_get_size(x_24);
x_33 = lean_array_push(x_24, x_30);
x_34 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_26);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_25);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_12);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_3);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = lean_apply_6(x_3, x_1, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_box(0);
x_16 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__2;
x_17 = lean_unbox(x_15);
x_18 = l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg(x_13, x_2, x_14, x_17, x_3, x_4, x_5, x_6, x_16, x_11);
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_box(0);
x_28 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__2;
x_29 = lean_unbox(x_27);
x_30 = l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg(x_24, x_2, x_26, x_29, x_3, x_4, x_5, x_6, x_28, x_11);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_inc(x_1);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__2___boxed), 9, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_1);
lean_inc(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = l_Lake_Package_keyword;
x_15 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_4);
lean_ctor_set(x_15, 3, x_1);
x_16 = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__0), 8, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_12);
lean_inc(x_8);
x_17 = l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1(x_16, x_5, x_6, x_7, x_8, x_9, x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_24 = lean_ctor_get(x_19, 2);
lean_dec(x_24);
x_25 = lean_ctor_get(x_8, 3);
lean_inc(x_25);
lean_dec(x_8);
x_26 = lean_st_ref_take(x_25, x_20);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_box(1);
x_30 = lean_unbox(x_29);
lean_inc(x_2);
x_31 = l_Lean_Name_toString(x_11, x_30, x_2);
x_32 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_33 = lean_string_append(x_31, x_32);
x_34 = l_Lake_Name_eraseHead(x_3);
x_35 = lean_unbox(x_29);
x_36 = l_Lean_Name_toString(x_34, x_35, x_2);
x_37 = lean_string_append(x_33, x_36);
lean_dec(x_36);
x_38 = lean_box(0);
lean_ctor_set(x_19, 2, x_37);
x_39 = lean_unbox(x_38);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_39);
lean_inc(x_19);
x_40 = l_Lake_Job_toOpaque___redArg(x_19);
x_41 = lean_array_push(x_27, x_40);
x_42 = lean_st_ref_set(x_25, x_41, x_28);
lean_dec(x_25);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = l_Lake_Job_renew___redArg(x_19);
lean_ctor_set(x_18, 0, x_45);
lean_ctor_set(x_42, 0, x_18);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = l_Lake_Job_renew___redArg(x_19);
lean_ctor_set(x_18, 0, x_47);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_18);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_49 = lean_ctor_get(x_19, 0);
x_50 = lean_ctor_get(x_19, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_19);
x_51 = lean_ctor_get(x_8, 3);
lean_inc(x_51);
lean_dec(x_8);
x_52 = lean_st_ref_take(x_51, x_20);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_box(1);
x_56 = lean_unbox(x_55);
lean_inc(x_2);
x_57 = l_Lean_Name_toString(x_11, x_56, x_2);
x_58 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_59 = lean_string_append(x_57, x_58);
x_60 = l_Lake_Name_eraseHead(x_3);
x_61 = lean_unbox(x_55);
x_62 = l_Lean_Name_toString(x_60, x_61, x_2);
x_63 = lean_string_append(x_59, x_62);
lean_dec(x_62);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_65, 0, x_49);
lean_ctor_set(x_65, 1, x_50);
lean_ctor_set(x_65, 2, x_63);
x_66 = lean_unbox(x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*3, x_66);
lean_inc(x_65);
x_67 = l_Lake_Job_toOpaque___redArg(x_65);
x_68 = lean_array_push(x_53, x_67);
x_69 = lean_st_ref_set(x_51, x_68, x_54);
lean_dec(x_51);
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
x_72 = l_Lake_Job_renew___redArg(x_65);
lean_ctor_set(x_18, 0, x_72);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_18);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_74 = lean_ctor_get(x_18, 1);
lean_inc(x_74);
lean_dec(x_18);
x_75 = lean_ctor_get(x_19, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_19, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 x_77 = x_19;
} else {
 lean_dec_ref(x_19);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_8, 3);
lean_inc(x_78);
lean_dec(x_8);
x_79 = lean_st_ref_take(x_78, x_20);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_box(1);
x_83 = lean_unbox(x_82);
lean_inc(x_2);
x_84 = l_Lean_Name_toString(x_11, x_83, x_2);
x_85 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_86 = lean_string_append(x_84, x_85);
x_87 = l_Lake_Name_eraseHead(x_3);
x_88 = lean_unbox(x_82);
x_89 = l_Lean_Name_toString(x_87, x_88, x_2);
x_90 = lean_string_append(x_86, x_89);
lean_dec(x_89);
x_91 = lean_box(0);
if (lean_is_scalar(x_77)) {
 x_92 = lean_alloc_ctor(0, 3, 1);
} else {
 x_92 = x_77;
}
lean_ctor_set(x_92, 0, x_75);
lean_ctor_set(x_92, 1, x_76);
lean_ctor_set(x_92, 2, x_90);
x_93 = lean_unbox(x_91);
lean_ctor_set_uint8(x_92, sizeof(void*)*3, x_93);
lean_inc(x_92);
x_94 = l_Lake_Job_toOpaque___redArg(x_92);
x_95 = lean_array_push(x_80, x_94);
x_96 = lean_st_ref_set(x_78, x_95, x_81);
lean_dec(x_78);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_98 = x_96;
} else {
 lean_dec_ref(x_96);
 x_98 = lean_box(0);
}
x_99 = l_Lake_Job_renew___redArg(x_92);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_74);
if (lean_is_scalar(x_98)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_98;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_97);
return x_101;
}
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_1 = l_Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1___closed__0;
x_2 = l_Lake_Package_buildCacheFacet;
x_3 = l_Lake_Package_optBuildCacheFacet;
x_4 = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__1), 10, 3);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_1);
lean_closure_set(x_4, 2, x_2);
x_5 = l_Lake_instDataKindUnit;
x_6 = l_Lake_Package_keyword;
x_7 = lean_box(1);
x_8 = l_Lake_Package_extraDepFacetConfig___closed__1;
x_9 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_5);
lean_ctor_set(x_9, 3, x_8);
x_10 = lean_unbox(x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_10);
x_11 = lean_unbox(x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*4 + 1, x_11);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lake_Package_buildCacheFacetConfig___lam__2(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
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
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
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
x_103 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__3;
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
x_113 = l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__1(x_99, x_111, x_2, x_3, x_4, x_5, x_112, x_12);
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
x_115 = l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__1(x_99, x_114, x_2, x_3, x_4, x_5, x_97, x_12);
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
x_21 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__0;
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_box(0);
x_24 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__2;
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
x_51 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__0), 2, 1);
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
x_60 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__0), 2, 1);
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
x_71 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__0), 2, 1);
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
x_88 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__0), 2, 1);
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
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".lake", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___lam__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("build.barrel", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_16; lean_object* x_17; lean_object* x_35; lean_object* x_36; 
lean_inc(x_6);
lean_inc(x_1);
x_35 = l_Lake_Package_getBarrelUrl___redArg(x_1, x_6, x_7, x_8);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
x_41 = l_Lake_Package_optBarrelFacetConfig___lam__2___closed__0;
x_42 = l_Lake_joinRelative(x_40, x_41);
x_43 = l_Lake_Package_optBarrelFacetConfig___lam__2___closed__1;
x_44 = l_Lake_joinRelative(x_42, x_43);
x_45 = l_Lake_Package_fetchBuildArchive(x_1, x_38, x_44, x_2, x_3, x_4, x_5, x_6, x_39, x_37);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_box(1);
x_50 = lean_unbox(x_49);
x_9 = x_50;
x_10 = x_48;
x_11 = x_47;
goto block_15;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
lean_dec(x_45);
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_dec(x_46);
x_16 = x_52;
x_17 = x_51;
goto block_34;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_ctor_get(x_35, 1);
lean_inc(x_53);
lean_dec(x_35);
x_54 = lean_ctor_get(x_36, 1);
lean_inc(x_54);
lean_dec(x_36);
x_16 = x_54;
x_17 = x_53;
goto block_34;
}
block_15:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_box(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
block_34:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get_uint8(x_16, sizeof(void*)*2);
x_20 = lean_box(2);
x_21 = lean_unbox(x_20);
x_22 = l_Lake_JobAction_merge(x_19, x_21);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_22);
x_23 = lean_box(0);
x_24 = lean_unbox(x_23);
x_9 = x_24;
x_10 = x_16;
x_11 = x_17;
goto block_15;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get_uint8(x_16, sizeof(void*)*2);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_25);
lean_dec(x_16);
x_28 = lean_box(2);
x_29 = lean_unbox(x_28);
x_30 = l_Lake_JobAction_merge(x_26, x_29);
x_31 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_27);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_30);
x_32 = lean_box(0);
x_33 = lean_unbox(x_32);
x_9 = x_33;
x_10 = x_31;
x_11 = x_17;
goto block_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_24; uint8_t x_25; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_14 = x_10;
} else {
 lean_dec_ref(x_10);
 x_14 = lean_box(0);
}
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
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_24 = lean_string_utf8_byte_size(x_17);
x_25 = lean_nat_dec_eq(x_24, x_8);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__3;
x_29 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_17, x_24, x_8);
x_30 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_17, x_29, x_24);
x_31 = lean_string_utf8_extract(x_17, x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_17);
x_32 = lean_string_append(x_28, x_31);
lean_dec(x_31);
x_33 = lean_box(1);
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
x_35 = lean_unbox(x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_35);
x_36 = lean_array_push(x_27, x_34);
lean_ctor_set(x_15, 0, x_36);
x_19 = x_15;
x_20 = x_13;
goto block_23;
}
else
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_37 = lean_ctor_get(x_15, 0);
x_38 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
x_39 = lean_ctor_get(x_15, 1);
lean_inc(x_39);
lean_inc(x_37);
lean_dec(x_15);
x_40 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__3;
x_41 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_17, x_24, x_8);
x_42 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_17, x_41, x_24);
x_43 = lean_string_utf8_extract(x_17, x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_17);
x_44 = lean_string_append(x_40, x_43);
lean_dec(x_43);
x_45 = lean_box(1);
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_44);
x_47 = lean_unbox(x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_47);
x_48 = lean_array_push(x_37, x_46);
x_49 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_39);
lean_ctor_set_uint8(x_49, sizeof(void*)*2, x_38);
x_19 = x_49;
x_20 = x_13;
goto block_23;
}
}
else
{
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_8);
x_19 = x_15;
x_20 = x_13;
goto block_23;
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
if (lean_is_scalar(x_16)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_16;
}
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
if (lean_is_scalar(x_14)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_14;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_50; 
lean_dec(x_8);
x_50 = !lean_is_exclusive(x_10);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_10, 0);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_11);
if (x_52 == 0)
{
return x_10;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_11, 0);
x_54 = lean_ctor_get(x_11, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_11);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_10, 0, x_55);
return x_10;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_10, 1);
lean_inc(x_56);
lean_dec(x_10);
x_57 = lean_ctor_get(x_11, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_11, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_59 = x_11;
} else {
 lean_dec_ref(x_11);
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
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_11 = lean_mk_empty_array_with_capacity(x_1);
x_12 = lean_box(0);
x_13 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__2;
x_14 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_unbox(x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_15);
x_16 = lean_box(1);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__0___boxed), 9, 8);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_5);
lean_closure_set(x_17, 3, x_6);
lean_closure_set(x_17, 4, x_7);
lean_closure_set(x_17, 5, x_8);
lean_closure_set(x_17, 6, x_14);
lean_closure_set(x_17, 7, x_1);
x_18 = lean_io_as_task(x_17, x_1, x_10);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set(x_22, 2, x_4);
x_23 = lean_unbox(x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_9);
lean_ctor_set(x_18, 0, x_24);
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_3);
lean_ctor_set(x_28, 2, x_4);
x_29 = lean_unbox(x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_29);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_9);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_inc(x_5);
x_12 = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__2), 8, 2);
lean_closure_set(x_12, 0, x_5);
lean_closure_set(x_12, 1, x_1);
x_13 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__0;
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__1), 10, 4);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_12);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_13);
lean_inc(x_9);
x_16 = l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0(x_15, x_6, x_7, x_8, x_9, x_10, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_23 = lean_ctor_get(x_18, 2);
lean_dec(x_23);
x_24 = lean_ctor_get(x_9, 3);
lean_inc(x_24);
lean_dec(x_9);
x_25 = lean_st_ref_take(x_24, x_19);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_5, 0);
lean_inc(x_28);
lean_dec(x_5);
x_29 = lean_box(1);
x_30 = lean_unbox(x_29);
lean_inc(x_3);
x_31 = l_Lean_Name_toString(x_28, x_30, x_3);
x_32 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_33 = lean_string_append(x_31, x_32);
x_34 = l_Lake_Name_eraseHead(x_4);
x_35 = lean_unbox(x_29);
x_36 = l_Lean_Name_toString(x_34, x_35, x_3);
x_37 = lean_string_append(x_33, x_36);
lean_dec(x_36);
lean_ctor_set(x_18, 2, x_37);
x_38 = lean_unbox(x_29);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_38);
lean_inc(x_18);
x_39 = l_Lake_Job_toOpaque___redArg(x_18);
x_40 = lean_array_push(x_26, x_39);
x_41 = lean_st_ref_set(x_24, x_40, x_27);
lean_dec(x_24);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
x_44 = l_Lake_Job_renew___redArg(x_18);
lean_ctor_set(x_17, 0, x_44);
lean_ctor_set(x_41, 0, x_17);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = l_Lake_Job_renew___redArg(x_18);
lean_ctor_set(x_17, 0, x_46);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_17);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_48 = lean_ctor_get(x_18, 0);
x_49 = lean_ctor_get(x_18, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_18);
x_50 = lean_ctor_get(x_9, 3);
lean_inc(x_50);
lean_dec(x_9);
x_51 = lean_st_ref_take(x_50, x_19);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_5, 0);
lean_inc(x_54);
lean_dec(x_5);
x_55 = lean_box(1);
x_56 = lean_unbox(x_55);
lean_inc(x_3);
x_57 = l_Lean_Name_toString(x_54, x_56, x_3);
x_58 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_59 = lean_string_append(x_57, x_58);
x_60 = l_Lake_Name_eraseHead(x_4);
x_61 = lean_unbox(x_55);
x_62 = l_Lean_Name_toString(x_60, x_61, x_3);
x_63 = lean_string_append(x_59, x_62);
lean_dec(x_62);
x_64 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_64, 0, x_48);
lean_ctor_set(x_64, 1, x_49);
lean_ctor_set(x_64, 2, x_63);
x_65 = lean_unbox(x_55);
lean_ctor_set_uint8(x_64, sizeof(void*)*3, x_65);
lean_inc(x_64);
x_66 = l_Lake_Job_toOpaque___redArg(x_64);
x_67 = lean_array_push(x_52, x_66);
x_68 = lean_st_ref_set(x_50, x_67, x_53);
lean_dec(x_50);
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
x_71 = l_Lake_Job_renew___redArg(x_64);
lean_ctor_set(x_17, 0, x_71);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_17);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_73 = lean_ctor_get(x_17, 1);
lean_inc(x_73);
lean_dec(x_17);
x_74 = lean_ctor_get(x_18, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_18, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 x_76 = x_18;
} else {
 lean_dec_ref(x_18);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_9, 3);
lean_inc(x_77);
lean_dec(x_9);
x_78 = lean_st_ref_take(x_77, x_19);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_ctor_get(x_5, 0);
lean_inc(x_81);
lean_dec(x_5);
x_82 = lean_box(1);
x_83 = lean_unbox(x_82);
lean_inc(x_3);
x_84 = l_Lean_Name_toString(x_81, x_83, x_3);
x_85 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_86 = lean_string_append(x_84, x_85);
x_87 = l_Lake_Name_eraseHead(x_4);
x_88 = lean_unbox(x_82);
x_89 = l_Lean_Name_toString(x_87, x_88, x_3);
x_90 = lean_string_append(x_86, x_89);
lean_dec(x_89);
if (lean_is_scalar(x_76)) {
 x_91 = lean_alloc_ctor(0, 3, 1);
} else {
 x_91 = x_76;
}
lean_ctor_set(x_91, 0, x_74);
lean_ctor_set(x_91, 1, x_75);
lean_ctor_set(x_91, 2, x_90);
x_92 = lean_unbox(x_82);
lean_ctor_set_uint8(x_91, sizeof(void*)*3, x_92);
lean_inc(x_91);
x_93 = l_Lake_Job_toOpaque___redArg(x_91);
x_94 = lean_array_push(x_79, x_93);
x_95 = lean_st_ref_set(x_77, x_94, x_80);
lean_dec(x_77);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_97 = x_95;
} else {
 lean_dec_ref(x_95);
 x_97 = lean_box(0);
}
x_98 = l_Lake_Job_renew___redArg(x_91);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_73);
if (lean_is_scalar(x_97)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_97;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_96);
return x_100;
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
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_1 = l_Lake_Package_optBarrelFacetConfig___closed__0;
x_2 = l_Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1___closed__0;
x_3 = l_Lake_Package_optReservoirBarrelFacet;
x_4 = l_Lake_Reservoir_lakeHeaders;
x_5 = l_Lake_instDataKindBool;
x_6 = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__3), 11, 4);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_3);
x_7 = l_Lake_Package_keyword;
x_8 = lean_box(1);
x_9 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_5);
lean_ctor_set(x_9, 3, x_1);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_10);
x_11 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*4 + 1, x_11);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lake_Package_optBarrelFacetConfig___lam__0(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to fetch Reservoir build", 31, 31);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
if (x_3 == 0)
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_7, 0);
x_39 = lean_ctor_get_uint8(x_38, sizeof(void*)*1 + 3);
x_40 = lean_box(2);
x_41 = lean_unbox(x_40);
x_42 = l_Lake_instDecidableEqVerbosity(x_39, x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_2);
lean_dec(x_1);
x_43 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0;
x_10 = x_43;
x_11 = x_8;
x_12 = x_9;
goto block_37;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_44 = lean_box(x_3);
x_45 = lean_alloc_closure((void*)(l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__1___boxed), 2, 1);
lean_closure_set(x_45, 0, x_44);
x_46 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1;
lean_inc(x_45);
x_47 = l_Lean_Name_toString(x_1, x_42, x_45);
x_48 = lean_string_append(x_46, x_47);
lean_dec(x_47);
x_49 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_50 = lean_string_append(x_48, x_49);
x_51 = l_Lake_Name_eraseHead(x_2);
x_52 = l_Lean_Name_toString(x_51, x_42, x_45);
x_53 = lean_string_append(x_50, x_52);
lean_dec(x_52);
x_54 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3;
x_55 = lean_string_append(x_53, x_54);
x_10 = x_55;
x_11 = x_8;
x_12 = x_9;
goto block_37;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_2);
lean_dec(x_1);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_8);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_9);
return x_58;
}
block_37:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = l_Lake_Package_barrelFacetConfig___lam__2___closed__0;
x_16 = lean_string_append(x_15, x_10);
lean_dec(x_10);
x_17 = lean_box(3);
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_unbox(x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_19);
x_20 = lean_array_get_size(x_14);
x_21 = lean_array_push(x_14, x_18);
lean_ctor_set(x_11, 0, x_21);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_11);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_12);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_inc(x_24);
lean_dec(x_11);
x_27 = l_Lake_Package_barrelFacetConfig___lam__2___closed__0;
x_28 = lean_string_append(x_27, x_10);
lean_dec(x_10);
x_29 = lean_box(3);
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_unbox(x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_31);
x_32 = lean_array_get_size(x_24);
x_33 = lean_array_push(x_24, x_30);
x_34 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_26);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_25);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_12);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_inc(x_1);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__2___boxed), 9, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_1);
lean_inc(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = l_Lake_Package_keyword;
x_15 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_4);
lean_ctor_set(x_15, 3, x_1);
x_16 = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__0), 8, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_12);
lean_inc(x_8);
x_17 = l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1(x_16, x_5, x_6, x_7, x_8, x_9, x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_24 = lean_ctor_get(x_19, 2);
lean_dec(x_24);
x_25 = lean_ctor_get(x_8, 3);
lean_inc(x_25);
lean_dec(x_8);
x_26 = lean_st_ref_take(x_25, x_20);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_box(1);
x_30 = lean_unbox(x_29);
lean_inc(x_2);
x_31 = l_Lean_Name_toString(x_11, x_30, x_2);
x_32 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_33 = lean_string_append(x_31, x_32);
x_34 = l_Lake_Name_eraseHead(x_3);
x_35 = lean_unbox(x_29);
x_36 = l_Lean_Name_toString(x_34, x_35, x_2);
x_37 = lean_string_append(x_33, x_36);
lean_dec(x_36);
x_38 = lean_box(0);
lean_ctor_set(x_19, 2, x_37);
x_39 = lean_unbox(x_38);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_39);
lean_inc(x_19);
x_40 = l_Lake_Job_toOpaque___redArg(x_19);
x_41 = lean_array_push(x_27, x_40);
x_42 = lean_st_ref_set(x_25, x_41, x_28);
lean_dec(x_25);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = l_Lake_Job_renew___redArg(x_19);
lean_ctor_set(x_18, 0, x_45);
lean_ctor_set(x_42, 0, x_18);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = l_Lake_Job_renew___redArg(x_19);
lean_ctor_set(x_18, 0, x_47);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_18);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_49 = lean_ctor_get(x_19, 0);
x_50 = lean_ctor_get(x_19, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_19);
x_51 = lean_ctor_get(x_8, 3);
lean_inc(x_51);
lean_dec(x_8);
x_52 = lean_st_ref_take(x_51, x_20);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_box(1);
x_56 = lean_unbox(x_55);
lean_inc(x_2);
x_57 = l_Lean_Name_toString(x_11, x_56, x_2);
x_58 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_59 = lean_string_append(x_57, x_58);
x_60 = l_Lake_Name_eraseHead(x_3);
x_61 = lean_unbox(x_55);
x_62 = l_Lean_Name_toString(x_60, x_61, x_2);
x_63 = lean_string_append(x_59, x_62);
lean_dec(x_62);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_65, 0, x_49);
lean_ctor_set(x_65, 1, x_50);
lean_ctor_set(x_65, 2, x_63);
x_66 = lean_unbox(x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*3, x_66);
lean_inc(x_65);
x_67 = l_Lake_Job_toOpaque___redArg(x_65);
x_68 = lean_array_push(x_53, x_67);
x_69 = lean_st_ref_set(x_51, x_68, x_54);
lean_dec(x_51);
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
x_72 = l_Lake_Job_renew___redArg(x_65);
lean_ctor_set(x_18, 0, x_72);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_18);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_74 = lean_ctor_get(x_18, 1);
lean_inc(x_74);
lean_dec(x_18);
x_75 = lean_ctor_get(x_19, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_19, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 x_77 = x_19;
} else {
 lean_dec_ref(x_19);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_8, 3);
lean_inc(x_78);
lean_dec(x_8);
x_79 = lean_st_ref_take(x_78, x_20);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_box(1);
x_83 = lean_unbox(x_82);
lean_inc(x_2);
x_84 = l_Lean_Name_toString(x_11, x_83, x_2);
x_85 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_86 = lean_string_append(x_84, x_85);
x_87 = l_Lake_Name_eraseHead(x_3);
x_88 = lean_unbox(x_82);
x_89 = l_Lean_Name_toString(x_87, x_88, x_2);
x_90 = lean_string_append(x_86, x_89);
lean_dec(x_89);
x_91 = lean_box(0);
if (lean_is_scalar(x_77)) {
 x_92 = lean_alloc_ctor(0, 3, 1);
} else {
 x_92 = x_77;
}
lean_ctor_set(x_92, 0, x_75);
lean_ctor_set(x_92, 1, x_76);
lean_ctor_set(x_92, 2, x_90);
x_93 = lean_unbox(x_91);
lean_ctor_set_uint8(x_92, sizeof(void*)*3, x_93);
lean_inc(x_92);
x_94 = l_Lake_Job_toOpaque___redArg(x_92);
x_95 = lean_array_push(x_80, x_94);
x_96 = lean_st_ref_set(x_78, x_95, x_81);
lean_dec(x_78);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_98 = x_96;
} else {
 lean_dec_ref(x_96);
 x_98 = lean_box(0);
}
x_99 = l_Lake_Job_renew___redArg(x_92);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_74);
if (lean_is_scalar(x_98)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_98;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_97);
return x_101;
}
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_1 = l_Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1___closed__0;
x_2 = l_Lake_Package_reservoirBarrelFacet;
x_3 = l_Lake_Package_optReservoirBarrelFacet;
x_4 = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__1), 10, 3);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_1);
lean_closure_set(x_4, 2, x_2);
x_5 = l_Lake_instDataKindUnit;
x_6 = l_Lake_Package_keyword;
x_7 = lean_box(1);
x_8 = l_Lake_Package_extraDepFacetConfig___closed__1;
x_9 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_5);
lean_ctor_set(x_9, 3, x_8);
x_10 = lean_unbox(x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_10);
x_11 = lean_unbox(x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*4 + 1, x_11);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lake_Package_barrelFacetConfig___lam__2(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_16; lean_object* x_17; lean_object* x_35; lean_object* x_36; 
lean_inc(x_1);
x_35 = l_Lake_Package_getReleaseUrl___redArg(x_1, x_7, x_8);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 16);
lean_inc(x_41);
x_42 = l_Lake_Package_optBarrelFacetConfig___lam__2___closed__0;
x_43 = l_Lake_joinRelative(x_40, x_42);
x_44 = l_Lake_joinRelative(x_43, x_41);
lean_dec(x_41);
x_45 = l_Lake_Package_fetchBuildArchive(x_1, x_38, x_44, x_2, x_3, x_4, x_5, x_6, x_39, x_37);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_box(1);
x_50 = lean_unbox(x_49);
x_9 = x_50;
x_10 = x_48;
x_11 = x_47;
goto block_15;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
lean_dec(x_45);
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_dec(x_46);
x_16 = x_52;
x_17 = x_51;
goto block_34;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_ctor_get(x_35, 1);
lean_inc(x_53);
lean_dec(x_35);
x_54 = lean_ctor_get(x_36, 1);
lean_inc(x_54);
lean_dec(x_36);
x_16 = x_54;
x_17 = x_53;
goto block_34;
}
block_15:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_box(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
block_34:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get_uint8(x_16, sizeof(void*)*2);
x_20 = lean_box(2);
x_21 = lean_unbox(x_20);
x_22 = l_Lake_JobAction_merge(x_19, x_21);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_22);
x_23 = lean_box(0);
x_24 = lean_unbox(x_23);
x_9 = x_24;
x_10 = x_16;
x_11 = x_17;
goto block_15;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get_uint8(x_16, sizeof(void*)*2);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_25);
lean_dec(x_16);
x_28 = lean_box(2);
x_29 = lean_unbox(x_28);
x_30 = l_Lake_JobAction_merge(x_26, x_29);
x_31 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_27);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_30);
x_32 = lean_box(0);
x_33 = lean_unbox(x_32);
x_9 = x_33;
x_10 = x_31;
x_11 = x_17;
goto block_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_inc(x_6);
x_13 = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__2), 8, 2);
lean_closure_set(x_13, 0, x_6);
lean_closure_set(x_13, 1, x_1);
x_14 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__0;
x_15 = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__1), 10, 4);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_14);
lean_inc(x_10);
x_16 = l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0(x_15, x_7, x_8, x_9, x_10, x_11, x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_23 = lean_ctor_get(x_18, 2);
lean_dec(x_23);
x_24 = lean_ctor_get(x_10, 3);
lean_inc(x_24);
lean_dec(x_10);
x_25 = lean_st_ref_take(x_24, x_19);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_6, 0);
lean_inc(x_28);
lean_dec(x_6);
x_29 = lean_box(1);
x_30 = lean_unbox(x_29);
lean_inc(x_4);
x_31 = l_Lean_Name_toString(x_28, x_30, x_4);
x_32 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_33 = lean_string_append(x_31, x_32);
x_34 = l_Lake_Name_eraseHead(x_5);
x_35 = lean_unbox(x_29);
x_36 = l_Lean_Name_toString(x_34, x_35, x_4);
x_37 = lean_string_append(x_33, x_36);
lean_dec(x_36);
lean_ctor_set(x_18, 2, x_37);
x_38 = lean_unbox(x_29);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_38);
lean_inc(x_18);
x_39 = l_Lake_Job_toOpaque___redArg(x_18);
x_40 = lean_array_push(x_26, x_39);
x_41 = lean_st_ref_set(x_24, x_40, x_27);
lean_dec(x_24);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
x_44 = l_Lake_Job_renew___redArg(x_18);
lean_ctor_set(x_17, 0, x_44);
lean_ctor_set(x_41, 0, x_17);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = l_Lake_Job_renew___redArg(x_18);
lean_ctor_set(x_17, 0, x_46);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_17);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_48 = lean_ctor_get(x_18, 0);
x_49 = lean_ctor_get(x_18, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_18);
x_50 = lean_ctor_get(x_10, 3);
lean_inc(x_50);
lean_dec(x_10);
x_51 = lean_st_ref_take(x_50, x_19);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_6, 0);
lean_inc(x_54);
lean_dec(x_6);
x_55 = lean_box(1);
x_56 = lean_unbox(x_55);
lean_inc(x_4);
x_57 = l_Lean_Name_toString(x_54, x_56, x_4);
x_58 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_59 = lean_string_append(x_57, x_58);
x_60 = l_Lake_Name_eraseHead(x_5);
x_61 = lean_unbox(x_55);
x_62 = l_Lean_Name_toString(x_60, x_61, x_4);
x_63 = lean_string_append(x_59, x_62);
lean_dec(x_62);
x_64 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_64, 0, x_48);
lean_ctor_set(x_64, 1, x_49);
lean_ctor_set(x_64, 2, x_63);
x_65 = lean_unbox(x_55);
lean_ctor_set_uint8(x_64, sizeof(void*)*3, x_65);
lean_inc(x_64);
x_66 = l_Lake_Job_toOpaque___redArg(x_64);
x_67 = lean_array_push(x_52, x_66);
x_68 = lean_st_ref_set(x_50, x_67, x_53);
lean_dec(x_50);
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
x_71 = l_Lake_Job_renew___redArg(x_64);
lean_ctor_set(x_17, 0, x_71);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_17);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_73 = lean_ctor_get(x_17, 1);
lean_inc(x_73);
lean_dec(x_17);
x_74 = lean_ctor_get(x_18, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_18, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 x_76 = x_18;
} else {
 lean_dec_ref(x_18);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_10, 3);
lean_inc(x_77);
lean_dec(x_10);
x_78 = lean_st_ref_take(x_77, x_19);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_ctor_get(x_6, 0);
lean_inc(x_81);
lean_dec(x_6);
x_82 = lean_box(1);
x_83 = lean_unbox(x_82);
lean_inc(x_4);
x_84 = l_Lean_Name_toString(x_81, x_83, x_4);
x_85 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_86 = lean_string_append(x_84, x_85);
x_87 = l_Lake_Name_eraseHead(x_5);
x_88 = lean_unbox(x_82);
x_89 = l_Lean_Name_toString(x_87, x_88, x_4);
x_90 = lean_string_append(x_86, x_89);
lean_dec(x_89);
if (lean_is_scalar(x_76)) {
 x_91 = lean_alloc_ctor(0, 3, 1);
} else {
 x_91 = x_76;
}
lean_ctor_set(x_91, 0, x_74);
lean_ctor_set(x_91, 1, x_75);
lean_ctor_set(x_91, 2, x_90);
x_92 = lean_unbox(x_82);
lean_ctor_set_uint8(x_91, sizeof(void*)*3, x_92);
lean_inc(x_91);
x_93 = l_Lake_Job_toOpaque___redArg(x_91);
x_94 = lean_array_push(x_79, x_93);
x_95 = lean_st_ref_set(x_77, x_94, x_80);
lean_dec(x_77);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_97 = x_95;
} else {
 lean_dec_ref(x_95);
 x_97 = lean_box(0);
}
x_98 = l_Lake_Job_renew___redArg(x_91);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_73);
if (lean_is_scalar(x_97)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_97;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_96);
return x_100;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_1 = l_Lake_Package_optBarrelFacetConfig___closed__0;
x_2 = l_Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1___closed__0;
x_3 = l_Lake_Package_optGitHubReleaseFacet;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lake_Package_optGitHubReleaseFacetConfig___closed__0;
x_6 = l_Lake_instDataKindBool;
x_7 = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__3), 12, 5);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_4);
lean_closure_set(x_7, 2, x_6);
lean_closure_set(x_7, 3, x_2);
lean_closure_set(x_7, 4, x_3);
x_8 = l_Lake_Package_keyword;
x_9 = lean_box(1);
x_10 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_6);
lean_ctor_set(x_10, 3, x_1);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*4, x_11);
x_12 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*4 + 1, x_12);
return x_10;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to fetch GitHub release", 30, 30);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
if (x_3 == 0)
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_7, 0);
x_39 = lean_ctor_get_uint8(x_38, sizeof(void*)*1 + 3);
x_40 = lean_box(2);
x_41 = lean_unbox(x_40);
x_42 = l_Lake_instDecidableEqVerbosity(x_39, x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_2);
lean_dec(x_1);
x_43 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0;
x_10 = x_43;
x_11 = x_8;
x_12 = x_9;
goto block_37;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_44 = lean_box(x_3);
x_45 = lean_alloc_closure((void*)(l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__1___boxed), 2, 1);
lean_closure_set(x_45, 0, x_44);
x_46 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1;
lean_inc(x_45);
x_47 = l_Lean_Name_toString(x_1, x_42, x_45);
x_48 = lean_string_append(x_46, x_47);
lean_dec(x_47);
x_49 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_50 = lean_string_append(x_48, x_49);
x_51 = l_Lake_Name_eraseHead(x_2);
x_52 = l_Lean_Name_toString(x_51, x_42, x_45);
x_53 = lean_string_append(x_50, x_52);
lean_dec(x_52);
x_54 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3;
x_55 = lean_string_append(x_53, x_54);
x_10 = x_55;
x_11 = x_8;
x_12 = x_9;
goto block_37;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_2);
lean_dec(x_1);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_8);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_9);
return x_58;
}
block_37:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = l_Lake_Package_gitHubReleaseFacetConfig___lam__2___closed__0;
x_16 = lean_string_append(x_15, x_10);
lean_dec(x_10);
x_17 = lean_box(3);
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_unbox(x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_19);
x_20 = lean_array_get_size(x_14);
x_21 = lean_array_push(x_14, x_18);
lean_ctor_set(x_11, 0, x_21);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_11);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_12);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_inc(x_24);
lean_dec(x_11);
x_27 = l_Lake_Package_gitHubReleaseFacetConfig___lam__2___closed__0;
x_28 = lean_string_append(x_27, x_10);
lean_dec(x_10);
x_29 = lean_box(3);
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_unbox(x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_31);
x_32 = lean_array_get_size(x_24);
x_33 = lean_array_push(x_24, x_30);
x_34 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_26);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_25);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_12);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_inc(x_1);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed), 9, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_1);
lean_inc(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = l_Lake_Package_keyword;
x_15 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_4);
lean_ctor_set(x_15, 3, x_1);
x_16 = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__0), 8, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_12);
lean_inc(x_8);
x_17 = l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1(x_16, x_5, x_6, x_7, x_8, x_9, x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_24 = lean_ctor_get(x_19, 2);
lean_dec(x_24);
x_25 = lean_ctor_get(x_8, 3);
lean_inc(x_25);
lean_dec(x_8);
x_26 = lean_st_ref_take(x_25, x_20);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_box(1);
x_30 = lean_unbox(x_29);
lean_inc(x_2);
x_31 = l_Lean_Name_toString(x_11, x_30, x_2);
x_32 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_33 = lean_string_append(x_31, x_32);
x_34 = l_Lake_Name_eraseHead(x_3);
x_35 = lean_unbox(x_29);
x_36 = l_Lean_Name_toString(x_34, x_35, x_2);
x_37 = lean_string_append(x_33, x_36);
lean_dec(x_36);
x_38 = lean_box(0);
lean_ctor_set(x_19, 2, x_37);
x_39 = lean_unbox(x_38);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_39);
lean_inc(x_19);
x_40 = l_Lake_Job_toOpaque___redArg(x_19);
x_41 = lean_array_push(x_27, x_40);
x_42 = lean_st_ref_set(x_25, x_41, x_28);
lean_dec(x_25);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = l_Lake_Job_renew___redArg(x_19);
lean_ctor_set(x_18, 0, x_45);
lean_ctor_set(x_42, 0, x_18);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = l_Lake_Job_renew___redArg(x_19);
lean_ctor_set(x_18, 0, x_47);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_18);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_49 = lean_ctor_get(x_19, 0);
x_50 = lean_ctor_get(x_19, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_19);
x_51 = lean_ctor_get(x_8, 3);
lean_inc(x_51);
lean_dec(x_8);
x_52 = lean_st_ref_take(x_51, x_20);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_box(1);
x_56 = lean_unbox(x_55);
lean_inc(x_2);
x_57 = l_Lean_Name_toString(x_11, x_56, x_2);
x_58 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_59 = lean_string_append(x_57, x_58);
x_60 = l_Lake_Name_eraseHead(x_3);
x_61 = lean_unbox(x_55);
x_62 = l_Lean_Name_toString(x_60, x_61, x_2);
x_63 = lean_string_append(x_59, x_62);
lean_dec(x_62);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_65, 0, x_49);
lean_ctor_set(x_65, 1, x_50);
lean_ctor_set(x_65, 2, x_63);
x_66 = lean_unbox(x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*3, x_66);
lean_inc(x_65);
x_67 = l_Lake_Job_toOpaque___redArg(x_65);
x_68 = lean_array_push(x_53, x_67);
x_69 = lean_st_ref_set(x_51, x_68, x_54);
lean_dec(x_51);
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
x_72 = l_Lake_Job_renew___redArg(x_65);
lean_ctor_set(x_18, 0, x_72);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_18);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_74 = lean_ctor_get(x_18, 1);
lean_inc(x_74);
lean_dec(x_18);
x_75 = lean_ctor_get(x_19, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_19, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 x_77 = x_19;
} else {
 lean_dec_ref(x_19);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_8, 3);
lean_inc(x_78);
lean_dec(x_8);
x_79 = lean_st_ref_take(x_78, x_20);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_box(1);
x_83 = lean_unbox(x_82);
lean_inc(x_2);
x_84 = l_Lean_Name_toString(x_11, x_83, x_2);
x_85 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
x_86 = lean_string_append(x_84, x_85);
x_87 = l_Lake_Name_eraseHead(x_3);
x_88 = lean_unbox(x_82);
x_89 = l_Lean_Name_toString(x_87, x_88, x_2);
x_90 = lean_string_append(x_86, x_89);
lean_dec(x_89);
x_91 = lean_box(0);
if (lean_is_scalar(x_77)) {
 x_92 = lean_alloc_ctor(0, 3, 1);
} else {
 x_92 = x_77;
}
lean_ctor_set(x_92, 0, x_75);
lean_ctor_set(x_92, 1, x_76);
lean_ctor_set(x_92, 2, x_90);
x_93 = lean_unbox(x_91);
lean_ctor_set_uint8(x_92, sizeof(void*)*3, x_93);
lean_inc(x_92);
x_94 = l_Lake_Job_toOpaque___redArg(x_92);
x_95 = lean_array_push(x_80, x_94);
x_96 = lean_st_ref_set(x_78, x_95, x_81);
lean_dec(x_78);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_98 = x_96;
} else {
 lean_dec_ref(x_96);
 x_98 = lean_box(0);
}
x_99 = l_Lake_Job_renew___redArg(x_92);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_74);
if (lean_is_scalar(x_98)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_98;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_97);
return x_101;
}
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_1 = l_Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1___closed__0;
x_2 = l_Lake_Package_gitHubReleaseFacet;
x_3 = l_Lake_Package_optGitHubReleaseFacet;
x_4 = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__1), 10, 3);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_1);
lean_closure_set(x_4, 2, x_2);
x_5 = l_Lake_instDataKindUnit;
x_6 = l_Lake_Package_keyword;
x_7 = lean_box(1);
x_8 = l_Lake_Package_extraDepFacetConfig___closed__1;
x_9 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_5);
lean_ctor_set(x_9, 3, x_8);
x_10 = lean_unbox(x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_10);
x_11 = lean_unbox(x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*4 + 1, x_11);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lake_Package_gitHubReleaseFacetConfig___lam__2(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lake_JobState_merge(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_5, sizeof(void*)*2);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_4, 0);
lean_dec(x_9);
lean_ctor_set(x_4, 0, x_6);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_7);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_7);
lean_ctor_set(x_2, 1, x_11);
return x_2;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
lean_inc(x_13);
x_14 = l_Lake_JobState_merge(x_1, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_14, sizeof(void*)*2);
lean_dec(x_14);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_18 = x_13;
} else {
 lean_dec_ref(x_13);
 x_18 = lean_box(0);
}
if (lean_is_scalar(x_18)) {
 x_19 = lean_alloc_ctor(0, 2, 1);
} else {
 x_19 = x_18;
}
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_2);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_inc(x_23);
x_25 = l_Lake_JobState_merge(x_1, x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_25, sizeof(void*)*2);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 0);
lean_dec(x_29);
x_30 = lean_array_get_size(x_24);
lean_dec(x_24);
x_31 = lean_nat_add(x_30, x_22);
lean_dec(x_22);
lean_dec(x_30);
lean_ctor_set(x_23, 0, x_26);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_27);
lean_ctor_set(x_2, 0, x_31);
return x_2;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_array_get_size(x_24);
lean_dec(x_24);
x_34 = lean_nat_add(x_33, x_22);
lean_dec(x_22);
lean_dec(x_33);
x_35 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_27);
lean_ctor_set(x_2, 1, x_35);
lean_ctor_set(x_2, 0, x_34);
return x_2;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_36 = lean_ctor_get(x_2, 0);
x_37 = lean_ctor_get(x_2, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_2);
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
lean_inc(x_37);
x_39 = l_Lake_JobState_merge(x_1, x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
lean_dec(x_39);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_43 = x_37;
} else {
 lean_dec_ref(x_37);
 x_43 = lean_box(0);
}
x_44 = lean_array_get_size(x_38);
lean_dec(x_38);
x_45 = lean_nat_add(x_44, x_36);
lean_dec(x_36);
lean_dec(x_44);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(0, 2, 1);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_42);
lean_ctor_set_uint8(x_46, sizeof(void*)*2, x_41);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_17; 
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_8, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_8, 0);
lean_inc(x_38);
lean_dec(x_8);
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_37, 1);
x_41 = l_Lake_BuildTrace_mix(x_1, x_40);
x_42 = lean_apply_1(x_2, x_38);
lean_ctor_set(x_37, 1, x_41);
x_43 = lean_box(1);
x_44 = lean_unbox(x_43);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_45 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_42, x_44, x_3, x_4, x_5, x_6, x_37, x_9);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_string_utf8_byte_size(x_50);
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_nat_dec_eq(x_52, x_53);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_49);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_56 = lean_ctor_get(x_49, 0);
x_57 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__3;
x_58 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_50, x_52, x_53);
x_59 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_50, x_58, x_52);
x_60 = lean_string_utf8_extract(x_50, x_58, x_59);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
x_61 = lean_string_append(x_57, x_60);
lean_dec(x_60);
x_62 = lean_box(1);
x_63 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_63, 0, x_61);
x_64 = lean_unbox(x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_64);
x_65 = lean_box(0);
x_66 = lean_array_push(x_56, x_63);
lean_ctor_set(x_49, 0, x_66);
x_67 = l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__1(x_51, x_65, x_3, x_4, x_5, x_6, x_49, x_48);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = x_67;
goto block_36;
}
else
{
lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_68 = lean_ctor_get(x_49, 0);
x_69 = lean_ctor_get_uint8(x_49, sizeof(void*)*2);
x_70 = lean_ctor_get(x_49, 1);
lean_inc(x_70);
lean_inc(x_68);
lean_dec(x_49);
x_71 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__3;
x_72 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_50, x_52, x_53);
x_73 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_50, x_72, x_52);
x_74 = lean_string_utf8_extract(x_50, x_72, x_73);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_50);
x_75 = lean_string_append(x_71, x_74);
lean_dec(x_74);
x_76 = lean_box(1);
x_77 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_77, 0, x_75);
x_78 = lean_unbox(x_76);
lean_ctor_set_uint8(x_77, sizeof(void*)*1, x_78);
x_79 = lean_box(0);
x_80 = lean_array_push(x_68, x_77);
x_81 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_70);
lean_ctor_set_uint8(x_81, sizeof(void*)*2, x_69);
x_82 = l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__1(x_51, x_79, x_3, x_4, x_5, x_6, x_81, x_48);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = x_82;
goto block_36;
}
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_52);
lean_dec(x_50);
x_83 = lean_box(0);
x_84 = l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__1(x_51, x_83, x_3, x_4, x_5, x_6, x_49, x_48);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = x_84;
goto block_36;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_85 = lean_ctor_get(x_45, 1);
lean_inc(x_85);
lean_dec(x_45);
x_86 = lean_ctor_get(x_46, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_46, 1);
lean_inc(x_87);
lean_dec(x_46);
x_10 = x_86;
x_11 = x_87;
x_12 = x_85;
goto block_16;
}
}
else
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; 
x_88 = lean_ctor_get(x_37, 0);
x_89 = lean_ctor_get_uint8(x_37, sizeof(void*)*2);
x_90 = lean_ctor_get(x_37, 1);
lean_inc(x_90);
lean_inc(x_88);
lean_dec(x_37);
x_91 = l_Lake_BuildTrace_mix(x_1, x_90);
x_92 = lean_apply_1(x_2, x_38);
x_93 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_93, 0, x_88);
lean_ctor_set(x_93, 1, x_91);
lean_ctor_set_uint8(x_93, sizeof(void*)*2, x_89);
x_94 = lean_box(1);
x_95 = lean_unbox(x_94);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_96 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_92, x_95, x_3, x_4, x_5, x_6, x_93, x_9);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_dec(x_96);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_101 = lean_ctor_get(x_98, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_98, 1);
lean_inc(x_102);
lean_dec(x_98);
x_103 = lean_string_utf8_byte_size(x_101);
x_104 = lean_unsigned_to_nat(0u);
x_105 = lean_nat_dec_eq(x_103, x_104);
if (x_105 == 0)
{
lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_106 = lean_ctor_get(x_100, 0);
lean_inc(x_106);
x_107 = lean_ctor_get_uint8(x_100, sizeof(void*)*2);
x_108 = lean_ctor_get(x_100, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_109 = x_100;
} else {
 lean_dec_ref(x_100);
 x_109 = lean_box(0);
}
x_110 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__3;
x_111 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_101, x_103, x_104);
x_112 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_101, x_111, x_103);
x_113 = lean_string_utf8_extract(x_101, x_111, x_112);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_101);
x_114 = lean_string_append(x_110, x_113);
lean_dec(x_113);
x_115 = lean_box(1);
x_116 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_116, 0, x_114);
x_117 = lean_unbox(x_115);
lean_ctor_set_uint8(x_116, sizeof(void*)*1, x_117);
x_118 = lean_box(0);
x_119 = lean_array_push(x_106, x_116);
if (lean_is_scalar(x_109)) {
 x_120 = lean_alloc_ctor(0, 2, 1);
} else {
 x_120 = x_109;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_108);
lean_ctor_set_uint8(x_120, sizeof(void*)*2, x_107);
x_121 = l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__1(x_102, x_118, x_3, x_4, x_5, x_6, x_120, x_99);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = x_121;
goto block_36;
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_103);
lean_dec(x_101);
x_122 = lean_box(0);
x_123 = l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__1(x_102, x_122, x_3, x_4, x_5, x_6, x_100, x_99);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = x_123;
goto block_36;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_124 = lean_ctor_get(x_96, 1);
lean_inc(x_124);
lean_dec(x_96);
x_125 = lean_ctor_get(x_97, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_97, 1);
lean_inc(x_126);
lean_dec(x_97);
x_10 = x_125;
x_11 = x_126;
x_12 = x_124;
goto block_16;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_127 = !lean_is_exclusive(x_8);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_task_pure(x_8);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_9);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_130 = lean_ctor_get(x_8, 0);
x_131 = lean_ctor_get(x_8, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_8);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_task_pure(x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_9);
return x_134;
}
}
block_16:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_task_pure(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
block_36:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(x_24, 0, x_22);
x_25 = lean_box(1);
x_26 = lean_unbox(x_25);
x_27 = lean_task_map(x_24, x_23, x_7, x_26);
lean_ctor_set(x_17, 0, x_27);
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_dec(x_17);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_dec(x_18);
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
lean_dec(x_19);
x_31 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(x_31, 0, x_29);
x_32 = lean_box(1);
x_33 = lean_unbox(x_32);
x_34 = lean_task_map(x_31, x_30, x_7, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_28);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_dec(x_13);
lean_inc(x_3);
x_14 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__2), 9, 7);
lean_closure_set(x_14, 0, x_9);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_5);
lean_closure_set(x_14, 3, x_6);
lean_closure_set(x_14, 4, x_7);
lean_closure_set(x_14, 5, x_8);
lean_closure_set(x_14, 6, x_3);
x_15 = lean_io_bind_task(x_12, x_14, x_3, x_4, x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_box(0);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_17);
lean_ctor_set(x_15, 0, x_1);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_box(0);
lean_ctor_set(x_1, 1, x_21);
lean_ctor_set(x_1, 0, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 2);
x_25 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
lean_inc(x_3);
x_26 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__2), 9, 7);
lean_closure_set(x_26, 0, x_9);
lean_closure_set(x_26, 1, x_2);
lean_closure_set(x_26, 2, x_5);
lean_closure_set(x_26, 3, x_6);
lean_closure_set(x_26, 4, x_7);
lean_closure_set(x_26, 5, x_8);
lean_closure_set(x_26, 6, x_3);
x_27 = lean_io_bind_task(x_23, x_26, x_3, x_4, x_10);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_24);
lean_ctor_set_uint8(x_32, sizeof(void*)*3, x_25);
if (lean_is_scalar(x_30)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_30;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 1);
lean_dec(x_10);
x_11 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__2;
lean_ctor_set(x_7, 1, x_11);
x_12 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
lean_inc(x_13);
lean_dec(x_7);
x_15 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__2;
x_16 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_14);
x_17 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_16, x_8);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_name_eq(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
x_14 = l_instDecidableNot___redArg(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__2;
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_18);
x_19 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_17, x_8);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_20, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
lean_ctor_set(x_20, 1, x_26);
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_20, 0);
lean_inc(x_27);
lean_dec(x_20);
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_19, 0, x_29);
return x_19;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_dec(x_19);
x_31 = lean_ctor_get(x_20, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_32 = x_20;
} else {
 lean_dec_ref(x_20);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get(x_21, 0);
lean_inc(x_33);
lean_dec(x_21);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
return x_35;
}
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
x_37 = !lean_is_exclusive(x_19);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_19, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_20);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_20, 1);
lean_dec(x_40);
x_41 = lean_ctor_get(x_36, 0);
lean_inc(x_41);
lean_dec(x_36);
lean_ctor_set(x_20, 1, x_41);
return x_19;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_20, 0);
lean_inc(x_42);
lean_dec(x_20);
x_43 = lean_ctor_get(x_36, 0);
lean_inc(x_43);
lean_dec(x_36);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_19, 0, x_44);
return x_19;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
lean_dec(x_19);
x_46 = lean_ctor_get(x_20, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_47 = x_20;
} else {
 lean_dec_ref(x_20);
 x_47 = lean_box(0);
}
x_48 = lean_ctor_get(x_36, 0);
lean_inc(x_48);
lean_dec(x_36);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_45);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_51 = l_Lake_Package_maybeFetchBuildCache(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; uint8_t x_62; 
x_55 = lean_ctor_get(x_52, 0);
x_56 = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_56, 0, x_2);
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_box(0);
x_59 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__2;
x_60 = lean_unbox(x_58);
x_61 = l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg(x_55, x_56, x_57, x_60, x_3, x_4, x_5, x_6, x_59, x_53);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 0);
lean_ctor_set(x_52, 0, x_63);
lean_ctor_set(x_61, 0, x_52);
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
lean_ctor_set(x_52, 0, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_52);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_67 = lean_ctor_get(x_52, 0);
x_68 = lean_ctor_get(x_52, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_52);
x_69 = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_69, 0, x_2);
x_70 = lean_unsigned_to_nat(0u);
x_71 = lean_box(0);
x_72 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__2;
x_73 = lean_unbox(x_71);
x_74 = l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg(x_67, x_69, x_70, x_73, x_3, x_4, x_5, x_6, x_72, x_53);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_77 = x_74;
} else {
 lean_dec_ref(x_74);
 x_77 = lean_box(0);
}
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_68);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_76);
return x_79;
}
}
else
{
uint8_t x_80; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_80 = !lean_is_exclusive(x_51);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_51, 0);
lean_dec(x_81);
x_82 = !lean_is_exclusive(x_52);
if (x_82 == 0)
{
return x_51;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_52, 0);
x_84 = lean_ctor_get(x_52, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_52);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_51, 0, x_85);
return x_51;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_86 = lean_ctor_get(x_51, 1);
lean_inc(x_86);
lean_dec(x_51);
x_87 = lean_ctor_get(x_52, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_52, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_89 = x_52;
} else {
 lean_dec_ref(x_52);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_86);
return x_91;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Package_afterBuildCacheAsync___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Lake_BuildTrace_mix(x_1, x_12);
x_14 = lean_apply_1(x_2, x_10);
lean_ctor_set(x_9, 1, x_13);
x_15 = lean_box(1);
x_16 = lean_unbox(x_15);
x_17 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_14, x_16, x_3, x_4, x_5, x_6, x_9, x_8);
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_35 = lean_ctor_get(x_22, 0);
x_36 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__3;
x_37 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_24, x_31, x_32);
x_38 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_24, x_37, x_31);
x_39 = lean_string_utf8_extract(x_24, x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_24);
x_40 = lean_string_append(x_36, x_39);
lean_dec(x_39);
x_41 = lean_box(1);
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_40);
x_43 = lean_unbox(x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_43);
x_44 = lean_array_push(x_35, x_42);
lean_ctor_set(x_22, 0, x_44);
x_26 = x_22;
x_27 = x_20;
goto block_30;
}
else
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_45 = lean_ctor_get(x_22, 0);
x_46 = lean_ctor_get_uint8(x_22, sizeof(void*)*2);
x_47 = lean_ctor_get(x_22, 1);
lean_inc(x_47);
lean_inc(x_45);
lean_dec(x_22);
x_48 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__3;
x_49 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_24, x_31, x_32);
x_50 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_24, x_49, x_31);
x_51 = lean_string_utf8_extract(x_24, x_49, x_50);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_24);
x_52 = lean_string_append(x_48, x_51);
lean_dec(x_51);
x_53 = lean_box(1);
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_52);
x_55 = lean_unbox(x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_55);
x_56 = lean_array_push(x_45, x_54);
x_57 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_47);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_46);
x_26 = x_57;
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
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_17);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_17, 0);
lean_dec(x_59);
x_60 = !lean_is_exclusive(x_18);
if (x_60 == 0)
{
return x_17;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_18, 0);
x_62 = lean_ctor_get(x_18, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_18);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_17, 0, x_63);
return x_17;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_17, 1);
lean_inc(x_64);
lean_dec(x_17);
x_65 = lean_ctor_get(x_18, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_18, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_67 = x_18;
} else {
 lean_dec_ref(x_18);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_64);
return x_69;
}
}
}
else
{
lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; 
x_70 = lean_ctor_get(x_9, 0);
x_71 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_72 = lean_ctor_get(x_9, 1);
lean_inc(x_72);
lean_inc(x_70);
lean_dec(x_9);
x_73 = l_Lake_BuildTrace_mix(x_1, x_72);
x_74 = lean_apply_1(x_2, x_10);
x_75 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_73);
lean_ctor_set_uint8(x_75, sizeof(void*)*2, x_71);
x_76 = lean_box(1);
x_77 = lean_unbox(x_76);
x_78 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_74, x_77, x_3, x_4, x_5, x_6, x_75, x_8);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
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
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_84 = x_79;
} else {
 lean_dec_ref(x_79);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_80, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_80, 1);
lean_inc(x_86);
lean_dec(x_80);
x_92 = lean_string_utf8_byte_size(x_85);
x_93 = lean_unsigned_to_nat(0u);
x_94 = lean_nat_dec_eq(x_92, x_93);
if (x_94 == 0)
{
lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; 
x_95 = lean_ctor_get(x_83, 0);
lean_inc(x_95);
x_96 = lean_ctor_get_uint8(x_83, sizeof(void*)*2);
x_97 = lean_ctor_get(x_83, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_98 = x_83;
} else {
 lean_dec_ref(x_83);
 x_98 = lean_box(0);
}
x_99 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__3;
x_100 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_85, x_92, x_93);
x_101 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_85, x_100, x_92);
x_102 = lean_string_utf8_extract(x_85, x_100, x_101);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_85);
x_103 = lean_string_append(x_99, x_102);
lean_dec(x_102);
x_104 = lean_box(1);
x_105 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_105, 0, x_103);
x_106 = lean_unbox(x_104);
lean_ctor_set_uint8(x_105, sizeof(void*)*1, x_106);
x_107 = lean_array_push(x_95, x_105);
if (lean_is_scalar(x_98)) {
 x_108 = lean_alloc_ctor(0, 2, 1);
} else {
 x_108 = x_98;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_97);
lean_ctor_set_uint8(x_108, sizeof(void*)*2, x_96);
x_87 = x_108;
x_88 = x_81;
goto block_91;
}
else
{
lean_dec(x_92);
lean_dec(x_85);
x_87 = x_83;
x_88 = x_81;
goto block_91;
}
block_91:
{
lean_object* x_89; lean_object* x_90; 
if (lean_is_scalar(x_84)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_84;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
if (lean_is_scalar(x_82)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_82;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_109 = lean_ctor_get(x_78, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_110 = x_78;
} else {
 lean_dec_ref(x_78);
 x_110 = lean_box(0);
}
x_111 = lean_ctor_get(x_79, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_79, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_113 = x_79;
} else {
 lean_dec_ref(x_79);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
if (lean_is_scalar(x_110)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_110;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_109);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_7);
if (x_116 == 0)
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_7);
lean_ctor_set(x_117, 1, x_8);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_7, 0);
x_119 = lean_ctor_get(x_7, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_7);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_8);
return x_121;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_dec(x_13);
x_14 = lean_alloc_closure((void*)(l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg___lam__0), 8, 6);
lean_closure_set(x_14, 0, x_9);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_5);
lean_closure_set(x_14, 3, x_6);
lean_closure_set(x_14, 4, x_7);
lean_closure_set(x_14, 5, x_8);
x_15 = lean_io_map_task(x_14, x_12, x_3, x_4, x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_box(0);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_17);
lean_ctor_set(x_15, 0, x_1);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_box(0);
lean_ctor_set(x_1, 1, x_21);
lean_ctor_set(x_1, 0, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 2);
x_25 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
x_26 = lean_alloc_closure((void*)(l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg___lam__0), 8, 6);
lean_closure_set(x_26, 0, x_9);
lean_closure_set(x_26, 1, x_2);
lean_closure_set(x_26, 2, x_5);
lean_closure_set(x_26, 3, x_6);
lean_closure_set(x_26, 4, x_7);
lean_closure_set(x_26, 5, x_8);
x_27 = lean_io_map_task(x_26, x_23, x_3, x_4, x_10);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_24);
lean_ctor_set_uint8(x_32, sizeof(void*)*3, x_25);
if (lean_is_scalar(x_30)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_30;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_24; uint8_t x_25; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_14 = x_10;
} else {
 lean_dec_ref(x_10);
 x_14 = lean_box(0);
}
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
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_24 = lean_string_utf8_byte_size(x_17);
x_25 = lean_nat_dec_eq(x_24, x_8);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__3;
x_29 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_17, x_24, x_8);
x_30 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_17, x_29, x_24);
x_31 = lean_string_utf8_extract(x_17, x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_17);
x_32 = lean_string_append(x_28, x_31);
lean_dec(x_31);
x_33 = lean_box(1);
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
x_35 = lean_unbox(x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_35);
x_36 = lean_array_push(x_27, x_34);
lean_ctor_set(x_15, 0, x_36);
x_19 = x_15;
x_20 = x_13;
goto block_23;
}
else
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_37 = lean_ctor_get(x_15, 0);
x_38 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
x_39 = lean_ctor_get(x_15, 1);
lean_inc(x_39);
lean_inc(x_37);
lean_dec(x_15);
x_40 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__3;
x_41 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_17, x_24, x_8);
x_42 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_17, x_41, x_24);
x_43 = lean_string_utf8_extract(x_17, x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_17);
x_44 = lean_string_append(x_40, x_43);
lean_dec(x_43);
x_45 = lean_box(1);
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_44);
x_47 = lean_unbox(x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_47);
x_48 = lean_array_push(x_37, x_46);
x_49 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_39);
lean_ctor_set_uint8(x_49, sizeof(void*)*2, x_38);
x_19 = x_49;
x_20 = x_13;
goto block_23;
}
}
else
{
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_8);
x_19 = x_15;
x_20 = x_13;
goto block_23;
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
if (lean_is_scalar(x_16)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_16;
}
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
if (lean_is_scalar(x_14)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_14;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_50; 
lean_dec(x_8);
x_50 = !lean_is_exclusive(x_10);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_10, 0);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_11);
if (x_52 == 0)
{
return x_10;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_11, 0);
x_54 = lean_ctor_get(x_11, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_11);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_10, 0, x_55);
return x_10;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_10, 1);
lean_inc(x_56);
lean_dec(x_10);
x_57 = lean_ctor_get(x_11, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_11, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_59 = x_11;
} else {
 lean_dec_ref(x_11);
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
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 1);
lean_dec(x_10);
x_11 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__2;
lean_ctor_set(x_7, 1, x_11);
x_12 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
lean_inc(x_13);
lean_dec(x_7);
x_15 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__2;
x_16 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_14);
x_17 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_16, x_8);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_name_eq(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
x_14 = l_instDecidableNot___redArg(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lake_Package_recFetchDeps___lam__1___closed__1;
x_17 = lean_box(1);
x_18 = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed), 9, 8);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_3);
lean_closure_set(x_18, 3, x_4);
lean_closure_set(x_18, 4, x_5);
lean_closure_set(x_18, 5, x_6);
lean_closure_set(x_18, 6, x_16);
lean_closure_set(x_18, 7, x_15);
x_19 = lean_io_as_task(x_18, x_15, x_8);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_box(0);
x_23 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__0;
x_24 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_14);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_7);
lean_ctor_set(x_19, 0, x_25);
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_box(0);
x_29 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__0;
x_30 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_14);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_7);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_33 = l_Lake_Package_maybeFetchBuildCache(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; uint8_t x_44; 
x_37 = lean_ctor_get(x_34, 0);
x_38 = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheSync___redArg___lam__1___boxed), 8, 1);
lean_closure_set(x_38, 0, x_2);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_box(0);
x_41 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__2;
x_42 = lean_unbox(x_40);
x_43 = l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg(x_37, x_38, x_39, x_42, x_3, x_4, x_5, x_6, x_41, x_35);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 0);
lean_ctor_set(x_34, 0, x_45);
lean_ctor_set(x_43, 0, x_34);
return x_43;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_43, 0);
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_43);
lean_ctor_set(x_34, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_34);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_49 = lean_ctor_get(x_34, 0);
x_50 = lean_ctor_get(x_34, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_34);
x_51 = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheSync___redArg___lam__1___boxed), 8, 1);
lean_closure_set(x_51, 0, x_2);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_box(0);
x_54 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__2;
x_55 = lean_unbox(x_53);
x_56 = l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg(x_49, x_51, x_52, x_55, x_3, x_4, x_5, x_6, x_54, x_35);
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
lean_ctor_set(x_60, 1, x_50);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_33);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_33, 0);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_34);
if (x_64 == 0)
{
return x_33;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_34, 0);
x_66 = lean_ctor_get(x_34, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_34);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_33, 0, x_67);
return x_33;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_33, 1);
lean_inc(x_68);
lean_dec(x_33);
x_69 = lean_ctor_get(x_34, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_34, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_71 = x_34;
} else {
 lean_dec_ref(x_34);
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
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Package_afterBuildCacheSync___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lake_Package_afterBuildCacheSync___redArg___lam__0(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lake_Package_afterBuildCacheSync___redArg___lam__1(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Package_depsFacetConfig;
x_2 = l_Lake_Package_depsFacet;
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Package_transDepsFacetConfig;
x_2 = l_Lake_Package_transDepsFacet;
x_3 = l_Lake_Package_initFacetConfigs___closed__0;
x_4 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Package_extraDepFacetConfig;
x_2 = l_Lake_Package_extraDepFacet;
x_3 = l_Lake_Package_initFacetConfigs___closed__1;
x_4 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Package_optBuildCacheFacetConfig;
x_2 = l_Lake_Package_optBuildCacheFacet;
x_3 = l_Lake_Package_initFacetConfigs___closed__2;
x_4 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Package_buildCacheFacetConfig;
x_2 = l_Lake_Package_buildCacheFacet;
x_3 = l_Lake_Package_initFacetConfigs___closed__3;
x_4 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Package_optBarrelFacetConfig;
x_2 = l_Lake_Package_optReservoirBarrelFacet;
x_3 = l_Lake_Package_initFacetConfigs___closed__4;
x_4 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Package_barrelFacetConfig;
x_2 = l_Lake_Package_reservoirBarrelFacet;
x_3 = l_Lake_Package_initFacetConfigs___closed__5;
x_4 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Package_optGitHubReleaseFacetConfig;
x_2 = l_Lake_Package_optGitHubReleaseFacet;
x_3 = l_Lake_Package_initFacetConfigs___closed__6;
x_4 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Package_gitHubReleaseFacetConfig;
x_2 = l_Lake_Package_gitHubReleaseFacet;
x_3 = l_Lake_Package_initFacetConfigs___closed__7;
x_4 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_initFacetConfigs___closed__8;
return x_1;
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
lean_object* initialize_Lake_Util_Git(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Sugar(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Common(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Targets(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Topological(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Reservoir(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Package(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Git(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Sugar(builtin, lean_io_mk_world());
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
res = initialize_Lake_Reservoir(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg___closed__0 = _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg___closed__0();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg___closed__0);
l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg___closed__1 = _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg___closed__1);
l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___closed__0 = _init_l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___closed__0();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___closed__0);
l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___closed__1 = _init_l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___closed__1();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___closed__1);
l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___closed__2 = _init_l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___closed__2();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___closed__2);
l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___closed__3 = _init_l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___closed__3();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___closed__3);
l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___closed__4 = _init_l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___closed__4();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___closed__4);
l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__0 = _init_l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__0();
lean_mark_persistent(l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__0);
l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__1 = _init_l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__1();
lean_mark_persistent(l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__1);
l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__2 = _init_l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__2();
lean_mark_persistent(l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__2);
l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__3 = _init_l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__3();
lean_mark_persistent(l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___closed__3);
l_Lake_Package_recFetchDeps___lam__1___closed__0 = _init_l_Lake_Package_recFetchDeps___lam__1___closed__0();
lean_mark_persistent(l_Lake_Package_recFetchDeps___lam__1___closed__0);
l_Lake_Package_recFetchDeps___lam__1___closed__1 = _init_l_Lake_Package_recFetchDeps___lam__1___closed__1();
lean_mark_persistent(l_Lake_Package_recFetchDeps___lam__1___closed__1);
l_Lake_Package_recFetchDeps___boxed__const__1 = _init_l_Lake_Package_recFetchDeps___boxed__const__1();
lean_mark_persistent(l_Lake_Package_recFetchDeps___boxed__const__1);
l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0___closed__0 = _init_l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0___closed__0);
l_Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1___closed__0 = _init_l_Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1___closed__0();
lean_mark_persistent(l_Array_toJson___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1___closed__0);
l_Lake_Package_depsFacetConfig___closed__0 = _init_l_Lake_Package_depsFacetConfig___closed__0();
lean_mark_persistent(l_Lake_Package_depsFacetConfig___closed__0);
l_Lake_Package_depsFacetConfig = _init_l_Lake_Package_depsFacetConfig();
lean_mark_persistent(l_Lake_Package_depsFacetConfig);
l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__0 = _init_l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__0();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__0);
l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__1 = _init_l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__1();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__1);
l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__2 = _init_l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__2();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__2);
l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__3 = _init_l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__3();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__3);
l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__4 = _init_l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__4();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__4);
l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__5 = _init_l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__5();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__5);
l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__6 = _init_l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__6();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7___closed__6);
l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7 = _init_l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7);
l_Lake_Package_transDepsFacetConfig___closed__0 = _init_l_Lake_Package_transDepsFacetConfig___closed__0();
lean_mark_persistent(l_Lake_Package_transDepsFacetConfig___closed__0);
l_Lake_Package_transDepsFacetConfig___closed__1 = _init_l_Lake_Package_transDepsFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Package_transDepsFacetConfig___closed__1);
l_Lake_Package_transDepsFacetConfig___closed__2 = _init_l_Lake_Package_transDepsFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Package_transDepsFacetConfig___closed__2);
l_Lake_Package_transDepsFacetConfig = _init_l_Lake_Package_transDepsFacetConfig();
lean_mark_persistent(l_Lake_Package_transDepsFacetConfig);
l_Lake_stdFormat___at___Lake_Package_optBuildCacheFacetConfig_spec__0___closed__0 = _init_l_Lake_stdFormat___at___Lake_Package_optBuildCacheFacetConfig_spec__0___closed__0();
lean_mark_persistent(l_Lake_stdFormat___at___Lake_Package_optBuildCacheFacetConfig_spec__0___closed__0);
l_Lake_stdFormat___at___Lake_Package_optBuildCacheFacetConfig_spec__0___closed__1 = _init_l_Lake_stdFormat___at___Lake_Package_optBuildCacheFacetConfig_spec__0___closed__1();
lean_mark_persistent(l_Lake_stdFormat___at___Lake_Package_optBuildCacheFacetConfig_spec__0___closed__1);
l_Lake_Package_optBuildCacheFacetConfig = _init_l_Lake_Package_optBuildCacheFacetConfig();
lean_mark_persistent(l_Lake_Package_optBuildCacheFacetConfig);
l_Lake_Package_maybeFetchBuildCache___closed__0 = _init_l_Lake_Package_maybeFetchBuildCache___closed__0();
lean_mark_persistent(l_Lake_Package_maybeFetchBuildCache___closed__0);
l_Lake_Package_maybeFetchBuildCache___closed__1 = _init_l_Lake_Package_maybeFetchBuildCache___closed__1();
lean_mark_persistent(l_Lake_Package_maybeFetchBuildCache___closed__1);
l_Lake_Package_maybeFetchBuildCache___closed__2 = _init_l_Lake_Package_maybeFetchBuildCache___closed__2();
lean_mark_persistent(l_Lake_Package_maybeFetchBuildCache___closed__2);
l_Lake_Package_maybeFetchBuildCache___closed__3 = _init_l_Lake_Package_maybeFetchBuildCache___closed__3();
lean_mark_persistent(l_Lake_Package_maybeFetchBuildCache___closed__3);
l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0 = _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1 = _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1);
l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2 = _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2);
l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3 = _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3);
l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___closed__0 = _init_l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___closed__0();
lean_mark_persistent(l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___closed__0);
l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___closed__1 = _init_l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___closed__1();
lean_mark_persistent(l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___closed__1);
l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___closed__2 = _init_l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___closed__2();
lean_mark_persistent(l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___closed__2);
l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___closed__3 = _init_l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___closed__3();
lean_mark_persistent(l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___closed__3);
l_Lake_Package_recBuildExtraDepTargets___closed__0 = _init_l_Lake_Package_recBuildExtraDepTargets___closed__0();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___closed__0);
l_Lake_Package_recBuildExtraDepTargets___closed__1 = _init_l_Lake_Package_recBuildExtraDepTargets___closed__1();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___closed__1);
l_Lake_Package_extraDepFacetConfig___closed__0 = _init_l_Lake_Package_extraDepFacetConfig___closed__0();
lean_mark_persistent(l_Lake_Package_extraDepFacetConfig___closed__0);
l_Lake_Package_extraDepFacetConfig___closed__1 = _init_l_Lake_Package_extraDepFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Package_extraDepFacetConfig___closed__1);
l_Lake_Package_extraDepFacetConfig___closed__2 = _init_l_Lake_Package_extraDepFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Package_extraDepFacetConfig___closed__2);
l_Lake_Package_extraDepFacetConfig = _init_l_Lake_Package_extraDepFacetConfig();
lean_mark_persistent(l_Lake_Package_extraDepFacetConfig);
l_Lake_Package_getBarrelUrl___redArg___closed__0 = _init_l_Lake_Package_getBarrelUrl___redArg___closed__0();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___redArg___closed__0);
l_Lake_Package_getBarrelUrl___redArg___closed__1 = _init_l_Lake_Package_getBarrelUrl___redArg___closed__1();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___redArg___closed__1);
l_Lake_Package_getBarrelUrl___redArg___closed__2 = _init_l_Lake_Package_getBarrelUrl___redArg___closed__2();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___redArg___closed__2);
l_Lake_Package_getBarrelUrl___redArg___closed__3 = _init_l_Lake_Package_getBarrelUrl___redArg___closed__3();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___redArg___closed__3);
l_Lake_Package_getBarrelUrl___redArg___closed__4 = _init_l_Lake_Package_getBarrelUrl___redArg___closed__4();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___redArg___closed__4);
l_Lake_Package_getBarrelUrl___redArg___closed__5 = _init_l_Lake_Package_getBarrelUrl___redArg___closed__5();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___redArg___closed__5);
l_Lake_Package_getBarrelUrl___redArg___closed__6 = _init_l_Lake_Package_getBarrelUrl___redArg___closed__6();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___redArg___closed__6);
l_Lake_Package_getBarrelUrl___redArg___closed__7 = _init_l_Lake_Package_getBarrelUrl___redArg___closed__7();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___redArg___closed__7);
l_Lake_Package_getBarrelUrl___redArg___closed__8 = _init_l_Lake_Package_getBarrelUrl___redArg___closed__8();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___redArg___closed__8);
l_Lake_Package_getBarrelUrl___redArg___closed__9 = _init_l_Lake_Package_getBarrelUrl___redArg___closed__9();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___redArg___closed__9);
l_Lake_Package_getBarrelUrl___redArg___closed__10 = _init_l_Lake_Package_getBarrelUrl___redArg___closed__10();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___redArg___closed__10);
l_Lake_Package_getBarrelUrl___redArg___closed__11 = _init_l_Lake_Package_getBarrelUrl___redArg___closed__11();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___redArg___closed__11);
l_Lake_Package_getBarrelUrl___redArg___closed__12 = _init_l_Lake_Package_getBarrelUrl___redArg___closed__12();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___redArg___closed__12);
l_Lake_Package_getBarrelUrl___redArg___closed__13 = _init_l_Lake_Package_getBarrelUrl___redArg___closed__13();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___redArg___closed__13);
l_Lake_Package_getBarrelUrl___redArg___closed__14 = _init_l_Lake_Package_getBarrelUrl___redArg___closed__14();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___redArg___closed__14);
l_Lake_Package_getBarrelUrl___redArg___closed__15 = _init_l_Lake_Package_getBarrelUrl___redArg___closed__15();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___redArg___closed__15);
l_Lake_Package_getBarrelUrl___redArg___closed__16 = _init_l_Lake_Package_getBarrelUrl___redArg___closed__16();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___redArg___closed__16);
l_Lake_Package_getBarrelUrl___redArg___closed__17 = _init_l_Lake_Package_getBarrelUrl___redArg___closed__17();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___redArg___closed__17);
l_Lake_Package_getBarrelUrl___redArg___closed__18 = _init_l_Lake_Package_getBarrelUrl___redArg___closed__18();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___redArg___closed__18);
l_Lake_Package_getBarrelUrl___redArg___closed__19 = _init_l_Lake_Package_getBarrelUrl___redArg___closed__19();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___redArg___closed__19);
l_Lake_Package_getReleaseUrl___redArg___closed__0 = _init_l_Lake_Package_getReleaseUrl___redArg___closed__0();
lean_mark_persistent(l_Lake_Package_getReleaseUrl___redArg___closed__0);
l_Lake_Package_getReleaseUrl___redArg___closed__1 = _init_l_Lake_Package_getReleaseUrl___redArg___closed__1();
lean_mark_persistent(l_Lake_Package_getReleaseUrl___redArg___closed__1);
l_Lake_Package_getReleaseUrl___redArg___closed__2 = _init_l_Lake_Package_getReleaseUrl___redArg___closed__2();
lean_mark_persistent(l_Lake_Package_getReleaseUrl___redArg___closed__2);
l_Lake_Package_getReleaseUrl___redArg___closed__3 = _init_l_Lake_Package_getReleaseUrl___redArg___closed__3();
lean_mark_persistent(l_Lake_Package_getReleaseUrl___redArg___closed__3);
l_Lake_Package_getReleaseUrl___redArg___closed__4 = _init_l_Lake_Package_getReleaseUrl___redArg___closed__4();
lean_mark_persistent(l_Lake_Package_getReleaseUrl___redArg___closed__4);
l_Lake_Package_getReleaseUrl___redArg___closed__5 = _init_l_Lake_Package_getReleaseUrl___redArg___closed__5();
lean_mark_persistent(l_Lake_Package_getReleaseUrl___redArg___closed__5);
l_Lake_Package_getReleaseUrl___redArg___closed__6 = _init_l_Lake_Package_getReleaseUrl___redArg___closed__6();
lean_mark_persistent(l_Lake_Package_getReleaseUrl___redArg___closed__6);
l_Lake_Package_getReleaseUrl___redArg___closed__7 = _init_l_Lake_Package_getReleaseUrl___redArg___closed__7();
lean_mark_persistent(l_Lake_Package_getReleaseUrl___redArg___closed__7);
l_Lake_Package_getReleaseUrl___redArg___closed__8 = _init_l_Lake_Package_getReleaseUrl___redArg___closed__8();
lean_mark_persistent(l_Lake_Package_getReleaseUrl___redArg___closed__8);
l_Lake_Package_getReleaseUrl___redArg___closed__9 = _init_l_Lake_Package_getReleaseUrl___redArg___closed__9();
lean_mark_persistent(l_Lake_Package_getReleaseUrl___redArg___closed__9);
l_Lake_Package_getReleaseUrl___redArg___closed__10 = _init_l_Lake_Package_getReleaseUrl___redArg___closed__10();
lean_mark_persistent(l_Lake_Package_getReleaseUrl___redArg___closed__10);
l_Lake_Package_getReleaseUrl___redArg___closed__11 = _init_l_Lake_Package_getReleaseUrl___redArg___closed__11();
lean_mark_persistent(l_Lake_Package_getReleaseUrl___redArg___closed__11);
l_Lake_Package_getReleaseUrl___redArg___closed__12 = _init_l_Lake_Package_getReleaseUrl___redArg___closed__12();
lean_mark_persistent(l_Lake_Package_getReleaseUrl___redArg___closed__12);
l_Lake_Package_getReleaseUrl___redArg___closed__13 = _init_l_Lake_Package_getReleaseUrl___redArg___closed__13();
lean_mark_persistent(l_Lake_Package_getReleaseUrl___redArg___closed__13);
l_Lake_Package_getReleaseUrl___redArg___closed__14 = _init_l_Lake_Package_getReleaseUrl___redArg___closed__14();
lean_mark_persistent(l_Lake_Package_getReleaseUrl___redArg___closed__14);
l_Lake_Package_fetchBuildArchive___closed__0 = _init_l_Lake_Package_fetchBuildArchive___closed__0();
lean_mark_persistent(l_Lake_Package_fetchBuildArchive___closed__0);
l_Lake_Package_fetchBuildArchive___closed__1 = _init_l_Lake_Package_fetchBuildArchive___closed__1();
lean_mark_persistent(l_Lake_Package_fetchBuildArchive___closed__1);
l_Lake_Package_fetchBuildArchive___closed__2 = _init_l_Lake_Package_fetchBuildArchive___closed__2();
lean_mark_persistent(l_Lake_Package_fetchBuildArchive___closed__2);
l_Lake_Package_fetchBuildArchive___closed__3 = _init_l_Lake_Package_fetchBuildArchive___closed__3();
lean_mark_persistent(l_Lake_Package_fetchBuildArchive___closed__3);
l_Lake_Package_fetchBuildArchive___closed__4 = _init_l_Lake_Package_fetchBuildArchive___closed__4();
lean_mark_persistent(l_Lake_Package_fetchBuildArchive___closed__4);
l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__0 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__0();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__0);
l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__1 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__1();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__1);
l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__2 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__2();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__2);
l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3);
l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__4 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__4();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__4);
l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__5 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__5();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__5);
l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__6 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__6();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__6);
l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__7 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__7();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__7);
l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__8 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__8();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__8);
l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__9 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__9();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__9);
l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__10 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__10();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__10);
l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__11 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__11();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__11);
l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__12 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__12();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__12);
l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__13 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__13();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__13);
l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___closed__0 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___closed__0();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___closed__0);
l_Lake_Package_buildCacheFacetConfig___lam__2___closed__0 = _init_l_Lake_Package_buildCacheFacetConfig___lam__2___closed__0();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig___lam__2___closed__0);
l_Lake_Package_buildCacheFacetConfig = _init_l_Lake_Package_buildCacheFacetConfig();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig);
l_Lake_Package_optBarrelFacetConfig___lam__2___closed__0 = _init_l_Lake_Package_optBarrelFacetConfig___lam__2___closed__0();
lean_mark_persistent(l_Lake_Package_optBarrelFacetConfig___lam__2___closed__0);
l_Lake_Package_optBarrelFacetConfig___lam__2___closed__1 = _init_l_Lake_Package_optBarrelFacetConfig___lam__2___closed__1();
lean_mark_persistent(l_Lake_Package_optBarrelFacetConfig___lam__2___closed__1);
l_Lake_Package_optBarrelFacetConfig___closed__0 = _init_l_Lake_Package_optBarrelFacetConfig___closed__0();
lean_mark_persistent(l_Lake_Package_optBarrelFacetConfig___closed__0);
l_Lake_Package_optBarrelFacetConfig = _init_l_Lake_Package_optBarrelFacetConfig();
lean_mark_persistent(l_Lake_Package_optBarrelFacetConfig);
l_Lake_Package_barrelFacetConfig___lam__2___closed__0 = _init_l_Lake_Package_barrelFacetConfig___lam__2___closed__0();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig___lam__2___closed__0);
l_Lake_Package_barrelFacetConfig = _init_l_Lake_Package_barrelFacetConfig();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig);
l_Lake_Package_optGitHubReleaseFacetConfig___closed__0 = _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__0();
lean_mark_persistent(l_Lake_Package_optGitHubReleaseFacetConfig___closed__0);
l_Lake_Package_optGitHubReleaseFacetConfig = _init_l_Lake_Package_optGitHubReleaseFacetConfig();
lean_mark_persistent(l_Lake_Package_optGitHubReleaseFacetConfig);
l_Lake_Package_gitHubReleaseFacetConfig___lam__2___closed__0 = _init_l_Lake_Package_gitHubReleaseFacetConfig___lam__2___closed__0();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig___lam__2___closed__0);
l_Lake_Package_gitHubReleaseFacetConfig = _init_l_Lake_Package_gitHubReleaseFacetConfig();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig);
l_Lake_Package_initFacetConfigs___closed__0 = _init_l_Lake_Package_initFacetConfigs___closed__0();
lean_mark_persistent(l_Lake_Package_initFacetConfigs___closed__0);
l_Lake_Package_initFacetConfigs___closed__1 = _init_l_Lake_Package_initFacetConfigs___closed__1();
lean_mark_persistent(l_Lake_Package_initFacetConfigs___closed__1);
l_Lake_Package_initFacetConfigs___closed__2 = _init_l_Lake_Package_initFacetConfigs___closed__2();
lean_mark_persistent(l_Lake_Package_initFacetConfigs___closed__2);
l_Lake_Package_initFacetConfigs___closed__3 = _init_l_Lake_Package_initFacetConfigs___closed__3();
lean_mark_persistent(l_Lake_Package_initFacetConfigs___closed__3);
l_Lake_Package_initFacetConfigs___closed__4 = _init_l_Lake_Package_initFacetConfigs___closed__4();
lean_mark_persistent(l_Lake_Package_initFacetConfigs___closed__4);
l_Lake_Package_initFacetConfigs___closed__5 = _init_l_Lake_Package_initFacetConfigs___closed__5();
lean_mark_persistent(l_Lake_Package_initFacetConfigs___closed__5);
l_Lake_Package_initFacetConfigs___closed__6 = _init_l_Lake_Package_initFacetConfigs___closed__6();
lean_mark_persistent(l_Lake_Package_initFacetConfigs___closed__6);
l_Lake_Package_initFacetConfigs___closed__7 = _init_l_Lake_Package_initFacetConfigs___closed__7();
lean_mark_persistent(l_Lake_Package_initFacetConfigs___closed__7);
l_Lake_Package_initFacetConfigs___closed__8 = _init_l_Lake_Package_initFacetConfigs___closed__8();
lean_mark_persistent(l_Lake_Package_initFacetConfigs___closed__8);
l_Lake_Package_initFacetConfigs = _init_l_Lake_Package_initFacetConfigs();
lean_mark_persistent(l_Lake_Package_initFacetConfigs);
l_Lake_initPackageFacetConfigs = _init_l_Lake_initPackageFacetConfigs();
lean_mark_persistent(l_Lake_initPackageFacetConfigs);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

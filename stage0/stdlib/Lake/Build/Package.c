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
static lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__3;
static lean_object* l_Lake_Package_recBuildExtraDepTargets___closed__1;
static lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__6;
static lean_object* l_Lake_stdFormat___at_Lake_Package_optBuildCacheFacetConfig___elambda__1___spec__1___closed__2;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initPackageFacetConfigs___closed__5;
lean_object* l_Lake_Package_fetchTargetJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterBuildCacheSync___spec__6(lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_afterBuildCacheSync___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__4;
static lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__2;
static lean_object* l_Lake_Package_depsFacetConfig___closed__2;
lean_object* l_Lean_Json_compress(lean_object*);
LEAN_EXPORT lean_object* l_Lake_initPackageFacetConfigs;
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeTransDeps___spec__7(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__5___closed__1;
LEAN_EXPORT lean_object* l_Lake_EquipT_pure___at_Lake_Package_recComputeTransDeps___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__6;
static lean_object* l_Lake_Package_getReleaseUrl___closed__11;
static lean_object* l_Lake_Package_getBarrelUrl___lambda__2___closed__10;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__7;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___elambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getReleaseUrl___closed__12;
static lean_object* l_Lake_Package_getReleaseUrl___closed__9;
static lean_object* l_Lake_Package_fetchBuildArchive___closed__2;
static lean_object* l_Lake_Package_getReleaseUrl___closed__2;
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_depsFacetConfig___closed__4;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_afterBuildCacheSync___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_transDepsFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_transDepsFacetConfig___closed__2;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_recBuildExtraDepTargets___closed__3;
static lean_object* l_Lake_Package_depsFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_Package_barrelFacetConfig___closed__2;
static lean_object* l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__6;
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_getReleaseUrl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_afterBuildCacheSync___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCache___closed__5;
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Package_afterBuildCacheSync___spec__4(lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCache___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig;
lean_object* l_Lake_Job_mix___rarg(lean_object*, lean_object*);
lean_object* l_Lake_download(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_buildUnlessUpToDate_x3f_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__3;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___lambda__1___boxed(lean_object*);
static lean_object* l_Lake_Package_optBarrelFacetConfig___elambda__2___lambda__1___closed__1;
static lean_object* l_Lake_Package_getReleaseUrl___closed__10;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
extern lean_object* l_Lake_Reservoir_lakeHeaders;
LEAN_EXPORT lean_object* l_Lake_EquipT_tryCatch___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate_x27___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recFetchDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__4;
static lean_object* l_Lake_Package_barrelFacetConfig___closed__1;
lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__4;
lean_object* l_Lake_Job_add___rarg(lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
static lean_object* l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__4;
static lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate_x27___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__7___closed__1;
static lean_object* l_Lake_Package_recFetchDeps___lambda__1___closed__2;
static lean_object* l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___rarg___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_getReleaseUrl___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___elambda__1(uint8_t, uint8_t);
lean_object* l_Lake_ensureJob___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__5;
static lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__9;
extern lean_object* l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__5;
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_buildCacheFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig;
lean_object* l_Lake_readTraceFile_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___elambda__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___lambda__2___closed__11;
static lean_object* l_Lake_Package_optBarrelFacetConfig___closed__3;
static lean_object* l_Lake_initPackageFacetConfigs___closed__3;
static lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_recComputeTransDeps___lambda__1(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Package_recComputeTransDeps___spec__2(lean_object*, lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__1;
static lean_object* l_Lake_Package_optBuildCacheFacetConfig___closed__4;
LEAN_EXPORT lean_object* l_Lake_EquipT_map___at_Lake_Package_recFetchDeps___spec__2(lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__1;
static lean_object* l_Lake_Package_maybeFetchBuildCache___closed__3;
LEAN_EXPORT lean_object* l_Lake_Package_fetchBuildArchive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lake_nullFormat___rarg(uint8_t, lean_object*);
lean_object* l_Lake_EquipT_bind___at_Lake_buildFileUnlessUpToDate_x27___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeTransDeps___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lake_Package_optBuildCacheFacetConfig___closed__5;
LEAN_EXPORT lean_object* l_Lake_EquipT_pure___at_Lake_Package_recComputeTransDeps___spec__8(lean_object*);
lean_object* lean_task_pure(lean_object*);
uint8_t l_instDecidableNot___rarg(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__3;
static lean_object* l_Lake_Package_transDepsFacetConfig___closed__3;
static lean_object* l_Lake_Package_getBarrelUrl___lambda__2___closed__4;
lean_object* l_Lake_captureProc_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_transDepsFacetConfig;
static lean_object* l_Lake_Package_getBarrelUrl___lambda__2___closed__2;
static lean_object* l_Lake_Package_gitHubReleaseFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___lambda__2___closed__5;
LEAN_EXPORT lean_object* l_Lake_Package_depsFacetConfig___elambda__1(uint8_t, lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___lambda__2___closed__15;
LEAN_EXPORT lean_object* l_IO_withStdout___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_Package_optBuildCacheFacetConfig___elambda__1___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___at_Lake_Package_fetchBuildArchive___spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___elambda__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_depsFacetConfig___elambda__1___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeTransDeps___spec__1___closed__2;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeTransDeps___spec__9___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchBuildArchive___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_nullFormat___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lake_BuildInfo_fetch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___closed__2;
static lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__1;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__4;
static lean_object* l_Lake_Package_optBuildCacheFacetConfig___closed__2;
static lean_object* l_Lake_initPackageFacetConfigs___closed__9;
static lean_object* l_Lake_initPackageFacetConfigs___closed__8;
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recComputeTransDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_withRegisterJob___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___lambda__2___closed__9;
LEAN_EXPORT lean_object* l_Lake_Package_transDepsFacetConfig___elambda__1(uint8_t, lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___lambda__1___closed__1;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeTransDeps___spec__9___closed__1;
static lean_object* l_Lake_Package_getBarrelUrl___lambda__2___closed__8;
static lean_object* l_Lake_Package_getReleaseUrl___closed__3;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseAsync(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_Package_recComputeTransDeps___spec__3(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lake_Package_buildCacheFacetConfig___closed__1;
static lean_object* l_Lake_initPackageFacetConfigs___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseSync___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getReleaseUrl___closed__7;
static lean_object* l_Lake_Package_gitHubReleaseFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_recComputeTransDeps___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__3;
lean_object* l_Lake_Job_mapM___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__2;
static lean_object* l_Lake_Package_barrelFacetConfig___elambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optReleaseFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseSync(lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__4;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Package_recComputeTransDeps___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchBuildArchive___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_String_fromUTF8_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___elambda__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__5;
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
static lean_object* l_Lake_Package_transDepsFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_Package_recBuildExtraDepTargets___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_getReleaseUrl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_optBuildCacheFacetConfig___closed__1;
static lean_object* l_Lake_Package_optBarrelFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchBuildArchive___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync(lean_object*);
static lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__3;
extern lean_object* l_Task_Priority_default;
static lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__6;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___elambda__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___at_Lake_Package_fetchBuildArchive___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_Package_optBuildCacheFacetConfig___elambda__1___spec__1(uint8_t, uint8_t);
static lean_object* l_Lake_Package_getReleaseUrl___closed__6;
static lean_object* l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterBuildCacheSync___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeTransDeps___spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_BuildTrace_nil;
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeTransDeps___spec__1(lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_buildFileUnlessUpToDate_x27___spec__5(lean_object*, lean_object*);
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___elambda__1(uint8_t, uint8_t);
static lean_object* l_Lake_Package_buildCacheFacetConfig___closed__3;
extern lean_object* l_Lake_defaultLakeDir;
lean_object* lean_string_from_utf8_unchecked(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchBuildArchive___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_extraDepFacetConfig___closed__5;
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___elambda__1(uint8_t, lean_object*);
static lean_object* l_Lake_Package_depsFacetConfig___closed__3;
lean_object* l_Lake_untar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCache___closed__4;
static lean_object* l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeTransDeps___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___at_Lake_Package_fetchBuildArchive___spec__2(lean_object*);
extern lean_object* l_Lake_Git_defaultRemote;
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_depsFacetConfig___elambda__1___spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_releaseFacetConfig;
LEAN_EXPORT lean_object* l_Lake_EquipT_map___at_Lake_Package_recFetchDeps___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__7___closed__2;
lean_object* l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1(uint8_t, lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__10;
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig;
lean_object* l_Lake_Job_bindM___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___lambda__2___closed__1;
static lean_object* l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_recFetchDeps___lambda__1(lean_object*);
static lean_object* l_Lake_Package_recFetchDeps___lambda__1___closed__1;
uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
static lean_object* l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_stdFormat___at_Lake_Package_optBuildCacheFacetConfig___elambda__1___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_depsFacetConfig;
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterBuildCacheSync___spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeTransDeps___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterBuildCacheSync___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_depsFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_Package_recComputeTransDeps___spec__5___at_Lake_Package_recComputeTransDeps___spec__6(lean_object*, lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCache___closed__1;
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_recComputeTransDeps___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___elambda__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_Package_getReleaseUrl___closed__5;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_Package_recComputeTransDeps___spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_optBuildCacheFacetConfig___closed__3;
static lean_object* l_Lake_Package_getBarrelUrl___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_Package_barrelFacetConfig___closed__3;
lean_object* l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_extraDepFacetConfig___closed__2;
static lean_object* l_Lake_Package_extraDepFacetConfig___closed__3;
static lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___closed__1;
static lean_object* l_Lake_Package_barrelFacetConfig___elambda__2___closed__3;
static lean_object* l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__5;
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterBuildCacheSync___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getReleaseUrl___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_Package_recComputeTransDeps___spec__5(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterBuildCacheSync___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___lambda__2___closed__3;
static lean_object* l_Lake_Package_extraDepFacetConfig___closed__4;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
lean_object* l_Substring_prevn(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig;
static lean_object* l_Lake_Package_getReleaseUrl___closed__4;
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Lake_uriEncode(lean_object*);
static lean_object* l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig;
static lean_object* l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_fetchOptRelease(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instHashablePackage___boxed(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__3;
static lean_object* l_Lake_Package_getReleaseUrl___closed__13;
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_fetchBuildArchive___closed__3;
static lean_object* l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig___elambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_initPackageFacetConfigs___closed__4;
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseAsync___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_depsFacetConfig___elambda__1___spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_fetchBuildArchive___closed__1;
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterBuildCacheSync___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_JobAction_merge(uint8_t, uint8_t);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync(lean_object*);
static lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___closed__3;
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_Package_recBuildExtraDepTargets___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_recBuildExtraDepTargets___closed__2;
size_t lean_usize_sub(size_t, size_t);
static lean_object* l_Lake_Package_getBarrelUrl___lambda__2___closed__13;
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___lambda__2___closed__12;
LEAN_EXPORT lean_object* l_IO_withStderr___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___lambda__1(lean_object*);
static lean_object* l_Lake_Package_recBuildExtraDepTargets___closed__4;
static lean_object* l_Lake_Package_gitHubReleaseFacetConfig___closed__3;
LEAN_EXPORT lean_object* l_Lake_EquipT_pure___at_Lake_Package_recComputeTransDeps___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initPackageFacetConfigs___closed__7;
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lake_Package_getReleaseUrl___closed__8;
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___elambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___elambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__2___closed__3;
lean_object* l_Lake_Env_toolchain(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__2;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__1;
static lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___closed__2;
lean_object* l_Lean_RBNode_insert___at_Lake_Workspace_addPackageFacetConfig___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instBEqPackage___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Package_depsFacetConfig___closed__5;
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig___elambda__1(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterBuildCacheSync___spec__3(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__1(uint8_t, lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__4;
static lean_object* l_Lake_Package_extraDepFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getReleaseUrl___lambda__1___closed__1;
static lean_object* l_Lake_initPackageFacetConfigs___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___closed__3;
static lean_object* l_Lake_Package_barrelFacetConfig___elambda__2___closed__1;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_Package_recFetchDeps___boxed__const__1;
static lean_object* l_Lake_Package_recComputeTransDeps___closed__1;
static lean_object* l_Lake_Package_recFetchDeps___closed__1;
static lean_object* l_Lake_initPackageFacetConfigs___closed__6;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__8;
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getReleaseUrl___closed__14;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_depsFacetConfig___elambda__1___spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_optBarrelFacetConfig___closed__1;
static lean_object* l_Lake_Package_getBarrelUrl___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___elambda__1(uint8_t, lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___lambda__2___closed__14;
static lean_object* l_Lake_Package_getBarrelUrl___lambda__2___closed__6;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_depsFacetConfig___elambda__1___spec__2___closed__1;
static lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lake_EquipT_tryCatch___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___lambda__2___closed__7;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___at_Lake_Package_fetchBuildArchive___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Package_afterBuildCacheSync___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Reservoir_pkgApiUrl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": package not found for dependency '", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' (this is likely a bug in Lake)", 32, 32);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_4, x_3, x_15);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_8, 1);
x_19 = lean_ctor_get(x_18, 4);
x_20 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_19, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_16);
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 2);
lean_inc(x_22);
lean_dec(x_21);
x_23 = 1;
x_24 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1;
x_25 = l_Lean_Name_toString(x_22, x_23, x_24);
x_26 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_28 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__3;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_Lean_Name_toString(x_17, x_23, x_24);
x_31 = lean_string_append(x_29, x_30);
lean_dec(x_30);
x_32 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__4;
x_33 = lean_string_append(x_31, x_32);
x_34 = 3;
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = lean_array_get_size(x_9);
x_37 = lean_array_push(x_9, x_35);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_10);
return x_39;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; 
lean_dec(x_17);
x_40 = lean_ctor_get(x_20, 0);
lean_inc(x_40);
lean_dec(x_20);
x_41 = 1;
x_42 = lean_usize_add(x_3, x_41);
x_43 = lean_array_uset(x_16, x_3, x_40);
x_3 = x_42;
x_4 = x_43;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EquipT_map___at_Lake_Package_recFetchDeps___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_apply_1(x_1, x_14);
lean_ctor_set(x_10, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_apply_1(x_1, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_ctor_get(x_10, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_23 = x_10;
} else {
 lean_dec_ref(x_10);
 x_23 = lean_box(0);
}
x_24 = lean_apply_1(x_1, x_21);
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_9, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_10);
if (x_29 == 0)
{
return x_9;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_10, 0);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_10);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_9, 0, x_32);
return x_9;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_9, 1);
lean_inc(x_33);
lean_dec(x_9);
x_34 = lean_ctor_get(x_10, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_10, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_36 = x_10;
} else {
 lean_dec_ref(x_10);
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
uint8_t x_39; 
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_9);
if (x_39 == 0)
{
return x_9;
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
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EquipT_map___at_Lake_Package_recFetchDeps___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_EquipT_map___at_Lake_Package_recFetchDeps___spec__2___rarg), 8, 0);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_recFetchDeps___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_recFetchDeps___lambda__1___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Package_recFetchDeps___lambda__1___closed__1;
x_2 = 0;
x_3 = l_Lake_BuildTrace_nil;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recFetchDeps___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_2 = l_Lake_Package_recFetchDeps___lambda__1___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
x_4 = lean_task_pure(x_3);
x_5 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_6 = 0;
x_7 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*2, x_6);
return x_7;
}
}
static lean_object* _init_l_Lake_Package_recFetchDeps___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_recFetchDeps___lambda__1), 1, 0);
return x_1;
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
lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_1, 7);
lean_inc(x_8);
x_9 = lean_array_size(x_8);
x_10 = lean_box_usize(x_9);
x_11 = l_Lake_Package_recFetchDeps___boxed__const__1;
x_12 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___boxed), 10, 4);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, x_8);
x_13 = l_Lake_Package_recFetchDeps___closed__1;
x_14 = lean_alloc_closure((void*)(l_Lake_EquipT_map___at_Lake_Package_recFetchDeps___spec__2___rarg), 8, 2);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_12);
x_15 = l_Lake_ensureJob___rarg(x_14, x_2, x_3, x_4, x_5, x_6, x_7);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Package_depsFacetConfig___elambda__1___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_depsFacetConfig___elambda__1___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_8 = lean_string_append(x_7, x_4);
lean_dec(x_4);
x_9 = lean_string_append(x_8, x_7);
x_10 = lean_ctor_get(x_6, 2);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec(x_10);
x_12 = 1;
x_13 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1;
x_14 = l_Lean_Name_toString(x_11, x_12, x_13);
x_15 = lean_string_append(x_9, x_14);
lean_dec(x_14);
x_16 = l_Array_foldlMUnsafe_fold___at_Lake_Package_depsFacetConfig___elambda__1___spec__2___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_2 = x_19;
x_4 = x_17;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_depsFacetConfig___elambda__1___spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = 1;
x_11 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1;
x_12 = l_Lean_Name_toString(x_9, x_10, x_11);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_7, x_2, x_13);
x_2 = x_15;
x_3 = x_16;
goto _start;
}
}
}
static lean_object* _init_l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__2;
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__3;
x_4 = l_Substring_prevn(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__4;
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__5;
x_4 = lean_string_utf8_extract(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__6;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__6;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_12 = l_Array_foldlMUnsafe_fold___at_Lake_Package_depsFacetConfig___elambda__1___spec__2(x_2, x_9, x_10, x_11);
lean_dec(x_2);
x_13 = lean_string_utf8_byte_size(x_12);
lean_inc(x_13);
lean_inc(x_12);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_nat_sub(x_13, x_4);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Substring_prevn(x_14, x_16, x_15);
lean_dec(x_14);
x_18 = lean_nat_add(x_4, x_17);
lean_dec(x_17);
x_19 = lean_string_utf8_extract(x_12, x_4, x_18);
lean_dec(x_18);
lean_dec(x_12);
return x_19;
}
}
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_array_size(x_2);
x_21 = 0;
x_22 = l_Array_mapMUnsafe_map___at_Lake_Package_depsFacetConfig___elambda__1___spec__3(x_20, x_21, x_2);
x_23 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_Json_compress(x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_depsFacetConfig___elambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_depsFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("deps", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_depsFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_depsFacetConfig___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_depsFacetConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_recFetchDeps), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_depsFacetConfig___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_depsFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_depsFacetConfig___closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Package_depsFacetConfig___closed__3;
x_2 = 0;
x_3 = l_Lake_Package_depsFacetConfig___closed__4;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_depsFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_depsFacetConfig___closed__5;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_depsFacetConfig___elambda__1___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_Package_depsFacetConfig___elambda__1___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_depsFacetConfig___elambda__1___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_Package_depsFacetConfig___elambda__1___spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_depsFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Package_depsFacetConfig___elambda__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Package_recComputeTransDeps___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_4, 2);
x_7 = lean_ctor_get(x_6, 2);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_8, 2);
x_10 = lean_name_eq(x_7, x_9);
if (x_10 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_Package_recComputeTransDeps___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_2, x_20);
lean_ctor_set(x_3, 2, x_21);
x_22 = lean_array_uset(x_2, x_20, x_3);
x_2 = x_22;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
x_26 = lean_ctor_get(x_3, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_27 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_24);
x_28 = lean_apply_1(x_1, x_24);
x_29 = lean_unbox_uint64(x_28);
lean_dec(x_28);
x_30 = 32;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = 16;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_38 = 1;
x_39 = lean_usize_sub(x_37, x_38);
x_40 = lean_usize_land(x_36, x_39);
x_41 = lean_array_uget(x_2, x_40);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_24);
lean_ctor_set(x_42, 1, x_25);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_array_uset(x_2, x_40, x_42);
x_2 = x_43;
x_3 = x_26;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_Package_recComputeTransDeps___spec__5___at_Lake_Package_recComputeTransDeps___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Name_hash___override(x_8);
lean_dec(x_8);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_1, x_20);
lean_ctor_set(x_2, 2, x_21);
x_22 = lean_array_uset(x_1, x_20, x_2);
x_1 = x_22;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
x_26 = lean_ctor_get(x_2, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_2);
x_27 = lean_array_get_size(x_1);
x_28 = lean_ctor_get(x_24, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 2);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Name_hash___override(x_29);
lean_dec(x_29);
x_31 = 32;
x_32 = lean_uint64_shift_right(x_30, x_31);
x_33 = lean_uint64_xor(x_30, x_32);
x_34 = 16;
x_35 = lean_uint64_shift_right(x_33, x_34);
x_36 = lean_uint64_xor(x_33, x_35);
x_37 = lean_uint64_to_usize(x_36);
x_38 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_39 = 1;
x_40 = lean_usize_sub(x_38, x_39);
x_41 = lean_usize_land(x_37, x_40);
x_42 = lean_array_uget(x_1, x_41);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_24);
lean_ctor_set(x_43, 1, x_25);
lean_ctor_set(x_43, 2, x_42);
x_44 = lean_array_uset(x_1, x_41, x_43);
x_1 = x_44;
x_2 = x_26;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_Package_recComputeTransDeps___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_Package_recComputeTransDeps___spec__5___at_Lake_Package_recComputeTransDeps___spec__6(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_Package_recComputeTransDeps___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_Package_recComputeTransDeps___spec__4(x_7, x_1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeTransDeps___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instHashablePackage___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeTransDeps___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instBEqPackage___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeTransDeps___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; uint8_t x_23; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Name_hash___override(x_9);
lean_dec(x_9);
x_11 = 32;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = 16;
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = lean_uint64_xor(x_13, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_19 = 1;
x_20 = lean_usize_sub(x_18, x_19);
x_21 = lean_usize_land(x_17, x_20);
x_22 = lean_array_uget(x_6, x_21);
x_23 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Package_recComputeTransDeps___spec__2(x_2, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_dec(x_1);
lean_inc(x_2);
x_25 = lean_array_push(x_24, x_2);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_22);
x_30 = lean_array_uset(x_6, x_21, x_29);
x_31 = lean_unsigned_to_nat(4u);
x_32 = lean_nat_mul(x_27, x_31);
x_33 = lean_unsigned_to_nat(3u);
x_34 = lean_nat_div(x_32, x_33);
lean_dec(x_32);
x_35 = lean_array_get_size(x_30);
x_36 = lean_nat_dec_le(x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_Package_recComputeTransDeps___spec__3(x_30);
lean_ctor_set(x_3, 1, x_37);
lean_ctor_set(x_3, 0, x_27);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_3);
lean_ctor_set(x_38, 1, x_25);
return x_38;
}
else
{
lean_object* x_39; 
lean_ctor_set(x_3, 1, x_30);
lean_ctor_set(x_3, 0, x_27);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_3);
lean_ctor_set(x_39, 1, x_25);
return x_39;
}
}
else
{
lean_dec(x_22);
lean_free_object(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_1;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; size_t x_52; size_t x_53; size_t x_54; size_t x_55; size_t x_56; lean_object* x_57; uint8_t x_58; 
x_40 = lean_ctor_get(x_3, 0);
x_41 = lean_ctor_get(x_3, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_3);
x_42 = lean_array_get_size(x_41);
x_43 = lean_ctor_get(x_2, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 2);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Lean_Name_hash___override(x_44);
lean_dec(x_44);
x_46 = 32;
x_47 = lean_uint64_shift_right(x_45, x_46);
x_48 = lean_uint64_xor(x_45, x_47);
x_49 = 16;
x_50 = lean_uint64_shift_right(x_48, x_49);
x_51 = lean_uint64_xor(x_48, x_50);
x_52 = lean_uint64_to_usize(x_51);
x_53 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_54 = 1;
x_55 = lean_usize_sub(x_53, x_54);
x_56 = lean_usize_land(x_52, x_55);
x_57 = lean_array_uget(x_41, x_56);
x_58 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Package_recComputeTransDeps___spec__2(x_2, x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_59 = lean_ctor_get(x_1, 1);
lean_inc(x_59);
lean_dec(x_1);
lean_inc(x_2);
x_60 = lean_array_push(x_59, x_2);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_40, x_61);
lean_dec(x_40);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_2);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_57);
x_65 = lean_array_uset(x_41, x_56, x_64);
x_66 = lean_unsigned_to_nat(4u);
x_67 = lean_nat_mul(x_62, x_66);
x_68 = lean_unsigned_to_nat(3u);
x_69 = lean_nat_div(x_67, x_68);
lean_dec(x_67);
x_70 = lean_array_get_size(x_65);
x_71 = lean_nat_dec_le(x_69, x_70);
lean_dec(x_70);
lean_dec(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_Package_recComputeTransDeps___spec__3(x_65);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_62);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_60);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_62);
lean_ctor_set(x_75, 1, x_65);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_60);
return x_76;
}
}
else
{
lean_dec(x_57);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_2);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeTransDeps___spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeTransDeps___spec__1(x_4, x_6);
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
LEAN_EXPORT lean_object* l_Lake_EquipT_pure___at_Lake_Package_recComputeTransDeps___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_EquipT_pure___at_Lake_Package_recComputeTransDeps___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_EquipT_pure___at_Lake_Package_recComputeTransDeps___spec__8___rarg___boxed), 7, 0);
return x_2;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeTransDeps___spec__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("transDeps", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeTransDeps___spec__9___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeTransDeps___spec__9___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeTransDeps___spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_37; 
x_37 = lean_usize_dec_eq(x_3, x_4);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_array_uget(x_2, x_3);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_ctor_get(x_9, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 4);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_41, x_39);
lean_dec(x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_5);
x_43 = lean_ctor_get(x_1, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 2);
lean_inc(x_44);
lean_dec(x_43);
x_45 = 1;
x_46 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1;
x_47 = l_Lean_Name_toString(x_44, x_45, x_46);
x_48 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_49 = lean_string_append(x_48, x_47);
lean_dec(x_47);
x_50 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__3;
x_51 = lean_string_append(x_49, x_50);
x_52 = l_Lean_Name_toString(x_39, x_45, x_46);
x_53 = lean_string_append(x_51, x_52);
lean_dec(x_52);
x_54 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__4;
x_55 = lean_string_append(x_53, x_54);
x_56 = 3;
x_57 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_56);
x_58 = lean_array_get_size(x_10);
x_59 = lean_array_push(x_10, x_57);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_11);
x_12 = x_61;
goto block_36;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_105; lean_object* x_106; lean_object* x_122; lean_object* x_123; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_39);
x_62 = lean_ctor_get(x_42, 0);
lean_inc(x_62);
lean_dec(x_42);
x_147 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeTransDeps___spec__9___closed__2;
lean_inc(x_62);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_62);
lean_ctor_set(x_148, 1, x_147);
lean_inc(x_6);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_149 = lean_apply_6(x_6, x_148, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
lean_dec(x_150);
x_154 = lean_ctor_get(x_152, 0);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_io_wait(x_154, x_151);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_155, 1);
lean_inc(x_158);
lean_dec(x_155);
x_159 = !lean_is_exclusive(x_156);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_160 = lean_ctor_get(x_156, 0);
x_161 = lean_ctor_get(x_156, 1);
lean_dec(x_161);
x_162 = lean_ctor_get(x_157, 0);
lean_inc(x_162);
lean_dec(x_157);
x_163 = lean_array_get_size(x_162);
x_164 = lean_unsigned_to_nat(0u);
x_165 = lean_nat_dec_lt(x_164, x_163);
if (x_165 == 0)
{
lean_dec(x_163);
lean_dec(x_162);
lean_ctor_set(x_156, 1, x_153);
x_122 = x_156;
x_123 = x_158;
goto block_146;
}
else
{
uint8_t x_166; 
x_166 = lean_nat_dec_le(x_163, x_163);
if (x_166 == 0)
{
lean_dec(x_163);
lean_dec(x_162);
lean_ctor_set(x_156, 1, x_153);
x_122 = x_156;
x_123 = x_158;
goto block_146;
}
else
{
size_t x_167; size_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
lean_free_object(x_156);
x_167 = 0;
x_168 = lean_usize_of_nat(x_163);
lean_dec(x_163);
x_169 = lean_box(0);
x_170 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_162, x_167, x_168, x_169, x_153, x_158);
lean_dec(x_162);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = !lean_is_exclusive(x_171);
if (x_173 == 0)
{
lean_object* x_174; 
x_174 = lean_ctor_get(x_171, 0);
lean_dec(x_174);
lean_ctor_set(x_171, 0, x_160);
x_122 = x_171;
x_123 = x_172;
goto block_146;
}
else
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_171, 1);
lean_inc(x_175);
lean_dec(x_171);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_160);
lean_ctor_set(x_176, 1, x_175);
x_122 = x_176;
x_123 = x_172;
goto block_146;
}
}
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_177 = lean_ctor_get(x_156, 0);
lean_inc(x_177);
lean_dec(x_156);
x_178 = lean_ctor_get(x_157, 0);
lean_inc(x_178);
lean_dec(x_157);
x_179 = lean_array_get_size(x_178);
x_180 = lean_unsigned_to_nat(0u);
x_181 = lean_nat_dec_lt(x_180, x_179);
if (x_181 == 0)
{
lean_object* x_182; 
lean_dec(x_179);
lean_dec(x_178);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_177);
lean_ctor_set(x_182, 1, x_153);
x_122 = x_182;
x_123 = x_158;
goto block_146;
}
else
{
uint8_t x_183; 
x_183 = lean_nat_dec_le(x_179, x_179);
if (x_183 == 0)
{
lean_object* x_184; 
lean_dec(x_179);
lean_dec(x_178);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_177);
lean_ctor_set(x_184, 1, x_153);
x_122 = x_184;
x_123 = x_158;
goto block_146;
}
else
{
size_t x_185; size_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_185 = 0;
x_186 = lean_usize_of_nat(x_179);
lean_dec(x_179);
x_187 = lean_box(0);
x_188 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_178, x_185, x_186, x_187, x_153, x_158);
lean_dec(x_178);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_192 = x_189;
} else {
 lean_dec_ref(x_189);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_177);
lean_ctor_set(x_193, 1, x_191);
x_122 = x_193;
x_123 = x_190;
goto block_146;
}
}
}
}
else
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_194 = lean_ctor_get(x_156, 1);
lean_inc(x_194);
x_195 = lean_ctor_get(x_155, 1);
lean_inc(x_195);
lean_dec(x_155);
x_196 = !lean_is_exclusive(x_156);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_197 = lean_ctor_get(x_156, 0);
x_198 = lean_ctor_get(x_156, 1);
lean_dec(x_198);
x_199 = lean_ctor_get(x_194, 0);
lean_inc(x_199);
lean_dec(x_194);
x_200 = lean_array_get_size(x_199);
x_201 = lean_unsigned_to_nat(0u);
x_202 = lean_nat_dec_lt(x_201, x_200);
if (x_202 == 0)
{
lean_dec(x_200);
lean_dec(x_199);
lean_ctor_set(x_156, 1, x_153);
x_122 = x_156;
x_123 = x_195;
goto block_146;
}
else
{
uint8_t x_203; 
x_203 = lean_nat_dec_le(x_200, x_200);
if (x_203 == 0)
{
lean_dec(x_200);
lean_dec(x_199);
lean_ctor_set(x_156, 1, x_153);
x_122 = x_156;
x_123 = x_195;
goto block_146;
}
else
{
size_t x_204; size_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
lean_free_object(x_156);
x_204 = 0;
x_205 = lean_usize_of_nat(x_200);
lean_dec(x_200);
x_206 = lean_box(0);
x_207 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_199, x_204, x_205, x_206, x_153, x_195);
lean_dec(x_199);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_210 = !lean_is_exclusive(x_208);
if (x_210 == 0)
{
lean_object* x_211; 
x_211 = lean_ctor_get(x_208, 0);
lean_dec(x_211);
lean_ctor_set_tag(x_208, 1);
lean_ctor_set(x_208, 0, x_197);
x_122 = x_208;
x_123 = x_209;
goto block_146;
}
else
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_208, 1);
lean_inc(x_212);
lean_dec(x_208);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_197);
lean_ctor_set(x_213, 1, x_212);
x_122 = x_213;
x_123 = x_209;
goto block_146;
}
}
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_214 = lean_ctor_get(x_156, 0);
lean_inc(x_214);
lean_dec(x_156);
x_215 = lean_ctor_get(x_194, 0);
lean_inc(x_215);
lean_dec(x_194);
x_216 = lean_array_get_size(x_215);
x_217 = lean_unsigned_to_nat(0u);
x_218 = lean_nat_dec_lt(x_217, x_216);
if (x_218 == 0)
{
lean_object* x_219; 
lean_dec(x_216);
lean_dec(x_215);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_214);
lean_ctor_set(x_219, 1, x_153);
x_122 = x_219;
x_123 = x_195;
goto block_146;
}
else
{
uint8_t x_220; 
x_220 = lean_nat_dec_le(x_216, x_216);
if (x_220 == 0)
{
lean_object* x_221; 
lean_dec(x_216);
lean_dec(x_215);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_214);
lean_ctor_set(x_221, 1, x_153);
x_122 = x_221;
x_123 = x_195;
goto block_146;
}
else
{
size_t x_222; size_t x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_222 = 0;
x_223 = lean_usize_of_nat(x_216);
lean_dec(x_216);
x_224 = lean_box(0);
x_225 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_215, x_222, x_223, x_224, x_153, x_195);
lean_dec(x_215);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec(x_225);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_229 = x_226;
} else {
 lean_dec_ref(x_226);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 2, 0);
} else {
 x_230 = x_229;
 lean_ctor_set_tag(x_230, 1);
}
lean_ctor_set(x_230, 0, x_214);
lean_ctor_set(x_230, 1, x_228);
x_122 = x_230;
x_123 = x_227;
goto block_146;
}
}
}
}
}
else
{
uint8_t x_231; 
lean_dec(x_153);
lean_dec(x_62);
lean_dec(x_5);
x_231 = !lean_is_exclusive(x_155);
if (x_231 == 0)
{
x_12 = x_155;
goto block_36;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_155, 0);
x_233 = lean_ctor_get(x_155, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_155);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
x_12 = x_234;
goto block_36;
}
}
}
else
{
uint8_t x_235; 
lean_dec(x_62);
lean_dec(x_5);
x_235 = !lean_is_exclusive(x_149);
if (x_235 == 0)
{
lean_object* x_236; uint8_t x_237; 
x_236 = lean_ctor_get(x_149, 0);
lean_dec(x_236);
x_237 = !lean_is_exclusive(x_150);
if (x_237 == 0)
{
x_12 = x_149;
goto block_36;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_150, 0);
x_239 = lean_ctor_get(x_150, 1);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_150);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
lean_ctor_set(x_149, 0, x_240);
x_12 = x_149;
goto block_36;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_241 = lean_ctor_get(x_149, 1);
lean_inc(x_241);
lean_dec(x_149);
x_242 = lean_ctor_get(x_150, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_150, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_244 = x_150;
} else {
 lean_dec_ref(x_150);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_243);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_241);
x_12 = x_246;
goto block_36;
}
}
}
else
{
uint8_t x_247; 
lean_dec(x_62);
lean_dec(x_5);
x_247 = !lean_is_exclusive(x_149);
if (x_247 == 0)
{
x_12 = x_149;
goto block_36;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_149, 0);
x_249 = lean_ctor_get(x_149, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_149);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
x_12 = x_250;
goto block_36;
}
}
block_104:
{
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_63, 0);
x_67 = lean_array_get_size(x_66);
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_nat_dec_lt(x_68, x_67);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_67);
lean_dec(x_66);
x_70 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeTransDeps___spec__1(x_5, x_62);
lean_ctor_set(x_63, 0, x_70);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_63);
lean_ctor_set(x_71, 1, x_64);
x_12 = x_71;
goto block_36;
}
else
{
uint8_t x_72; 
x_72 = lean_nat_dec_le(x_67, x_67);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_67);
lean_dec(x_66);
x_73 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeTransDeps___spec__1(x_5, x_62);
lean_ctor_set(x_63, 0, x_73);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_63);
lean_ctor_set(x_74, 1, x_64);
x_12 = x_74;
goto block_36;
}
else
{
size_t x_75; size_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = 0;
x_76 = lean_usize_of_nat(x_67);
lean_dec(x_67);
x_77 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeTransDeps___spec__7(x_66, x_75, x_76, x_5);
lean_dec(x_66);
x_78 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeTransDeps___spec__1(x_77, x_62);
lean_ctor_set(x_63, 0, x_78);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_63);
lean_ctor_set(x_79, 1, x_64);
x_12 = x_79;
goto block_36;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_80 = lean_ctor_get(x_63, 0);
x_81 = lean_ctor_get(x_63, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_63);
x_82 = lean_array_get_size(x_80);
x_83 = lean_unsigned_to_nat(0u);
x_84 = lean_nat_dec_lt(x_83, x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_82);
lean_dec(x_80);
x_85 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeTransDeps___spec__1(x_5, x_62);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_81);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_64);
x_12 = x_87;
goto block_36;
}
else
{
uint8_t x_88; 
x_88 = lean_nat_dec_le(x_82, x_82);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_82);
lean_dec(x_80);
x_89 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeTransDeps___spec__1(x_5, x_62);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_81);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_64);
x_12 = x_91;
goto block_36;
}
else
{
size_t x_92; size_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_92 = 0;
x_93 = lean_usize_of_nat(x_82);
lean_dec(x_82);
x_94 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeTransDeps___spec__7(x_80, x_92, x_93, x_5);
lean_dec(x_80);
x_95 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeTransDeps___spec__1(x_94, x_62);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_81);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_64);
x_12 = x_97;
goto block_36;
}
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_62);
lean_dec(x_5);
x_98 = !lean_is_exclusive(x_63);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_63);
lean_ctor_set(x_99, 1, x_64);
x_12 = x_99;
goto block_36;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_63, 0);
x_101 = lean_ctor_get(x_63, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_63);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_64);
x_12 = x_103;
goto block_36;
}
}
}
block_121:
{
if (lean_obj_tag(x_105) == 0)
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_105);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_105, 1);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec(x_108);
lean_ctor_set(x_105, 1, x_109);
x_63 = x_105;
x_64 = x_106;
goto block_104;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_105, 0);
x_111 = lean_ctor_get(x_105, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_105);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec(x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_112);
x_63 = x_113;
x_64 = x_106;
goto block_104;
}
}
else
{
uint8_t x_114; 
x_114 = !lean_is_exclusive(x_105);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_105, 1);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
lean_dec(x_115);
lean_ctor_set(x_105, 1, x_116);
x_63 = x_105;
x_64 = x_106;
goto block_104;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_105, 0);
x_118 = lean_ctor_get(x_105, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_105);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec(x_118);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_119);
x_63 = x_120;
x_64 = x_106;
goto block_104;
}
}
}
block_146:
{
if (lean_obj_tag(x_122) == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_122);
if (x_124 == 0)
{
lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_122, 1);
x_126 = 0;
x_127 = l_Lake_BuildTrace_nil;
x_128 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_127);
lean_ctor_set_uint8(x_128, sizeof(void*)*2, x_126);
lean_ctor_set(x_122, 1, x_128);
x_105 = x_122;
x_106 = x_123;
goto block_121;
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_129 = lean_ctor_get(x_122, 0);
x_130 = lean_ctor_get(x_122, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_122);
x_131 = 0;
x_132 = l_Lake_BuildTrace_nil;
x_133 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_132);
lean_ctor_set_uint8(x_133, sizeof(void*)*2, x_131);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_129);
lean_ctor_set(x_134, 1, x_133);
x_105 = x_134;
x_106 = x_123;
goto block_121;
}
}
else
{
uint8_t x_135; 
x_135 = !lean_is_exclusive(x_122);
if (x_135 == 0)
{
lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_122, 1);
x_137 = 0;
x_138 = l_Lake_BuildTrace_nil;
x_139 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_138);
lean_ctor_set_uint8(x_139, sizeof(void*)*2, x_137);
lean_ctor_set(x_122, 1, x_139);
x_105 = x_122;
x_106 = x_123;
goto block_121;
}
else
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_140 = lean_ctor_get(x_122, 0);
x_141 = lean_ctor_get(x_122, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_122);
x_142 = 0;
x_143 = l_Lake_BuildTrace_nil;
x_144 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set_uint8(x_144, sizeof(void*)*2, x_142);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_140);
lean_ctor_set(x_145, 1, x_144);
x_105 = x_145;
x_106 = x_123;
goto block_121;
}
}
}
}
}
else
{
lean_object* x_251; lean_object* x_252; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_5);
lean_ctor_set(x_251, 1, x_10);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_11);
return x_252;
}
block_36:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_5 = x_15;
x_10 = x_16;
x_11 = x_14;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_12, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_12, 0, x_25);
return x_12;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_dec(x_12);
x_27 = lean_ctor_get(x_13, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_29 = x_13;
} else {
 lean_dec_ref(x_13);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(1, 2, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_12);
if (x_32 == 0)
{
return x_12;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_12, 0);
x_34 = lean_ctor_get(x_12, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_12);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recComputeTransDeps___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_Lake_Package_recFetchDeps___lambda__1___closed__2;
lean_inc(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_task_pure(x_4);
x_6 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_7 = 0;
x_8 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_7);
return x_8;
}
}
static lean_object* _init_l_Lake_Package_recComputeTransDeps___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_recComputeTransDeps___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_recComputeTransDeps___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recComputeTransDeps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_1, 7);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_lt(x_10, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_12 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_13 = lean_alloc_closure((void*)(l_Lake_EquipT_pure___at_Lake_Package_recComputeTransDeps___spec__8___rarg___boxed), 7, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = l_Lake_Package_recComputeTransDeps___closed__1;
x_15 = lean_alloc_closure((void*)(l_Lake_EquipT_map___at_Lake_Package_recFetchDeps___spec__2___rarg), 8, 2);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_13);
x_16 = l_Lake_ensureJob___rarg(x_15, x_2, x_3, x_4, x_5, x_6, x_7);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_9, x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_18 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_19 = lean_alloc_closure((void*)(l_Lake_EquipT_pure___at_Lake_Package_recComputeTransDeps___spec__8___rarg___boxed), 7, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = l_Lake_Package_recComputeTransDeps___closed__1;
x_21 = lean_alloc_closure((void*)(l_Lake_EquipT_map___at_Lake_Package_recFetchDeps___spec__2___rarg), 8, 2);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, x_19);
x_22 = l_Lake_ensureJob___rarg(x_21, x_2, x_3, x_4, x_5, x_6, x_7);
return x_22;
}
else
{
size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_24 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_25 = l_Lake_Package_recComputeTransDeps___boxed__const__1;
x_26 = lean_box_usize(x_23);
x_27 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeTransDeps___spec__9___boxed), 11, 5);
lean_closure_set(x_27, 0, x_1);
lean_closure_set(x_27, 1, x_8);
lean_closure_set(x_27, 2, x_25);
lean_closure_set(x_27, 3, x_26);
lean_closure_set(x_27, 4, x_24);
x_28 = l_Lake_Package_recComputeTransDeps___closed__1;
x_29 = lean_alloc_closure((void*)(l_Lake_EquipT_map___at_Lake_Package_recFetchDeps___spec__2___rarg), 8, 2);
lean_closure_set(x_29, 0, x_28);
lean_closure_set(x_29, 1, x_27);
x_30 = l_Lake_ensureJob___rarg(x_29, x_2, x_3, x_4, x_5, x_6, x_7);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Package_recComputeTransDeps___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Package_recComputeTransDeps___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeTransDeps___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeTransDeps___spec__7(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_EquipT_pure___at_Lake_Package_recComputeTransDeps___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_EquipT_pure___at_Lake_Package_recComputeTransDeps___spec__8___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeTransDeps___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeTransDeps___spec__9(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recComputeTransDeps___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_recComputeTransDeps___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_transDepsFacetConfig___elambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1(x_1, x_2);
return x_3;
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
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_transDepsFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_transDepsFacetConfig___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Package_transDepsFacetConfig___closed__1;
x_2 = 0;
x_3 = l_Lake_Package_transDepsFacetConfig___closed__2;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_transDepsFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_transDepsFacetConfig___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_transDepsFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Package_transDepsFacetConfig___elambda__1(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optBarrel", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optRelease", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*29 + 1);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__2;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_apply_6(x_2, x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__4;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_apply_6(x_2, x_14, x_3, x_4, x_5, x_6, x_7);
return x_15;
}
}
}
static lean_object* _init_l_Lake_stdFormat___at_Lake_Package_optBuildCacheFacetConfig___elambda__1___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_stdFormat___at_Lake_Package_optBuildCacheFacetConfig___elambda__1___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_Package_optBuildCacheFacetConfig___elambda__1___spec__1(uint8_t x_1, uint8_t x_2) {
_start:
{
if (x_1 == 0)
{
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at_Lake_Package_optBuildCacheFacetConfig___elambda__1___spec__1___closed__1;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = l_Lake_stdFormat___at_Lake_Package_optBuildCacheFacetConfig___elambda__1___spec__1___closed__2;
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
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig___elambda__1(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at_Lake_Package_optBuildCacheFacetConfig___elambda__1___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optCache", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_optBuildCacheFacetConfig___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_optBuildCacheFacetConfig___elambda__2), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_optBuildCacheFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig___closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Package_optBuildCacheFacetConfig___closed__3;
x_2 = 1;
x_3 = l_Lake_Package_optBuildCacheFacetConfig___closed__4;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_optBuildCacheFacetConfig___closed__5;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_Package_optBuildCacheFacetConfig___elambda__1___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_stdFormat___at_Lake_Package_optBuildCacheFacetConfig___elambda__1___spec__1(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_Package_optBuildCacheFacetConfig___elambda__1(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_Package_maybeFetchBuildCache___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lake_Package_recFetchDeps___lambda__1___closed__2;
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_maybeFetchBuildCache___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_maybeFetchBuildCache___closed__1;
x_2 = lean_task_pure(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_maybeFetchBuildCache___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lake_Package_maybeFetchBuildCache___closed__2;
x_2 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_maybeFetchBuildCache___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("leanprover", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_maybeFetchBuildCache___closed__5() {
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
lean_object* x_8; lean_object* x_9; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_148 = lean_ctor_get(x_5, 1);
lean_inc(x_148);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec(x_148);
x_150 = lean_ctor_get_uint8(x_149, sizeof(void*)*11);
lean_dec(x_149);
if (x_150 == 0)
{
uint8_t x_151; lean_object* x_152; lean_object* x_153; 
x_151 = 1;
x_152 = lean_box(x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_6);
x_8 = x_153;
x_9 = x_7;
goto block_147;
}
else
{
uint8_t x_154; lean_object* x_155; lean_object* x_156; 
x_154 = 0;
x_155 = lean_box(x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_6);
x_8 = x_156;
x_9 = x_7;
goto block_147;
}
block_147:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 1);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 8);
lean_inc(x_15);
x_16 = l_System_FilePath_join(x_13, x_15);
lean_dec(x_15);
x_17 = l_System_FilePath_pathExists(x_16, x_9);
lean_dec(x_16);
x_18 = lean_unbox(x_11);
lean_dec(x_11);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = l_Lake_Package_maybeFetchBuildCache___closed__3;
lean_ctor_set(x_8, 0, x_21);
lean_ctor_set(x_17, 0, x_8);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = l_Lake_Package_maybeFetchBuildCache___closed__3;
lean_ctor_set(x_8, 0, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = lean_ctor_get_uint8(x_14, sizeof(void*)*29 + 1);
lean_dec(x_14);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_29 = lean_ctor_get(x_17, 1);
x_30 = lean_ctor_get(x_17, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lake_Env_toolchain(x_32);
lean_dec(x_32);
x_34 = lean_ctor_get(x_1, 5);
lean_inc(x_34);
x_35 = l_Lake_Package_maybeFetchBuildCache___closed__4;
x_36 = lean_string_dec_eq(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = l_Lake_Package_maybeFetchBuildCache___closed__5;
x_38 = lean_string_dec_eq(x_34, x_37);
lean_dec(x_34);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_33);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = l_Lake_Package_maybeFetchBuildCache___closed__3;
lean_ctor_set(x_8, 0, x_39);
lean_ctor_set(x_17, 0, x_8);
return x_17;
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_string_utf8_byte_size(x_33);
lean_dec(x_33);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_nat_dec_eq(x_40, x_41);
lean_dec(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_free_object(x_17);
lean_free_object(x_8);
x_43 = l_Lake_Package_optBuildCacheFacetConfig___closed__2;
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_apply_6(x_2, x_44, x_3, x_4, x_5, x_12, x_29);
return x_45;
}
else
{
lean_object* x_46; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = l_Lake_Package_maybeFetchBuildCache___closed__3;
lean_ctor_set(x_8, 0, x_46);
lean_ctor_set(x_17, 0, x_8);
return x_17;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_34);
x_47 = lean_string_utf8_byte_size(x_33);
lean_dec(x_33);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_nat_dec_eq(x_47, x_48);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_free_object(x_17);
lean_free_object(x_8);
x_50 = l_Lake_Package_optBuildCacheFacetConfig___closed__2;
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_apply_6(x_2, x_51, x_3, x_4, x_5, x_12, x_29);
return x_52;
}
else
{
lean_object* x_53; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = l_Lake_Package_maybeFetchBuildCache___closed__3;
lean_ctor_set(x_8, 0, x_53);
lean_ctor_set(x_17, 0, x_8);
return x_17;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_54 = lean_ctor_get(x_17, 1);
lean_inc(x_54);
lean_dec(x_17);
x_55 = lean_ctor_get(x_5, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lake_Env_toolchain(x_56);
lean_dec(x_56);
x_58 = lean_ctor_get(x_1, 5);
lean_inc(x_58);
x_59 = l_Lake_Package_maybeFetchBuildCache___closed__4;
x_60 = lean_string_dec_eq(x_58, x_59);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = l_Lake_Package_maybeFetchBuildCache___closed__5;
x_62 = lean_string_dec_eq(x_58, x_61);
lean_dec(x_58);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = l_Lake_Package_maybeFetchBuildCache___closed__3;
lean_ctor_set(x_8, 0, x_63);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_8);
lean_ctor_set(x_64, 1, x_54);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_string_utf8_byte_size(x_57);
lean_dec(x_57);
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_nat_dec_eq(x_65, x_66);
lean_dec(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_free_object(x_8);
x_68 = l_Lake_Package_optBuildCacheFacetConfig___closed__2;
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_apply_6(x_2, x_69, x_3, x_4, x_5, x_12, x_54);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = l_Lake_Package_maybeFetchBuildCache___closed__3;
lean_ctor_set(x_8, 0, x_71);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_8);
lean_ctor_set(x_72, 1, x_54);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
lean_dec(x_58);
x_73 = lean_string_utf8_byte_size(x_57);
lean_dec(x_57);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_nat_dec_eq(x_73, x_74);
lean_dec(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_free_object(x_8);
x_76 = l_Lake_Package_optBuildCacheFacetConfig___closed__2;
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_1);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_apply_6(x_2, x_77, x_3, x_4, x_5, x_12, x_54);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = l_Lake_Package_maybeFetchBuildCache___closed__3;
lean_ctor_set(x_8, 0, x_79);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_8);
lean_ctor_set(x_80, 1, x_54);
return x_80;
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_free_object(x_8);
x_81 = lean_ctor_get(x_17, 1);
lean_inc(x_81);
lean_dec(x_17);
x_82 = l_Lake_Package_optBuildCacheFacetConfig___closed__2;
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_apply_6(x_2, x_83, x_3, x_4, x_5, x_12, x_81);
return x_84;
}
}
else
{
uint8_t x_85; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_17);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_17, 0);
lean_dec(x_86);
x_87 = l_Lake_Package_maybeFetchBuildCache___closed__3;
lean_ctor_set(x_8, 0, x_87);
lean_ctor_set(x_17, 0, x_8);
return x_17;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_17, 1);
lean_inc(x_88);
lean_dec(x_17);
x_89 = l_Lake_Package_maybeFetchBuildCache___closed__3;
lean_ctor_set(x_8, 0, x_89);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_8);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_91 = lean_ctor_get(x_8, 0);
x_92 = lean_ctor_get(x_8, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_8);
x_93 = lean_ctor_get(x_1, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_1, 2);
lean_inc(x_94);
x_95 = lean_ctor_get(x_94, 8);
lean_inc(x_95);
x_96 = l_System_FilePath_join(x_93, x_95);
lean_dec(x_95);
x_97 = l_System_FilePath_pathExists(x_96, x_9);
lean_dec(x_96);
x_98 = lean_unbox(x_91);
lean_dec(x_91);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_94);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_100 = x_97;
} else {
 lean_dec_ref(x_97);
 x_100 = lean_box(0);
}
x_101 = l_Lake_Package_maybeFetchBuildCache___closed__3;
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_92);
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_100;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_99);
return x_103;
}
else
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_97, 0);
lean_inc(x_104);
x_105 = lean_unbox(x_104);
lean_dec(x_104);
if (x_105 == 0)
{
uint8_t x_106; 
x_106 = lean_ctor_get_uint8(x_94, sizeof(void*)*29 + 1);
lean_dec(x_94);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_107 = lean_ctor_get(x_97, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_108 = x_97;
} else {
 lean_dec_ref(x_97);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_5, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_111 = l_Lake_Env_toolchain(x_110);
lean_dec(x_110);
x_112 = lean_ctor_get(x_1, 5);
lean_inc(x_112);
x_113 = l_Lake_Package_maybeFetchBuildCache___closed__4;
x_114 = lean_string_dec_eq(x_112, x_113);
if (x_114 == 0)
{
lean_object* x_115; uint8_t x_116; 
x_115 = l_Lake_Package_maybeFetchBuildCache___closed__5;
x_116 = lean_string_dec_eq(x_112, x_115);
lean_dec(x_112);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_111);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_117 = l_Lake_Package_maybeFetchBuildCache___closed__3;
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_92);
if (lean_is_scalar(x_108)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_108;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_107);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_120 = lean_string_utf8_byte_size(x_111);
lean_dec(x_111);
x_121 = lean_unsigned_to_nat(0u);
x_122 = lean_nat_dec_eq(x_120, x_121);
lean_dec(x_120);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_108);
x_123 = l_Lake_Package_optBuildCacheFacetConfig___closed__2;
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_1);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_apply_6(x_2, x_124, x_3, x_4, x_5, x_92, x_107);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_126 = l_Lake_Package_maybeFetchBuildCache___closed__3;
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_92);
if (lean_is_scalar(x_108)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_108;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_107);
return x_128;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; 
lean_dec(x_112);
x_129 = lean_string_utf8_byte_size(x_111);
lean_dec(x_111);
x_130 = lean_unsigned_to_nat(0u);
x_131 = lean_nat_dec_eq(x_129, x_130);
lean_dec(x_129);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_108);
x_132 = l_Lake_Package_optBuildCacheFacetConfig___closed__2;
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_1);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_apply_6(x_2, x_133, x_3, x_4, x_5, x_92, x_107);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_135 = l_Lake_Package_maybeFetchBuildCache___closed__3;
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_92);
if (lean_is_scalar(x_108)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_108;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_107);
return x_137;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_97, 1);
lean_inc(x_138);
lean_dec(x_97);
x_139 = l_Lake_Package_optBuildCacheFacetConfig___closed__2;
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_1);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_apply_6(x_2, x_140, x_3, x_4, x_5, x_92, x_138);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_94);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_142 = lean_ctor_get(x_97, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_143 = x_97;
} else {
 lean_dec_ref(x_97);
 x_143 = lean_box(0);
}
x_144 = l_Lake_Package_maybeFetchBuildCache___closed__3;
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_92);
if (lean_is_scalar(x_143)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_143;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_142);
return x_146;
}
}
}
}
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" (run with '-v' for details)", 28, 28);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" (see '", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' for details)", 14, 14);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*1 + 3);
x_12 = 2;
x_13 = l_Lake_instDecidableEqVerbosity(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__1;
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
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
lean_dec(x_17);
x_19 = 1;
x_20 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1;
x_21 = l_Lean_Name_toString(x_18, x_19, x_20);
x_22 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__2;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_25 = lean_string_append(x_23, x_24);
x_26 = l_Lean_Name_toString(x_2, x_19, x_20);
x_27 = lean_string_append(x_25, x_26);
lean_dec(x_26);
x_28 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__4;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_7);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_8);
return x_31;
}
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_34 = lean_ctor_get(x_7, 1);
lean_inc(x_34);
lean_inc(x_32);
lean_dec(x_7);
x_35 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_33);
x_36 = lean_ctor_get(x_6, 0);
x_37 = lean_ctor_get_uint8(x_36, sizeof(void*)*1 + 3);
x_38 = 2;
x_39 = l_Lake_instDecidableEqVerbosity(x_37, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_2);
lean_dec(x_1);
x_40 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__1;
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_35);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_8);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_43 = lean_ctor_get(x_1, 2);
lean_inc(x_43);
lean_dec(x_1);
x_44 = lean_ctor_get(x_43, 2);
lean_inc(x_44);
lean_dec(x_43);
x_45 = 1;
x_46 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1;
x_47 = l_Lean_Name_toString(x_44, x_45, x_46);
x_48 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__2;
x_49 = lean_string_append(x_48, x_47);
lean_dec(x_47);
x_50 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_51 = lean_string_append(x_49, x_50);
x_52 = l_Lean_Name_toString(x_2, x_45, x_46);
x_53 = lean_string_append(x_51, x_52);
lean_dec(x_52);
x_54 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__4;
x_55 = lean_string_append(x_53, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_35);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_8);
return x_57;
}
}
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
static lean_object* _init_l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("building from source; failed to fetch Reservoir build", 53, 53);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__1;
x_2 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__2;
x_2 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__3;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__2;
x_2 = 1;
x_3 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("building from source; failed to fetch GitHub release", 52, 52);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__6;
x_2 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__7;
x_2 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__9() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 2;
x_2 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__8;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__10() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__4;
x_2 = 1;
x_3 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_2 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get_uint8(x_9, sizeof(void*)*29 + 1);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*1 + 3);
x_15 = 2;
x_16 = l_Lake_instDecidableEqVerbosity(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_9);
x_17 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__4;
x_18 = lean_array_push(x_12, x_17);
lean_ctor_set(x_7, 0, x_18);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_8);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_22 = lean_ctor_get(x_9, 2);
lean_inc(x_22);
lean_dec(x_9);
x_23 = 1;
x_24 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1;
x_25 = l_Lean_Name_toString(x_22, x_23, x_24);
x_26 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__2;
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_28 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__5;
x_31 = lean_string_append(x_29, x_30);
x_32 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__4;
x_33 = lean_string_append(x_31, x_32);
x_34 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__1;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_37 = lean_string_append(x_35, x_36);
x_38 = 0;
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_38);
x_40 = lean_array_push(x_12, x_39);
lean_ctor_set(x_7, 0, x_40);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_7);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_8);
return x_43;
}
}
else
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; 
x_44 = lean_ctor_get(x_7, 0);
x_45 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_46 = lean_ctor_get(x_7, 1);
lean_inc(x_46);
lean_inc(x_44);
lean_dec(x_7);
x_47 = lean_ctor_get(x_6, 0);
x_48 = lean_ctor_get_uint8(x_47, sizeof(void*)*1 + 3);
x_49 = 2;
x_50 = l_Lake_instDecidableEqVerbosity(x_48, x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_9);
x_51 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__4;
x_52 = lean_array_push(x_44, x_51);
x_53 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_46);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_45);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_8);
return x_56;
}
else
{
lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_57 = lean_ctor_get(x_9, 2);
lean_inc(x_57);
lean_dec(x_9);
x_58 = 1;
x_59 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1;
x_60 = l_Lean_Name_toString(x_57, x_58, x_59);
x_61 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__2;
x_62 = lean_string_append(x_61, x_60);
lean_dec(x_60);
x_63 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_64 = lean_string_append(x_62, x_63);
x_65 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__5;
x_66 = lean_string_append(x_64, x_65);
x_67 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__4;
x_68 = lean_string_append(x_66, x_67);
x_69 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__1;
x_70 = lean_string_append(x_69, x_68);
lean_dec(x_68);
x_71 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_72 = lean_string_append(x_70, x_71);
x_73 = 0;
x_74 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_73);
x_75 = lean_array_push(x_44, x_74);
x_76 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_46);
lean_ctor_set_uint8(x_76, sizeof(void*)*2, x_45);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_8);
return x_79;
}
}
}
else
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_7);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; 
x_81 = lean_ctor_get(x_7, 0);
x_82 = lean_ctor_get(x_6, 0);
x_83 = lean_ctor_get_uint8(x_82, sizeof(void*)*1 + 3);
x_84 = 2;
x_85 = l_Lake_instDecidableEqVerbosity(x_83, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_9);
x_86 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__9;
x_87 = lean_array_push(x_81, x_86);
lean_ctor_set(x_7, 0, x_87);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_7);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_8);
return x_90;
}
else
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_91 = lean_ctor_get(x_9, 2);
lean_inc(x_91);
lean_dec(x_9);
x_92 = 1;
x_93 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1;
x_94 = l_Lean_Name_toString(x_91, x_92, x_93);
x_95 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__2;
x_96 = lean_string_append(x_95, x_94);
lean_dec(x_94);
x_97 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_98 = lean_string_append(x_96, x_97);
x_99 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__10;
x_100 = lean_string_append(x_98, x_99);
x_101 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__4;
x_102 = lean_string_append(x_100, x_101);
x_103 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__6;
x_104 = lean_string_append(x_103, x_102);
lean_dec(x_102);
x_105 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_106 = lean_string_append(x_104, x_105);
x_107 = 2;
x_108 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set_uint8(x_108, sizeof(void*)*1, x_107);
x_109 = lean_array_push(x_81, x_108);
lean_ctor_set(x_7, 0, x_109);
x_110 = lean_box(0);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_7);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_8);
return x_112;
}
}
else
{
lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; 
x_113 = lean_ctor_get(x_7, 0);
x_114 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_115 = lean_ctor_get(x_7, 1);
lean_inc(x_115);
lean_inc(x_113);
lean_dec(x_7);
x_116 = lean_ctor_get(x_6, 0);
x_117 = lean_ctor_get_uint8(x_116, sizeof(void*)*1 + 3);
x_118 = 2;
x_119 = l_Lake_instDecidableEqVerbosity(x_117, x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_9);
x_120 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__9;
x_121 = lean_array_push(x_113, x_120);
x_122 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_115);
lean_ctor_set_uint8(x_122, sizeof(void*)*2, x_114);
x_123 = lean_box(0);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_8);
return x_125;
}
else
{
lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_126 = lean_ctor_get(x_9, 2);
lean_inc(x_126);
lean_dec(x_9);
x_127 = 1;
x_128 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1;
x_129 = l_Lean_Name_toString(x_126, x_127, x_128);
x_130 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__2;
x_131 = lean_string_append(x_130, x_129);
lean_dec(x_129);
x_132 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_133 = lean_string_append(x_131, x_132);
x_134 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__10;
x_135 = lean_string_append(x_133, x_134);
x_136 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__4;
x_137 = lean_string_append(x_135, x_136);
x_138 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__6;
x_139 = lean_string_append(x_138, x_137);
lean_dec(x_137);
x_140 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_141 = lean_string_append(x_139, x_140);
x_142 = 2;
x_143 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set_uint8(x_143, sizeof(void*)*1, x_142);
x_144 = lean_array_push(x_113, x_143);
x_145 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_115);
lean_ctor_set_uint8(x_145, sizeof(void*)*2, x_114);
x_146 = lean_box(0);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_145);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_8);
return x_148;
}
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_1);
x_149 = lean_box(0);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_7);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_8);
return x_151;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Lake_Package_maybeFetchBuildCache(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
x_14 = lean_alloc_closure((void*)(l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___boxed), 8, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = l_Task_Priority_default;
x_16 = 0;
x_17 = l_Lake_BuildTrace_nil;
x_18 = l_Lake_Job_mapM___rarg(x_12, x_14, x_15, x_16, x_2, x_3, x_4, x_5, x_17, x_10);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
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
uint8_t x_24; 
lean_free_object(x_9);
lean_dec(x_13);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_9);
x_30 = lean_alloc_closure((void*)(l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___boxed), 8, 1);
lean_closure_set(x_30, 0, x_1);
x_31 = l_Task_Priority_default;
x_32 = 0;
x_33 = l_Lake_BuildTrace_nil;
x_34 = l_Lake_Job_mapM___rarg(x_28, x_30, x_31, x_32, x_2, x_3, x_4, x_5, x_33, x_10);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_29);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_29);
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_42 = x_34;
} else {
 lean_dec_ref(x_34);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_8);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_8, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_9);
if (x_46 == 0)
{
return x_8;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_9, 0);
x_48 = lean_ctor_get(x_9, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_9);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_8, 0, x_49);
return x_8;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_8, 1);
lean_inc(x_50);
lean_dec(x_8);
x_51 = lean_ctor_get(x_9, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_9, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_53 = x_9;
} else {
 lean_dec_ref(x_9);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_50);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_8);
if (x_56 == 0)
{
return x_8;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_8, 0);
x_58 = lean_ctor_get(x_8, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_8);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_fetchOptRelease(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Package_maybeFetchBuildCacheWithWarning(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_6, x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_uget(x_4, x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_18 = l_Lake_Package_fetchTargetJob(x_1, x_17, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
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
x_23 = l_Lake_Job_mix___rarg(x_7, x_21);
x_24 = 1;
x_25 = lean_usize_add(x_6, x_24);
x_6 = x_25;
x_7 = x_23;
x_12 = x_22;
x_13 = x_20;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
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
uint8_t x_39; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_18, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_Package_recBuildExtraDepTargets___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_apply_7(x_2, x_12, x_3, x_4, x_5, x_6, x_13, x_11);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_9, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_24 = x_10;
} else {
 lean_dec_ref(x_10);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(1, 2, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
return x_9;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_9);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_Package_recBuildExtraDepTargets___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Package_recBuildExtraDepTargets___spec__2___rarg), 8, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 4);
x_12 = lean_box(0);
x_13 = lean_array_size(x_11);
x_14 = 0;
x_15 = l_Array_forIn_x27Unsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1(x_2, x_11, x_12, x_11, x_13, x_14, x_3, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_26 = x_16;
} else {
 lean_dec_ref(x_16);
 x_26 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_15, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
return x_15;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_15, 0, x_34);
return x_15;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_15, 1);
lean_inc(x_35);
lean_dec(x_15);
x_36 = lean_ctor_get(x_16, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_16, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_38 = x_16;
} else {
 lean_dec_ref(x_16);
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
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_15);
if (x_41 == 0)
{
return x_15;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_15, 0);
x_43 = lean_ctor_get(x_15, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_15);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_recFetchDeps___lambda__1___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__1;
x_2 = lean_task_pure(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__2;
x_2 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_11, 2);
x_13 = lean_ctor_get(x_12, 2);
x_14 = lean_name_eq(x_3, x_13);
x_15 = l_instDecidableNot___rarg(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__3;
x_17 = lean_box(0);
x_18 = l_Lake_Package_recBuildExtraDepTargets___lambda__3(x_1, x_2, x_16, x_17, x_5, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
else
{
lean_object* x_19; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_19 = l_Lake_Package_maybeFetchBuildCacheWithWarning(x_2, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__3;
x_25 = l_Lake_Job_add___rarg(x_24, x_22);
x_26 = lean_box(0);
x_27 = l_Lake_Package_recBuildExtraDepTargets___lambda__3(x_1, x_2, x_25, x_26, x_5, x_6, x_7, x_8, x_23, x_21);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_19, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_19;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_19, 0, x_33);
return x_19;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_dec(x_19);
x_35 = lean_ctor_get(x_20, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_37 = x_20;
} else {
 lean_dec_ref(x_20);
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
else
{
uint8_t x_40; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_19);
if (x_40 == 0)
{
return x_19;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_19, 0);
x_42 = lean_ctor_get(x_19, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_19);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":extraDep", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_recBuildExtraDepTargets___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_recBuildExtraDepTargets___lambda__2___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_recBuildExtraDepTargets___closed__2;
x_2 = l_Lake_Package_recBuildExtraDepTargets___closed__3;
x_3 = lean_alloc_closure((void*)(l_Lake_EquipT_map___at_Lake_Package_recFetchDeps___spec__2___rarg), 8, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
x_10 = 1;
x_11 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1;
lean_inc(x_9);
x_12 = l_Lean_Name_toString(x_9, x_10, x_11);
x_13 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_Lake_Package_recBuildExtraDepTargets___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_alloc_closure((void*)(l_Lake_Package_recBuildExtraDepTargets___lambda__4___boxed), 10, 3);
lean_closure_set(x_17, 0, x_8);
lean_closure_set(x_17, 1, x_1);
lean_closure_set(x_17, 2, x_9);
x_18 = l_Lake_Package_recBuildExtraDepTargets___closed__4;
x_19 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Package_recBuildExtraDepTargets___spec__2___rarg), 8, 2);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_17);
x_20 = 0;
x_21 = l_Lake_withRegisterJob___rarg(x_16, x_19, x_20, x_2, x_3, x_4, x_5, x_6, x_7);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_recBuildExtraDepTargets___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Package_recBuildExtraDepTargets___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_Package_recBuildExtraDepTargets___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_Package_recBuildExtraDepTargets___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___elambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_nullFormat___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("extraDep", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_extraDepFacetConfig___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_recBuildExtraDepTargets), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_extraDepFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig___closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Package_extraDepFacetConfig___closed__3;
x_2 = 1;
x_3 = l_Lake_Package_extraDepFacetConfig___closed__4;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_extraDepFacetConfig___closed__5;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Package_extraDepFacetConfig___elambda__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/barrel\?rev=", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("&toolchain=", 11, 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_12 = lean_string_append(x_11, x_3);
x_13 = l_Lake_Package_getBarrelUrl___lambda__1___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_string_append(x_14, x_1);
x_16 = l_Lake_Package_getBarrelUrl___lambda__1___closed__2;
x_17 = lean_string_append(x_15, x_16);
x_18 = l_Lake_Env_toolchain(x_2);
x_19 = l_Lake_uriEncode(x_18);
lean_dec(x_18);
x_20 = lean_string_append(x_17, x_19);
lean_dec(x_19);
x_21 = lean_string_append(x_20, x_11);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_9);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HEAD", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_getBarrelUrl___lambda__2___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--end-of-options", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_getBarrelUrl___lambda__2___closed__3;
x_2 = l_Lake_Package_getBarrelUrl___lambda__2___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--verify", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_getBarrelUrl___lambda__2___closed__5;
x_2 = l_Lake_Package_getBarrelUrl___lambda__2___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rev-parse", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_getBarrelUrl___lambda__2___closed__7;
x_2 = l_Lake_Package_getBarrelUrl___lambda__2___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_getBarrelUrl___lambda__2___closed__8;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___lambda__2___closed__10() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_2, 0, x_1);
lean_ctor_set_uint8(x_2, 1, x_1);
lean_ctor_set_uint8(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___lambda__2___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("git", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___lambda__2___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to resolve HEAD revision", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___lambda__2___closed__13() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 3;
x_2 = l_Lake_Package_getBarrelUrl___lambda__2___closed__12;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___lambda__2___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean toolchain not known; Reservoir only hosts builds for known toolchains", 74, 74);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___lambda__2___closed__15() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 3;
x_2 = l_Lake_Package_getBarrelUrl___lambda__2___closed__14;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 5);
lean_inc(x_11);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_9);
x_17 = l_Lake_Package_getBarrelUrl___lambda__2___closed__10;
x_18 = l_Lake_Package_getBarrelUrl___lambda__2___closed__11;
x_19 = l_Lake_Package_getBarrelUrl___lambda__2___closed__9;
x_20 = l_Lake_Package_recFetchDeps___lambda__1___closed__1;
x_21 = 0;
x_22 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_16);
lean_ctor_set(x_22, 4, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*5, x_21);
x_23 = l_Lake_captureProc_x3f(x_22, x_8);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_11);
lean_dec(x_10);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = lean_array_get_size(x_13);
x_28 = l_Lake_Package_getBarrelUrl___lambda__2___closed__13;
x_29 = lean_array_push(x_13, x_28);
lean_ctor_set(x_7, 0, x_29);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_7);
lean_ctor_set(x_23, 0, x_30);
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec(x_23);
x_32 = lean_array_get_size(x_13);
x_33 = l_Lake_Package_getBarrelUrl___lambda__2___closed__13;
x_34 = lean_array_push(x_13, x_33);
lean_ctor_set(x_7, 0, x_34);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_7);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_23);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_38 = lean_ctor_get(x_23, 1);
x_39 = lean_ctor_get(x_23, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_24, 0);
lean_inc(x_40);
lean_dec(x_24);
x_41 = lean_ctor_get(x_10, 2);
lean_inc(x_41);
lean_dec(x_10);
x_42 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1;
x_43 = l_Lean_Name_toString(x_41, x_21, x_42);
x_44 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_13);
x_45 = lean_ctor_get(x_44, 1);
x_46 = l_Lake_Reservoir_pkgApiUrl(x_45, x_11, x_43);
lean_dec(x_43);
lean_dec(x_11);
x_47 = l_Lake_Env_toolchain(x_45);
x_48 = lean_string_utf8_byte_size(x_47);
lean_dec(x_47);
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_nat_dec_eq(x_48, x_49);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_free_object(x_23);
lean_dec(x_15);
lean_dec(x_13);
x_51 = lean_box(0);
x_52 = l_Lake_Package_getBarrelUrl___lambda__1(x_40, x_45, x_46, x_51, x_3, x_4, x_5, x_6, x_7, x_38);
lean_dec(x_46);
lean_dec(x_40);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_40);
x_53 = lean_array_get_size(x_13);
x_54 = l_Lake_Package_getBarrelUrl___lambda__2___closed__15;
x_55 = lean_array_push(x_13, x_54);
x_56 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_15);
lean_ctor_set_uint8(x_56, sizeof(void*)*2, x_14);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_23, 0, x_57);
return x_23;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_58 = lean_ctor_get(x_23, 1);
lean_inc(x_58);
lean_dec(x_23);
x_59 = lean_ctor_get(x_24, 0);
lean_inc(x_59);
lean_dec(x_24);
x_60 = lean_ctor_get(x_10, 2);
lean_inc(x_60);
lean_dec(x_10);
x_61 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1;
x_62 = l_Lean_Name_toString(x_60, x_21, x_61);
x_63 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_13);
x_64 = lean_ctor_get(x_63, 1);
x_65 = l_Lake_Reservoir_pkgApiUrl(x_64, x_11, x_62);
lean_dec(x_62);
lean_dec(x_11);
x_66 = l_Lake_Env_toolchain(x_64);
x_67 = lean_string_utf8_byte_size(x_66);
lean_dec(x_66);
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_nat_dec_eq(x_67, x_68);
lean_dec(x_67);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_15);
lean_dec(x_13);
x_70 = lean_box(0);
x_71 = l_Lake_Package_getBarrelUrl___lambda__1(x_59, x_64, x_65, x_70, x_3, x_4, x_5, x_6, x_7, x_58);
lean_dec(x_65);
lean_dec(x_59);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_65);
lean_dec(x_7);
lean_dec(x_59);
x_72 = lean_array_get_size(x_13);
x_73 = l_Lake_Package_getBarrelUrl___lambda__2___closed__15;
x_74 = lean_array_push(x_13, x_73);
x_75 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_15);
lean_ctor_set_uint8(x_75, sizeof(void*)*2, x_14);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_58);
return x_77;
}
}
}
}
else
{
lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_78 = lean_ctor_get(x_7, 0);
x_79 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_80 = lean_ctor_get(x_7, 1);
lean_inc(x_80);
lean_inc(x_78);
lean_dec(x_7);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_9);
x_82 = l_Lake_Package_getBarrelUrl___lambda__2___closed__10;
x_83 = l_Lake_Package_getBarrelUrl___lambda__2___closed__11;
x_84 = l_Lake_Package_getBarrelUrl___lambda__2___closed__9;
x_85 = l_Lake_Package_recFetchDeps___lambda__1___closed__1;
x_86 = 0;
x_87 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_87, 0, x_82);
lean_ctor_set(x_87, 1, x_83);
lean_ctor_set(x_87, 2, x_84);
lean_ctor_set(x_87, 3, x_81);
lean_ctor_set(x_87, 4, x_85);
lean_ctor_set_uint8(x_87, sizeof(void*)*5, x_86);
x_88 = l_Lake_captureProc_x3f(x_87, x_8);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_11);
lean_dec(x_10);
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
x_92 = lean_array_get_size(x_78);
x_93 = l_Lake_Package_getBarrelUrl___lambda__2___closed__13;
x_94 = lean_array_push(x_78, x_93);
x_95 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_80);
lean_ctor_set_uint8(x_95, sizeof(void*)*2, x_79);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_92);
lean_ctor_set(x_96, 1, x_95);
if (lean_is_scalar(x_91)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_91;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_90);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_98 = lean_ctor_get(x_88, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_99 = x_88;
} else {
 lean_dec_ref(x_88);
 x_99 = lean_box(0);
}
x_100 = lean_ctor_get(x_89, 0);
lean_inc(x_100);
lean_dec(x_89);
x_101 = lean_ctor_get(x_10, 2);
lean_inc(x_101);
lean_dec(x_10);
x_102 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1;
x_103 = l_Lean_Name_toString(x_101, x_86, x_102);
x_104 = lean_ctor_get(x_6, 1);
lean_inc(x_80);
lean_inc(x_78);
x_105 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_105, 0, x_78);
lean_ctor_set(x_105, 1, x_80);
lean_ctor_set_uint8(x_105, sizeof(void*)*2, x_79);
x_106 = lean_ctor_get(x_104, 1);
x_107 = l_Lake_Reservoir_pkgApiUrl(x_106, x_11, x_103);
lean_dec(x_103);
lean_dec(x_11);
x_108 = l_Lake_Env_toolchain(x_106);
x_109 = lean_string_utf8_byte_size(x_108);
lean_dec(x_108);
x_110 = lean_unsigned_to_nat(0u);
x_111 = lean_nat_dec_eq(x_109, x_110);
lean_dec(x_109);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_99);
lean_dec(x_80);
lean_dec(x_78);
x_112 = lean_box(0);
x_113 = l_Lake_Package_getBarrelUrl___lambda__1(x_100, x_106, x_107, x_112, x_3, x_4, x_5, x_6, x_105, x_98);
lean_dec(x_107);
lean_dec(x_100);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_107);
lean_dec(x_105);
lean_dec(x_100);
x_114 = lean_array_get_size(x_78);
x_115 = l_Lake_Package_getBarrelUrl___lambda__2___closed__15;
x_116 = lean_array_push(x_78, x_115);
x_117 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_80);
lean_ctor_set_uint8(x_117, sizeof(void*)*2, x_79);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_114);
lean_ctor_set(x_118, 1, x_117);
if (lean_is_scalar(x_99)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_99;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_98);
return x_119;
}
}
}
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("package has no Reservoir scope", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getBarrelUrl___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 3;
x_2 = l_Lake_Package_getBarrelUrl___closed__1;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_1, 5);
lean_inc(x_8);
x_9 = lean_string_utf8_byte_size(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l_Lake_Package_getBarrelUrl___lambda__2(x_1, x_12, x_2, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_array_get_size(x_15);
x_17 = l_Lake_Package_getBarrelUrl___closed__2;
x_18 = lean_array_push(x_15, x_17);
lean_ctor_set(x_6, 0, x_18);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_6);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
lean_inc(x_21);
lean_dec(x_6);
x_24 = lean_array_get_size(x_21);
x_25 = l_Lake_Package_getBarrelUrl___closed__2;
x_26 = lean_array_push(x_21, x_25);
x_27 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_22);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_7);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_Package_getBarrelUrl___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Package_getBarrelUrl___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Package_getBarrelUrl(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lake_Package_getReleaseUrl___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no release tag found for revision", 33, 33);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_getReleaseUrl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; 
x_8 = l_Lake_Package_getReleaseUrl___lambda__1___closed__1;
x_9 = lean_string_append(x_8, x_1);
x_10 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = 3;
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_12);
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_array_get_size(x_15);
x_17 = lean_array_push(x_15, x_13);
lean_ctor_set(x_6, 0, x_17);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_6);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
lean_inc(x_20);
lean_dec(x_6);
x_23 = lean_array_get_size(x_20);
x_24 = lean_array_push(x_20, x_13);
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_21);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_7);
return x_27;
}
}
}
static lean_object* _init_l_Lake_Package_getReleaseUrl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--exact-match", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getReleaseUrl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_getReleaseUrl___closed__1;
x_2 = l_Lake_Package_getBarrelUrl___lambda__2___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_getReleaseUrl___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--tags", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getReleaseUrl___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_getReleaseUrl___closed__3;
x_2 = l_Lake_Package_getReleaseUrl___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_getReleaseUrl___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("describe", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getReleaseUrl___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_getReleaseUrl___closed__5;
x_2 = l_Lake_Package_getReleaseUrl___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_getReleaseUrl___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_getReleaseUrl___closed__6;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_getReleaseUrl___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_getReleaseUrl___lambda__1___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getReleaseUrl___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" '", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getReleaseUrl___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getReleaseUrl___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/releases/download/", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getReleaseUrl___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getReleaseUrl___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("release repository URL not known; the package may need to set 'releaseRepo'", 75, 75);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_getReleaseUrl___closed__14() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 3;
x_2 = l_Lake_Package_getReleaseUrl___closed__13;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_getReleaseUrl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 6);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 14);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
x_13 = l_Lake_Git_defaultRemote;
lean_inc(x_8);
x_14 = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(x_13, x_8, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_143; 
x_143 = lean_ctor_get(x_9, 13);
lean_inc(x_143);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_144 = lean_string_utf8_byte_size(x_10);
x_145 = lean_unsigned_to_nat(0u);
x_146 = lean_nat_dec_eq(x_144, x_145);
lean_dec(x_144);
if (x_146 == 0)
{
lean_object* x_147; 
lean_dec(x_10);
x_147 = lean_box(0);
x_15 = x_147;
goto block_142;
}
else
{
lean_object* x_148; 
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_10);
x_15 = x_148;
goto block_142;
}
}
else
{
uint8_t x_149; 
lean_dec(x_10);
x_149 = !lean_is_exclusive(x_143);
if (x_149 == 0)
{
x_15 = x_143;
goto block_142;
}
else
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_143, 0);
lean_inc(x_150);
lean_dec(x_143);
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_150);
x_15 = x_151;
goto block_142;
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_10);
x_152 = !lean_is_exclusive(x_11);
if (x_152 == 0)
{
x_15 = x_11;
goto block_142;
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_11, 0);
lean_inc(x_153);
lean_dec(x_11);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
x_15 = x_154;
goto block_142;
}
}
block_142:
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
x_19 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_21 = x_6;
} else {
 lean_dec_ref(x_6);
 x_21 = lean_box(0);
}
if (lean_obj_tag(x_15) == 0)
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_79 = lean_array_get_size(x_12);
x_80 = l_Lake_Package_getReleaseUrl___closed__14;
x_81 = lean_array_push(x_12, x_80);
x_82 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_20);
lean_ctor_set_uint8(x_82, sizeof(void*)*2, x_19);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set(x_14, 0, x_83);
return x_14;
}
else
{
lean_object* x_84; 
lean_free_object(x_14);
x_84 = lean_ctor_get(x_17, 0);
lean_inc(x_84);
lean_dec(x_17);
x_22 = x_84;
goto block_78;
}
}
else
{
lean_object* x_85; 
lean_free_object(x_14);
lean_dec(x_17);
x_85 = lean_ctor_get(x_15, 0);
lean_inc(x_85);
lean_dec(x_15);
x_22 = x_85;
goto block_78;
}
block_78:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_8);
x_24 = l_Lake_Package_getBarrelUrl___lambda__2___closed__10;
x_25 = l_Lake_Package_getBarrelUrl___lambda__2___closed__11;
x_26 = l_Lake_Package_getReleaseUrl___closed__7;
x_27 = l_Lake_Package_recFetchDeps___lambda__1___closed__1;
x_28 = 0;
lean_inc(x_23);
x_29 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_23);
lean_ctor_set(x_29, 4, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*5, x_28);
x_30 = l_Lake_captureProc_x3f(x_29, x_18);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_22);
lean_dec(x_9);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lake_Package_getReleaseUrl___closed__8;
x_34 = l_Lake_Package_getBarrelUrl___lambda__2___closed__9;
x_35 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_35, 0, x_24);
lean_ctor_set(x_35, 1, x_25);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set(x_35, 3, x_23);
lean_ctor_set(x_35, 4, x_27);
lean_ctor_set_uint8(x_35, sizeof(void*)*5, x_28);
x_36 = l_Lake_captureProc_x3f(x_35, x_32);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
if (lean_is_scalar(x_21)) {
 x_39 = lean_alloc_ctor(0, 2, 1);
} else {
 x_39 = x_21;
}
lean_ctor_set(x_39, 0, x_12);
lean_ctor_set(x_39, 1, x_20);
lean_ctor_set_uint8(x_39, sizeof(void*)*2, x_19);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_41 = lean_apply_7(x_33, x_40, x_2, x_3, x_4, x_5, x_39, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_37, 0);
lean_inc(x_42);
lean_dec(x_37);
x_43 = l_Lake_Package_getReleaseUrl___closed__9;
x_44 = lean_string_append(x_43, x_42);
lean_dec(x_42);
x_45 = l_Lake_Package_getReleaseUrl___closed__10;
x_46 = lean_string_append(x_44, x_45);
x_47 = lean_apply_7(x_33, x_46, x_2, x_3, x_4, x_5, x_39, x_38);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_30);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_49 = lean_ctor_get(x_30, 0);
lean_dec(x_49);
x_50 = lean_ctor_get(x_31, 0);
lean_inc(x_50);
lean_dec(x_31);
if (lean_is_scalar(x_21)) {
 x_51 = lean_alloc_ctor(0, 2, 1);
} else {
 x_51 = x_21;
}
lean_ctor_set(x_51, 0, x_12);
lean_ctor_set(x_51, 1, x_20);
lean_ctor_set_uint8(x_51, sizeof(void*)*2, x_19);
x_52 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_53 = lean_string_append(x_52, x_22);
lean_dec(x_22);
x_54 = l_Lake_Package_getReleaseUrl___closed__11;
x_55 = lean_string_append(x_53, x_54);
x_56 = lean_string_append(x_55, x_50);
lean_dec(x_50);
x_57 = l_Lake_Package_getReleaseUrl___closed__12;
x_58 = lean_string_append(x_56, x_57);
x_59 = lean_ctor_get(x_9, 16);
lean_inc(x_59);
lean_dec(x_9);
x_60 = lean_string_append(x_58, x_59);
lean_dec(x_59);
x_61 = lean_string_append(x_60, x_52);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_51);
lean_ctor_set(x_30, 0, x_62);
return x_30;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_63 = lean_ctor_get(x_30, 1);
lean_inc(x_63);
lean_dec(x_30);
x_64 = lean_ctor_get(x_31, 0);
lean_inc(x_64);
lean_dec(x_31);
if (lean_is_scalar(x_21)) {
 x_65 = lean_alloc_ctor(0, 2, 1);
} else {
 x_65 = x_21;
}
lean_ctor_set(x_65, 0, x_12);
lean_ctor_set(x_65, 1, x_20);
lean_ctor_set_uint8(x_65, sizeof(void*)*2, x_19);
x_66 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_67 = lean_string_append(x_66, x_22);
lean_dec(x_22);
x_68 = l_Lake_Package_getReleaseUrl___closed__11;
x_69 = lean_string_append(x_67, x_68);
x_70 = lean_string_append(x_69, x_64);
lean_dec(x_64);
x_71 = l_Lake_Package_getReleaseUrl___closed__12;
x_72 = lean_string_append(x_70, x_71);
x_73 = lean_ctor_get(x_9, 16);
lean_inc(x_73);
lean_dec(x_9);
x_74 = lean_string_append(x_72, x_73);
lean_dec(x_73);
x_75 = lean_string_append(x_74, x_66);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_65);
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
lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_86 = lean_ctor_get(x_14, 0);
x_87 = lean_ctor_get(x_14, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_14);
x_88 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_89 = lean_ctor_get(x_6, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_90 = x_6;
} else {
 lean_dec_ref(x_6);
 x_90 = lean_box(0);
}
if (lean_obj_tag(x_15) == 0)
{
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_90);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_134 = lean_array_get_size(x_12);
x_135 = l_Lake_Package_getReleaseUrl___closed__14;
x_136 = lean_array_push(x_12, x_135);
x_137 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_89);
lean_ctor_set_uint8(x_137, sizeof(void*)*2, x_88);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_134);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_87);
return x_139;
}
else
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_86, 0);
lean_inc(x_140);
lean_dec(x_86);
x_91 = x_140;
goto block_133;
}
}
else
{
lean_object* x_141; 
lean_dec(x_86);
x_141 = lean_ctor_get(x_15, 0);
lean_inc(x_141);
lean_dec(x_15);
x_91 = x_141;
goto block_133;
}
block_133:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_8);
x_93 = l_Lake_Package_getBarrelUrl___lambda__2___closed__10;
x_94 = l_Lake_Package_getBarrelUrl___lambda__2___closed__11;
x_95 = l_Lake_Package_getReleaseUrl___closed__7;
x_96 = l_Lake_Package_recFetchDeps___lambda__1___closed__1;
x_97 = 0;
lean_inc(x_92);
x_98 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_98, 0, x_93);
lean_ctor_set(x_98, 1, x_94);
lean_ctor_set(x_98, 2, x_95);
lean_ctor_set(x_98, 3, x_92);
lean_ctor_set(x_98, 4, x_96);
lean_ctor_set_uint8(x_98, sizeof(void*)*5, x_97);
x_99 = l_Lake_captureProc_x3f(x_98, x_87);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_91);
lean_dec(x_9);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = l_Lake_Package_getReleaseUrl___closed__8;
x_103 = l_Lake_Package_getBarrelUrl___lambda__2___closed__9;
x_104 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_104, 0, x_93);
lean_ctor_set(x_104, 1, x_94);
lean_ctor_set(x_104, 2, x_103);
lean_ctor_set(x_104, 3, x_92);
lean_ctor_set(x_104, 4, x_96);
lean_ctor_set_uint8(x_104, sizeof(void*)*5, x_97);
x_105 = l_Lake_captureProc_x3f(x_104, x_101);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
if (lean_is_scalar(x_90)) {
 x_108 = lean_alloc_ctor(0, 2, 1);
} else {
 x_108 = x_90;
}
lean_ctor_set(x_108, 0, x_12);
lean_ctor_set(x_108, 1, x_89);
lean_ctor_set_uint8(x_108, sizeof(void*)*2, x_88);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_110 = lean_apply_7(x_102, x_109, x_2, x_3, x_4, x_5, x_108, x_107);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_111 = lean_ctor_get(x_106, 0);
lean_inc(x_111);
lean_dec(x_106);
x_112 = l_Lake_Package_getReleaseUrl___closed__9;
x_113 = lean_string_append(x_112, x_111);
lean_dec(x_111);
x_114 = l_Lake_Package_getReleaseUrl___closed__10;
x_115 = lean_string_append(x_113, x_114);
x_116 = lean_apply_7(x_102, x_115, x_2, x_3, x_4, x_5, x_108, x_107);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_92);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_117 = lean_ctor_get(x_99, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_118 = x_99;
} else {
 lean_dec_ref(x_99);
 x_118 = lean_box(0);
}
x_119 = lean_ctor_get(x_100, 0);
lean_inc(x_119);
lean_dec(x_100);
if (lean_is_scalar(x_90)) {
 x_120 = lean_alloc_ctor(0, 2, 1);
} else {
 x_120 = x_90;
}
lean_ctor_set(x_120, 0, x_12);
lean_ctor_set(x_120, 1, x_89);
lean_ctor_set_uint8(x_120, sizeof(void*)*2, x_88);
x_121 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_122 = lean_string_append(x_121, x_91);
lean_dec(x_91);
x_123 = l_Lake_Package_getReleaseUrl___closed__11;
x_124 = lean_string_append(x_122, x_123);
x_125 = lean_string_append(x_124, x_119);
lean_dec(x_119);
x_126 = l_Lake_Package_getReleaseUrl___closed__12;
x_127 = lean_string_append(x_125, x_126);
x_128 = lean_ctor_get(x_9, 16);
lean_inc(x_128);
lean_dec(x_9);
x_129 = lean_string_append(x_127, x_128);
lean_dec(x_128);
x_130 = lean_string_append(x_129, x_121);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_120);
if (lean_is_scalar(x_118)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_118;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_117);
return x_132;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_getReleaseUrl___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Package_getReleaseUrl___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___at_Lake_Package_fetchBuildArchive___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_dec(x_12);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_buildFileUnlessUpToDate_x27___spec__5(x_13, x_3);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_18 = 0;
x_19 = lean_box(x_18);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_9);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_inc(x_21);
lean_dec(x_8);
x_24 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_22);
x_25 = 0;
x_26 = lean_box(x_25);
lean_ctor_set(x_2, 1, x_24);
lean_ctor_set(x_2, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_9);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_8);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate_x27___spec__3(x_1, x_4, x_9);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_31);
lean_ctor_set(x_29, 0, x_2);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_29);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_2);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_8, 0);
x_36 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_37 = lean_ctor_get(x_8, 1);
lean_inc(x_37);
lean_inc(x_35);
lean_dec(x_8);
x_38 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate_x27___spec__3(x_1, x_4, x_9);
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
x_42 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_42, 0, x_35);
lean_ctor_set(x_42, 1, x_37);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_36);
lean_ctor_set(x_2, 1, x_42);
lean_ctor_set(x_2, 0, x_39);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_8);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = l_System_FilePath_pathExists(x_1, x_9);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_47);
lean_ctor_set(x_45, 0, x_2);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_45, 0);
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_45);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_2);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_51 = lean_ctor_get(x_8, 0);
x_52 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_53 = lean_ctor_get(x_8, 1);
lean_inc(x_53);
lean_inc(x_51);
lean_dec(x_8);
x_54 = l_System_FilePath_pathExists(x_1, x_9);
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
x_58 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_58, 0, x_51);
lean_ctor_set(x_58, 1, x_53);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_52);
lean_ctor_set(x_2, 1, x_58);
lean_ctor_set(x_2, 0, x_55);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_2);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_2, 0);
lean_inc(x_60);
lean_dec(x_2);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_buildFileUnlessUpToDate_x27___spec__5(x_61, x_3);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_7, 0);
x_64 = lean_ctor_get_uint8(x_63, sizeof(void*)*1);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_4);
x_65 = lean_ctor_get(x_8, 0);
lean_inc(x_65);
x_66 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_67 = lean_ctor_get(x_8, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_68 = x_8;
} else {
 lean_dec_ref(x_8);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 2, 1);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_67);
lean_ctor_set_uint8(x_69, sizeof(void*)*2, x_66);
x_70 = 0;
x_71 = lean_box(x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_9);
return x_73;
}
else
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_74 = lean_ctor_get(x_8, 0);
lean_inc(x_74);
x_75 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_76 = lean_ctor_get(x_8, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_77 = x_8;
} else {
 lean_dec_ref(x_8);
 x_77 = lean_box(0);
}
x_78 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate_x27___spec__3(x_1, x_4, x_9);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_81 = x_78;
} else {
 lean_dec_ref(x_78);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_82 = lean_alloc_ctor(0, 2, 1);
} else {
 x_82 = x_77;
}
lean_ctor_set(x_82, 0, x_74);
lean_ctor_set(x_82, 1, x_76);
lean_ctor_set_uint8(x_82, sizeof(void*)*2, x_75);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_82);
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
else
{
lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_4);
x_85 = lean_ctor_get(x_8, 0);
lean_inc(x_85);
x_86 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_87 = lean_ctor_get(x_8, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_88 = x_8;
} else {
 lean_dec_ref(x_8);
 x_88 = lean_box(0);
}
x_89 = l_System_FilePath_pathExists(x_1, x_9);
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
if (lean_is_scalar(x_88)) {
 x_93 = lean_alloc_ctor(0, 2, 1);
} else {
 x_93 = x_88;
}
lean_ctor_set(x_93, 0, x_85);
lean_ctor_set(x_93, 1, x_87);
lean_ctor_set_uint8(x_93, sizeof(void*)*2, x_86);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_90);
lean_ctor_set(x_94, 1, x_93);
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
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___at_Lake_Package_fetchBuildArchive___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_checkHashUpToDate___at_Lake_Package_fetchBuildArchive___spec__2___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchBuildArchive___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchBuildArchive___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_273; 
x_15 = lean_alloc_closure((void*)(l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchBuildArchive___spec__1___lambda__1___boxed), 9, 3);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
x_273 = !lean_is_exclusive(x_13);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
x_274 = lean_ctor_get(x_13, 0);
x_275 = l_System_FilePath_pathExists(x_7, x_14);
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_unbox(x_276);
lean_dec(x_276);
if (x_277 == 0)
{
uint8_t x_278; 
lean_dec(x_9);
x_278 = !lean_is_exclusive(x_275);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; 
x_279 = lean_ctor_get(x_275, 1);
x_280 = lean_ctor_get(x_275, 0);
lean_dec(x_280);
x_281 = lean_ctor_get(x_6, 1);
lean_inc(x_281);
x_282 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate_x27___spec__3(x_5, x_281, x_279);
x_283 = !lean_is_exclusive(x_282);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_284 = lean_ctor_get(x_282, 0);
x_285 = lean_ctor_get(x_282, 1);
x_286 = lean_unbox(x_284);
lean_dec(x_284);
if (x_286 == 0)
{
lean_object* x_287; 
lean_free_object(x_282);
lean_free_object(x_275);
x_287 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_15, x_8, x_4, x_10, x_11, x_12, x_13, x_285);
return x_287;
}
else
{
uint8_t x_288; lean_object* x_289; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
x_288 = 1;
x_289 = lean_box(x_288);
lean_ctor_set(x_275, 1, x_13);
lean_ctor_set(x_275, 0, x_289);
lean_ctor_set(x_282, 0, x_275);
return x_282;
}
}
else
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; 
x_290 = lean_ctor_get(x_282, 0);
x_291 = lean_ctor_get(x_282, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_282);
x_292 = lean_unbox(x_290);
lean_dec(x_290);
if (x_292 == 0)
{
lean_object* x_293; 
lean_free_object(x_275);
x_293 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_15, x_8, x_4, x_10, x_11, x_12, x_13, x_291);
return x_293;
}
else
{
uint8_t x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
x_294 = 1;
x_295 = lean_box(x_294);
lean_ctor_set(x_275, 1, x_13);
lean_ctor_set(x_275, 0, x_295);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_275);
lean_ctor_set(x_296, 1, x_291);
return x_296;
}
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; 
x_297 = lean_ctor_get(x_275, 1);
lean_inc(x_297);
lean_dec(x_275);
x_298 = lean_ctor_get(x_6, 1);
lean_inc(x_298);
x_299 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate_x27___spec__3(x_5, x_298, x_297);
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_302 = x_299;
} else {
 lean_dec_ref(x_299);
 x_302 = lean_box(0);
}
x_303 = lean_unbox(x_300);
lean_dec(x_300);
if (x_303 == 0)
{
lean_object* x_304; 
lean_dec(x_302);
x_304 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_15, x_8, x_4, x_10, x_11, x_12, x_13, x_301);
return x_304;
}
else
{
uint8_t x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
x_305 = 1;
x_306 = lean_box(x_305);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_13);
if (lean_is_scalar(x_302)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_302;
}
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_301);
return x_308;
}
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; 
x_309 = lean_ctor_get(x_275, 1);
lean_inc(x_309);
lean_dec(x_275);
x_310 = l_Lake_readTraceFile_x3f(x_7, x_274, x_309);
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_310, 1);
lean_inc(x_312);
lean_dec(x_310);
x_313 = !lean_is_exclusive(x_311);
if (x_313 == 0)
{
lean_object* x_314; 
x_314 = lean_ctor_get(x_311, 1);
lean_ctor_set(x_13, 0, x_314);
lean_ctor_set(x_311, 1, x_13);
x_16 = x_311;
x_17 = x_312;
goto block_272;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_311, 0);
x_316 = lean_ctor_get(x_311, 1);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_311);
lean_ctor_set(x_13, 0, x_316);
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_13);
x_16 = x_317;
x_17 = x_312;
goto block_272;
}
}
}
else
{
lean_object* x_318; uint8_t x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_318 = lean_ctor_get(x_13, 0);
x_319 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
x_320 = lean_ctor_get(x_13, 1);
lean_inc(x_320);
lean_inc(x_318);
lean_dec(x_13);
x_321 = l_System_FilePath_pathExists(x_7, x_14);
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_unbox(x_322);
lean_dec(x_322);
if (x_323 == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; 
lean_dec(x_9);
x_324 = lean_ctor_get(x_321, 1);
lean_inc(x_324);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 x_325 = x_321;
} else {
 lean_dec_ref(x_321);
 x_325 = lean_box(0);
}
x_326 = lean_ctor_get(x_6, 1);
lean_inc(x_326);
x_327 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate_x27___spec__3(x_5, x_326, x_324);
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 x_330 = x_327;
} else {
 lean_dec_ref(x_327);
 x_330 = lean_box(0);
}
x_331 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_331, 0, x_318);
lean_ctor_set(x_331, 1, x_320);
lean_ctor_set_uint8(x_331, sizeof(void*)*2, x_319);
x_332 = lean_unbox(x_328);
lean_dec(x_328);
if (x_332 == 0)
{
lean_object* x_333; 
lean_dec(x_330);
lean_dec(x_325);
x_333 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_15, x_8, x_4, x_10, x_11, x_12, x_331, x_329);
return x_333;
}
else
{
uint8_t x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
x_334 = 1;
x_335 = lean_box(x_334);
if (lean_is_scalar(x_325)) {
 x_336 = lean_alloc_ctor(0, 2, 0);
} else {
 x_336 = x_325;
}
lean_ctor_set(x_336, 0, x_335);
lean_ctor_set(x_336, 1, x_331);
if (lean_is_scalar(x_330)) {
 x_337 = lean_alloc_ctor(0, 2, 0);
} else {
 x_337 = x_330;
}
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_329);
return x_337;
}
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_338 = lean_ctor_get(x_321, 1);
lean_inc(x_338);
lean_dec(x_321);
x_339 = l_Lake_readTraceFile_x3f(x_7, x_318, x_338);
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_339, 1);
lean_inc(x_341);
lean_dec(x_339);
x_342 = lean_ctor_get(x_340, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_340, 1);
lean_inc(x_343);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 x_344 = x_340;
} else {
 lean_dec_ref(x_340);
 x_344 = lean_box(0);
}
x_345 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_345, 0, x_343);
lean_ctor_set(x_345, 1, x_320);
lean_ctor_set_uint8(x_345, sizeof(void*)*2, x_319);
if (lean_is_scalar(x_344)) {
 x_346 = lean_alloc_ctor(0, 2, 0);
} else {
 x_346 = x_344;
}
lean_ctor_set(x_346, 0, x_342);
lean_ctor_set(x_346, 1, x_345);
x_16 = x_346;
x_17 = x_341;
goto block_272;
}
}
block_272:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_16, 1);
x_21 = lean_ctor_get(x_16, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_23, sizeof(void*)*1);
lean_dec(x_23);
x_25 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate_x27___spec__3(x_5, x_9, x_17);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
if (x_24 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_free_object(x_25);
lean_dec(x_27);
lean_free_object(x_16);
x_29 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_15, x_8, x_4, x_10, x_11, x_12, x_20, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
x_32 = lean_unbox(x_30);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; 
lean_free_object(x_25);
lean_free_object(x_16);
x_33 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_15, x_8, x_4, x_10, x_11, x_12, x_20, x_31);
return x_33;
}
else
{
uint8_t x_34; lean_object* x_35; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
x_34 = 1;
x_35 = lean_box(x_34);
lean_ctor_set(x_16, 0, x_35);
lean_ctor_set(x_25, 0, x_16);
return x_25;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_25);
if (x_24 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
lean_free_object(x_16);
x_38 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_15, x_8, x_4, x_10, x_11, x_12, x_20, x_37);
return x_38;
}
else
{
uint8_t x_39; 
x_39 = lean_unbox(x_36);
lean_dec(x_36);
if (x_39 == 0)
{
lean_object* x_40; 
lean_free_object(x_16);
x_40 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_15, x_8, x_4, x_10, x_11, x_12, x_20, x_37);
return x_40;
}
else
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
x_41 = 1;
x_42 = lean_box(x_41);
lean_ctor_set(x_16, 0, x_42);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_16);
lean_ctor_set(x_43, 1, x_37);
return x_43;
}
}
}
}
else
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_20, 0);
x_45 = lean_ctor_get_uint8(x_20, sizeof(void*)*2);
x_46 = lean_ctor_get(x_20, 1);
lean_inc(x_46);
lean_inc(x_44);
lean_dec(x_20);
x_47 = lean_ctor_get(x_12, 0);
lean_inc(x_47);
x_48 = lean_ctor_get_uint8(x_47, sizeof(void*)*1);
lean_dec(x_47);
x_49 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate_x27___spec__3(x_5, x_9, x_17);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
x_53 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_53, 0, x_44);
lean_ctor_set(x_53, 1, x_46);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_45);
if (x_48 == 0)
{
lean_object* x_54; 
lean_dec(x_52);
lean_dec(x_50);
lean_free_object(x_16);
x_54 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_15, x_8, x_4, x_10, x_11, x_12, x_53, x_51);
return x_54;
}
else
{
uint8_t x_55; 
x_55 = lean_unbox(x_50);
lean_dec(x_50);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_52);
lean_free_object(x_16);
x_56 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_15, x_8, x_4, x_10, x_11, x_12, x_53, x_51);
return x_56;
}
else
{
uint8_t x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
x_57 = 1;
x_58 = lean_box(x_57);
lean_ctor_set(x_16, 1, x_53);
lean_ctor_set(x_16, 0, x_58);
if (lean_is_scalar(x_52)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_52;
}
lean_ctor_set(x_59, 0, x_16);
lean_ctor_set(x_59, 1, x_51);
return x_59;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_60 = lean_ctor_get(x_16, 1);
lean_inc(x_60);
lean_dec(x_16);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get_uint8(x_60, sizeof(void*)*2);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_64 = x_60;
} else {
 lean_dec_ref(x_60);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_12, 0);
lean_inc(x_65);
x_66 = lean_ctor_get_uint8(x_65, sizeof(void*)*1);
lean_dec(x_65);
x_67 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate_x27___spec__3(x_5, x_9, x_17);
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
if (lean_is_scalar(x_64)) {
 x_71 = lean_alloc_ctor(0, 2, 1);
} else {
 x_71 = x_64;
}
lean_ctor_set(x_71, 0, x_61);
lean_ctor_set(x_71, 1, x_63);
lean_ctor_set_uint8(x_71, sizeof(void*)*2, x_62);
if (x_66 == 0)
{
lean_object* x_72; 
lean_dec(x_70);
lean_dec(x_68);
x_72 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_15, x_8, x_4, x_10, x_11, x_12, x_71, x_69);
return x_72;
}
else
{
uint8_t x_73; 
x_73 = lean_unbox(x_68);
lean_dec(x_68);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_70);
x_74 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_15, x_8, x_4, x_10, x_11, x_12, x_71, x_69);
return x_74;
}
else
{
uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
x_75 = 1;
x_76 = lean_box(x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_71);
if (lean_is_scalar(x_70)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_70;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_69);
return x_78;
}
}
}
}
else
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_18);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_80 = lean_ctor_get(x_18, 0);
x_81 = lean_ctor_get(x_16, 1);
lean_inc(x_81);
lean_dec(x_16);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
lean_ctor_set(x_18, 0, x_82);
lean_inc(x_6);
x_84 = l_Lake_checkHashUpToDate___at_Lake_Package_fetchBuildArchive___spec__2___rarg(x_5, x_6, x_18, x_9, x_10, x_11, x_12, x_81, x_17);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_unbox(x_86);
lean_dec(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_83);
x_88 = lean_ctor_get(x_84, 1);
lean_inc(x_88);
lean_dec(x_84);
x_89 = lean_ctor_get(x_85, 1);
lean_inc(x_89);
lean_dec(x_85);
x_90 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_15, x_8, x_4, x_10, x_11, x_12, x_89, x_88);
return x_90;
}
else
{
uint8_t x_91; 
lean_dec(x_15);
lean_dec(x_6);
x_91 = !lean_is_exclusive(x_85);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = lean_ctor_get(x_85, 1);
x_93 = lean_ctor_get(x_85, 0);
lean_dec(x_93);
x_94 = !lean_is_exclusive(x_84);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_84, 1);
x_96 = lean_ctor_get(x_84, 0);
lean_dec(x_96);
x_97 = !lean_is_exclusive(x_92);
if (x_97 == 0)
{
uint8_t x_98; uint8_t x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_98 = lean_ctor_get_uint8(x_92, sizeof(void*)*2);
x_99 = 1;
x_100 = l_Lake_JobAction_merge(x_98, x_99);
lean_ctor_set_uint8(x_92, sizeof(void*)*2, x_100);
x_101 = lean_array_get_size(x_83);
x_102 = lean_unsigned_to_nat(0u);
x_103 = lean_nat_dec_lt(x_102, x_101);
if (x_103 == 0)
{
uint8_t x_104; lean_object* x_105; 
lean_dec(x_101);
lean_dec(x_83);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_104 = 1;
x_105 = lean_box(x_104);
lean_ctor_set(x_85, 0, x_105);
return x_84;
}
else
{
uint8_t x_106; 
x_106 = lean_nat_dec_le(x_101, x_101);
if (x_106 == 0)
{
uint8_t x_107; lean_object* x_108; 
lean_dec(x_101);
lean_dec(x_83);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_107 = 1;
x_108 = lean_box(x_107);
lean_ctor_set(x_85, 0, x_108);
return x_84;
}
else
{
size_t x_109; size_t x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
lean_free_object(x_84);
lean_free_object(x_85);
x_109 = 0;
x_110 = lean_usize_of_nat(x_101);
lean_dec(x_101);
x_111 = lean_box(0);
x_112 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate_x27___spec__6(x_83, x_109, x_110, x_111, x_4, x_10, x_11, x_12, x_92, x_95);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_83);
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_112, 0);
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
lean_object* x_116; uint8_t x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_114, 0);
lean_dec(x_116);
x_117 = 1;
x_118 = lean_box(x_117);
lean_ctor_set(x_114, 0, x_118);
return x_112;
}
else
{
lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_114, 1);
lean_inc(x_119);
lean_dec(x_114);
x_120 = 1;
x_121 = lean_box(x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_119);
lean_ctor_set(x_112, 0, x_122);
return x_112;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_123 = lean_ctor_get(x_112, 0);
x_124 = lean_ctor_get(x_112, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_112);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_126 = x_123;
} else {
 lean_dec_ref(x_123);
 x_126 = lean_box(0);
}
x_127 = 1;
x_128 = lean_box(x_127);
if (lean_is_scalar(x_126)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_126;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_125);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_124);
return x_130;
}
}
}
}
else
{
lean_object* x_131; uint8_t x_132; lean_object* x_133; uint8_t x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_131 = lean_ctor_get(x_92, 0);
x_132 = lean_ctor_get_uint8(x_92, sizeof(void*)*2);
x_133 = lean_ctor_get(x_92, 1);
lean_inc(x_133);
lean_inc(x_131);
lean_dec(x_92);
x_134 = 1;
x_135 = l_Lake_JobAction_merge(x_132, x_134);
x_136 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_136, 0, x_131);
lean_ctor_set(x_136, 1, x_133);
lean_ctor_set_uint8(x_136, sizeof(void*)*2, x_135);
x_137 = lean_array_get_size(x_83);
x_138 = lean_unsigned_to_nat(0u);
x_139 = lean_nat_dec_lt(x_138, x_137);
if (x_139 == 0)
{
uint8_t x_140; lean_object* x_141; 
lean_dec(x_137);
lean_dec(x_83);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_140 = 1;
x_141 = lean_box(x_140);
lean_ctor_set(x_85, 1, x_136);
lean_ctor_set(x_85, 0, x_141);
return x_84;
}
else
{
uint8_t x_142; 
x_142 = lean_nat_dec_le(x_137, x_137);
if (x_142 == 0)
{
uint8_t x_143; lean_object* x_144; 
lean_dec(x_137);
lean_dec(x_83);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_143 = 1;
x_144 = lean_box(x_143);
lean_ctor_set(x_85, 1, x_136);
lean_ctor_set(x_85, 0, x_144);
return x_84;
}
else
{
size_t x_145; size_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_free_object(x_84);
lean_free_object(x_85);
x_145 = 0;
x_146 = lean_usize_of_nat(x_137);
lean_dec(x_137);
x_147 = lean_box(0);
x_148 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate_x27___spec__6(x_83, x_145, x_146, x_147, x_4, x_10, x_11, x_12, x_136, x_95);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_83);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_151 = x_148;
} else {
 lean_dec_ref(x_148);
 x_151 = lean_box(0);
}
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_153 = x_149;
} else {
 lean_dec_ref(x_149);
 x_153 = lean_box(0);
}
x_154 = 1;
x_155 = lean_box(x_154);
if (lean_is_scalar(x_153)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_153;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_152);
if (lean_is_scalar(x_151)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_151;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_150);
return x_157;
}
}
}
}
else
{
lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_158 = lean_ctor_get(x_84, 1);
lean_inc(x_158);
lean_dec(x_84);
x_159 = lean_ctor_get(x_92, 0);
lean_inc(x_159);
x_160 = lean_ctor_get_uint8(x_92, sizeof(void*)*2);
x_161 = lean_ctor_get(x_92, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_162 = x_92;
} else {
 lean_dec_ref(x_92);
 x_162 = lean_box(0);
}
x_163 = 1;
x_164 = l_Lake_JobAction_merge(x_160, x_163);
if (lean_is_scalar(x_162)) {
 x_165 = lean_alloc_ctor(0, 2, 1);
} else {
 x_165 = x_162;
}
lean_ctor_set(x_165, 0, x_159);
lean_ctor_set(x_165, 1, x_161);
lean_ctor_set_uint8(x_165, sizeof(void*)*2, x_164);
x_166 = lean_array_get_size(x_83);
x_167 = lean_unsigned_to_nat(0u);
x_168 = lean_nat_dec_lt(x_167, x_166);
if (x_168 == 0)
{
uint8_t x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_166);
lean_dec(x_83);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_169 = 1;
x_170 = lean_box(x_169);
lean_ctor_set(x_85, 1, x_165);
lean_ctor_set(x_85, 0, x_170);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_85);
lean_ctor_set(x_171, 1, x_158);
return x_171;
}
else
{
uint8_t x_172; 
x_172 = lean_nat_dec_le(x_166, x_166);
if (x_172 == 0)
{
uint8_t x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_166);
lean_dec(x_83);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_173 = 1;
x_174 = lean_box(x_173);
lean_ctor_set(x_85, 1, x_165);
lean_ctor_set(x_85, 0, x_174);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_85);
lean_ctor_set(x_175, 1, x_158);
return x_175;
}
else
{
size_t x_176; size_t x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_free_object(x_85);
x_176 = 0;
x_177 = lean_usize_of_nat(x_166);
lean_dec(x_166);
x_178 = lean_box(0);
x_179 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate_x27___spec__6(x_83, x_176, x_177, x_178, x_4, x_10, x_11, x_12, x_165, x_158);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_83);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_182 = x_179;
} else {
 lean_dec_ref(x_179);
 x_182 = lean_box(0);
}
x_183 = lean_ctor_get(x_180, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_184 = x_180;
} else {
 lean_dec_ref(x_180);
 x_184 = lean_box(0);
}
x_185 = 1;
x_186 = lean_box(x_185);
if (lean_is_scalar(x_184)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_184;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_183);
if (lean_is_scalar(x_182)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_182;
}
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_181);
return x_188;
}
}
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_189 = lean_ctor_get(x_85, 1);
lean_inc(x_189);
lean_dec(x_85);
x_190 = lean_ctor_get(x_84, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_191 = x_84;
} else {
 lean_dec_ref(x_84);
 x_191 = lean_box(0);
}
x_192 = lean_ctor_get(x_189, 0);
lean_inc(x_192);
x_193 = lean_ctor_get_uint8(x_189, sizeof(void*)*2);
x_194 = lean_ctor_get(x_189, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_195 = x_189;
} else {
 lean_dec_ref(x_189);
 x_195 = lean_box(0);
}
x_196 = 1;
x_197 = l_Lake_JobAction_merge(x_193, x_196);
if (lean_is_scalar(x_195)) {
 x_198 = lean_alloc_ctor(0, 2, 1);
} else {
 x_198 = x_195;
}
lean_ctor_set(x_198, 0, x_192);
lean_ctor_set(x_198, 1, x_194);
lean_ctor_set_uint8(x_198, sizeof(void*)*2, x_197);
x_199 = lean_array_get_size(x_83);
x_200 = lean_unsigned_to_nat(0u);
x_201 = lean_nat_dec_lt(x_200, x_199);
if (x_201 == 0)
{
uint8_t x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_199);
lean_dec(x_83);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_202 = 1;
x_203 = lean_box(x_202);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_198);
if (lean_is_scalar(x_191)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_191;
}
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_190);
return x_205;
}
else
{
uint8_t x_206; 
x_206 = lean_nat_dec_le(x_199, x_199);
if (x_206 == 0)
{
uint8_t x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_199);
lean_dec(x_83);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_207 = 1;
x_208 = lean_box(x_207);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_198);
if (lean_is_scalar(x_191)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_191;
}
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_190);
return x_210;
}
else
{
size_t x_211; size_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_191);
x_211 = 0;
x_212 = lean_usize_of_nat(x_199);
lean_dec(x_199);
x_213 = lean_box(0);
x_214 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate_x27___spec__6(x_83, x_211, x_212, x_213, x_4, x_10, x_11, x_12, x_198, x_190);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_83);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_217 = x_214;
} else {
 lean_dec_ref(x_214);
 x_217 = lean_box(0);
}
x_218 = lean_ctor_get(x_215, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_219 = x_215;
} else {
 lean_dec_ref(x_215);
 x_219 = lean_box(0);
}
x_220 = 1;
x_221 = lean_box(x_220);
if (lean_is_scalar(x_219)) {
 x_222 = lean_alloc_ctor(0, 2, 0);
} else {
 x_222 = x_219;
}
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_218);
if (lean_is_scalar(x_217)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_217;
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_216);
return x_223;
}
}
}
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_224 = lean_ctor_get(x_18, 0);
lean_inc(x_224);
lean_dec(x_18);
x_225 = lean_ctor_get(x_16, 1);
lean_inc(x_225);
lean_dec(x_16);
x_226 = lean_ctor_get(x_224, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_224, 1);
lean_inc(x_227);
lean_dec(x_224);
x_228 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_228, 0, x_226);
lean_inc(x_6);
x_229 = l_Lake_checkHashUpToDate___at_Lake_Package_fetchBuildArchive___spec__2___rarg(x_5, x_6, x_228, x_9, x_10, x_11, x_12, x_225, x_17);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_unbox(x_231);
lean_dec(x_231);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_227);
x_233 = lean_ctor_get(x_229, 1);
lean_inc(x_233);
lean_dec(x_229);
x_234 = lean_ctor_get(x_230, 1);
lean_inc(x_234);
lean_dec(x_230);
x_235 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_15, x_8, x_4, x_10, x_11, x_12, x_234, x_233);
return x_235;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; uint8_t x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
lean_dec(x_15);
lean_dec(x_6);
x_236 = lean_ctor_get(x_230, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_237 = x_230;
} else {
 lean_dec_ref(x_230);
 x_237 = lean_box(0);
}
x_238 = lean_ctor_get(x_229, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_239 = x_229;
} else {
 lean_dec_ref(x_229);
 x_239 = lean_box(0);
}
x_240 = lean_ctor_get(x_236, 0);
lean_inc(x_240);
x_241 = lean_ctor_get_uint8(x_236, sizeof(void*)*2);
x_242 = lean_ctor_get(x_236, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_243 = x_236;
} else {
 lean_dec_ref(x_236);
 x_243 = lean_box(0);
}
x_244 = 1;
x_245 = l_Lake_JobAction_merge(x_241, x_244);
if (lean_is_scalar(x_243)) {
 x_246 = lean_alloc_ctor(0, 2, 1);
} else {
 x_246 = x_243;
}
lean_ctor_set(x_246, 0, x_240);
lean_ctor_set(x_246, 1, x_242);
lean_ctor_set_uint8(x_246, sizeof(void*)*2, x_245);
x_247 = lean_array_get_size(x_227);
x_248 = lean_unsigned_to_nat(0u);
x_249 = lean_nat_dec_lt(x_248, x_247);
if (x_249 == 0)
{
uint8_t x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_247);
lean_dec(x_227);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_250 = 1;
x_251 = lean_box(x_250);
if (lean_is_scalar(x_237)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_237;
}
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_246);
if (lean_is_scalar(x_239)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_239;
}
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_238);
return x_253;
}
else
{
uint8_t x_254; 
x_254 = lean_nat_dec_le(x_247, x_247);
if (x_254 == 0)
{
uint8_t x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_247);
lean_dec(x_227);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_255 = 1;
x_256 = lean_box(x_255);
if (lean_is_scalar(x_237)) {
 x_257 = lean_alloc_ctor(0, 2, 0);
} else {
 x_257 = x_237;
}
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_246);
if (lean_is_scalar(x_239)) {
 x_258 = lean_alloc_ctor(0, 2, 0);
} else {
 x_258 = x_239;
}
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_238);
return x_258;
}
else
{
size_t x_259; size_t x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_239);
lean_dec(x_237);
x_259 = 0;
x_260 = lean_usize_of_nat(x_247);
lean_dec(x_247);
x_261 = lean_box(0);
x_262 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate_x27___spec__6(x_227, x_259, x_260, x_261, x_4, x_10, x_11, x_12, x_246, x_238);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_227);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_265 = x_262;
} else {
 lean_dec_ref(x_262);
 x_265 = lean_box(0);
}
x_266 = lean_ctor_get(x_263, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_267 = x_263;
} else {
 lean_dec_ref(x_263);
 x_267 = lean_box(0);
}
x_268 = 1;
x_269 = lean_box(x_268);
if (lean_is_scalar(x_267)) {
 x_270 = lean_alloc_ctor(0, 2, 0);
} else {
 x_270 = x_267;
}
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_266);
if (lean_is_scalar(x_265)) {
 x_271 = lean_alloc_ctor(0, 2, 0);
} else {
 x_271 = x_265;
}
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_264);
return x_271;
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lake_Package_fetchBuildArchive___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchBuildArchive___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_fetchBuildArchive___closed__3() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lake_Package_fetchBuildArchive___closed__2;
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_fetchBuildArchive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint64_t x_11; uint64_t x_12; uint64_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_11 = lean_string_hash(x_2);
x_12 = 1723;
x_13 = lean_uint64_mix_hash(x_12, x_11);
x_14 = l_Lake_Package_fetchBuildArchive___closed__1;
lean_inc(x_3);
x_15 = l_System_FilePath_addExtension(x_3, x_14);
x_16 = l_Lake_Package_fetchBuildArchive___closed__3;
x_17 = lean_box_uint64(x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = 2;
lean_inc(x_3);
x_20 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchBuildArchive___spec__1(x_2, x_3, x_4, x_5, x_3, x_18, x_15, x_19, x_16, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 2);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_ctor_get(x_27, 8);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_System_FilePath_join(x_26, x_28);
lean_dec(x_28);
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_ctor_get_uint8(x_25, sizeof(void*)*2);
x_33 = l_System_FilePath_pathExists(x_29, x_22);
x_34 = lean_unbox(x_24);
lean_dec(x_24);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
lean_free_object(x_21);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lake_JobAction_merge(x_32, x_19);
x_37 = 1;
x_38 = l_Lake_untar(x_3, x_29, x_37, x_31, x_35);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_38, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_39, 1);
lean_ctor_set(x_25, 0, x_43);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_36);
lean_ctor_set(x_39, 1, x_25);
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_39, 0);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_39);
lean_ctor_set(x_25, 0, x_45);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_36);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_25);
lean_ctor_set(x_38, 0, x_46);
return x_38;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_dec(x_38);
x_48 = lean_ctor_get(x_39, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_39, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_50 = x_39;
} else {
 lean_dec_ref(x_39);
 x_50 = lean_box(0);
}
lean_ctor_set(x_25, 0, x_49);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_36);
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_25);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_47);
return x_52;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_38);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_38, 0);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_39);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_39, 1);
lean_ctor_set(x_25, 0, x_56);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_36);
lean_ctor_set(x_39, 1, x_25);
return x_38;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_39, 0);
x_58 = lean_ctor_get(x_39, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_39);
lean_ctor_set(x_25, 0, x_58);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_36);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_25);
lean_ctor_set(x_38, 0, x_59);
return x_38;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_38, 1);
lean_inc(x_60);
lean_dec(x_38);
x_61 = lean_ctor_get(x_39, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_39, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_63 = x_39;
} else {
 lean_dec_ref(x_39);
 x_63 = lean_box(0);
}
lean_ctor_set(x_25, 0, x_62);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_36);
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_25);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_60);
return x_65;
}
}
}
else
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_33, 0);
lean_inc(x_66);
x_67 = lean_unbox(x_66);
lean_dec(x_66);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; 
lean_free_object(x_21);
x_68 = lean_ctor_get(x_33, 1);
lean_inc(x_68);
lean_dec(x_33);
x_69 = l_Lake_JobAction_merge(x_32, x_19);
x_70 = 1;
x_71 = l_Lake_untar(x_3, x_29, x_70, x_31, x_68);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_71);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_71, 0);
lean_dec(x_74);
x_75 = !lean_is_exclusive(x_72);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_72, 1);
lean_ctor_set(x_25, 0, x_76);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_69);
lean_ctor_set(x_72, 1, x_25);
return x_71;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_72, 0);
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_72);
lean_ctor_set(x_25, 0, x_78);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_69);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_25);
lean_ctor_set(x_71, 0, x_79);
return x_71;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_80 = lean_ctor_get(x_71, 1);
lean_inc(x_80);
lean_dec(x_71);
x_81 = lean_ctor_get(x_72, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_72, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_83 = x_72;
} else {
 lean_dec_ref(x_72);
 x_83 = lean_box(0);
}
lean_ctor_set(x_25, 0, x_82);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_69);
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_25);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_80);
return x_85;
}
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_71);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_71, 0);
lean_dec(x_87);
x_88 = !lean_is_exclusive(x_72);
if (x_88 == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_72, 1);
lean_ctor_set(x_25, 0, x_89);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_69);
lean_ctor_set(x_72, 1, x_25);
return x_71;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_72, 0);
x_91 = lean_ctor_get(x_72, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_72);
lean_ctor_set(x_25, 0, x_91);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_69);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_25);
lean_ctor_set(x_71, 0, x_92);
return x_71;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_71, 1);
lean_inc(x_93);
lean_dec(x_71);
x_94 = lean_ctor_get(x_72, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_72, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_96 = x_72;
} else {
 lean_dec_ref(x_72);
 x_96 = lean_box(0);
}
lean_ctor_set(x_25, 0, x_95);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_69);
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_25);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_93);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_29);
lean_dec(x_3);
x_99 = !lean_is_exclusive(x_33);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_33, 0);
lean_dec(x_100);
x_101 = lean_box(0);
lean_ctor_set(x_21, 0, x_101);
lean_ctor_set(x_33, 0, x_21);
return x_33;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_33, 1);
lean_inc(x_102);
lean_dec(x_33);
x_103 = lean_box(0);
lean_ctor_set(x_21, 0, x_103);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_21);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
}
}
else
{
lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_105 = lean_ctor_get(x_25, 0);
x_106 = lean_ctor_get_uint8(x_25, sizeof(void*)*2);
x_107 = lean_ctor_get(x_25, 1);
lean_inc(x_107);
lean_inc(x_105);
lean_dec(x_25);
x_108 = l_System_FilePath_pathExists(x_29, x_22);
x_109 = lean_unbox(x_24);
lean_dec(x_24);
if (x_109 == 0)
{
lean_object* x_110; uint8_t x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; 
lean_free_object(x_21);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l_Lake_JobAction_merge(x_106, x_19);
x_112 = 1;
x_113 = l_Lake_untar(x_3, x_29, x_112, x_105, x_110);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_116 = x_113;
} else {
 lean_dec_ref(x_113);
 x_116 = lean_box(0);
}
x_117 = lean_ctor_get(x_114, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_119 = x_114;
} else {
 lean_dec_ref(x_114);
 x_119 = lean_box(0);
}
x_120 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_107);
lean_ctor_set_uint8(x_120, sizeof(void*)*2, x_111);
if (lean_is_scalar(x_119)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_119;
}
lean_ctor_set(x_121, 0, x_117);
lean_ctor_set(x_121, 1, x_120);
if (lean_is_scalar(x_116)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_116;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_115);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_123 = lean_ctor_get(x_113, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_124 = x_113;
} else {
 lean_dec_ref(x_113);
 x_124 = lean_box(0);
}
x_125 = lean_ctor_get(x_114, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_114, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_127 = x_114;
} else {
 lean_dec_ref(x_114);
 x_127 = lean_box(0);
}
x_128 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_107);
lean_ctor_set_uint8(x_128, sizeof(void*)*2, x_111);
if (lean_is_scalar(x_127)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_127;
}
lean_ctor_set(x_129, 0, x_125);
lean_ctor_set(x_129, 1, x_128);
if (lean_is_scalar(x_124)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_124;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_123);
return x_130;
}
}
else
{
lean_object* x_131; uint8_t x_132; 
x_131 = lean_ctor_get(x_108, 0);
lean_inc(x_131);
x_132 = lean_unbox(x_131);
lean_dec(x_131);
if (x_132 == 0)
{
lean_object* x_133; uint8_t x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; 
lean_free_object(x_21);
x_133 = lean_ctor_get(x_108, 1);
lean_inc(x_133);
lean_dec(x_108);
x_134 = l_Lake_JobAction_merge(x_106, x_19);
x_135 = 1;
x_136 = l_Lake_untar(x_3, x_29, x_135, x_105, x_133);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_139 = x_136;
} else {
 lean_dec_ref(x_136);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_137, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_137, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_142 = x_137;
} else {
 lean_dec_ref(x_137);
 x_142 = lean_box(0);
}
x_143 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_107);
lean_ctor_set_uint8(x_143, sizeof(void*)*2, x_134);
if (lean_is_scalar(x_142)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_142;
}
lean_ctor_set(x_144, 0, x_140);
lean_ctor_set(x_144, 1, x_143);
if (lean_is_scalar(x_139)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_139;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_138);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_146 = lean_ctor_get(x_136, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_147 = x_136;
} else {
 lean_dec_ref(x_136);
 x_147 = lean_box(0);
}
x_148 = lean_ctor_get(x_137, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_137, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_150 = x_137;
} else {
 lean_dec_ref(x_137);
 x_150 = lean_box(0);
}
x_151 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_107);
lean_ctor_set_uint8(x_151, sizeof(void*)*2, x_134);
if (lean_is_scalar(x_150)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_150;
}
lean_ctor_set(x_152, 0, x_148);
lean_ctor_set(x_152, 1, x_151);
if (lean_is_scalar(x_147)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_147;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_146);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_29);
lean_dec(x_3);
x_154 = lean_ctor_get(x_108, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_155 = x_108;
} else {
 lean_dec_ref(x_108);
 x_155 = lean_box(0);
}
x_156 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_156, 0, x_105);
lean_ctor_set(x_156, 1, x_107);
lean_ctor_set_uint8(x_156, sizeof(void*)*2, x_106);
x_157 = lean_box(0);
lean_ctor_set(x_21, 1, x_156);
lean_ctor_set(x_21, 0, x_157);
if (lean_is_scalar(x_155)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_155;
}
lean_ctor_set(x_158, 0, x_21);
lean_ctor_set(x_158, 1, x_154);
return x_158;
}
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_159 = lean_ctor_get(x_21, 0);
x_160 = lean_ctor_get(x_21, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_21);
x_161 = lean_ctor_get(x_1, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_1, 2);
lean_inc(x_162);
lean_dec(x_1);
x_163 = lean_ctor_get(x_162, 8);
lean_inc(x_163);
lean_dec(x_162);
x_164 = l_System_FilePath_join(x_161, x_163);
lean_dec(x_163);
x_165 = lean_ctor_get(x_160, 0);
lean_inc(x_165);
x_166 = lean_ctor_get_uint8(x_160, sizeof(void*)*2);
x_167 = lean_ctor_get(x_160, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_168 = x_160;
} else {
 lean_dec_ref(x_160);
 x_168 = lean_box(0);
}
x_169 = l_System_FilePath_pathExists(x_164, x_22);
x_170 = lean_unbox(x_159);
lean_dec(x_159);
if (x_170 == 0)
{
lean_object* x_171; uint8_t x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; 
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = l_Lake_JobAction_merge(x_166, x_19);
x_173 = 1;
x_174 = l_Lake_untar(x_3, x_164, x_173, x_165, x_171);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_177 = x_174;
} else {
 lean_dec_ref(x_174);
 x_177 = lean_box(0);
}
x_178 = lean_ctor_get(x_175, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_175, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_180 = x_175;
} else {
 lean_dec_ref(x_175);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_181 = lean_alloc_ctor(0, 2, 1);
} else {
 x_181 = x_168;
}
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_167);
lean_ctor_set_uint8(x_181, sizeof(void*)*2, x_172);
if (lean_is_scalar(x_180)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_180;
}
lean_ctor_set(x_182, 0, x_178);
lean_ctor_set(x_182, 1, x_181);
if (lean_is_scalar(x_177)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_177;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_176);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_184 = lean_ctor_get(x_174, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_185 = x_174;
} else {
 lean_dec_ref(x_174);
 x_185 = lean_box(0);
}
x_186 = lean_ctor_get(x_175, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_175, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_188 = x_175;
} else {
 lean_dec_ref(x_175);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_189 = lean_alloc_ctor(0, 2, 1);
} else {
 x_189 = x_168;
}
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_167);
lean_ctor_set_uint8(x_189, sizeof(void*)*2, x_172);
if (lean_is_scalar(x_188)) {
 x_190 = lean_alloc_ctor(1, 2, 0);
} else {
 x_190 = x_188;
}
lean_ctor_set(x_190, 0, x_186);
lean_ctor_set(x_190, 1, x_189);
if (lean_is_scalar(x_185)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_185;
}
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_184);
return x_191;
}
}
else
{
lean_object* x_192; uint8_t x_193; 
x_192 = lean_ctor_get(x_169, 0);
lean_inc(x_192);
x_193 = lean_unbox(x_192);
lean_dec(x_192);
if (x_193 == 0)
{
lean_object* x_194; uint8_t x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; 
x_194 = lean_ctor_get(x_169, 1);
lean_inc(x_194);
lean_dec(x_169);
x_195 = l_Lake_JobAction_merge(x_166, x_19);
x_196 = 1;
x_197 = l_Lake_untar(x_3, x_164, x_196, x_165, x_194);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_200 = x_197;
} else {
 lean_dec_ref(x_197);
 x_200 = lean_box(0);
}
x_201 = lean_ctor_get(x_198, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_198, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_203 = x_198;
} else {
 lean_dec_ref(x_198);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_204 = lean_alloc_ctor(0, 2, 1);
} else {
 x_204 = x_168;
}
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_167);
lean_ctor_set_uint8(x_204, sizeof(void*)*2, x_195);
if (lean_is_scalar(x_203)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_203;
}
lean_ctor_set(x_205, 0, x_201);
lean_ctor_set(x_205, 1, x_204);
if (lean_is_scalar(x_200)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_200;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_199);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_207 = lean_ctor_get(x_197, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_208 = x_197;
} else {
 lean_dec_ref(x_197);
 x_208 = lean_box(0);
}
x_209 = lean_ctor_get(x_198, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_198, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_211 = x_198;
} else {
 lean_dec_ref(x_198);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_212 = lean_alloc_ctor(0, 2, 1);
} else {
 x_212 = x_168;
}
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_167);
lean_ctor_set_uint8(x_212, sizeof(void*)*2, x_195);
if (lean_is_scalar(x_211)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_211;
}
lean_ctor_set(x_213, 0, x_209);
lean_ctor_set(x_213, 1, x_212);
if (lean_is_scalar(x_208)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_208;
}
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_207);
return x_214;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_164);
lean_dec(x_3);
x_215 = lean_ctor_get(x_169, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_216 = x_169;
} else {
 lean_dec_ref(x_169);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_217 = lean_alloc_ctor(0, 2, 1);
} else {
 x_217 = x_168;
}
lean_ctor_set(x_217, 0, x_165);
lean_ctor_set(x_217, 1, x_167);
lean_ctor_set_uint8(x_217, sizeof(void*)*2, x_166);
x_218 = lean_box(0);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_217);
if (lean_is_scalar(x_216)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_216;
}
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_215);
return x_220;
}
}
}
}
else
{
uint8_t x_221; 
lean_dec(x_3);
lean_dec(x_1);
x_221 = !lean_is_exclusive(x_20);
if (x_221 == 0)
{
lean_object* x_222; uint8_t x_223; 
x_222 = lean_ctor_get(x_20, 0);
lean_dec(x_222);
x_223 = !lean_is_exclusive(x_21);
if (x_223 == 0)
{
return x_20;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_21, 0);
x_225 = lean_ctor_get(x_21, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_21);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
lean_ctor_set(x_20, 0, x_226);
return x_20;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_227 = lean_ctor_get(x_20, 1);
lean_inc(x_227);
lean_dec(x_20);
x_228 = lean_ctor_get(x_21, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_21, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_230 = x_21;
} else {
 lean_dec_ref(x_21);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(1, 2, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_228);
lean_ctor_set(x_231, 1, x_229);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_227);
return x_232;
}
}
}
else
{
uint8_t x_233; 
lean_dec(x_3);
lean_dec(x_1);
x_233 = !lean_is_exclusive(x_20);
if (x_233 == 0)
{
return x_20;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_20, 0);
x_235 = lean_ctor_get(x_20, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_20);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___at_Lake_Package_fetchBuildArchive___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_checkHashUpToDate___at_Lake_Package_fetchBuildArchive___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___at_Lake_Package_fetchBuildArchive___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_checkHashUpToDate___at_Lake_Package_fetchBuildArchive___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchBuildArchive___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchBuildArchive___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchBuildArchive___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_8);
lean_dec(x_8);
x_16 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchBuildArchive___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_15, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_EquipT_tryCatch___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_apply_7(x_2, x_16, x_3, x_4, x_5, x_6, x_17, x_15);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EquipT_tryCatch___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_EquipT_tryCatch___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_31; 
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
x_34 = lean_get_set_stdout(x_1, x_8);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
x_47 = lean_get_set_stdout(x_35, x_40);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_38, 0, x_50);
x_9 = x_38;
x_10 = x_48;
goto block_30;
}
else
{
uint8_t x_51; 
lean_free_object(x_39);
lean_dec(x_46);
lean_dec(x_45);
lean_free_object(x_38);
lean_dec(x_42);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_47, 0);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_47);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_39, 0);
x_56 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_inc(x_55);
lean_dec(x_39);
x_58 = lean_get_set_stdout(x_35, x_40);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_56);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_42);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_38, 1, x_60);
lean_ctor_set(x_38, 0, x_62);
x_9 = x_38;
x_10 = x_59;
goto block_30;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_57);
lean_dec(x_55);
lean_free_object(x_38);
lean_dec(x_42);
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_65 = x_58;
} else {
 lean_dec_ref(x_58);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_38, 0);
lean_inc(x_67);
lean_dec(x_38);
x_68 = lean_ctor_get(x_39, 0);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_70 = lean_ctor_get(x_39, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_71 = x_39;
} else {
 lean_dec_ref(x_39);
 x_71 = lean_box(0);
}
x_72 = lean_get_set_stdout(x_35, x_40);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 2, 1);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_70);
lean_ctor_set_uint8(x_74, sizeof(void*)*2, x_69);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_67);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
x_9 = x_77;
x_10 = x_73;
goto block_30;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_67);
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_80 = x_72;
} else {
 lean_dec_ref(x_72);
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
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_38, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_37, 1);
lean_inc(x_83);
lean_dec(x_37);
x_84 = !lean_is_exclusive(x_38);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_38, 0);
x_86 = lean_ctor_get(x_38, 1);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_82);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_82, 0);
x_89 = lean_ctor_get(x_82, 1);
x_90 = lean_get_set_stdout(x_35, x_83);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_9 = x_38;
x_10 = x_91;
goto block_30;
}
else
{
uint8_t x_92; 
lean_free_object(x_82);
lean_dec(x_89);
lean_dec(x_88);
lean_free_object(x_38);
lean_dec(x_85);
x_92 = !lean_is_exclusive(x_90);
if (x_92 == 0)
{
return x_90;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_90, 0);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_90);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_82, 0);
x_97 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_98 = lean_ctor_get(x_82, 1);
lean_inc(x_98);
lean_inc(x_96);
lean_dec(x_82);
x_99 = lean_get_set_stdout(x_35, x_83);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_101, 0, x_96);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set_uint8(x_101, sizeof(void*)*2, x_97);
lean_ctor_set(x_38, 1, x_101);
x_9 = x_38;
x_10 = x_100;
goto block_30;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_98);
lean_dec(x_96);
lean_free_object(x_38);
lean_dec(x_85);
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_104 = x_99;
} else {
 lean_dec_ref(x_99);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_38, 0);
lean_inc(x_106);
lean_dec(x_38);
x_107 = lean_ctor_get(x_82, 0);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_109 = lean_ctor_get(x_82, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_110 = x_82;
} else {
 lean_dec_ref(x_82);
 x_110 = lean_box(0);
}
x_111 = lean_get_set_stdout(x_35, x_83);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
if (lean_is_scalar(x_110)) {
 x_113 = lean_alloc_ctor(0, 2, 1);
} else {
 x_113 = x_110;
}
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_109);
lean_ctor_set_uint8(x_113, sizeof(void*)*2, x_108);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_106);
lean_ctor_set(x_114, 1, x_113);
x_9 = x_114;
x_10 = x_112;
goto block_30;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_106);
x_115 = lean_ctor_get(x_111, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_117 = x_111;
} else {
 lean_dec_ref(x_111);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_35);
x_119 = !lean_is_exclusive(x_37);
if (x_119 == 0)
{
return x_37;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_37, 0);
x_121 = lean_ctor_get(x_37, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_37);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_free_object(x_7);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_34);
if (x_123 == 0)
{
return x_34;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_34, 0);
x_125 = lean_ctor_get(x_34, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_34);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_7, 0);
x_128 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_129 = lean_ctor_get(x_7, 1);
lean_inc(x_129);
lean_inc(x_127);
lean_dec(x_7);
x_130 = lean_get_set_stdout(x_1, x_8);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_133, 0, x_127);
lean_ctor_set(x_133, 1, x_129);
lean_ctor_set_uint8(x_133, sizeof(void*)*2, x_128);
x_134 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_133, x_132);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_139 = x_135;
} else {
 lean_dec_ref(x_135);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_136, 0);
lean_inc(x_140);
x_141 = lean_ctor_get_uint8(x_136, sizeof(void*)*2);
x_142 = lean_ctor_get(x_136, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_143 = x_136;
} else {
 lean_dec_ref(x_136);
 x_143 = lean_box(0);
}
x_144 = lean_get_set_stdout(x_131, x_137);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
if (lean_is_scalar(x_143)) {
 x_146 = lean_alloc_ctor(0, 2, 1);
} else {
 x_146 = x_143;
}
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_142);
lean_ctor_set_uint8(x_146, sizeof(void*)*2, x_141);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_138);
lean_ctor_set(x_148, 1, x_147);
if (lean_is_scalar(x_139)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_139;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_146);
x_9 = x_149;
x_10 = x_145;
goto block_30;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
x_150 = lean_ctor_get(x_144, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_144, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_152 = x_144;
} else {
 lean_dec_ref(x_144);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_154 = lean_ctor_get(x_135, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_134, 1);
lean_inc(x_155);
lean_dec(x_134);
x_156 = lean_ctor_get(x_135, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_157 = x_135;
} else {
 lean_dec_ref(x_135);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_154, 0);
lean_inc(x_158);
x_159 = lean_ctor_get_uint8(x_154, sizeof(void*)*2);
x_160 = lean_ctor_get(x_154, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_161 = x_154;
} else {
 lean_dec_ref(x_154);
 x_161 = lean_box(0);
}
x_162 = lean_get_set_stdout(x_131, x_155);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 2, 1);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_158);
lean_ctor_set(x_164, 1, x_160);
lean_ctor_set_uint8(x_164, sizeof(void*)*2, x_159);
if (lean_is_scalar(x_157)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_157;
}
lean_ctor_set(x_165, 0, x_156);
lean_ctor_set(x_165, 1, x_164);
x_9 = x_165;
x_10 = x_163;
goto block_30;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
x_166 = lean_ctor_get(x_162, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_162, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_168 = x_162;
} else {
 lean_dec_ref(x_162);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_131);
x_170 = lean_ctor_get(x_134, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_134, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_172 = x_134;
} else {
 lean_dec_ref(x_134);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_129);
lean_dec(x_127);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_174 = lean_ctor_get(x_130, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_130, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_176 = x_130;
} else {
 lean_dec_ref(x_130);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
block_30:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_14);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_31; 
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
x_34 = lean_get_set_stdin(x_1, x_8);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
x_47 = lean_get_set_stdin(x_35, x_40);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_38, 0, x_50);
x_9 = x_38;
x_10 = x_48;
goto block_30;
}
else
{
uint8_t x_51; 
lean_free_object(x_39);
lean_dec(x_46);
lean_dec(x_45);
lean_free_object(x_38);
lean_dec(x_42);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_47, 0);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_47);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_39, 0);
x_56 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_inc(x_55);
lean_dec(x_39);
x_58 = lean_get_set_stdin(x_35, x_40);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_56);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_42);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_38, 1, x_60);
lean_ctor_set(x_38, 0, x_62);
x_9 = x_38;
x_10 = x_59;
goto block_30;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_57);
lean_dec(x_55);
lean_free_object(x_38);
lean_dec(x_42);
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_65 = x_58;
} else {
 lean_dec_ref(x_58);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_38, 0);
lean_inc(x_67);
lean_dec(x_38);
x_68 = lean_ctor_get(x_39, 0);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_70 = lean_ctor_get(x_39, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_71 = x_39;
} else {
 lean_dec_ref(x_39);
 x_71 = lean_box(0);
}
x_72 = lean_get_set_stdin(x_35, x_40);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 2, 1);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_70);
lean_ctor_set_uint8(x_74, sizeof(void*)*2, x_69);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_67);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
x_9 = x_77;
x_10 = x_73;
goto block_30;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_67);
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_80 = x_72;
} else {
 lean_dec_ref(x_72);
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
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_38, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_37, 1);
lean_inc(x_83);
lean_dec(x_37);
x_84 = !lean_is_exclusive(x_38);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_38, 0);
x_86 = lean_ctor_get(x_38, 1);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_82);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_82, 0);
x_89 = lean_ctor_get(x_82, 1);
x_90 = lean_get_set_stdin(x_35, x_83);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_9 = x_38;
x_10 = x_91;
goto block_30;
}
else
{
uint8_t x_92; 
lean_free_object(x_82);
lean_dec(x_89);
lean_dec(x_88);
lean_free_object(x_38);
lean_dec(x_85);
x_92 = !lean_is_exclusive(x_90);
if (x_92 == 0)
{
return x_90;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_90, 0);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_90);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_82, 0);
x_97 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_98 = lean_ctor_get(x_82, 1);
lean_inc(x_98);
lean_inc(x_96);
lean_dec(x_82);
x_99 = lean_get_set_stdin(x_35, x_83);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_101, 0, x_96);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set_uint8(x_101, sizeof(void*)*2, x_97);
lean_ctor_set(x_38, 1, x_101);
x_9 = x_38;
x_10 = x_100;
goto block_30;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_98);
lean_dec(x_96);
lean_free_object(x_38);
lean_dec(x_85);
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_104 = x_99;
} else {
 lean_dec_ref(x_99);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_38, 0);
lean_inc(x_106);
lean_dec(x_38);
x_107 = lean_ctor_get(x_82, 0);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_109 = lean_ctor_get(x_82, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_110 = x_82;
} else {
 lean_dec_ref(x_82);
 x_110 = lean_box(0);
}
x_111 = lean_get_set_stdin(x_35, x_83);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
if (lean_is_scalar(x_110)) {
 x_113 = lean_alloc_ctor(0, 2, 1);
} else {
 x_113 = x_110;
}
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_109);
lean_ctor_set_uint8(x_113, sizeof(void*)*2, x_108);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_106);
lean_ctor_set(x_114, 1, x_113);
x_9 = x_114;
x_10 = x_112;
goto block_30;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_106);
x_115 = lean_ctor_get(x_111, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_117 = x_111;
} else {
 lean_dec_ref(x_111);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_35);
x_119 = !lean_is_exclusive(x_37);
if (x_119 == 0)
{
return x_37;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_37, 0);
x_121 = lean_ctor_get(x_37, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_37);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_free_object(x_7);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_34);
if (x_123 == 0)
{
return x_34;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_34, 0);
x_125 = lean_ctor_get(x_34, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_34);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_7, 0);
x_128 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_129 = lean_ctor_get(x_7, 1);
lean_inc(x_129);
lean_inc(x_127);
lean_dec(x_7);
x_130 = lean_get_set_stdin(x_1, x_8);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_133, 0, x_127);
lean_ctor_set(x_133, 1, x_129);
lean_ctor_set_uint8(x_133, sizeof(void*)*2, x_128);
x_134 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_133, x_132);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_139 = x_135;
} else {
 lean_dec_ref(x_135);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_136, 0);
lean_inc(x_140);
x_141 = lean_ctor_get_uint8(x_136, sizeof(void*)*2);
x_142 = lean_ctor_get(x_136, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_143 = x_136;
} else {
 lean_dec_ref(x_136);
 x_143 = lean_box(0);
}
x_144 = lean_get_set_stdin(x_131, x_137);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
if (lean_is_scalar(x_143)) {
 x_146 = lean_alloc_ctor(0, 2, 1);
} else {
 x_146 = x_143;
}
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_142);
lean_ctor_set_uint8(x_146, sizeof(void*)*2, x_141);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_138);
lean_ctor_set(x_148, 1, x_147);
if (lean_is_scalar(x_139)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_139;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_146);
x_9 = x_149;
x_10 = x_145;
goto block_30;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
x_150 = lean_ctor_get(x_144, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_144, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_152 = x_144;
} else {
 lean_dec_ref(x_144);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_154 = lean_ctor_get(x_135, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_134, 1);
lean_inc(x_155);
lean_dec(x_134);
x_156 = lean_ctor_get(x_135, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_157 = x_135;
} else {
 lean_dec_ref(x_135);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_154, 0);
lean_inc(x_158);
x_159 = lean_ctor_get_uint8(x_154, sizeof(void*)*2);
x_160 = lean_ctor_get(x_154, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_161 = x_154;
} else {
 lean_dec_ref(x_154);
 x_161 = lean_box(0);
}
x_162 = lean_get_set_stdin(x_131, x_155);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 2, 1);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_158);
lean_ctor_set(x_164, 1, x_160);
lean_ctor_set_uint8(x_164, sizeof(void*)*2, x_159);
if (lean_is_scalar(x_157)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_157;
}
lean_ctor_set(x_165, 0, x_156);
lean_ctor_set(x_165, 1, x_164);
x_9 = x_165;
x_10 = x_163;
goto block_30;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
x_166 = lean_ctor_get(x_162, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_162, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_168 = x_162;
} else {
 lean_dec_ref(x_162);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_131);
x_170 = lean_ctor_get(x_134, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_134, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_172 = x_134;
} else {
 lean_dec_ref(x_134);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_129);
lean_dec(x_127);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_174 = lean_ctor_get(x_130, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_130, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_176 = x_130;
} else {
 lean_dec_ref(x_130);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
block_30:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_14);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_31; 
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
x_34 = lean_get_set_stderr(x_1, x_8);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
x_47 = lean_get_set_stderr(x_35, x_40);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_38, 0, x_50);
x_9 = x_38;
x_10 = x_48;
goto block_30;
}
else
{
uint8_t x_51; 
lean_free_object(x_39);
lean_dec(x_46);
lean_dec(x_45);
lean_free_object(x_38);
lean_dec(x_42);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_47, 0);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_47);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_39, 0);
x_56 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_inc(x_55);
lean_dec(x_39);
x_58 = lean_get_set_stderr(x_35, x_40);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_56);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_42);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_38, 1, x_60);
lean_ctor_set(x_38, 0, x_62);
x_9 = x_38;
x_10 = x_59;
goto block_30;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_57);
lean_dec(x_55);
lean_free_object(x_38);
lean_dec(x_42);
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_65 = x_58;
} else {
 lean_dec_ref(x_58);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_38, 0);
lean_inc(x_67);
lean_dec(x_38);
x_68 = lean_ctor_get(x_39, 0);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_70 = lean_ctor_get(x_39, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_71 = x_39;
} else {
 lean_dec_ref(x_39);
 x_71 = lean_box(0);
}
x_72 = lean_get_set_stderr(x_35, x_40);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 2, 1);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_70);
lean_ctor_set_uint8(x_74, sizeof(void*)*2, x_69);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_67);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
x_9 = x_77;
x_10 = x_73;
goto block_30;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_67);
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_80 = x_72;
} else {
 lean_dec_ref(x_72);
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
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_38, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_37, 1);
lean_inc(x_83);
lean_dec(x_37);
x_84 = !lean_is_exclusive(x_38);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_38, 0);
x_86 = lean_ctor_get(x_38, 1);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_82);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_82, 0);
x_89 = lean_ctor_get(x_82, 1);
x_90 = lean_get_set_stderr(x_35, x_83);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_9 = x_38;
x_10 = x_91;
goto block_30;
}
else
{
uint8_t x_92; 
lean_free_object(x_82);
lean_dec(x_89);
lean_dec(x_88);
lean_free_object(x_38);
lean_dec(x_85);
x_92 = !lean_is_exclusive(x_90);
if (x_92 == 0)
{
return x_90;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_90, 0);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_90);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_82, 0);
x_97 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_98 = lean_ctor_get(x_82, 1);
lean_inc(x_98);
lean_inc(x_96);
lean_dec(x_82);
x_99 = lean_get_set_stderr(x_35, x_83);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_101, 0, x_96);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set_uint8(x_101, sizeof(void*)*2, x_97);
lean_ctor_set(x_38, 1, x_101);
x_9 = x_38;
x_10 = x_100;
goto block_30;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_98);
lean_dec(x_96);
lean_free_object(x_38);
lean_dec(x_85);
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_104 = x_99;
} else {
 lean_dec_ref(x_99);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_38, 0);
lean_inc(x_106);
lean_dec(x_38);
x_107 = lean_ctor_get(x_82, 0);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_109 = lean_ctor_get(x_82, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_110 = x_82;
} else {
 lean_dec_ref(x_82);
 x_110 = lean_box(0);
}
x_111 = lean_get_set_stderr(x_35, x_83);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
if (lean_is_scalar(x_110)) {
 x_113 = lean_alloc_ctor(0, 2, 1);
} else {
 x_113 = x_110;
}
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_109);
lean_ctor_set_uint8(x_113, sizeof(void*)*2, x_108);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_106);
lean_ctor_set(x_114, 1, x_113);
x_9 = x_114;
x_10 = x_112;
goto block_30;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_106);
x_115 = lean_ctor_get(x_111, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_117 = x_111;
} else {
 lean_dec_ref(x_111);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_35);
x_119 = !lean_is_exclusive(x_37);
if (x_119 == 0)
{
return x_37;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_37, 0);
x_121 = lean_ctor_get(x_37, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_37);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_free_object(x_7);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_34);
if (x_123 == 0)
{
return x_34;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_34, 0);
x_125 = lean_ctor_get(x_34, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_34);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_7, 0);
x_128 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_129 = lean_ctor_get(x_7, 1);
lean_inc(x_129);
lean_inc(x_127);
lean_dec(x_7);
x_130 = lean_get_set_stderr(x_1, x_8);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_133, 0, x_127);
lean_ctor_set(x_133, 1, x_129);
lean_ctor_set_uint8(x_133, sizeof(void*)*2, x_128);
x_134 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_133, x_132);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_139 = x_135;
} else {
 lean_dec_ref(x_135);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_136, 0);
lean_inc(x_140);
x_141 = lean_ctor_get_uint8(x_136, sizeof(void*)*2);
x_142 = lean_ctor_get(x_136, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_143 = x_136;
} else {
 lean_dec_ref(x_136);
 x_143 = lean_box(0);
}
x_144 = lean_get_set_stderr(x_131, x_137);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
if (lean_is_scalar(x_143)) {
 x_146 = lean_alloc_ctor(0, 2, 1);
} else {
 x_146 = x_143;
}
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_142);
lean_ctor_set_uint8(x_146, sizeof(void*)*2, x_141);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_138);
lean_ctor_set(x_148, 1, x_147);
if (lean_is_scalar(x_139)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_139;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_146);
x_9 = x_149;
x_10 = x_145;
goto block_30;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
x_150 = lean_ctor_get(x_144, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_144, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_152 = x_144;
} else {
 lean_dec_ref(x_144);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_154 = lean_ctor_get(x_135, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_134, 1);
lean_inc(x_155);
lean_dec(x_134);
x_156 = lean_ctor_get(x_135, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_157 = x_135;
} else {
 lean_dec_ref(x_135);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_154, 0);
lean_inc(x_158);
x_159 = lean_ctor_get_uint8(x_154, sizeof(void*)*2);
x_160 = lean_ctor_get(x_154, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_161 = x_154;
} else {
 lean_dec_ref(x_154);
 x_161 = lean_box(0);
}
x_162 = lean_get_set_stderr(x_131, x_155);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 2, 1);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_158);
lean_ctor_set(x_164, 1, x_160);
lean_ctor_set_uint8(x_164, sizeof(void*)*2, x_159);
if (lean_is_scalar(x_157)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_157;
}
lean_ctor_set(x_165, 0, x_156);
lean_ctor_set(x_165, 1, x_164);
x_9 = x_165;
x_10 = x_163;
goto block_30;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
x_166 = lean_ctor_get(x_162, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_162, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_168 = x_162;
} else {
 lean_dec_ref(x_162);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_131);
x_170 = lean_ctor_get(x_134, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_134, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_172 = x_134;
} else {
 lean_dec_ref(x_134);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_129);
lean_dec(x_127);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_174 = lean_ctor_get(x_130, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_130, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_176 = x_130;
} else {
 lean_dec_ref(x_130);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
block_30:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_14);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_ByteArray_empty;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.String.Extra", 22, 22);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String.fromUTF8!", 16, 16);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid UTF-8 string", 20, 20);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__2;
x_2 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__3;
x_3 = lean_unsigned_to_nat(100u);
x_4 = lean_unsigned_to_nat(47u);
x_5 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
x_12 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__1;
x_13 = lean_st_mk_ref(x_12, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_mk_ref(x_12, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_IO_FS_Stream_ofBuffer(x_14);
lean_inc(x_17);
x_20 = l_IO_FS_Stream_ofBuffer(x_17);
if (x_2 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_closure((void*)(l_IO_withStdout___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__3), 8, 2);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, x_1);
x_22 = l_IO_withStdin___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__4(x_19, x_21, x_3, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
x_32 = lean_st_ref_get(x_17, x_25);
lean_dec(x_17);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_string_validate_utf8(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_35);
x_37 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__5;
x_38 = l_panic___at_String_fromUTF8_x21___spec__1(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_27);
lean_ctor_set(x_23, 0, x_39);
lean_ctor_set(x_32, 0, x_23);
return x_32;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_string_from_utf8_unchecked(x_35);
lean_dec(x_35);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_27);
lean_ctor_set(x_23, 0, x_41);
lean_ctor_set(x_32, 0, x_23);
return x_32;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_ctor_get(x_32, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_32);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_string_validate_utf8(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_44);
x_46 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__5;
x_47 = l_panic___at_String_fromUTF8_x21___spec__1(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_27);
lean_ctor_set(x_23, 0, x_48);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_23);
lean_ctor_set(x_49, 1, x_43);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_string_from_utf8_unchecked(x_44);
lean_dec(x_44);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_27);
lean_ctor_set(x_23, 0, x_51);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_23);
lean_ctor_set(x_52, 1, x_43);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_free_object(x_24);
lean_dec(x_31);
lean_dec(x_30);
lean_free_object(x_23);
lean_dec(x_27);
x_53 = !lean_is_exclusive(x_32);
if (x_53 == 0)
{
return x_32;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_32, 0);
x_55 = lean_ctor_get(x_32, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_32);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_24, 0);
x_58 = lean_ctor_get_uint8(x_24, sizeof(void*)*2);
x_59 = lean_ctor_get(x_24, 1);
lean_inc(x_59);
lean_inc(x_57);
lean_dec(x_24);
x_60 = lean_st_ref_get(x_17, x_25);
lean_dec(x_17);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
x_64 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_59);
lean_ctor_set_uint8(x_64, sizeof(void*)*2, x_58);
x_65 = lean_ctor_get(x_61, 0);
lean_inc(x_65);
lean_dec(x_61);
x_66 = lean_string_validate_utf8(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_65);
x_67 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__5;
x_68 = l_panic___at_String_fromUTF8_x21___spec__1(x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_27);
lean_ctor_set(x_23, 1, x_64);
lean_ctor_set(x_23, 0, x_69);
if (lean_is_scalar(x_63)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_63;
}
lean_ctor_set(x_70, 0, x_23);
lean_ctor_set(x_70, 1, x_62);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_string_from_utf8_unchecked(x_65);
lean_dec(x_65);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_27);
lean_ctor_set(x_23, 1, x_64);
lean_ctor_set(x_23, 0, x_72);
if (lean_is_scalar(x_63)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_63;
}
lean_ctor_set(x_73, 0, x_23);
lean_ctor_set(x_73, 1, x_62);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_59);
lean_dec(x_57);
lean_free_object(x_23);
lean_dec(x_27);
x_74 = lean_ctor_get(x_60, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_60, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_76 = x_60;
} else {
 lean_dec_ref(x_60);
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
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_23, 0);
lean_inc(x_78);
lean_dec(x_23);
x_79 = lean_ctor_get(x_24, 0);
lean_inc(x_79);
x_80 = lean_ctor_get_uint8(x_24, sizeof(void*)*2);
x_81 = lean_ctor_get(x_24, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_82 = x_24;
} else {
 lean_dec_ref(x_24);
 x_82 = lean_box(0);
}
x_83 = lean_st_ref_get(x_17, x_25);
lean_dec(x_17);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_87 = lean_alloc_ctor(0, 2, 1);
} else {
 x_87 = x_82;
}
lean_ctor_set(x_87, 0, x_79);
lean_ctor_set(x_87, 1, x_81);
lean_ctor_set_uint8(x_87, sizeof(void*)*2, x_80);
x_88 = lean_ctor_get(x_84, 0);
lean_inc(x_88);
lean_dec(x_84);
x_89 = lean_string_validate_utf8(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_88);
x_90 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__5;
x_91 = l_panic___at_String_fromUTF8_x21___spec__1(x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_78);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_87);
if (lean_is_scalar(x_86)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_86;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_85);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_string_from_utf8_unchecked(x_88);
lean_dec(x_88);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_78);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_87);
if (lean_is_scalar(x_86)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_86;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_85);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_78);
x_99 = lean_ctor_get(x_83, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_83, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_101 = x_83;
} else {
 lean_dec_ref(x_83);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_17);
x_103 = !lean_is_exclusive(x_22);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_22, 0);
lean_dec(x_104);
x_105 = !lean_is_exclusive(x_23);
if (x_105 == 0)
{
return x_22;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_23, 0);
x_107 = lean_ctor_get(x_23, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_23);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set(x_22, 0, x_108);
return x_22;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_109 = lean_ctor_get(x_22, 1);
lean_inc(x_109);
lean_dec(x_22);
x_110 = lean_ctor_get(x_23, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_23, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_112 = x_23;
} else {
 lean_dec_ref(x_23);
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
}
else
{
uint8_t x_115; 
lean_dec(x_17);
x_115 = !lean_is_exclusive(x_22);
if (x_115 == 0)
{
return x_22;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_22, 0);
x_117 = lean_ctor_get(x_22, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_22);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_inc(x_20);
x_119 = lean_alloc_closure((void*)(l_IO_withStderr___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__5), 8, 2);
lean_closure_set(x_119, 0, x_20);
lean_closure_set(x_119, 1, x_1);
x_120 = lean_alloc_closure((void*)(l_IO_withStdout___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__3), 8, 2);
lean_closure_set(x_120, 0, x_20);
lean_closure_set(x_120, 1, x_119);
x_121 = l_IO_withStdin___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__4(x_19, x_120, x_3, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_dec(x_121);
x_125 = !lean_is_exclusive(x_122);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_126 = lean_ctor_get(x_122, 0);
x_127 = lean_ctor_get(x_122, 1);
lean_dec(x_127);
x_128 = !lean_is_exclusive(x_123);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_123, 0);
x_130 = lean_ctor_get(x_123, 1);
x_131 = lean_st_ref_get(x_17, x_124);
lean_dec(x_17);
if (lean_obj_tag(x_131) == 0)
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_ctor_get(x_131, 0);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
lean_dec(x_133);
x_135 = lean_string_validate_utf8(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_134);
x_136 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__5;
x_137 = l_panic___at_String_fromUTF8_x21___spec__1(x_136);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_126);
lean_ctor_set(x_122, 0, x_138);
lean_ctor_set(x_131, 0, x_122);
return x_131;
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_string_from_utf8_unchecked(x_134);
lean_dec(x_134);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_126);
lean_ctor_set(x_122, 0, x_140);
lean_ctor_set(x_131, 0, x_122);
return x_131;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_141 = lean_ctor_get(x_131, 0);
x_142 = lean_ctor_get(x_131, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_131);
x_143 = lean_ctor_get(x_141, 0);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_string_validate_utf8(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_143);
x_145 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__5;
x_146 = l_panic___at_String_fromUTF8_x21___spec__1(x_145);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_126);
lean_ctor_set(x_122, 0, x_147);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_122);
lean_ctor_set(x_148, 1, x_142);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_string_from_utf8_unchecked(x_143);
lean_dec(x_143);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_126);
lean_ctor_set(x_122, 0, x_150);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_122);
lean_ctor_set(x_151, 1, x_142);
return x_151;
}
}
}
else
{
uint8_t x_152; 
lean_free_object(x_123);
lean_dec(x_130);
lean_dec(x_129);
lean_free_object(x_122);
lean_dec(x_126);
x_152 = !lean_is_exclusive(x_131);
if (x_152 == 0)
{
return x_131;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_131, 0);
x_154 = lean_ctor_get(x_131, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_131);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; 
x_156 = lean_ctor_get(x_123, 0);
x_157 = lean_ctor_get_uint8(x_123, sizeof(void*)*2);
x_158 = lean_ctor_get(x_123, 1);
lean_inc(x_158);
lean_inc(x_156);
lean_dec(x_123);
x_159 = lean_st_ref_get(x_17, x_124);
lean_dec(x_17);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_162 = x_159;
} else {
 lean_dec_ref(x_159);
 x_162 = lean_box(0);
}
x_163 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_163, 0, x_156);
lean_ctor_set(x_163, 1, x_158);
lean_ctor_set_uint8(x_163, sizeof(void*)*2, x_157);
x_164 = lean_ctor_get(x_160, 0);
lean_inc(x_164);
lean_dec(x_160);
x_165 = lean_string_validate_utf8(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_164);
x_166 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__5;
x_167 = l_panic___at_String_fromUTF8_x21___spec__1(x_166);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_126);
lean_ctor_set(x_122, 1, x_163);
lean_ctor_set(x_122, 0, x_168);
if (lean_is_scalar(x_162)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_162;
}
lean_ctor_set(x_169, 0, x_122);
lean_ctor_set(x_169, 1, x_161);
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_string_from_utf8_unchecked(x_164);
lean_dec(x_164);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_126);
lean_ctor_set(x_122, 1, x_163);
lean_ctor_set(x_122, 0, x_171);
if (lean_is_scalar(x_162)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_162;
}
lean_ctor_set(x_172, 0, x_122);
lean_ctor_set(x_172, 1, x_161);
return x_172;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_158);
lean_dec(x_156);
lean_free_object(x_122);
lean_dec(x_126);
x_173 = lean_ctor_get(x_159, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_159, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_175 = x_159;
} else {
 lean_dec_ref(x_159);
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
}
else
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_177 = lean_ctor_get(x_122, 0);
lean_inc(x_177);
lean_dec(x_122);
x_178 = lean_ctor_get(x_123, 0);
lean_inc(x_178);
x_179 = lean_ctor_get_uint8(x_123, sizeof(void*)*2);
x_180 = lean_ctor_get(x_123, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_181 = x_123;
} else {
 lean_dec_ref(x_123);
 x_181 = lean_box(0);
}
x_182 = lean_st_ref_get(x_17, x_124);
lean_dec(x_17);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_185 = x_182;
} else {
 lean_dec_ref(x_182);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_186 = lean_alloc_ctor(0, 2, 1);
} else {
 x_186 = x_181;
}
lean_ctor_set(x_186, 0, x_178);
lean_ctor_set(x_186, 1, x_180);
lean_ctor_set_uint8(x_186, sizeof(void*)*2, x_179);
x_187 = lean_ctor_get(x_183, 0);
lean_inc(x_187);
lean_dec(x_183);
x_188 = lean_string_validate_utf8(x_187);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_187);
x_189 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__5;
x_190 = l_panic___at_String_fromUTF8_x21___spec__1(x_189);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_177);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_186);
if (lean_is_scalar(x_185)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_185;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_184);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_194 = lean_string_from_utf8_unchecked(x_187);
lean_dec(x_187);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_177);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_186);
if (lean_is_scalar(x_185)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_185;
}
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_184);
return x_197;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_178);
lean_dec(x_177);
x_198 = lean_ctor_get(x_182, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_182, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_200 = x_182;
} else {
 lean_dec_ref(x_182);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
}
}
else
{
uint8_t x_202; 
lean_dec(x_17);
x_202 = !lean_is_exclusive(x_121);
if (x_202 == 0)
{
lean_object* x_203; uint8_t x_204; 
x_203 = lean_ctor_get(x_121, 0);
lean_dec(x_203);
x_204 = !lean_is_exclusive(x_122);
if (x_204 == 0)
{
return x_121;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_122, 0);
x_206 = lean_ctor_get(x_122, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_122);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
lean_ctor_set(x_121, 0, x_207);
return x_121;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_208 = lean_ctor_get(x_121, 1);
lean_inc(x_208);
lean_dec(x_121);
x_209 = lean_ctor_get(x_122, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_122, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_211 = x_122;
} else {
 lean_dec_ref(x_122);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_210);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_208);
return x_213;
}
}
}
else
{
uint8_t x_214; 
lean_dec(x_17);
x_214 = !lean_is_exclusive(x_121);
if (x_214 == 0)
{
return x_121;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_121, 0);
x_216 = lean_ctor_get(x_121, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_121);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
}
}
else
{
uint8_t x_218; 
lean_dec(x_14);
lean_free_object(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_218 = !lean_is_exclusive(x_16);
if (x_218 == 0)
{
return x_16;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_16, 0);
x_220 = lean_ctor_get(x_16, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_16);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
}
else
{
uint8_t x_222; 
lean_free_object(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_222 = !lean_is_exclusive(x_13);
if (x_222 == 0)
{
return x_13;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_13, 0);
x_224 = lean_ctor_get(x_13, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_13);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
else
{
lean_object* x_226; uint8_t x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_226 = lean_ctor_get(x_7, 0);
x_227 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_228 = lean_ctor_get(x_7, 1);
lean_inc(x_228);
lean_inc(x_226);
lean_dec(x_7);
x_229 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__1;
x_230 = lean_st_mk_ref(x_229, x_8);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = lean_st_mk_ref(x_229, x_232);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_236, 0, x_226);
lean_ctor_set(x_236, 1, x_228);
lean_ctor_set_uint8(x_236, sizeof(void*)*2, x_227);
x_237 = l_IO_FS_Stream_ofBuffer(x_231);
lean_inc(x_234);
x_238 = l_IO_FS_Stream_ofBuffer(x_234);
if (x_2 == 0)
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_alloc_closure((void*)(l_IO_withStdout___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__3), 8, 2);
lean_closure_set(x_239, 0, x_238);
lean_closure_set(x_239, 1, x_1);
x_240 = l_IO_withStdin___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__4(x_237, x_239, x_3, x_4, x_5, x_6, x_236, x_235);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_240, 1);
lean_inc(x_243);
lean_dec(x_240);
x_244 = lean_ctor_get(x_241, 0);
lean_inc(x_244);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_245 = x_241;
} else {
 lean_dec_ref(x_241);
 x_245 = lean_box(0);
}
x_246 = lean_ctor_get(x_242, 0);
lean_inc(x_246);
x_247 = lean_ctor_get_uint8(x_242, sizeof(void*)*2);
x_248 = lean_ctor_get(x_242, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_249 = x_242;
} else {
 lean_dec_ref(x_242);
 x_249 = lean_box(0);
}
x_250 = lean_st_ref_get(x_234, x_243);
lean_dec(x_234);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_253 = x_250;
} else {
 lean_dec_ref(x_250);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_254 = lean_alloc_ctor(0, 2, 1);
} else {
 x_254 = x_249;
}
lean_ctor_set(x_254, 0, x_246);
lean_ctor_set(x_254, 1, x_248);
lean_ctor_set_uint8(x_254, sizeof(void*)*2, x_247);
x_255 = lean_ctor_get(x_251, 0);
lean_inc(x_255);
lean_dec(x_251);
x_256 = lean_string_validate_utf8(x_255);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_255);
x_257 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__5;
x_258 = l_panic___at_String_fromUTF8_x21___spec__1(x_257);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_244);
if (lean_is_scalar(x_245)) {
 x_260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_260 = x_245;
}
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_254);
if (lean_is_scalar(x_253)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_253;
}
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_252);
return x_261;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_262 = lean_string_from_utf8_unchecked(x_255);
lean_dec(x_255);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_244);
if (lean_is_scalar(x_245)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_245;
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_254);
if (lean_is_scalar(x_253)) {
 x_265 = lean_alloc_ctor(0, 2, 0);
} else {
 x_265 = x_253;
}
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_252);
return x_265;
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
x_266 = lean_ctor_get(x_250, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_250, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_268 = x_250;
} else {
 lean_dec_ref(x_250);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(1, 2, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_266);
lean_ctor_set(x_269, 1, x_267);
return x_269;
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_234);
x_270 = lean_ctor_get(x_240, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_271 = x_240;
} else {
 lean_dec_ref(x_240);
 x_271 = lean_box(0);
}
x_272 = lean_ctor_get(x_241, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_241, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_274 = x_241;
} else {
 lean_dec_ref(x_241);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(1, 2, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_272);
lean_ctor_set(x_275, 1, x_273);
if (lean_is_scalar(x_271)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_271;
}
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_270);
return x_276;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_234);
x_277 = lean_ctor_get(x_240, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_240, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_279 = x_240;
} else {
 lean_dec_ref(x_240);
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
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_inc(x_238);
x_281 = lean_alloc_closure((void*)(l_IO_withStderr___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__5), 8, 2);
lean_closure_set(x_281, 0, x_238);
lean_closure_set(x_281, 1, x_1);
x_282 = lean_alloc_closure((void*)(l_IO_withStdout___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__3), 8, 2);
lean_closure_set(x_282, 0, x_238);
lean_closure_set(x_282, 1, x_281);
x_283 = l_IO_withStdin___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__4(x_237, x_282, x_3, x_4, x_5, x_6, x_236, x_235);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_285 = lean_ctor_get(x_284, 1);
lean_inc(x_285);
x_286 = lean_ctor_get(x_283, 1);
lean_inc(x_286);
lean_dec(x_283);
x_287 = lean_ctor_get(x_284, 0);
lean_inc(x_287);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_288 = x_284;
} else {
 lean_dec_ref(x_284);
 x_288 = lean_box(0);
}
x_289 = lean_ctor_get(x_285, 0);
lean_inc(x_289);
x_290 = lean_ctor_get_uint8(x_285, sizeof(void*)*2);
x_291 = lean_ctor_get(x_285, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_292 = x_285;
} else {
 lean_dec_ref(x_285);
 x_292 = lean_box(0);
}
x_293 = lean_st_ref_get(x_234, x_286);
lean_dec(x_234);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_296 = x_293;
} else {
 lean_dec_ref(x_293);
 x_296 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_297 = lean_alloc_ctor(0, 2, 1);
} else {
 x_297 = x_292;
}
lean_ctor_set(x_297, 0, x_289);
lean_ctor_set(x_297, 1, x_291);
lean_ctor_set_uint8(x_297, sizeof(void*)*2, x_290);
x_298 = lean_ctor_get(x_294, 0);
lean_inc(x_298);
lean_dec(x_294);
x_299 = lean_string_validate_utf8(x_298);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_298);
x_300 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__5;
x_301 = l_panic___at_String_fromUTF8_x21___spec__1(x_300);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_287);
if (lean_is_scalar(x_288)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_288;
}
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_297);
if (lean_is_scalar(x_296)) {
 x_304 = lean_alloc_ctor(0, 2, 0);
} else {
 x_304 = x_296;
}
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_295);
return x_304;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_305 = lean_string_from_utf8_unchecked(x_298);
lean_dec(x_298);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_287);
if (lean_is_scalar(x_288)) {
 x_307 = lean_alloc_ctor(0, 2, 0);
} else {
 x_307 = x_288;
}
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_297);
if (lean_is_scalar(x_296)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_296;
}
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_295);
return x_308;
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_292);
lean_dec(x_291);
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_287);
x_309 = lean_ctor_get(x_293, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_293, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_311 = x_293;
} else {
 lean_dec_ref(x_293);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(1, 2, 0);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_309);
lean_ctor_set(x_312, 1, x_310);
return x_312;
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_234);
x_313 = lean_ctor_get(x_283, 1);
lean_inc(x_313);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_314 = x_283;
} else {
 lean_dec_ref(x_283);
 x_314 = lean_box(0);
}
x_315 = lean_ctor_get(x_284, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_284, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_317 = x_284;
} else {
 lean_dec_ref(x_284);
 x_317 = lean_box(0);
}
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(1, 2, 0);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_315);
lean_ctor_set(x_318, 1, x_316);
if (lean_is_scalar(x_314)) {
 x_319 = lean_alloc_ctor(0, 2, 0);
} else {
 x_319 = x_314;
}
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_313);
return x_319;
}
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_234);
x_320 = lean_ctor_get(x_283, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_283, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_322 = x_283;
} else {
 lean_dec_ref(x_283);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 2, 0);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_320);
lean_ctor_set(x_323, 1, x_321);
return x_323;
}
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_231);
lean_dec(x_228);
lean_dec(x_226);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_324 = lean_ctor_get(x_233, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_233, 1);
lean_inc(x_325);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_326 = x_233;
} else {
 lean_dec_ref(x_233);
 x_326 = lean_box(0);
}
if (lean_is_scalar(x_326)) {
 x_327 = lean_alloc_ctor(1, 2, 0);
} else {
 x_327 = x_326;
}
lean_ctor_set(x_327, 0, x_324);
lean_ctor_set(x_327, 1, x_325);
return x_327;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_228);
lean_dec(x_226);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_328 = lean_ctor_get(x_230, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_230, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_330 = x_230;
} else {
 lean_dec_ref(x_230);
 x_330 = lean_box(0);
}
if (lean_is_scalar(x_330)) {
 x_331 = lean_alloc_ctor(1, 2, 0);
} else {
 x_331 = x_330;
}
lean_ctor_set(x_331, 0, x_328);
lean_ctor_set(x_331, 1, x_329);
return x_331;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_2);
x_11 = lean_apply_1(x_1, x_2);
x_12 = l_Lake_Package_fetchBuildArchive(x_2, x_4, x_11, x_3, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
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
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = 1;
x_19 = lean_box(x_18);
lean_ctor_set(x_13, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_21 = 1;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_12, 0, x_23);
return x_12;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_dec(x_12);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_26 = x_13;
} else {
 lean_dec_ref(x_13);
 x_26 = lean_box(0);
}
x_27 = 1;
x_28 = lean_box(x_27);
if (lean_is_scalar(x_26)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_26;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_12);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_12, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_13);
if (x_33 == 0)
{
return x_12;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_13, 0);
x_35 = lean_ctor_get(x_13, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_13);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_12, 0, x_36);
return x_12;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
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
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_12);
if (x_43 == 0)
{
return x_12;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_12, 0);
x_45 = lean_ctor_get(x_12, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_12);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_10 = 2;
x_11 = l_Lake_JobAction_merge(x_9, x_10);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_11);
x_12 = 0;
x_13 = lean_box(x_12);
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
lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_inc(x_16);
lean_dec(x_6);
x_19 = 2;
x_20 = l_Lake_JobAction_merge(x_17, x_19);
x_21 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set_uint8(x_21, sizeof(void*)*2, x_20);
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_7);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_string_utf8_byte_size(x_14);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; 
x_19 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_14, x_16, x_17);
x_20 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_14, x_19, x_16);
x_21 = lean_string_utf8_extract(x_14, x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
x_22 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__5___closed__1;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_25 = lean_string_append(x_23, x_24);
x_26 = 1;
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_array_push(x_29, x_27);
lean_ctor_set(x_13, 0, x_30);
x_31 = lean_box(0);
x_32 = lean_unbox(x_15);
lean_dec(x_15);
x_33 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__4(x_32, x_31, x_2, x_3, x_4, x_5, x_13, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_33;
}
else
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_13, 0);
x_35 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_inc(x_34);
lean_dec(x_13);
x_37 = lean_array_push(x_34, x_27);
x_38 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_35);
x_39 = lean_box(0);
x_40 = lean_unbox(x_15);
lean_dec(x_15);
x_41 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__4(x_40, x_39, x_2, x_3, x_4, x_5, x_38, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_41;
}
}
else
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; 
lean_dec(x_16);
lean_dec(x_14);
x_42 = lean_box(0);
x_43 = lean_unbox(x_15);
lean_dec(x_15);
x_44 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__4(x_43, x_42, x_2, x_3, x_4, x_5, x_13, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_9);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_9, 0);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_10);
if (x_47 == 0)
{
return x_9;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_10, 0);
x_49 = lean_ctor_get(x_10, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_10);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_9, 0, x_50);
return x_9;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_9, 1);
lean_inc(x_51);
lean_dec(x_9);
x_52 = lean_ctor_get(x_10, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_10, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_54 = x_10;
} else {
 lean_dec_ref(x_10);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_51);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_9);
if (x_57 == 0)
{
return x_9;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_9, 0);
x_59 = lean_ctor_get(x_9, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_9);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lake_Package_recFetchDeps___lambda__1___closed__2;
x_9 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__5), 7, 6);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_4);
lean_closure_set(x_9, 4, x_5);
lean_closure_set(x_9, 5, x_8);
x_10 = l_Task_Priority_default;
x_11 = lean_io_as_task(x_9, x_10, x_7);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_15 = 0;
x_16 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_21 = 0;
x_22 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_6);
x_25 = !lean_is_exclusive(x_11);
if (x_25 == 0)
{
return x_11;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_11);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__2___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__7___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__3___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_12 = lean_ctor_get(x_5, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
x_14 = 1;
x_15 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1;
x_16 = l_Lean_Name_toString(x_13, x_14, x_15);
x_17 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Lean_Name_toString(x_1, x_14, x_15);
x_22 = lean_string_append(x_20, x_21);
lean_dec(x_21);
x_23 = lean_string_append(x_22, x_17);
lean_inc(x_5);
x_24 = lean_apply_1(x_2, x_5);
x_25 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__1), 10, 3);
lean_closure_set(x_25, 0, x_3);
lean_closure_set(x_25, 1, x_5);
lean_closure_set(x_25, 2, x_4);
x_26 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_buildFileUnlessUpToDate_x27___spec__1___rarg), 8, 2);
lean_closure_set(x_26, 0, x_24);
lean_closure_set(x_26, 1, x_25);
x_27 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__7___closed__1;
x_28 = lean_alloc_closure((void*)(l_Lake_EquipT_tryCatch___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___rarg), 8, 2);
lean_closure_set(x_28, 0, x_26);
lean_closure_set(x_28, 1, x_27);
x_29 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__7___closed__2;
x_30 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_buildFileUnlessUpToDate_x27___spec__1___rarg), 8, 2);
lean_closure_set(x_30, 0, x_28);
lean_closure_set(x_30, 1, x_29);
x_31 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__6), 7, 1);
lean_closure_set(x_31, 0, x_30);
x_32 = l_Lake_withRegisterJob___rarg(x_23, x_31, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
return x_32;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_stdFormat___at_Lake_Package_optBuildCacheFacetConfig___elambda__1___spec__1___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__7), 11, 4);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_3);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_4);
x_7 = 1;
x_8 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___closed__1;
x_9 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*2, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__3(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__4(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to fetch ", 16, 16);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (x_5 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*1 + 3);
x_16 = 2;
x_17 = l_Lake_instDecidableEqVerbosity(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_4);
lean_dec(x_3);
x_18 = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1___closed__1;
x_19 = lean_string_append(x_18, x_1);
x_20 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_21 = lean_string_append(x_19, x_20);
x_22 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_string_append(x_23, x_20);
x_25 = 3;
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_25);
x_27 = lean_array_get_size(x_13);
x_28 = lean_array_push(x_13, x_26);
lean_ctor_set(x_10, 0, x_28);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_10);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_11);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_31 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__2;
x_32 = lean_string_append(x_31, x_2);
x_33 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_34 = lean_string_append(x_32, x_33);
x_35 = 1;
x_36 = l_Lean_Name_toString(x_3, x_35, x_4);
x_37 = lean_string_append(x_34, x_36);
lean_dec(x_36);
x_38 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__4;
x_39 = lean_string_append(x_37, x_38);
x_40 = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1___closed__1;
x_41 = lean_string_append(x_40, x_1);
x_42 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_43 = lean_string_append(x_41, x_42);
x_44 = lean_string_append(x_43, x_39);
lean_dec(x_39);
x_45 = lean_string_append(x_44, x_42);
x_46 = 3;
x_47 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_46);
x_48 = lean_array_get_size(x_13);
x_49 = lean_array_push(x_13, x_47);
lean_ctor_set(x_10, 0, x_49);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_10);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_11);
return x_51;
}
}
else
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; 
x_52 = lean_ctor_get(x_10, 0);
x_53 = lean_ctor_get_uint8(x_10, sizeof(void*)*2);
x_54 = lean_ctor_get(x_10, 1);
lean_inc(x_54);
lean_inc(x_52);
lean_dec(x_10);
x_55 = lean_ctor_get(x_9, 0);
x_56 = lean_ctor_get_uint8(x_55, sizeof(void*)*1 + 3);
x_57 = 2;
x_58 = l_Lake_instDecidableEqVerbosity(x_56, x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_4);
lean_dec(x_3);
x_59 = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1___closed__1;
x_60 = lean_string_append(x_59, x_1);
x_61 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_62 = lean_string_append(x_60, x_61);
x_63 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__1;
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_string_append(x_64, x_61);
x_66 = 3;
x_67 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_66);
x_68 = lean_array_get_size(x_52);
x_69 = lean_array_push(x_52, x_67);
x_70 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_54);
lean_ctor_set_uint8(x_70, sizeof(void*)*2, x_53);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_11);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_73 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__2;
x_74 = lean_string_append(x_73, x_2);
x_75 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_76 = lean_string_append(x_74, x_75);
x_77 = 1;
x_78 = l_Lean_Name_toString(x_3, x_77, x_4);
x_79 = lean_string_append(x_76, x_78);
lean_dec(x_78);
x_80 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__4;
x_81 = lean_string_append(x_79, x_80);
x_82 = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1___closed__1;
x_83 = lean_string_append(x_82, x_1);
x_84 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_85 = lean_string_append(x_83, x_84);
x_86 = lean_string_append(x_85, x_81);
lean_dec(x_81);
x_87 = lean_string_append(x_86, x_84);
x_88 = 3;
x_89 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_88);
x_90 = lean_array_get_size(x_52);
x_91 = lean_array_push(x_52, x_89);
x_92 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_54);
lean_ctor_set_uint8(x_92, sizeof(void*)*2, x_53);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_11);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_4);
lean_dec(x_3);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_10);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_11);
return x_97;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1___boxed), 11, 4);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
x_13 = l_Task_Priority_default;
x_14 = 0;
x_15 = l_Lake_BuildTrace_nil;
x_16 = l_Lake_Job_mapM___rarg(x_5, x_12, x_13, x_14, x_6, x_7, x_8, x_9, x_15, x_11);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_10);
lean_ctor_set(x_16, 0, x_19);
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
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_10);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_10);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_11 = lean_ctor_get(x_4, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_dec(x_11);
x_13 = 1;
x_14 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1;
x_15 = l_Lean_Name_toString(x_12, x_13, x_14);
x_16 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_17 = lean_string_append(x_16, x_15);
x_18 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_Lean_Name_toString(x_1, x_13, x_14);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = lean_string_append(x_21, x_16);
lean_inc(x_2);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_2);
x_24 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_24, 0, x_23);
lean_closure_set(x_24, 1, lean_box(0));
x_25 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__2), 11, 4);
lean_closure_set(x_25, 0, x_3);
lean_closure_set(x_25, 1, x_15);
lean_closure_set(x_25, 2, x_2);
lean_closure_set(x_25, 3, x_14);
x_26 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Package_recBuildExtraDepTargets___spec__2___rarg), 8, 2);
lean_closure_set(x_26, 0, x_24);
lean_closure_set(x_26, 1, x_25);
x_27 = 0;
x_28 = l_Lake_withRegisterJob___rarg(x_22, x_26, x_27, x_5, x_6, x_7, x_8, x_9, x_10);
return x_28;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_nullFormat___rarg___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__3), 10, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_3);
x_7 = 1;
x_8 = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___closed__1;
x_9 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*2, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_nullFormat___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("build cache", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1___closed__1;
x_2 = l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__2;
x_2 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__3;
x_2 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__4;
x_2 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 3;
x_2 = l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__5;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (x_4 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*1 + 3);
x_15 = 2;
x_16 = l_Lake_instDecidableEqVerbosity(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_array_get_size(x_12);
x_18 = l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__6;
x_19 = lean_array_push(x_12, x_18);
lean_ctor_set(x_9, 0, x_19);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_9);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_10);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__2;
x_23 = lean_string_append(x_22, x_1);
x_24 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_25 = lean_string_append(x_23, x_24);
x_26 = 1;
x_27 = l_Lean_Name_toString(x_2, x_26, x_3);
x_28 = lean_string_append(x_25, x_27);
lean_dec(x_27);
x_29 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__4;
x_30 = lean_string_append(x_28, x_29);
x_31 = l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__3;
x_32 = lean_string_append(x_31, x_30);
lean_dec(x_30);
x_33 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_34 = lean_string_append(x_32, x_33);
x_35 = 3;
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_35);
x_37 = lean_array_get_size(x_12);
x_38 = lean_array_push(x_12, x_36);
lean_ctor_set(x_9, 0, x_38);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_9);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_10);
return x_40;
}
}
else
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; 
x_41 = lean_ctor_get(x_9, 0);
x_42 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_43 = lean_ctor_get(x_9, 1);
lean_inc(x_43);
lean_inc(x_41);
lean_dec(x_9);
x_44 = lean_ctor_get(x_8, 0);
x_45 = lean_ctor_get_uint8(x_44, sizeof(void*)*1 + 3);
x_46 = 2;
x_47 = l_Lake_instDecidableEqVerbosity(x_45, x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_3);
lean_dec(x_2);
x_48 = lean_array_get_size(x_41);
x_49 = l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__6;
x_50 = lean_array_push(x_41, x_49);
x_51 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_43);
lean_ctor_set_uint8(x_51, sizeof(void*)*2, x_42);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_10);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_54 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__2;
x_55 = lean_string_append(x_54, x_1);
x_56 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_57 = lean_string_append(x_55, x_56);
x_58 = 1;
x_59 = l_Lean_Name_toString(x_2, x_58, x_3);
x_60 = lean_string_append(x_57, x_59);
lean_dec(x_59);
x_61 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__4;
x_62 = lean_string_append(x_60, x_61);
x_63 = l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__3;
x_64 = lean_string_append(x_63, x_62);
lean_dec(x_62);
x_65 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_66 = lean_string_append(x_64, x_65);
x_67 = 3;
x_68 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set_uint8(x_68, sizeof(void*)*1, x_67);
x_69 = lean_array_get_size(x_41);
x_70 = lean_array_push(x_41, x_68);
x_71 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_43);
lean_ctor_set_uint8(x_71, sizeof(void*)*2, x_42);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_10);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_3);
lean_dec(x_2);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_9);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_10);
return x_76;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___boxed), 10, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
x_12 = l_Task_Priority_default;
x_13 = 0;
x_14 = l_Lake_BuildTrace_nil;
x_15 = l_Lake_Job_mapM___rarg(x_4, x_11, x_12, x_13, x_5, x_6, x_7, x_8, x_14, x_10);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
lean_ctor_set(x_15, 0, x_18);
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
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_9);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_9);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___elambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cache", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___elambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_buildCacheFacetConfig___elambda__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___elambda__2___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Package_buildCacheFacetConfig___elambda__2___closed__2;
x_2 = 1;
x_3 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = 1;
x_11 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1;
x_12 = l_Lean_Name_toString(x_9, x_10, x_11);
x_13 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_14 = lean_string_append(x_13, x_12);
x_15 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lake_Package_buildCacheFacetConfig___elambda__2___closed__3;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_13);
x_20 = l_Lake_Package_optBuildCacheFacetConfig___closed__2;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, lean_box(0));
x_23 = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__2), 10, 3);
lean_closure_set(x_23, 0, x_12);
lean_closure_set(x_23, 1, x_20);
lean_closure_set(x_23, 2, x_11);
x_24 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Package_recBuildExtraDepTargets___spec__2___rarg), 8, 2);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_23);
x_25 = 0;
x_26 = l_Lake_withRegisterJob___rarg(x_19, x_24, x_25, x_2, x_3, x_4, x_5, x_6, x_7);
return x_26;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___elambda__2), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Package_buildCacheFacetConfig___closed__1;
x_2 = 1;
x_3 = l_Lake_Package_buildCacheFacetConfig___closed__2;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_buildCacheFacetConfig___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Package_buildCacheFacetConfig___elambda__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___elambda__1(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at_Lake_Package_optBuildCacheFacetConfig___elambda__1___spec__1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___elambda__2___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("build.barrel", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___elambda__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = l_Lake_defaultLakeDir;
x_11 = l_System_FilePath_join(x_9, x_10);
x_12 = l_Lake_Package_optBarrelFacetConfig___elambda__2___lambda__1___closed__1;
x_13 = l_System_FilePath_join(x_11, x_12);
x_14 = l_Lake_Reservoir_lakeHeaders;
x_15 = l_Lake_Package_fetchBuildArchive(x_1, x_2, x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = 1;
x_22 = lean_box(x_21);
lean_ctor_set(x_16, 0, x_22);
return x_15;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_dec(x_16);
x_24 = 1;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_15, 0, x_26);
return x_15;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_dec(x_15);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_29 = x_16;
} else {
 lean_dec_ref(x_16);
 x_29 = lean_box(0);
}
x_30 = 1;
x_31 = lean_box(x_30);
if (lean_is_scalar(x_29)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_29;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_15, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
return x_15;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_16, 0);
x_38 = lean_ctor_get(x_16, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_16);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_15, 0, x_39);
return x_15;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 1);
lean_inc(x_40);
lean_dec(x_15);
x_41 = lean_ctor_get(x_16, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_16, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_43 = x_16;
} else {
 lean_dec_ref(x_16);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
return x_45;
}
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_15);
if (x_46 == 0)
{
return x_15;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_15, 0);
x_48 = lean_ctor_get(x_15, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_15);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = 1;
x_11 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1;
x_12 = l_Lean_Name_toString(x_9, x_10, x_11);
x_13 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__5;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_13);
lean_inc(x_1);
x_20 = lean_alloc_closure((void*)(l_Lake_Package_getBarrelUrl___boxed), 7, 1);
lean_closure_set(x_20, 0, x_1);
x_21 = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___elambda__2___lambda__1), 8, 1);
lean_closure_set(x_21, 0, x_1);
x_22 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_buildFileUnlessUpToDate_x27___spec__1___rarg), 8, 2);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
x_23 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__7___closed__1;
x_24 = lean_alloc_closure((void*)(l_Lake_EquipT_tryCatch___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___rarg), 8, 2);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_23);
x_25 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__7___closed__2;
x_26 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_buildFileUnlessUpToDate_x27___spec__1___rarg), 8, 2);
lean_closure_set(x_26, 0, x_24);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__6), 7, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = l_Lake_withRegisterJob___rarg(x_19, x_27, x_10, x_2, x_3, x_4, x_5, x_6, x_7);
return x_28;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___elambda__2), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Package_optBarrelFacetConfig___closed__1;
x_2 = 1;
x_3 = l_Lake_Package_optBarrelFacetConfig___closed__2;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_optBarrelFacetConfig___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_Package_optBarrelFacetConfig___elambda__1(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___elambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_nullFormat___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Reservoir build", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1___closed__1;
x_2 = l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__2;
x_2 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__3;
x_2 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__4;
x_2 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 3;
x_2 = l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__5;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (x_4 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*1 + 3);
x_15 = 2;
x_16 = l_Lake_instDecidableEqVerbosity(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_array_get_size(x_12);
x_18 = l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__6;
x_19 = lean_array_push(x_12, x_18);
lean_ctor_set(x_9, 0, x_19);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_9);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_10);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__2;
x_23 = lean_string_append(x_22, x_1);
x_24 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_25 = lean_string_append(x_23, x_24);
x_26 = 1;
x_27 = l_Lean_Name_toString(x_2, x_26, x_3);
x_28 = lean_string_append(x_25, x_27);
lean_dec(x_27);
x_29 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__4;
x_30 = lean_string_append(x_28, x_29);
x_31 = l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__3;
x_32 = lean_string_append(x_31, x_30);
lean_dec(x_30);
x_33 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_34 = lean_string_append(x_32, x_33);
x_35 = 3;
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_35);
x_37 = lean_array_get_size(x_12);
x_38 = lean_array_push(x_12, x_36);
lean_ctor_set(x_9, 0, x_38);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_9);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_10);
return x_40;
}
}
else
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; 
x_41 = lean_ctor_get(x_9, 0);
x_42 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_43 = lean_ctor_get(x_9, 1);
lean_inc(x_43);
lean_inc(x_41);
lean_dec(x_9);
x_44 = lean_ctor_get(x_8, 0);
x_45 = lean_ctor_get_uint8(x_44, sizeof(void*)*1 + 3);
x_46 = 2;
x_47 = l_Lake_instDecidableEqVerbosity(x_45, x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_3);
lean_dec(x_2);
x_48 = lean_array_get_size(x_41);
x_49 = l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__6;
x_50 = lean_array_push(x_41, x_49);
x_51 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_43);
lean_ctor_set_uint8(x_51, sizeof(void*)*2, x_42);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_10);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_54 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__2;
x_55 = lean_string_append(x_54, x_1);
x_56 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_57 = lean_string_append(x_55, x_56);
x_58 = 1;
x_59 = l_Lean_Name_toString(x_2, x_58, x_3);
x_60 = lean_string_append(x_57, x_59);
lean_dec(x_59);
x_61 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__4;
x_62 = lean_string_append(x_60, x_61);
x_63 = l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__3;
x_64 = lean_string_append(x_63, x_62);
lean_dec(x_62);
x_65 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_66 = lean_string_append(x_64, x_65);
x_67 = 3;
x_68 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set_uint8(x_68, sizeof(void*)*1, x_67);
x_69 = lean_array_get_size(x_41);
x_70 = lean_array_push(x_41, x_68);
x_71 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_43);
lean_ctor_set_uint8(x_71, sizeof(void*)*2, x_42);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_10);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_3);
lean_dec(x_2);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_9);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_10);
return x_76;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___elambda__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___boxed), 10, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
x_12 = l_Task_Priority_default;
x_13 = 0;
x_14 = l_Lake_BuildTrace_nil;
x_15 = l_Lake_Job_mapM___rarg(x_4, x_11, x_12, x_13, x_5, x_6, x_7, x_8, x_14, x_10);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
lean_ctor_set(x_15, 0, x_18);
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
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_9);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_9);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___elambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("barrel", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___elambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_barrelFacetConfig___elambda__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___elambda__2___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Package_barrelFacetConfig___elambda__2___closed__2;
x_2 = 1;
x_3 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = 1;
x_11 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1;
x_12 = l_Lean_Name_toString(x_9, x_10, x_11);
x_13 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_14 = lean_string_append(x_13, x_12);
x_15 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lake_Package_barrelFacetConfig___elambda__2___closed__3;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_13);
x_20 = l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__2;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, lean_box(0));
x_23 = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___elambda__2___lambda__2), 10, 3);
lean_closure_set(x_23, 0, x_12);
lean_closure_set(x_23, 1, x_20);
lean_closure_set(x_23, 2, x_11);
x_24 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Package_recBuildExtraDepTargets___spec__2___rarg), 8, 2);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_23);
x_25 = 0;
x_26 = l_Lake_withRegisterJob___rarg(x_19, x_24, x_25, x_2, x_3, x_4, x_5, x_6, x_7);
return x_26;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___elambda__2), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Package_barrelFacetConfig___closed__1;
x_2 = 1;
x_3 = l_Lake_Package_barrelFacetConfig___closed__2;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_barrelFacetConfig___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Package_barrelFacetConfig___elambda__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___elambda__1(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at_Lake_Package_optBuildCacheFacetConfig___elambda__1___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___elambda__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = l_Lake_defaultLakeDir;
x_13 = l_System_FilePath_join(x_11, x_12);
x_14 = lean_ctor_get(x_2, 16);
x_15 = l_System_FilePath_join(x_13, x_14);
x_16 = l_Lake_Package_fetchBuildArchive(x_1, x_4, x_15, x_3, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = 1;
x_23 = lean_box(x_22);
lean_ctor_set(x_17, 0, x_23);
return x_16;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = 1;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_16, 0, x_27);
return x_16;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_dec(x_16);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_30 = x_17;
} else {
 lean_dec_ref(x_17);
 x_30 = lean_box(0);
}
x_31 = 1;
x_32 = lean_box(x_31);
if (lean_is_scalar(x_30)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_30;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_28);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_16);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_16, 0);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_17);
if (x_37 == 0)
{
return x_16;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_17, 0);
x_39 = lean_ctor_get(x_17, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_17);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_16, 0, x_40);
return x_16;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_16, 1);
lean_inc(x_41);
lean_dec(x_16);
x_42 = lean_ctor_get(x_17, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_17, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_44 = x_17;
} else {
 lean_dec_ref(x_17);
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
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_16);
if (x_47 == 0)
{
return x_16;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_16, 0);
x_49 = lean_ctor_get(x_16, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_16);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___elambda__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = 0;
x_10 = l_Lake_BuildTrace_nil;
x_11 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_9);
x_12 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__5), 7, 6);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_5);
lean_closure_set(x_12, 4, x_6);
lean_closure_set(x_12, 5, x_11);
x_13 = l_Task_Priority_default;
x_14 = lean_io_as_task(x_12, x_13, x_8);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_18 = 0;
x_19 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_24 = 0;
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_7);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_7);
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
return x_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_14);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
x_10 = 1;
x_11 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1;
x_12 = l_Lean_Name_toString(x_9, x_10, x_11);
x_13 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__10;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_13);
lean_inc(x_1);
x_20 = lean_alloc_closure((void*)(l_Lake_Package_getReleaseUrl), 7, 1);
lean_closure_set(x_20, 0, x_1);
x_21 = l_Lake_Package_recFetchDeps___lambda__1___closed__1;
x_22 = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___elambda__2___lambda__1___boxed), 10, 3);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_8);
lean_closure_set(x_22, 2, x_21);
x_23 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_buildFileUnlessUpToDate_x27___spec__1___rarg), 8, 2);
lean_closure_set(x_23, 0, x_20);
lean_closure_set(x_23, 1, x_22);
x_24 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__7___closed__1;
x_25 = lean_alloc_closure((void*)(l_Lake_EquipT_tryCatch___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___rarg), 8, 2);
lean_closure_set(x_25, 0, x_23);
lean_closure_set(x_25, 1, x_24);
x_26 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__7___closed__2;
x_27 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_buildFileUnlessUpToDate_x27___spec__1___rarg), 8, 2);
lean_closure_set(x_27, 0, x_25);
lean_closure_set(x_27, 1, x_26);
x_28 = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___elambda__2___lambda__2), 8, 2);
lean_closure_set(x_28, 0, x_21);
lean_closure_set(x_28, 1, x_27);
x_29 = l_Lake_withRegisterJob___rarg(x_19, x_28, x_10, x_2, x_3, x_4, x_5, x_6, x_7);
return x_29;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___elambda__2), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Package_optGitHubReleaseFacetConfig___closed__1;
x_2 = 1;
x_3 = l_Lake_Package_optGitHubReleaseFacetConfig___closed__2;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_optGitHubReleaseFacetConfig___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_Package_optGitHubReleaseFacetConfig___elambda__1(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___elambda__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_Package_optGitHubReleaseFacetConfig___elambda__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l_Lake_Package_optReleaseFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_optGitHubReleaseFacetConfig;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_nullFormat___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("GitHub release", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1___closed__1;
x_2 = l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__2;
x_2 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__3;
x_2 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__4;
x_2 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 3;
x_2 = l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__5;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (x_4 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*1 + 3);
x_15 = 2;
x_16 = l_Lake_instDecidableEqVerbosity(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_array_get_size(x_12);
x_18 = l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__6;
x_19 = lean_array_push(x_12, x_18);
lean_ctor_set(x_9, 0, x_19);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_9);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_10);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__2;
x_23 = lean_string_append(x_22, x_1);
x_24 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_25 = lean_string_append(x_23, x_24);
x_26 = 1;
x_27 = l_Lean_Name_toString(x_2, x_26, x_3);
x_28 = lean_string_append(x_25, x_27);
lean_dec(x_27);
x_29 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__4;
x_30 = lean_string_append(x_28, x_29);
x_31 = l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__3;
x_32 = lean_string_append(x_31, x_30);
lean_dec(x_30);
x_33 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_34 = lean_string_append(x_32, x_33);
x_35 = 3;
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_35);
x_37 = lean_array_get_size(x_12);
x_38 = lean_array_push(x_12, x_36);
lean_ctor_set(x_9, 0, x_38);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_9);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_10);
return x_40;
}
}
else
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; 
x_41 = lean_ctor_get(x_9, 0);
x_42 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_43 = lean_ctor_get(x_9, 1);
lean_inc(x_43);
lean_inc(x_41);
lean_dec(x_9);
x_44 = lean_ctor_get(x_8, 0);
x_45 = lean_ctor_get_uint8(x_44, sizeof(void*)*1 + 3);
x_46 = 2;
x_47 = l_Lake_instDecidableEqVerbosity(x_45, x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_3);
lean_dec(x_2);
x_48 = lean_array_get_size(x_41);
x_49 = l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__6;
x_50 = lean_array_push(x_41, x_49);
x_51 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_43);
lean_ctor_set_uint8(x_51, sizeof(void*)*2, x_42);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_10);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_54 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__2;
x_55 = lean_string_append(x_54, x_1);
x_56 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_57 = lean_string_append(x_55, x_56);
x_58 = 1;
x_59 = l_Lean_Name_toString(x_2, x_58, x_3);
x_60 = lean_string_append(x_57, x_59);
lean_dec(x_59);
x_61 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__4;
x_62 = lean_string_append(x_60, x_61);
x_63 = l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__3;
x_64 = lean_string_append(x_63, x_62);
lean_dec(x_62);
x_65 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_66 = lean_string_append(x_64, x_65);
x_67 = 3;
x_68 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set_uint8(x_68, sizeof(void*)*1, x_67);
x_69 = lean_array_get_size(x_41);
x_70 = lean_array_push(x_41, x_68);
x_71 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_43);
lean_ctor_set_uint8(x_71, sizeof(void*)*2, x_42);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_10);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_3);
lean_dec(x_2);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_9);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_10);
return x_76;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___boxed), 10, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
x_12 = l_Task_Priority_default;
x_13 = 0;
x_14 = l_Lake_BuildTrace_nil;
x_15 = l_Lake_Job_mapM___rarg(x_4, x_11, x_12, x_13, x_5, x_6, x_7, x_8, x_14, x_10);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
lean_ctor_set(x_15, 0, x_18);
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
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_9);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_9);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("release", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___closed__2;
x_2 = 1;
x_3 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = 1;
x_11 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1;
x_12 = l_Lean_Name_toString(x_9, x_10, x_11);
x_13 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_14 = lean_string_append(x_13, x_12);
x_15 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___closed__3;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_13);
x_20 = l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__4;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, lean_box(0));
x_23 = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__2), 10, 3);
lean_closure_set(x_23, 0, x_12);
lean_closure_set(x_23, 1, x_20);
lean_closure_set(x_23, 2, x_11);
x_24 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Package_recBuildExtraDepTargets___spec__2___rarg), 8, 2);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_23);
x_25 = 0;
x_26 = l_Lake_withRegisterJob___rarg(x_19, x_24, x_25, x_2, x_3, x_4, x_5, x_6, x_7);
return x_26;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___elambda__2), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Package_gitHubReleaseFacetConfig___closed__1;
x_2 = 1;
x_3 = l_Lake_Package_gitHubReleaseFacetConfig___closed__2;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_gitHubReleaseFacetConfig___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Package_gitHubReleaseFacetConfig___elambda__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
static lean_object* _init_l_Lake_Package_releaseFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_gitHubReleaseFacetConfig;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___rarg___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 1);
lean_dec(x_10);
x_11 = l_Lake_BuildTrace_nil;
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
x_15 = l_Lake_BuildTrace_nil;
x_16 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_14);
x_17 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_16, x_8);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_10, 2);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_name_eq(x_12, x_14);
lean_dec(x_14);
lean_dec(x_12);
x_16 = l_instDecidableNot___rarg(x_15);
if (x_16 == 0)
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_17 = 0;
x_18 = l_Lake_BuildTrace_nil;
x_19 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_17);
x_20 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_19, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
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
x_25 = lean_ctor_get(x_21, 1);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
lean_ctor_set(x_21, 1, x_26);
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
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
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
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
}
else
{
uint8_t x_38; 
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
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
lean_ctor_set(x_21, 1, x_42);
return x_20;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_21, 0);
x_44 = lean_ctor_get(x_21, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_21);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_20, 0, x_46);
return x_20;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_20, 1);
lean_inc(x_47);
lean_dec(x_20);
x_48 = lean_ctor_get(x_21, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_21, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_50 = x_21;
} else {
 lean_dec_ref(x_21);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_47);
return x_53;
}
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_20);
if (x_54 == 0)
{
return x_20;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_20, 0);
x_56 = lean_ctor_get(x_20, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_20);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_58 = l_Lake_Package_maybeFetchBuildCache(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = !lean_is_exclusive(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_59, 0);
x_63 = lean_ctor_get(x_59, 1);
x_64 = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheAsync___rarg___lambda__1___boxed), 8, 1);
lean_closure_set(x_64, 0, x_2);
x_65 = l_Task_Priority_default;
x_66 = 0;
x_67 = l_Lake_BuildTrace_nil;
x_68 = l_Lake_Job_bindM___rarg(x_62, x_64, x_65, x_66, x_3, x_4, x_5, x_6, x_67, x_60);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_68, 0);
lean_ctor_set(x_59, 0, x_70);
lean_ctor_set(x_68, 0, x_59);
return x_68;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_68, 0);
x_72 = lean_ctor_get(x_68, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_68);
lean_ctor_set(x_59, 0, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_59);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
else
{
uint8_t x_74; 
lean_free_object(x_59);
lean_dec(x_63);
x_74 = !lean_is_exclusive(x_68);
if (x_74 == 0)
{
return x_68;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_68, 0);
x_76 = lean_ctor_get(x_68, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_68);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; 
x_78 = lean_ctor_get(x_59, 0);
x_79 = lean_ctor_get(x_59, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_59);
x_80 = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheAsync___rarg___lambda__1___boxed), 8, 1);
lean_closure_set(x_80, 0, x_2);
x_81 = l_Task_Priority_default;
x_82 = 0;
x_83 = l_Lake_BuildTrace_nil;
x_84 = l_Lake_Job_bindM___rarg(x_78, x_80, x_81, x_82, x_3, x_4, x_5, x_6, x_83, x_60);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_87 = x_84;
} else {
 lean_dec_ref(x_84);
 x_87 = lean_box(0);
}
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_79);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_79);
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_92 = x_84;
} else {
 lean_dec_ref(x_84);
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
uint8_t x_94; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_94 = !lean_is_exclusive(x_58);
if (x_94 == 0)
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_ctor_get(x_58, 0);
lean_dec(x_95);
x_96 = !lean_is_exclusive(x_59);
if (x_96 == 0)
{
return x_58;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_59, 0);
x_98 = lean_ctor_get(x_59, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_59);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set(x_58, 0, x_99);
return x_58;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_100 = lean_ctor_get(x_58, 1);
lean_inc(x_100);
lean_dec(x_58);
x_101 = lean_ctor_get(x_59, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_59, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_103 = x_59;
} else {
 lean_dec_ref(x_59);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_100);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_106 = !lean_is_exclusive(x_58);
if (x_106 == 0)
{
return x_58;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_58, 0);
x_108 = lean_ctor_get(x_58, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_58);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheAsync___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lake_Package_afterBuildCacheAsync___rarg___lambda__1(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseAsync___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Package_afterBuildCacheAsync___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseAsync(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Package_afterReleaseAsync___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterBuildCacheSync___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_31; 
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
x_34 = lean_get_set_stdout(x_1, x_8);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
x_47 = lean_get_set_stdout(x_35, x_40);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_38, 0, x_50);
x_9 = x_38;
x_10 = x_48;
goto block_30;
}
else
{
uint8_t x_51; 
lean_free_object(x_39);
lean_dec(x_46);
lean_dec(x_45);
lean_free_object(x_38);
lean_dec(x_42);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_47, 0);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_47);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_39, 0);
x_56 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_inc(x_55);
lean_dec(x_39);
x_58 = lean_get_set_stdout(x_35, x_40);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_56);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_42);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_38, 1, x_60);
lean_ctor_set(x_38, 0, x_62);
x_9 = x_38;
x_10 = x_59;
goto block_30;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_57);
lean_dec(x_55);
lean_free_object(x_38);
lean_dec(x_42);
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_65 = x_58;
} else {
 lean_dec_ref(x_58);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_38, 0);
lean_inc(x_67);
lean_dec(x_38);
x_68 = lean_ctor_get(x_39, 0);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_70 = lean_ctor_get(x_39, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_71 = x_39;
} else {
 lean_dec_ref(x_39);
 x_71 = lean_box(0);
}
x_72 = lean_get_set_stdout(x_35, x_40);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 2, 1);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_70);
lean_ctor_set_uint8(x_74, sizeof(void*)*2, x_69);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_67);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
x_9 = x_77;
x_10 = x_73;
goto block_30;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_67);
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_80 = x_72;
} else {
 lean_dec_ref(x_72);
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
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_38, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_37, 1);
lean_inc(x_83);
lean_dec(x_37);
x_84 = !lean_is_exclusive(x_38);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_38, 0);
x_86 = lean_ctor_get(x_38, 1);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_82);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_82, 0);
x_89 = lean_ctor_get(x_82, 1);
x_90 = lean_get_set_stdout(x_35, x_83);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_9 = x_38;
x_10 = x_91;
goto block_30;
}
else
{
uint8_t x_92; 
lean_free_object(x_82);
lean_dec(x_89);
lean_dec(x_88);
lean_free_object(x_38);
lean_dec(x_85);
x_92 = !lean_is_exclusive(x_90);
if (x_92 == 0)
{
return x_90;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_90, 0);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_90);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_82, 0);
x_97 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_98 = lean_ctor_get(x_82, 1);
lean_inc(x_98);
lean_inc(x_96);
lean_dec(x_82);
x_99 = lean_get_set_stdout(x_35, x_83);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_101, 0, x_96);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set_uint8(x_101, sizeof(void*)*2, x_97);
lean_ctor_set(x_38, 1, x_101);
x_9 = x_38;
x_10 = x_100;
goto block_30;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_98);
lean_dec(x_96);
lean_free_object(x_38);
lean_dec(x_85);
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_104 = x_99;
} else {
 lean_dec_ref(x_99);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_38, 0);
lean_inc(x_106);
lean_dec(x_38);
x_107 = lean_ctor_get(x_82, 0);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_109 = lean_ctor_get(x_82, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_110 = x_82;
} else {
 lean_dec_ref(x_82);
 x_110 = lean_box(0);
}
x_111 = lean_get_set_stdout(x_35, x_83);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
if (lean_is_scalar(x_110)) {
 x_113 = lean_alloc_ctor(0, 2, 1);
} else {
 x_113 = x_110;
}
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_109);
lean_ctor_set_uint8(x_113, sizeof(void*)*2, x_108);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_106);
lean_ctor_set(x_114, 1, x_113);
x_9 = x_114;
x_10 = x_112;
goto block_30;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_106);
x_115 = lean_ctor_get(x_111, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_117 = x_111;
} else {
 lean_dec_ref(x_111);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_35);
x_119 = !lean_is_exclusive(x_37);
if (x_119 == 0)
{
return x_37;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_37, 0);
x_121 = lean_ctor_get(x_37, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_37);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_free_object(x_7);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_34);
if (x_123 == 0)
{
return x_34;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_34, 0);
x_125 = lean_ctor_get(x_34, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_34);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_7, 0);
x_128 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_129 = lean_ctor_get(x_7, 1);
lean_inc(x_129);
lean_inc(x_127);
lean_dec(x_7);
x_130 = lean_get_set_stdout(x_1, x_8);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_133, 0, x_127);
lean_ctor_set(x_133, 1, x_129);
lean_ctor_set_uint8(x_133, sizeof(void*)*2, x_128);
x_134 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_133, x_132);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_139 = x_135;
} else {
 lean_dec_ref(x_135);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_136, 0);
lean_inc(x_140);
x_141 = lean_ctor_get_uint8(x_136, sizeof(void*)*2);
x_142 = lean_ctor_get(x_136, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_143 = x_136;
} else {
 lean_dec_ref(x_136);
 x_143 = lean_box(0);
}
x_144 = lean_get_set_stdout(x_131, x_137);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
if (lean_is_scalar(x_143)) {
 x_146 = lean_alloc_ctor(0, 2, 1);
} else {
 x_146 = x_143;
}
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_142);
lean_ctor_set_uint8(x_146, sizeof(void*)*2, x_141);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_138);
lean_ctor_set(x_148, 1, x_147);
if (lean_is_scalar(x_139)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_139;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_146);
x_9 = x_149;
x_10 = x_145;
goto block_30;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
x_150 = lean_ctor_get(x_144, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_144, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_152 = x_144;
} else {
 lean_dec_ref(x_144);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_154 = lean_ctor_get(x_135, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_134, 1);
lean_inc(x_155);
lean_dec(x_134);
x_156 = lean_ctor_get(x_135, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_157 = x_135;
} else {
 lean_dec_ref(x_135);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_154, 0);
lean_inc(x_158);
x_159 = lean_ctor_get_uint8(x_154, sizeof(void*)*2);
x_160 = lean_ctor_get(x_154, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_161 = x_154;
} else {
 lean_dec_ref(x_154);
 x_161 = lean_box(0);
}
x_162 = lean_get_set_stdout(x_131, x_155);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 2, 1);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_158);
lean_ctor_set(x_164, 1, x_160);
lean_ctor_set_uint8(x_164, sizeof(void*)*2, x_159);
if (lean_is_scalar(x_157)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_157;
}
lean_ctor_set(x_165, 0, x_156);
lean_ctor_set(x_165, 1, x_164);
x_9 = x_165;
x_10 = x_163;
goto block_30;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
x_166 = lean_ctor_get(x_162, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_162, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_168 = x_162;
} else {
 lean_dec_ref(x_162);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_131);
x_170 = lean_ctor_get(x_134, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_134, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_172 = x_134;
} else {
 lean_dec_ref(x_134);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_129);
lean_dec(x_127);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_174 = lean_ctor_get(x_130, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_130, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_176 = x_130;
} else {
 lean_dec_ref(x_130);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
block_30:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_14);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterBuildCacheSync___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_afterBuildCacheSync___spec__2___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterBuildCacheSync___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_31; 
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
x_34 = lean_get_set_stdin(x_1, x_8);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
x_47 = lean_get_set_stdin(x_35, x_40);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_38, 0, x_50);
x_9 = x_38;
x_10 = x_48;
goto block_30;
}
else
{
uint8_t x_51; 
lean_free_object(x_39);
lean_dec(x_46);
lean_dec(x_45);
lean_free_object(x_38);
lean_dec(x_42);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_47, 0);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_47);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_39, 0);
x_56 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_inc(x_55);
lean_dec(x_39);
x_58 = lean_get_set_stdin(x_35, x_40);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_56);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_42);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_38, 1, x_60);
lean_ctor_set(x_38, 0, x_62);
x_9 = x_38;
x_10 = x_59;
goto block_30;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_57);
lean_dec(x_55);
lean_free_object(x_38);
lean_dec(x_42);
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_65 = x_58;
} else {
 lean_dec_ref(x_58);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_38, 0);
lean_inc(x_67);
lean_dec(x_38);
x_68 = lean_ctor_get(x_39, 0);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_70 = lean_ctor_get(x_39, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_71 = x_39;
} else {
 lean_dec_ref(x_39);
 x_71 = lean_box(0);
}
x_72 = lean_get_set_stdin(x_35, x_40);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 2, 1);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_70);
lean_ctor_set_uint8(x_74, sizeof(void*)*2, x_69);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_67);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
x_9 = x_77;
x_10 = x_73;
goto block_30;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_67);
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_80 = x_72;
} else {
 lean_dec_ref(x_72);
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
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_38, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_37, 1);
lean_inc(x_83);
lean_dec(x_37);
x_84 = !lean_is_exclusive(x_38);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_38, 0);
x_86 = lean_ctor_get(x_38, 1);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_82);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_82, 0);
x_89 = lean_ctor_get(x_82, 1);
x_90 = lean_get_set_stdin(x_35, x_83);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_9 = x_38;
x_10 = x_91;
goto block_30;
}
else
{
uint8_t x_92; 
lean_free_object(x_82);
lean_dec(x_89);
lean_dec(x_88);
lean_free_object(x_38);
lean_dec(x_85);
x_92 = !lean_is_exclusive(x_90);
if (x_92 == 0)
{
return x_90;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_90, 0);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_90);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_82, 0);
x_97 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_98 = lean_ctor_get(x_82, 1);
lean_inc(x_98);
lean_inc(x_96);
lean_dec(x_82);
x_99 = lean_get_set_stdin(x_35, x_83);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_101, 0, x_96);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set_uint8(x_101, sizeof(void*)*2, x_97);
lean_ctor_set(x_38, 1, x_101);
x_9 = x_38;
x_10 = x_100;
goto block_30;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_98);
lean_dec(x_96);
lean_free_object(x_38);
lean_dec(x_85);
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_104 = x_99;
} else {
 lean_dec_ref(x_99);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_38, 0);
lean_inc(x_106);
lean_dec(x_38);
x_107 = lean_ctor_get(x_82, 0);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_109 = lean_ctor_get(x_82, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_110 = x_82;
} else {
 lean_dec_ref(x_82);
 x_110 = lean_box(0);
}
x_111 = lean_get_set_stdin(x_35, x_83);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
if (lean_is_scalar(x_110)) {
 x_113 = lean_alloc_ctor(0, 2, 1);
} else {
 x_113 = x_110;
}
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_109);
lean_ctor_set_uint8(x_113, sizeof(void*)*2, x_108);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_106);
lean_ctor_set(x_114, 1, x_113);
x_9 = x_114;
x_10 = x_112;
goto block_30;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_106);
x_115 = lean_ctor_get(x_111, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_117 = x_111;
} else {
 lean_dec_ref(x_111);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_35);
x_119 = !lean_is_exclusive(x_37);
if (x_119 == 0)
{
return x_37;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_37, 0);
x_121 = lean_ctor_get(x_37, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_37);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_free_object(x_7);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_34);
if (x_123 == 0)
{
return x_34;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_34, 0);
x_125 = lean_ctor_get(x_34, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_34);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_7, 0);
x_128 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_129 = lean_ctor_get(x_7, 1);
lean_inc(x_129);
lean_inc(x_127);
lean_dec(x_7);
x_130 = lean_get_set_stdin(x_1, x_8);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_133, 0, x_127);
lean_ctor_set(x_133, 1, x_129);
lean_ctor_set_uint8(x_133, sizeof(void*)*2, x_128);
x_134 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_133, x_132);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_139 = x_135;
} else {
 lean_dec_ref(x_135);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_136, 0);
lean_inc(x_140);
x_141 = lean_ctor_get_uint8(x_136, sizeof(void*)*2);
x_142 = lean_ctor_get(x_136, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_143 = x_136;
} else {
 lean_dec_ref(x_136);
 x_143 = lean_box(0);
}
x_144 = lean_get_set_stdin(x_131, x_137);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
if (lean_is_scalar(x_143)) {
 x_146 = lean_alloc_ctor(0, 2, 1);
} else {
 x_146 = x_143;
}
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_142);
lean_ctor_set_uint8(x_146, sizeof(void*)*2, x_141);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_138);
lean_ctor_set(x_148, 1, x_147);
if (lean_is_scalar(x_139)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_139;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_146);
x_9 = x_149;
x_10 = x_145;
goto block_30;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
x_150 = lean_ctor_get(x_144, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_144, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_152 = x_144;
} else {
 lean_dec_ref(x_144);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_154 = lean_ctor_get(x_135, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_134, 1);
lean_inc(x_155);
lean_dec(x_134);
x_156 = lean_ctor_get(x_135, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_157 = x_135;
} else {
 lean_dec_ref(x_135);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_154, 0);
lean_inc(x_158);
x_159 = lean_ctor_get_uint8(x_154, sizeof(void*)*2);
x_160 = lean_ctor_get(x_154, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_161 = x_154;
} else {
 lean_dec_ref(x_154);
 x_161 = lean_box(0);
}
x_162 = lean_get_set_stdin(x_131, x_155);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 2, 1);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_158);
lean_ctor_set(x_164, 1, x_160);
lean_ctor_set_uint8(x_164, sizeof(void*)*2, x_159);
if (lean_is_scalar(x_157)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_157;
}
lean_ctor_set(x_165, 0, x_156);
lean_ctor_set(x_165, 1, x_164);
x_9 = x_165;
x_10 = x_163;
goto block_30;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
x_166 = lean_ctor_get(x_162, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_162, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_168 = x_162;
} else {
 lean_dec_ref(x_162);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_131);
x_170 = lean_ctor_get(x_134, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_134, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_172 = x_134;
} else {
 lean_dec_ref(x_134);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_129);
lean_dec(x_127);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_174 = lean_ctor_get(x_130, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_130, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_176 = x_130;
} else {
 lean_dec_ref(x_130);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
block_30:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_14);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterBuildCacheSync___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdin___at_Lake_Package_afterBuildCacheSync___spec__3___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Package_afterBuildCacheSync___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_31; 
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
x_34 = lean_get_set_stderr(x_1, x_8);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
x_47 = lean_get_set_stderr(x_35, x_40);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_38, 0, x_50);
x_9 = x_38;
x_10 = x_48;
goto block_30;
}
else
{
uint8_t x_51; 
lean_free_object(x_39);
lean_dec(x_46);
lean_dec(x_45);
lean_free_object(x_38);
lean_dec(x_42);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_47, 0);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_47);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_39, 0);
x_56 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_inc(x_55);
lean_dec(x_39);
x_58 = lean_get_set_stderr(x_35, x_40);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_56);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_42);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_38, 1, x_60);
lean_ctor_set(x_38, 0, x_62);
x_9 = x_38;
x_10 = x_59;
goto block_30;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_57);
lean_dec(x_55);
lean_free_object(x_38);
lean_dec(x_42);
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_65 = x_58;
} else {
 lean_dec_ref(x_58);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_38, 0);
lean_inc(x_67);
lean_dec(x_38);
x_68 = lean_ctor_get(x_39, 0);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_70 = lean_ctor_get(x_39, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_71 = x_39;
} else {
 lean_dec_ref(x_39);
 x_71 = lean_box(0);
}
x_72 = lean_get_set_stderr(x_35, x_40);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 2, 1);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_70);
lean_ctor_set_uint8(x_74, sizeof(void*)*2, x_69);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_67);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
x_9 = x_77;
x_10 = x_73;
goto block_30;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_67);
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_80 = x_72;
} else {
 lean_dec_ref(x_72);
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
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_38, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_37, 1);
lean_inc(x_83);
lean_dec(x_37);
x_84 = !lean_is_exclusive(x_38);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_38, 0);
x_86 = lean_ctor_get(x_38, 1);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_82);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_82, 0);
x_89 = lean_ctor_get(x_82, 1);
x_90 = lean_get_set_stderr(x_35, x_83);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_9 = x_38;
x_10 = x_91;
goto block_30;
}
else
{
uint8_t x_92; 
lean_free_object(x_82);
lean_dec(x_89);
lean_dec(x_88);
lean_free_object(x_38);
lean_dec(x_85);
x_92 = !lean_is_exclusive(x_90);
if (x_92 == 0)
{
return x_90;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_90, 0);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_90);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_82, 0);
x_97 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_98 = lean_ctor_get(x_82, 1);
lean_inc(x_98);
lean_inc(x_96);
lean_dec(x_82);
x_99 = lean_get_set_stderr(x_35, x_83);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_101, 0, x_96);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set_uint8(x_101, sizeof(void*)*2, x_97);
lean_ctor_set(x_38, 1, x_101);
x_9 = x_38;
x_10 = x_100;
goto block_30;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_98);
lean_dec(x_96);
lean_free_object(x_38);
lean_dec(x_85);
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_104 = x_99;
} else {
 lean_dec_ref(x_99);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_38, 0);
lean_inc(x_106);
lean_dec(x_38);
x_107 = lean_ctor_get(x_82, 0);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_109 = lean_ctor_get(x_82, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_110 = x_82;
} else {
 lean_dec_ref(x_82);
 x_110 = lean_box(0);
}
x_111 = lean_get_set_stderr(x_35, x_83);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
if (lean_is_scalar(x_110)) {
 x_113 = lean_alloc_ctor(0, 2, 1);
} else {
 x_113 = x_110;
}
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_109);
lean_ctor_set_uint8(x_113, sizeof(void*)*2, x_108);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_106);
lean_ctor_set(x_114, 1, x_113);
x_9 = x_114;
x_10 = x_112;
goto block_30;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_106);
x_115 = lean_ctor_get(x_111, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_117 = x_111;
} else {
 lean_dec_ref(x_111);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_35);
x_119 = !lean_is_exclusive(x_37);
if (x_119 == 0)
{
return x_37;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_37, 0);
x_121 = lean_ctor_get(x_37, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_37);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_free_object(x_7);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_34);
if (x_123 == 0)
{
return x_34;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_34, 0);
x_125 = lean_ctor_get(x_34, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_34);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_7, 0);
x_128 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_129 = lean_ctor_get(x_7, 1);
lean_inc(x_129);
lean_inc(x_127);
lean_dec(x_7);
x_130 = lean_get_set_stderr(x_1, x_8);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_133, 0, x_127);
lean_ctor_set(x_133, 1, x_129);
lean_ctor_set_uint8(x_133, sizeof(void*)*2, x_128);
x_134 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_133, x_132);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_139 = x_135;
} else {
 lean_dec_ref(x_135);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_136, 0);
lean_inc(x_140);
x_141 = lean_ctor_get_uint8(x_136, sizeof(void*)*2);
x_142 = lean_ctor_get(x_136, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_143 = x_136;
} else {
 lean_dec_ref(x_136);
 x_143 = lean_box(0);
}
x_144 = lean_get_set_stderr(x_131, x_137);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
if (lean_is_scalar(x_143)) {
 x_146 = lean_alloc_ctor(0, 2, 1);
} else {
 x_146 = x_143;
}
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_142);
lean_ctor_set_uint8(x_146, sizeof(void*)*2, x_141);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_138);
lean_ctor_set(x_148, 1, x_147);
if (lean_is_scalar(x_139)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_139;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_146);
x_9 = x_149;
x_10 = x_145;
goto block_30;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
x_150 = lean_ctor_get(x_144, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_144, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_152 = x_144;
} else {
 lean_dec_ref(x_144);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_154 = lean_ctor_get(x_135, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_134, 1);
lean_inc(x_155);
lean_dec(x_134);
x_156 = lean_ctor_get(x_135, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_157 = x_135;
} else {
 lean_dec_ref(x_135);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_154, 0);
lean_inc(x_158);
x_159 = lean_ctor_get_uint8(x_154, sizeof(void*)*2);
x_160 = lean_ctor_get(x_154, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_161 = x_154;
} else {
 lean_dec_ref(x_154);
 x_161 = lean_box(0);
}
x_162 = lean_get_set_stderr(x_131, x_155);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 2, 1);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_158);
lean_ctor_set(x_164, 1, x_160);
lean_ctor_set_uint8(x_164, sizeof(void*)*2, x_159);
if (lean_is_scalar(x_157)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_157;
}
lean_ctor_set(x_165, 0, x_156);
lean_ctor_set(x_165, 1, x_164);
x_9 = x_165;
x_10 = x_163;
goto block_30;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
x_166 = lean_ctor_get(x_162, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_162, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_168 = x_162;
} else {
 lean_dec_ref(x_162);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_131);
x_170 = lean_ctor_get(x_134, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_134, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_172 = x_134;
} else {
 lean_dec_ref(x_134);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_129);
lean_dec(x_127);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_174 = lean_ctor_get(x_130, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_130, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_176 = x_130;
} else {
 lean_dec_ref(x_130);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
block_30:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_14);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Package_afterBuildCacheSync___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_Package_afterBuildCacheSync___spec__4___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterBuildCacheSync___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_31; 
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
x_34 = lean_get_set_stdout(x_1, x_8);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
x_47 = lean_get_set_stdout(x_35, x_40);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_38, 0, x_50);
x_9 = x_38;
x_10 = x_48;
goto block_30;
}
else
{
uint8_t x_51; 
lean_free_object(x_39);
lean_dec(x_46);
lean_dec(x_45);
lean_free_object(x_38);
lean_dec(x_42);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_47, 0);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_47);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_39, 0);
x_56 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_inc(x_55);
lean_dec(x_39);
x_58 = lean_get_set_stdout(x_35, x_40);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_56);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_42);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_38, 1, x_60);
lean_ctor_set(x_38, 0, x_62);
x_9 = x_38;
x_10 = x_59;
goto block_30;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_57);
lean_dec(x_55);
lean_free_object(x_38);
lean_dec(x_42);
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_65 = x_58;
} else {
 lean_dec_ref(x_58);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_38, 0);
lean_inc(x_67);
lean_dec(x_38);
x_68 = lean_ctor_get(x_39, 0);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_70 = lean_ctor_get(x_39, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_71 = x_39;
} else {
 lean_dec_ref(x_39);
 x_71 = lean_box(0);
}
x_72 = lean_get_set_stdout(x_35, x_40);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 2, 1);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_70);
lean_ctor_set_uint8(x_74, sizeof(void*)*2, x_69);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_67);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
x_9 = x_77;
x_10 = x_73;
goto block_30;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_67);
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_80 = x_72;
} else {
 lean_dec_ref(x_72);
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
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_38, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_37, 1);
lean_inc(x_83);
lean_dec(x_37);
x_84 = !lean_is_exclusive(x_38);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_38, 0);
x_86 = lean_ctor_get(x_38, 1);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_82);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_82, 0);
x_89 = lean_ctor_get(x_82, 1);
x_90 = lean_get_set_stdout(x_35, x_83);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_9 = x_38;
x_10 = x_91;
goto block_30;
}
else
{
uint8_t x_92; 
lean_free_object(x_82);
lean_dec(x_89);
lean_dec(x_88);
lean_free_object(x_38);
lean_dec(x_85);
x_92 = !lean_is_exclusive(x_90);
if (x_92 == 0)
{
return x_90;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_90, 0);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_90);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_82, 0);
x_97 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_98 = lean_ctor_get(x_82, 1);
lean_inc(x_98);
lean_inc(x_96);
lean_dec(x_82);
x_99 = lean_get_set_stdout(x_35, x_83);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_101, 0, x_96);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set_uint8(x_101, sizeof(void*)*2, x_97);
lean_ctor_set(x_38, 1, x_101);
x_9 = x_38;
x_10 = x_100;
goto block_30;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_98);
lean_dec(x_96);
lean_free_object(x_38);
lean_dec(x_85);
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_104 = x_99;
} else {
 lean_dec_ref(x_99);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_38, 0);
lean_inc(x_106);
lean_dec(x_38);
x_107 = lean_ctor_get(x_82, 0);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_109 = lean_ctor_get(x_82, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_110 = x_82;
} else {
 lean_dec_ref(x_82);
 x_110 = lean_box(0);
}
x_111 = lean_get_set_stdout(x_35, x_83);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
if (lean_is_scalar(x_110)) {
 x_113 = lean_alloc_ctor(0, 2, 1);
} else {
 x_113 = x_110;
}
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_109);
lean_ctor_set_uint8(x_113, sizeof(void*)*2, x_108);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_106);
lean_ctor_set(x_114, 1, x_113);
x_9 = x_114;
x_10 = x_112;
goto block_30;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_106);
x_115 = lean_ctor_get(x_111, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_117 = x_111;
} else {
 lean_dec_ref(x_111);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_35);
x_119 = !lean_is_exclusive(x_37);
if (x_119 == 0)
{
return x_37;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_37, 0);
x_121 = lean_ctor_get(x_37, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_37);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_free_object(x_7);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_34);
if (x_123 == 0)
{
return x_34;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_34, 0);
x_125 = lean_ctor_get(x_34, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_34);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_7, 0);
x_128 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_129 = lean_ctor_get(x_7, 1);
lean_inc(x_129);
lean_inc(x_127);
lean_dec(x_7);
x_130 = lean_get_set_stdout(x_1, x_8);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_133, 0, x_127);
lean_ctor_set(x_133, 1, x_129);
lean_ctor_set_uint8(x_133, sizeof(void*)*2, x_128);
x_134 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_133, x_132);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_139 = x_135;
} else {
 lean_dec_ref(x_135);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_136, 0);
lean_inc(x_140);
x_141 = lean_ctor_get_uint8(x_136, sizeof(void*)*2);
x_142 = lean_ctor_get(x_136, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_143 = x_136;
} else {
 lean_dec_ref(x_136);
 x_143 = lean_box(0);
}
x_144 = lean_get_set_stdout(x_131, x_137);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
if (lean_is_scalar(x_143)) {
 x_146 = lean_alloc_ctor(0, 2, 1);
} else {
 x_146 = x_143;
}
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_142);
lean_ctor_set_uint8(x_146, sizeof(void*)*2, x_141);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_138);
lean_ctor_set(x_148, 1, x_147);
if (lean_is_scalar(x_139)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_139;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_146);
x_9 = x_149;
x_10 = x_145;
goto block_30;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
x_150 = lean_ctor_get(x_144, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_144, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_152 = x_144;
} else {
 lean_dec_ref(x_144);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_154 = lean_ctor_get(x_135, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_134, 1);
lean_inc(x_155);
lean_dec(x_134);
x_156 = lean_ctor_get(x_135, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_157 = x_135;
} else {
 lean_dec_ref(x_135);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_154, 0);
lean_inc(x_158);
x_159 = lean_ctor_get_uint8(x_154, sizeof(void*)*2);
x_160 = lean_ctor_get(x_154, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_161 = x_154;
} else {
 lean_dec_ref(x_154);
 x_161 = lean_box(0);
}
x_162 = lean_get_set_stdout(x_131, x_155);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 2, 1);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_158);
lean_ctor_set(x_164, 1, x_160);
lean_ctor_set_uint8(x_164, sizeof(void*)*2, x_159);
if (lean_is_scalar(x_157)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_157;
}
lean_ctor_set(x_165, 0, x_156);
lean_ctor_set(x_165, 1, x_164);
x_9 = x_165;
x_10 = x_163;
goto block_30;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
x_166 = lean_ctor_get(x_162, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_162, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_168 = x_162;
} else {
 lean_dec_ref(x_162);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_131);
x_170 = lean_ctor_get(x_134, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_134, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_172 = x_134;
} else {
 lean_dec_ref(x_134);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_129);
lean_dec(x_127);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_174 = lean_ctor_get(x_130, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_130, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_176 = x_130;
} else {
 lean_dec_ref(x_130);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
block_30:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_14);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterBuildCacheSync___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_afterBuildCacheSync___spec__5___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterBuildCacheSync___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_31; 
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
x_34 = lean_get_set_stdin(x_1, x_8);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
x_47 = lean_get_set_stdin(x_35, x_40);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_38, 0, x_50);
x_9 = x_38;
x_10 = x_48;
goto block_30;
}
else
{
uint8_t x_51; 
lean_free_object(x_39);
lean_dec(x_46);
lean_dec(x_45);
lean_free_object(x_38);
lean_dec(x_42);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_47, 0);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_47);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_39, 0);
x_56 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_inc(x_55);
lean_dec(x_39);
x_58 = lean_get_set_stdin(x_35, x_40);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_56);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_42);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_38, 1, x_60);
lean_ctor_set(x_38, 0, x_62);
x_9 = x_38;
x_10 = x_59;
goto block_30;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_57);
lean_dec(x_55);
lean_free_object(x_38);
lean_dec(x_42);
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_65 = x_58;
} else {
 lean_dec_ref(x_58);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_38, 0);
lean_inc(x_67);
lean_dec(x_38);
x_68 = lean_ctor_get(x_39, 0);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_70 = lean_ctor_get(x_39, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_71 = x_39;
} else {
 lean_dec_ref(x_39);
 x_71 = lean_box(0);
}
x_72 = lean_get_set_stdin(x_35, x_40);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 2, 1);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_70);
lean_ctor_set_uint8(x_74, sizeof(void*)*2, x_69);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_67);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
x_9 = x_77;
x_10 = x_73;
goto block_30;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_67);
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_80 = x_72;
} else {
 lean_dec_ref(x_72);
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
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_38, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_37, 1);
lean_inc(x_83);
lean_dec(x_37);
x_84 = !lean_is_exclusive(x_38);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_38, 0);
x_86 = lean_ctor_get(x_38, 1);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_82);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_82, 0);
x_89 = lean_ctor_get(x_82, 1);
x_90 = lean_get_set_stdin(x_35, x_83);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_9 = x_38;
x_10 = x_91;
goto block_30;
}
else
{
uint8_t x_92; 
lean_free_object(x_82);
lean_dec(x_89);
lean_dec(x_88);
lean_free_object(x_38);
lean_dec(x_85);
x_92 = !lean_is_exclusive(x_90);
if (x_92 == 0)
{
return x_90;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_90, 0);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_90);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_82, 0);
x_97 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_98 = lean_ctor_get(x_82, 1);
lean_inc(x_98);
lean_inc(x_96);
lean_dec(x_82);
x_99 = lean_get_set_stdin(x_35, x_83);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_101, 0, x_96);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set_uint8(x_101, sizeof(void*)*2, x_97);
lean_ctor_set(x_38, 1, x_101);
x_9 = x_38;
x_10 = x_100;
goto block_30;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_98);
lean_dec(x_96);
lean_free_object(x_38);
lean_dec(x_85);
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_104 = x_99;
} else {
 lean_dec_ref(x_99);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_38, 0);
lean_inc(x_106);
lean_dec(x_38);
x_107 = lean_ctor_get(x_82, 0);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_109 = lean_ctor_get(x_82, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_110 = x_82;
} else {
 lean_dec_ref(x_82);
 x_110 = lean_box(0);
}
x_111 = lean_get_set_stdin(x_35, x_83);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
if (lean_is_scalar(x_110)) {
 x_113 = lean_alloc_ctor(0, 2, 1);
} else {
 x_113 = x_110;
}
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_109);
lean_ctor_set_uint8(x_113, sizeof(void*)*2, x_108);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_106);
lean_ctor_set(x_114, 1, x_113);
x_9 = x_114;
x_10 = x_112;
goto block_30;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_106);
x_115 = lean_ctor_get(x_111, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_117 = x_111;
} else {
 lean_dec_ref(x_111);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_35);
x_119 = !lean_is_exclusive(x_37);
if (x_119 == 0)
{
return x_37;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_37, 0);
x_121 = lean_ctor_get(x_37, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_37);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_free_object(x_7);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_34);
if (x_123 == 0)
{
return x_34;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_34, 0);
x_125 = lean_ctor_get(x_34, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_34);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_7, 0);
x_128 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_129 = lean_ctor_get(x_7, 1);
lean_inc(x_129);
lean_inc(x_127);
lean_dec(x_7);
x_130 = lean_get_set_stdin(x_1, x_8);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_133, 0, x_127);
lean_ctor_set(x_133, 1, x_129);
lean_ctor_set_uint8(x_133, sizeof(void*)*2, x_128);
x_134 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_133, x_132);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_139 = x_135;
} else {
 lean_dec_ref(x_135);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_136, 0);
lean_inc(x_140);
x_141 = lean_ctor_get_uint8(x_136, sizeof(void*)*2);
x_142 = lean_ctor_get(x_136, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_143 = x_136;
} else {
 lean_dec_ref(x_136);
 x_143 = lean_box(0);
}
x_144 = lean_get_set_stdin(x_131, x_137);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
if (lean_is_scalar(x_143)) {
 x_146 = lean_alloc_ctor(0, 2, 1);
} else {
 x_146 = x_143;
}
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_142);
lean_ctor_set_uint8(x_146, sizeof(void*)*2, x_141);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_138);
lean_ctor_set(x_148, 1, x_147);
if (lean_is_scalar(x_139)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_139;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_146);
x_9 = x_149;
x_10 = x_145;
goto block_30;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
x_150 = lean_ctor_get(x_144, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_144, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_152 = x_144;
} else {
 lean_dec_ref(x_144);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_154 = lean_ctor_get(x_135, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_134, 1);
lean_inc(x_155);
lean_dec(x_134);
x_156 = lean_ctor_get(x_135, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_157 = x_135;
} else {
 lean_dec_ref(x_135);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_154, 0);
lean_inc(x_158);
x_159 = lean_ctor_get_uint8(x_154, sizeof(void*)*2);
x_160 = lean_ctor_get(x_154, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_161 = x_154;
} else {
 lean_dec_ref(x_154);
 x_161 = lean_box(0);
}
x_162 = lean_get_set_stdin(x_131, x_155);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 2, 1);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_158);
lean_ctor_set(x_164, 1, x_160);
lean_ctor_set_uint8(x_164, sizeof(void*)*2, x_159);
if (lean_is_scalar(x_157)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_157;
}
lean_ctor_set(x_165, 0, x_156);
lean_ctor_set(x_165, 1, x_164);
x_9 = x_165;
x_10 = x_163;
goto block_30;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
x_166 = lean_ctor_get(x_162, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_162, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_168 = x_162;
} else {
 lean_dec_ref(x_162);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_131);
x_170 = lean_ctor_get(x_134, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_134, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_172 = x_134;
} else {
 lean_dec_ref(x_134);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_129);
lean_dec(x_127);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_174 = lean_ctor_get(x_130, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_130, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_176 = x_130;
} else {
 lean_dec_ref(x_130);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
block_30:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_14);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterBuildCacheSync___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdin___at_Lake_Package_afterBuildCacheSync___spec__6___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_afterBuildCacheSync___spec__1___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
x_12 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__1;
x_13 = lean_st_mk_ref(x_12, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_mk_ref(x_12, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_IO_FS_Stream_ofBuffer(x_14);
lean_inc(x_17);
x_20 = l_IO_FS_Stream_ofBuffer(x_17);
if (x_2 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_afterBuildCacheSync___spec__2___rarg), 8, 2);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, x_1);
x_22 = l_IO_withStdin___at_Lake_Package_afterBuildCacheSync___spec__3___rarg(x_19, x_21, x_3, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
x_32 = lean_st_ref_get(x_17, x_25);
lean_dec(x_17);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_string_validate_utf8(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_35);
x_37 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__5;
x_38 = l_panic___at_String_fromUTF8_x21___spec__1(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_27);
lean_ctor_set(x_23, 0, x_39);
lean_ctor_set(x_32, 0, x_23);
return x_32;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_string_from_utf8_unchecked(x_35);
lean_dec(x_35);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_27);
lean_ctor_set(x_23, 0, x_41);
lean_ctor_set(x_32, 0, x_23);
return x_32;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_ctor_get(x_32, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_32);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_string_validate_utf8(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_44);
x_46 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__5;
x_47 = l_panic___at_String_fromUTF8_x21___spec__1(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_27);
lean_ctor_set(x_23, 0, x_48);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_23);
lean_ctor_set(x_49, 1, x_43);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_string_from_utf8_unchecked(x_44);
lean_dec(x_44);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_27);
lean_ctor_set(x_23, 0, x_51);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_23);
lean_ctor_set(x_52, 1, x_43);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_free_object(x_24);
lean_dec(x_31);
lean_dec(x_30);
lean_free_object(x_23);
lean_dec(x_27);
x_53 = !lean_is_exclusive(x_32);
if (x_53 == 0)
{
return x_32;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_32, 0);
x_55 = lean_ctor_get(x_32, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_32);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_24, 0);
x_58 = lean_ctor_get_uint8(x_24, sizeof(void*)*2);
x_59 = lean_ctor_get(x_24, 1);
lean_inc(x_59);
lean_inc(x_57);
lean_dec(x_24);
x_60 = lean_st_ref_get(x_17, x_25);
lean_dec(x_17);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
x_64 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_59);
lean_ctor_set_uint8(x_64, sizeof(void*)*2, x_58);
x_65 = lean_ctor_get(x_61, 0);
lean_inc(x_65);
lean_dec(x_61);
x_66 = lean_string_validate_utf8(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_65);
x_67 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__5;
x_68 = l_panic___at_String_fromUTF8_x21___spec__1(x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_27);
lean_ctor_set(x_23, 1, x_64);
lean_ctor_set(x_23, 0, x_69);
if (lean_is_scalar(x_63)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_63;
}
lean_ctor_set(x_70, 0, x_23);
lean_ctor_set(x_70, 1, x_62);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_string_from_utf8_unchecked(x_65);
lean_dec(x_65);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_27);
lean_ctor_set(x_23, 1, x_64);
lean_ctor_set(x_23, 0, x_72);
if (lean_is_scalar(x_63)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_63;
}
lean_ctor_set(x_73, 0, x_23);
lean_ctor_set(x_73, 1, x_62);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_59);
lean_dec(x_57);
lean_free_object(x_23);
lean_dec(x_27);
x_74 = lean_ctor_get(x_60, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_60, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_76 = x_60;
} else {
 lean_dec_ref(x_60);
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
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_23, 0);
lean_inc(x_78);
lean_dec(x_23);
x_79 = lean_ctor_get(x_24, 0);
lean_inc(x_79);
x_80 = lean_ctor_get_uint8(x_24, sizeof(void*)*2);
x_81 = lean_ctor_get(x_24, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_82 = x_24;
} else {
 lean_dec_ref(x_24);
 x_82 = lean_box(0);
}
x_83 = lean_st_ref_get(x_17, x_25);
lean_dec(x_17);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_87 = lean_alloc_ctor(0, 2, 1);
} else {
 x_87 = x_82;
}
lean_ctor_set(x_87, 0, x_79);
lean_ctor_set(x_87, 1, x_81);
lean_ctor_set_uint8(x_87, sizeof(void*)*2, x_80);
x_88 = lean_ctor_get(x_84, 0);
lean_inc(x_88);
lean_dec(x_84);
x_89 = lean_string_validate_utf8(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_88);
x_90 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__5;
x_91 = l_panic___at_String_fromUTF8_x21___spec__1(x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_78);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_87);
if (lean_is_scalar(x_86)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_86;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_85);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_string_from_utf8_unchecked(x_88);
lean_dec(x_88);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_78);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_87);
if (lean_is_scalar(x_86)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_86;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_85);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_78);
x_99 = lean_ctor_get(x_83, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_83, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_101 = x_83;
} else {
 lean_dec_ref(x_83);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_17);
x_103 = !lean_is_exclusive(x_22);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_22, 0);
lean_dec(x_104);
x_105 = !lean_is_exclusive(x_23);
if (x_105 == 0)
{
return x_22;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_23, 0);
x_107 = lean_ctor_get(x_23, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_23);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set(x_22, 0, x_108);
return x_22;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_109 = lean_ctor_get(x_22, 1);
lean_inc(x_109);
lean_dec(x_22);
x_110 = lean_ctor_get(x_23, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_23, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_112 = x_23;
} else {
 lean_dec_ref(x_23);
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
}
else
{
uint8_t x_115; 
lean_dec(x_17);
x_115 = !lean_is_exclusive(x_22);
if (x_115 == 0)
{
return x_22;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_22, 0);
x_117 = lean_ctor_get(x_22, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_22);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_inc(x_20);
x_119 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_Package_afterBuildCacheSync___spec__4___rarg), 8, 2);
lean_closure_set(x_119, 0, x_20);
lean_closure_set(x_119, 1, x_1);
x_120 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_afterBuildCacheSync___spec__5___rarg), 8, 2);
lean_closure_set(x_120, 0, x_20);
lean_closure_set(x_120, 1, x_119);
x_121 = l_IO_withStdin___at_Lake_Package_afterBuildCacheSync___spec__6___rarg(x_19, x_120, x_3, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_dec(x_121);
x_125 = !lean_is_exclusive(x_122);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_126 = lean_ctor_get(x_122, 0);
x_127 = lean_ctor_get(x_122, 1);
lean_dec(x_127);
x_128 = !lean_is_exclusive(x_123);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_123, 0);
x_130 = lean_ctor_get(x_123, 1);
x_131 = lean_st_ref_get(x_17, x_124);
lean_dec(x_17);
if (lean_obj_tag(x_131) == 0)
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_ctor_get(x_131, 0);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
lean_dec(x_133);
x_135 = lean_string_validate_utf8(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_134);
x_136 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__5;
x_137 = l_panic___at_String_fromUTF8_x21___spec__1(x_136);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_126);
lean_ctor_set(x_122, 0, x_138);
lean_ctor_set(x_131, 0, x_122);
return x_131;
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_string_from_utf8_unchecked(x_134);
lean_dec(x_134);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_126);
lean_ctor_set(x_122, 0, x_140);
lean_ctor_set(x_131, 0, x_122);
return x_131;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_141 = lean_ctor_get(x_131, 0);
x_142 = lean_ctor_get(x_131, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_131);
x_143 = lean_ctor_get(x_141, 0);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_string_validate_utf8(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_143);
x_145 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__5;
x_146 = l_panic___at_String_fromUTF8_x21___spec__1(x_145);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_126);
lean_ctor_set(x_122, 0, x_147);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_122);
lean_ctor_set(x_148, 1, x_142);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_string_from_utf8_unchecked(x_143);
lean_dec(x_143);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_126);
lean_ctor_set(x_122, 0, x_150);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_122);
lean_ctor_set(x_151, 1, x_142);
return x_151;
}
}
}
else
{
uint8_t x_152; 
lean_free_object(x_123);
lean_dec(x_130);
lean_dec(x_129);
lean_free_object(x_122);
lean_dec(x_126);
x_152 = !lean_is_exclusive(x_131);
if (x_152 == 0)
{
return x_131;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_131, 0);
x_154 = lean_ctor_get(x_131, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_131);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; 
x_156 = lean_ctor_get(x_123, 0);
x_157 = lean_ctor_get_uint8(x_123, sizeof(void*)*2);
x_158 = lean_ctor_get(x_123, 1);
lean_inc(x_158);
lean_inc(x_156);
lean_dec(x_123);
x_159 = lean_st_ref_get(x_17, x_124);
lean_dec(x_17);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_162 = x_159;
} else {
 lean_dec_ref(x_159);
 x_162 = lean_box(0);
}
x_163 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_163, 0, x_156);
lean_ctor_set(x_163, 1, x_158);
lean_ctor_set_uint8(x_163, sizeof(void*)*2, x_157);
x_164 = lean_ctor_get(x_160, 0);
lean_inc(x_164);
lean_dec(x_160);
x_165 = lean_string_validate_utf8(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_164);
x_166 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__5;
x_167 = l_panic___at_String_fromUTF8_x21___spec__1(x_166);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_126);
lean_ctor_set(x_122, 1, x_163);
lean_ctor_set(x_122, 0, x_168);
if (lean_is_scalar(x_162)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_162;
}
lean_ctor_set(x_169, 0, x_122);
lean_ctor_set(x_169, 1, x_161);
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_string_from_utf8_unchecked(x_164);
lean_dec(x_164);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_126);
lean_ctor_set(x_122, 1, x_163);
lean_ctor_set(x_122, 0, x_171);
if (lean_is_scalar(x_162)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_162;
}
lean_ctor_set(x_172, 0, x_122);
lean_ctor_set(x_172, 1, x_161);
return x_172;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_158);
lean_dec(x_156);
lean_free_object(x_122);
lean_dec(x_126);
x_173 = lean_ctor_get(x_159, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_159, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_175 = x_159;
} else {
 lean_dec_ref(x_159);
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
}
else
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_177 = lean_ctor_get(x_122, 0);
lean_inc(x_177);
lean_dec(x_122);
x_178 = lean_ctor_get(x_123, 0);
lean_inc(x_178);
x_179 = lean_ctor_get_uint8(x_123, sizeof(void*)*2);
x_180 = lean_ctor_get(x_123, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_181 = x_123;
} else {
 lean_dec_ref(x_123);
 x_181 = lean_box(0);
}
x_182 = lean_st_ref_get(x_17, x_124);
lean_dec(x_17);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_185 = x_182;
} else {
 lean_dec_ref(x_182);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_186 = lean_alloc_ctor(0, 2, 1);
} else {
 x_186 = x_181;
}
lean_ctor_set(x_186, 0, x_178);
lean_ctor_set(x_186, 1, x_180);
lean_ctor_set_uint8(x_186, sizeof(void*)*2, x_179);
x_187 = lean_ctor_get(x_183, 0);
lean_inc(x_187);
lean_dec(x_183);
x_188 = lean_string_validate_utf8(x_187);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_187);
x_189 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__5;
x_190 = l_panic___at_String_fromUTF8_x21___spec__1(x_189);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_177);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_186);
if (lean_is_scalar(x_185)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_185;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_184);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_194 = lean_string_from_utf8_unchecked(x_187);
lean_dec(x_187);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_177);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_186);
if (lean_is_scalar(x_185)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_185;
}
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_184);
return x_197;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_178);
lean_dec(x_177);
x_198 = lean_ctor_get(x_182, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_182, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_200 = x_182;
} else {
 lean_dec_ref(x_182);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
}
}
else
{
uint8_t x_202; 
lean_dec(x_17);
x_202 = !lean_is_exclusive(x_121);
if (x_202 == 0)
{
lean_object* x_203; uint8_t x_204; 
x_203 = lean_ctor_get(x_121, 0);
lean_dec(x_203);
x_204 = !lean_is_exclusive(x_122);
if (x_204 == 0)
{
return x_121;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_122, 0);
x_206 = lean_ctor_get(x_122, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_122);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
lean_ctor_set(x_121, 0, x_207);
return x_121;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_208 = lean_ctor_get(x_121, 1);
lean_inc(x_208);
lean_dec(x_121);
x_209 = lean_ctor_get(x_122, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_122, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_211 = x_122;
} else {
 lean_dec_ref(x_122);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_210);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_208);
return x_213;
}
}
}
else
{
uint8_t x_214; 
lean_dec(x_17);
x_214 = !lean_is_exclusive(x_121);
if (x_214 == 0)
{
return x_121;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_121, 0);
x_216 = lean_ctor_get(x_121, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_121);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
}
}
else
{
uint8_t x_218; 
lean_dec(x_14);
lean_free_object(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_218 = !lean_is_exclusive(x_16);
if (x_218 == 0)
{
return x_16;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_16, 0);
x_220 = lean_ctor_get(x_16, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_16);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
}
else
{
uint8_t x_222; 
lean_free_object(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_222 = !lean_is_exclusive(x_13);
if (x_222 == 0)
{
return x_13;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_13, 0);
x_224 = lean_ctor_get(x_13, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_13);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
else
{
lean_object* x_226; uint8_t x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_226 = lean_ctor_get(x_7, 0);
x_227 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_228 = lean_ctor_get(x_7, 1);
lean_inc(x_228);
lean_inc(x_226);
lean_dec(x_7);
x_229 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__1;
x_230 = lean_st_mk_ref(x_229, x_8);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = lean_st_mk_ref(x_229, x_232);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_236, 0, x_226);
lean_ctor_set(x_236, 1, x_228);
lean_ctor_set_uint8(x_236, sizeof(void*)*2, x_227);
x_237 = l_IO_FS_Stream_ofBuffer(x_231);
lean_inc(x_234);
x_238 = l_IO_FS_Stream_ofBuffer(x_234);
if (x_2 == 0)
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_afterBuildCacheSync___spec__2___rarg), 8, 2);
lean_closure_set(x_239, 0, x_238);
lean_closure_set(x_239, 1, x_1);
x_240 = l_IO_withStdin___at_Lake_Package_afterBuildCacheSync___spec__3___rarg(x_237, x_239, x_3, x_4, x_5, x_6, x_236, x_235);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_240, 1);
lean_inc(x_243);
lean_dec(x_240);
x_244 = lean_ctor_get(x_241, 0);
lean_inc(x_244);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_245 = x_241;
} else {
 lean_dec_ref(x_241);
 x_245 = lean_box(0);
}
x_246 = lean_ctor_get(x_242, 0);
lean_inc(x_246);
x_247 = lean_ctor_get_uint8(x_242, sizeof(void*)*2);
x_248 = lean_ctor_get(x_242, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_249 = x_242;
} else {
 lean_dec_ref(x_242);
 x_249 = lean_box(0);
}
x_250 = lean_st_ref_get(x_234, x_243);
lean_dec(x_234);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_253 = x_250;
} else {
 lean_dec_ref(x_250);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_254 = lean_alloc_ctor(0, 2, 1);
} else {
 x_254 = x_249;
}
lean_ctor_set(x_254, 0, x_246);
lean_ctor_set(x_254, 1, x_248);
lean_ctor_set_uint8(x_254, sizeof(void*)*2, x_247);
x_255 = lean_ctor_get(x_251, 0);
lean_inc(x_255);
lean_dec(x_251);
x_256 = lean_string_validate_utf8(x_255);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_255);
x_257 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__5;
x_258 = l_panic___at_String_fromUTF8_x21___spec__1(x_257);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_244);
if (lean_is_scalar(x_245)) {
 x_260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_260 = x_245;
}
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_254);
if (lean_is_scalar(x_253)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_253;
}
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_252);
return x_261;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_262 = lean_string_from_utf8_unchecked(x_255);
lean_dec(x_255);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_244);
if (lean_is_scalar(x_245)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_245;
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_254);
if (lean_is_scalar(x_253)) {
 x_265 = lean_alloc_ctor(0, 2, 0);
} else {
 x_265 = x_253;
}
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_252);
return x_265;
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
x_266 = lean_ctor_get(x_250, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_250, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_268 = x_250;
} else {
 lean_dec_ref(x_250);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(1, 2, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_266);
lean_ctor_set(x_269, 1, x_267);
return x_269;
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_234);
x_270 = lean_ctor_get(x_240, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_271 = x_240;
} else {
 lean_dec_ref(x_240);
 x_271 = lean_box(0);
}
x_272 = lean_ctor_get(x_241, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_241, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_274 = x_241;
} else {
 lean_dec_ref(x_241);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(1, 2, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_272);
lean_ctor_set(x_275, 1, x_273);
if (lean_is_scalar(x_271)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_271;
}
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_270);
return x_276;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_234);
x_277 = lean_ctor_get(x_240, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_240, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_279 = x_240;
} else {
 lean_dec_ref(x_240);
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
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_inc(x_238);
x_281 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_Package_afterBuildCacheSync___spec__4___rarg), 8, 2);
lean_closure_set(x_281, 0, x_238);
lean_closure_set(x_281, 1, x_1);
x_282 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_afterBuildCacheSync___spec__5___rarg), 8, 2);
lean_closure_set(x_282, 0, x_238);
lean_closure_set(x_282, 1, x_281);
x_283 = l_IO_withStdin___at_Lake_Package_afterBuildCacheSync___spec__6___rarg(x_237, x_282, x_3, x_4, x_5, x_6, x_236, x_235);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_285 = lean_ctor_get(x_284, 1);
lean_inc(x_285);
x_286 = lean_ctor_get(x_283, 1);
lean_inc(x_286);
lean_dec(x_283);
x_287 = lean_ctor_get(x_284, 0);
lean_inc(x_287);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_288 = x_284;
} else {
 lean_dec_ref(x_284);
 x_288 = lean_box(0);
}
x_289 = lean_ctor_get(x_285, 0);
lean_inc(x_289);
x_290 = lean_ctor_get_uint8(x_285, sizeof(void*)*2);
x_291 = lean_ctor_get(x_285, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_292 = x_285;
} else {
 lean_dec_ref(x_285);
 x_292 = lean_box(0);
}
x_293 = lean_st_ref_get(x_234, x_286);
lean_dec(x_234);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_296 = x_293;
} else {
 lean_dec_ref(x_293);
 x_296 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_297 = lean_alloc_ctor(0, 2, 1);
} else {
 x_297 = x_292;
}
lean_ctor_set(x_297, 0, x_289);
lean_ctor_set(x_297, 1, x_291);
lean_ctor_set_uint8(x_297, sizeof(void*)*2, x_290);
x_298 = lean_ctor_get(x_294, 0);
lean_inc(x_298);
lean_dec(x_294);
x_299 = lean_string_validate_utf8(x_298);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_298);
x_300 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__5;
x_301 = l_panic___at_String_fromUTF8_x21___spec__1(x_300);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_287);
if (lean_is_scalar(x_288)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_288;
}
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_297);
if (lean_is_scalar(x_296)) {
 x_304 = lean_alloc_ctor(0, 2, 0);
} else {
 x_304 = x_296;
}
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_295);
return x_304;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_305 = lean_string_from_utf8_unchecked(x_298);
lean_dec(x_298);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_287);
if (lean_is_scalar(x_288)) {
 x_307 = lean_alloc_ctor(0, 2, 0);
} else {
 x_307 = x_288;
}
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_297);
if (lean_is_scalar(x_296)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_296;
}
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_295);
return x_308;
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_292);
lean_dec(x_291);
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_287);
x_309 = lean_ctor_get(x_293, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_293, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_311 = x_293;
} else {
 lean_dec_ref(x_293);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(1, 2, 0);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_309);
lean_ctor_set(x_312, 1, x_310);
return x_312;
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_234);
x_313 = lean_ctor_get(x_283, 1);
lean_inc(x_313);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_314 = x_283;
} else {
 lean_dec_ref(x_283);
 x_314 = lean_box(0);
}
x_315 = lean_ctor_get(x_284, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_284, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_317 = x_284;
} else {
 lean_dec_ref(x_284);
 x_317 = lean_box(0);
}
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(1, 2, 0);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_315);
lean_ctor_set(x_318, 1, x_316);
if (lean_is_scalar(x_314)) {
 x_319 = lean_alloc_ctor(0, 2, 0);
} else {
 x_319 = x_314;
}
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_313);
return x_319;
}
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_234);
x_320 = lean_ctor_get(x_283, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_283, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_322 = x_283;
} else {
 lean_dec_ref(x_283);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 2, 0);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_320);
lean_ctor_set(x_323, 1, x_321);
return x_323;
}
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_231);
lean_dec(x_228);
lean_dec(x_226);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_324 = lean_ctor_get(x_233, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_233, 1);
lean_inc(x_325);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_326 = x_233;
} else {
 lean_dec_ref(x_233);
 x_326 = lean_box(0);
}
if (lean_is_scalar(x_326)) {
 x_327 = lean_alloc_ctor(1, 2, 0);
} else {
 x_327 = x_326;
}
lean_ctor_set(x_327, 0, x_324);
lean_ctor_set(x_327, 1, x_325);
return x_327;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_228);
lean_dec(x_226);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_328 = lean_ctor_get(x_230, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_230, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_330 = x_230;
} else {
 lean_dec_ref(x_230);
 x_330 = lean_box(0);
}
if (lean_is_scalar(x_330)) {
 x_331 = lean_alloc_ctor(1, 2, 0);
} else {
 x_331 = x_330;
}
lean_ctor_set(x_331, 0, x_328);
lean_ctor_set(x_331, 1, x_329);
return x_331;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_afterBuildCacheSync___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___at_Lake_Package_afterBuildCacheSync___spec__1___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_IO_FS_withIsolatedStreams___at_Lake_Package_afterBuildCacheSync___spec__1___rarg(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_string_utf8_byte_size(x_14);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; 
x_19 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_14, x_16, x_17);
x_20 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_14, x_19, x_16);
x_21 = lean_string_utf8_extract(x_14, x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
x_22 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__5___closed__1;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_25 = lean_string_append(x_23, x_24);
x_26 = 1;
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_array_push(x_29, x_27);
lean_ctor_set(x_13, 0, x_30);
x_31 = lean_box(0);
x_32 = l_Lake_Package_afterBuildCacheSync___rarg___lambda__1(x_15, x_31, x_2, x_3, x_4, x_5, x_13, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_32;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
x_35 = lean_ctor_get(x_13, 1);
lean_inc(x_35);
lean_inc(x_33);
lean_dec(x_13);
x_36 = lean_array_push(x_33, x_27);
x_37 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_34);
x_38 = lean_box(0);
x_39 = l_Lake_Package_afterBuildCacheSync___rarg___lambda__1(x_15, x_38, x_2, x_3, x_4, x_5, x_37, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_16);
lean_dec(x_14);
x_40 = lean_box(0);
x_41 = l_Lake_Package_afterBuildCacheSync___rarg___lambda__1(x_15, x_40, x_2, x_3, x_4, x_5, x_13, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_9);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_9, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_10);
if (x_44 == 0)
{
return x_9;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_10, 0);
x_46 = lean_ctor_get(x_10, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_10);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_9, 0, x_47);
return x_9;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_9, 1);
lean_inc(x_48);
lean_dec(x_9);
x_49 = lean_ctor_get(x_10, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_10, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_51 = x_10;
} else {
 lean_dec_ref(x_10);
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
else
{
uint8_t x_54; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_9);
if (x_54 == 0)
{
return x_9;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_9, 0);
x_56 = lean_ctor_get(x_9, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_9);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_10, 2);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_name_eq(x_12, x_14);
lean_dec(x_14);
lean_dec(x_12);
x_16 = l_instDecidableNot___rarg(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_17 = l_Lake_Package_recFetchDeps___lambda__1___closed__2;
x_18 = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheSync___rarg___lambda__2), 7, 6);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_3);
lean_closure_set(x_18, 2, x_4);
lean_closure_set(x_18, 3, x_5);
lean_closure_set(x_18, 4, x_6);
lean_closure_set(x_18, 5, x_17);
x_19 = l_Task_Priority_default;
x_20 = lean_io_as_task(x_18, x_19, x_8);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_24 = 0;
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_7);
lean_ctor_set(x_20, 0, x_26);
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
x_29 = l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2;
x_30 = 0;
x_31 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_7);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_7);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
return x_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_38 = l_Lake_Package_maybeFetchBuildCache(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_39, 0);
x_43 = lean_ctor_get(x_39, 1);
x_44 = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheAsync___rarg___lambda__1___boxed), 8, 1);
lean_closure_set(x_44, 0, x_2);
x_45 = l_Task_Priority_default;
x_46 = 0;
x_47 = l_Lake_BuildTrace_nil;
x_48 = l_Lake_Job_mapM___rarg(x_42, x_44, x_45, x_46, x_3, x_4, x_5, x_6, x_47, x_40);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
lean_ctor_set(x_39, 0, x_50);
lean_ctor_set(x_48, 0, x_39);
return x_48;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_48, 0);
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_48);
lean_ctor_set(x_39, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_39);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_free_object(x_39);
lean_dec(x_43);
x_54 = !lean_is_exclusive(x_48);
if (x_54 == 0)
{
return x_48;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_48, 0);
x_56 = lean_ctor_get(x_48, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_48);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_39, 0);
x_59 = lean_ctor_get(x_39, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_39);
x_60 = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheAsync___rarg___lambda__1___boxed), 8, 1);
lean_closure_set(x_60, 0, x_2);
x_61 = l_Task_Priority_default;
x_62 = 0;
x_63 = l_Lake_BuildTrace_nil;
x_64 = l_Lake_Job_mapM___rarg(x_58, x_60, x_61, x_62, x_3, x_4, x_5, x_6, x_63, x_40);
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
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_59);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_59);
x_70 = lean_ctor_get(x_64, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_64, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_72 = x_64;
} else {
 lean_dec_ref(x_64);
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
else
{
uint8_t x_74; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_38);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_38, 0);
lean_dec(x_75);
x_76 = !lean_is_exclusive(x_39);
if (x_76 == 0)
{
return x_38;
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
lean_ctor_set(x_38, 0, x_79);
return x_38;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_80 = lean_ctor_get(x_38, 1);
lean_inc(x_80);
lean_dec(x_38);
x_81 = lean_ctor_get(x_39, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_39, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_83 = x_39;
} else {
 lean_dec_ref(x_39);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_80);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_86 = !lean_is_exclusive(x_38);
if (x_86 == 0)
{
return x_38;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_38, 0);
x_88 = lean_ctor_get(x_38, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_38);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheSync___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_afterBuildCacheSync___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_IO_FS_withIsolatedStreams___at_Lake_Package_afterBuildCacheSync___spec__1___rarg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Package_afterBuildCacheSync___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseSync___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Package_afterBuildCacheSync___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseSync(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Package_afterReleaseSync___rarg), 8, 0);
return x_2;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_depsFacetConfig___closed__2;
x_3 = l_Lake_Package_depsFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addPackageFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initPackageFacetConfigs___closed__1;
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeTransDeps___spec__9___closed__2;
x_3 = l_Lake_Package_transDepsFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addPackageFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initPackageFacetConfigs___closed__2;
x_2 = l_Lake_Package_extraDepFacetConfig___closed__2;
x_3 = l_Lake_Package_extraDepFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addPackageFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initPackageFacetConfigs___closed__3;
x_2 = l_Lake_Package_optBuildCacheFacetConfig___closed__2;
x_3 = l_Lake_Package_optBuildCacheFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addPackageFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initPackageFacetConfigs___closed__4;
x_2 = l_Lake_Package_buildCacheFacetConfig___elambda__2___closed__2;
x_3 = l_Lake_Package_buildCacheFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addPackageFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initPackageFacetConfigs___closed__5;
x_2 = l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__2;
x_3 = l_Lake_Package_optBarrelFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addPackageFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initPackageFacetConfigs___closed__6;
x_2 = l_Lake_Package_barrelFacetConfig___elambda__2___closed__2;
x_3 = l_Lake_Package_barrelFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addPackageFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initPackageFacetConfigs___closed__7;
x_2 = l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__4;
x_3 = l_Lake_Package_optGitHubReleaseFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addPackageFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initPackageFacetConfigs___closed__8;
x_2 = l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___closed__2;
x_3 = l_Lake_Package_gitHubReleaseFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addPackageFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_initPackageFacetConfigs___closed__9;
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
l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__1);
l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__2);
l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__3 = _init_l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__3);
l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__4 = _init_l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Package_recFetchDeps___spec__1___closed__4);
l_Lake_Package_recFetchDeps___lambda__1___closed__1 = _init_l_Lake_Package_recFetchDeps___lambda__1___closed__1();
lean_mark_persistent(l_Lake_Package_recFetchDeps___lambda__1___closed__1);
l_Lake_Package_recFetchDeps___lambda__1___closed__2 = _init_l_Lake_Package_recFetchDeps___lambda__1___closed__2();
lean_mark_persistent(l_Lake_Package_recFetchDeps___lambda__1___closed__2);
l_Lake_Package_recFetchDeps___closed__1 = _init_l_Lake_Package_recFetchDeps___closed__1();
lean_mark_persistent(l_Lake_Package_recFetchDeps___closed__1);
l_Lake_Package_recFetchDeps___boxed__const__1 = _init_l_Lake_Package_recFetchDeps___boxed__const__1();
lean_mark_persistent(l_Lake_Package_recFetchDeps___boxed__const__1);
l_Array_foldlMUnsafe_fold___at_Lake_Package_depsFacetConfig___elambda__1___spec__2___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Package_depsFacetConfig___elambda__1___spec__2___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Package_depsFacetConfig___elambda__1___spec__2___closed__1);
l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__1 = _init_l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__1();
lean_mark_persistent(l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__1);
l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__2 = _init_l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__2();
lean_mark_persistent(l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__2);
l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__3 = _init_l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__3();
lean_mark_persistent(l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__3);
l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__4 = _init_l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__4();
lean_mark_persistent(l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__4);
l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__5 = _init_l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__5();
lean_mark_persistent(l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__5);
l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__6 = _init_l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__6();
lean_mark_persistent(l_Lake_stdFormat___at_Lake_Package_depsFacetConfig___elambda__1___spec__1___closed__6);
l_Lake_Package_depsFacetConfig___closed__1 = _init_l_Lake_Package_depsFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Package_depsFacetConfig___closed__1);
l_Lake_Package_depsFacetConfig___closed__2 = _init_l_Lake_Package_depsFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Package_depsFacetConfig___closed__2);
l_Lake_Package_depsFacetConfig___closed__3 = _init_l_Lake_Package_depsFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Package_depsFacetConfig___closed__3);
l_Lake_Package_depsFacetConfig___closed__4 = _init_l_Lake_Package_depsFacetConfig___closed__4();
lean_mark_persistent(l_Lake_Package_depsFacetConfig___closed__4);
l_Lake_Package_depsFacetConfig___closed__5 = _init_l_Lake_Package_depsFacetConfig___closed__5();
lean_mark_persistent(l_Lake_Package_depsFacetConfig___closed__5);
l_Lake_Package_depsFacetConfig = _init_l_Lake_Package_depsFacetConfig();
lean_mark_persistent(l_Lake_Package_depsFacetConfig);
l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeTransDeps___spec__1___closed__1 = _init_l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeTransDeps___spec__1___closed__1();
lean_mark_persistent(l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeTransDeps___spec__1___closed__1);
l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeTransDeps___spec__1___closed__2 = _init_l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeTransDeps___spec__1___closed__2();
lean_mark_persistent(l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeTransDeps___spec__1___closed__2);
l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeTransDeps___spec__9___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeTransDeps___spec__9___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeTransDeps___spec__9___closed__1);
l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeTransDeps___spec__9___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeTransDeps___spec__9___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeTransDeps___spec__9___closed__2);
l_Lake_Package_recComputeTransDeps___closed__1 = _init_l_Lake_Package_recComputeTransDeps___closed__1();
lean_mark_persistent(l_Lake_Package_recComputeTransDeps___closed__1);
l_Lake_Package_recComputeTransDeps___boxed__const__1 = _init_l_Lake_Package_recComputeTransDeps___boxed__const__1();
lean_mark_persistent(l_Lake_Package_recComputeTransDeps___boxed__const__1);
l_Lake_Package_transDepsFacetConfig___closed__1 = _init_l_Lake_Package_transDepsFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Package_transDepsFacetConfig___closed__1);
l_Lake_Package_transDepsFacetConfig___closed__2 = _init_l_Lake_Package_transDepsFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Package_transDepsFacetConfig___closed__2);
l_Lake_Package_transDepsFacetConfig___closed__3 = _init_l_Lake_Package_transDepsFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Package_transDepsFacetConfig___closed__3);
l_Lake_Package_transDepsFacetConfig = _init_l_Lake_Package_transDepsFacetConfig();
lean_mark_persistent(l_Lake_Package_transDepsFacetConfig);
l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__1 = _init_l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__1();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__1);
l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__2 = _init_l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__2();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__2);
l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__3 = _init_l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__3();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__3);
l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__4 = _init_l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__4();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__4);
l_Lake_stdFormat___at_Lake_Package_optBuildCacheFacetConfig___elambda__1___spec__1___closed__1 = _init_l_Lake_stdFormat___at_Lake_Package_optBuildCacheFacetConfig___elambda__1___spec__1___closed__1();
lean_mark_persistent(l_Lake_stdFormat___at_Lake_Package_optBuildCacheFacetConfig___elambda__1___spec__1___closed__1);
l_Lake_stdFormat___at_Lake_Package_optBuildCacheFacetConfig___elambda__1___spec__1___closed__2 = _init_l_Lake_stdFormat___at_Lake_Package_optBuildCacheFacetConfig___elambda__1___spec__1___closed__2();
lean_mark_persistent(l_Lake_stdFormat___at_Lake_Package_optBuildCacheFacetConfig___elambda__1___spec__1___closed__2);
l_Lake_Package_optBuildCacheFacetConfig___closed__1 = _init_l_Lake_Package_optBuildCacheFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Package_optBuildCacheFacetConfig___closed__1);
l_Lake_Package_optBuildCacheFacetConfig___closed__2 = _init_l_Lake_Package_optBuildCacheFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Package_optBuildCacheFacetConfig___closed__2);
l_Lake_Package_optBuildCacheFacetConfig___closed__3 = _init_l_Lake_Package_optBuildCacheFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Package_optBuildCacheFacetConfig___closed__3);
l_Lake_Package_optBuildCacheFacetConfig___closed__4 = _init_l_Lake_Package_optBuildCacheFacetConfig___closed__4();
lean_mark_persistent(l_Lake_Package_optBuildCacheFacetConfig___closed__4);
l_Lake_Package_optBuildCacheFacetConfig___closed__5 = _init_l_Lake_Package_optBuildCacheFacetConfig___closed__5();
lean_mark_persistent(l_Lake_Package_optBuildCacheFacetConfig___closed__5);
l_Lake_Package_optBuildCacheFacetConfig = _init_l_Lake_Package_optBuildCacheFacetConfig();
lean_mark_persistent(l_Lake_Package_optBuildCacheFacetConfig);
l_Lake_Package_maybeFetchBuildCache___closed__1 = _init_l_Lake_Package_maybeFetchBuildCache___closed__1();
lean_mark_persistent(l_Lake_Package_maybeFetchBuildCache___closed__1);
l_Lake_Package_maybeFetchBuildCache___closed__2 = _init_l_Lake_Package_maybeFetchBuildCache___closed__2();
lean_mark_persistent(l_Lake_Package_maybeFetchBuildCache___closed__2);
l_Lake_Package_maybeFetchBuildCache___closed__3 = _init_l_Lake_Package_maybeFetchBuildCache___closed__3();
lean_mark_persistent(l_Lake_Package_maybeFetchBuildCache___closed__3);
l_Lake_Package_maybeFetchBuildCache___closed__4 = _init_l_Lake_Package_maybeFetchBuildCache___closed__4();
lean_mark_persistent(l_Lake_Package_maybeFetchBuildCache___closed__4);
l_Lake_Package_maybeFetchBuildCache___closed__5 = _init_l_Lake_Package_maybeFetchBuildCache___closed__5();
lean_mark_persistent(l_Lake_Package_maybeFetchBuildCache___closed__5);
l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__1 = _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__1();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__1);
l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__2 = _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__2();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__2);
l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3 = _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3);
l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__4 = _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__4();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__4);
l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__1 = _init_l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__1();
lean_mark_persistent(l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__1);
l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__2 = _init_l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__2();
lean_mark_persistent(l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__2);
l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__3 = _init_l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__3();
lean_mark_persistent(l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__3);
l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__4 = _init_l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__4();
lean_mark_persistent(l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__4);
l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__5 = _init_l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__5();
lean_mark_persistent(l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__5);
l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__6 = _init_l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__6();
lean_mark_persistent(l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__6);
l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__7 = _init_l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__7();
lean_mark_persistent(l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__7);
l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__8 = _init_l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__8();
lean_mark_persistent(l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__8);
l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__9 = _init_l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__9();
lean_mark_persistent(l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__9);
l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__10 = _init_l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__10();
lean_mark_persistent(l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__10);
l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__1 = _init_l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__1();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__1);
l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__2 = _init_l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__2();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__2);
l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__3 = _init_l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__3();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__3);
l_Lake_Package_recBuildExtraDepTargets___closed__1 = _init_l_Lake_Package_recBuildExtraDepTargets___closed__1();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___closed__1);
l_Lake_Package_recBuildExtraDepTargets___closed__2 = _init_l_Lake_Package_recBuildExtraDepTargets___closed__2();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___closed__2);
l_Lake_Package_recBuildExtraDepTargets___closed__3 = _init_l_Lake_Package_recBuildExtraDepTargets___closed__3();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___closed__3);
l_Lake_Package_recBuildExtraDepTargets___closed__4 = _init_l_Lake_Package_recBuildExtraDepTargets___closed__4();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___closed__4);
l_Lake_Package_extraDepFacetConfig___closed__1 = _init_l_Lake_Package_extraDepFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Package_extraDepFacetConfig___closed__1);
l_Lake_Package_extraDepFacetConfig___closed__2 = _init_l_Lake_Package_extraDepFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Package_extraDepFacetConfig___closed__2);
l_Lake_Package_extraDepFacetConfig___closed__3 = _init_l_Lake_Package_extraDepFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Package_extraDepFacetConfig___closed__3);
l_Lake_Package_extraDepFacetConfig___closed__4 = _init_l_Lake_Package_extraDepFacetConfig___closed__4();
lean_mark_persistent(l_Lake_Package_extraDepFacetConfig___closed__4);
l_Lake_Package_extraDepFacetConfig___closed__5 = _init_l_Lake_Package_extraDepFacetConfig___closed__5();
lean_mark_persistent(l_Lake_Package_extraDepFacetConfig___closed__5);
l_Lake_Package_extraDepFacetConfig = _init_l_Lake_Package_extraDepFacetConfig();
lean_mark_persistent(l_Lake_Package_extraDepFacetConfig);
l_Lake_Package_getBarrelUrl___lambda__1___closed__1 = _init_l_Lake_Package_getBarrelUrl___lambda__1___closed__1();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___lambda__1___closed__1);
l_Lake_Package_getBarrelUrl___lambda__1___closed__2 = _init_l_Lake_Package_getBarrelUrl___lambda__1___closed__2();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___lambda__1___closed__2);
l_Lake_Package_getBarrelUrl___lambda__2___closed__1 = _init_l_Lake_Package_getBarrelUrl___lambda__2___closed__1();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___lambda__2___closed__1);
l_Lake_Package_getBarrelUrl___lambda__2___closed__2 = _init_l_Lake_Package_getBarrelUrl___lambda__2___closed__2();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___lambda__2___closed__2);
l_Lake_Package_getBarrelUrl___lambda__2___closed__3 = _init_l_Lake_Package_getBarrelUrl___lambda__2___closed__3();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___lambda__2___closed__3);
l_Lake_Package_getBarrelUrl___lambda__2___closed__4 = _init_l_Lake_Package_getBarrelUrl___lambda__2___closed__4();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___lambda__2___closed__4);
l_Lake_Package_getBarrelUrl___lambda__2___closed__5 = _init_l_Lake_Package_getBarrelUrl___lambda__2___closed__5();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___lambda__2___closed__5);
l_Lake_Package_getBarrelUrl___lambda__2___closed__6 = _init_l_Lake_Package_getBarrelUrl___lambda__2___closed__6();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___lambda__2___closed__6);
l_Lake_Package_getBarrelUrl___lambda__2___closed__7 = _init_l_Lake_Package_getBarrelUrl___lambda__2___closed__7();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___lambda__2___closed__7);
l_Lake_Package_getBarrelUrl___lambda__2___closed__8 = _init_l_Lake_Package_getBarrelUrl___lambda__2___closed__8();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___lambda__2___closed__8);
l_Lake_Package_getBarrelUrl___lambda__2___closed__9 = _init_l_Lake_Package_getBarrelUrl___lambda__2___closed__9();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___lambda__2___closed__9);
l_Lake_Package_getBarrelUrl___lambda__2___closed__10 = _init_l_Lake_Package_getBarrelUrl___lambda__2___closed__10();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___lambda__2___closed__10);
l_Lake_Package_getBarrelUrl___lambda__2___closed__11 = _init_l_Lake_Package_getBarrelUrl___lambda__2___closed__11();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___lambda__2___closed__11);
l_Lake_Package_getBarrelUrl___lambda__2___closed__12 = _init_l_Lake_Package_getBarrelUrl___lambda__2___closed__12();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___lambda__2___closed__12);
l_Lake_Package_getBarrelUrl___lambda__2___closed__13 = _init_l_Lake_Package_getBarrelUrl___lambda__2___closed__13();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___lambda__2___closed__13);
l_Lake_Package_getBarrelUrl___lambda__2___closed__14 = _init_l_Lake_Package_getBarrelUrl___lambda__2___closed__14();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___lambda__2___closed__14);
l_Lake_Package_getBarrelUrl___lambda__2___closed__15 = _init_l_Lake_Package_getBarrelUrl___lambda__2___closed__15();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___lambda__2___closed__15);
l_Lake_Package_getBarrelUrl___closed__1 = _init_l_Lake_Package_getBarrelUrl___closed__1();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___closed__1);
l_Lake_Package_getBarrelUrl___closed__2 = _init_l_Lake_Package_getBarrelUrl___closed__2();
lean_mark_persistent(l_Lake_Package_getBarrelUrl___closed__2);
l_Lake_Package_getReleaseUrl___lambda__1___closed__1 = _init_l_Lake_Package_getReleaseUrl___lambda__1___closed__1();
lean_mark_persistent(l_Lake_Package_getReleaseUrl___lambda__1___closed__1);
l_Lake_Package_getReleaseUrl___closed__1 = _init_l_Lake_Package_getReleaseUrl___closed__1();
lean_mark_persistent(l_Lake_Package_getReleaseUrl___closed__1);
l_Lake_Package_getReleaseUrl___closed__2 = _init_l_Lake_Package_getReleaseUrl___closed__2();
lean_mark_persistent(l_Lake_Package_getReleaseUrl___closed__2);
l_Lake_Package_getReleaseUrl___closed__3 = _init_l_Lake_Package_getReleaseUrl___closed__3();
lean_mark_persistent(l_Lake_Package_getReleaseUrl___closed__3);
l_Lake_Package_getReleaseUrl___closed__4 = _init_l_Lake_Package_getReleaseUrl___closed__4();
lean_mark_persistent(l_Lake_Package_getReleaseUrl___closed__4);
l_Lake_Package_getReleaseUrl___closed__5 = _init_l_Lake_Package_getReleaseUrl___closed__5();
lean_mark_persistent(l_Lake_Package_getReleaseUrl___closed__5);
l_Lake_Package_getReleaseUrl___closed__6 = _init_l_Lake_Package_getReleaseUrl___closed__6();
lean_mark_persistent(l_Lake_Package_getReleaseUrl___closed__6);
l_Lake_Package_getReleaseUrl___closed__7 = _init_l_Lake_Package_getReleaseUrl___closed__7();
lean_mark_persistent(l_Lake_Package_getReleaseUrl___closed__7);
l_Lake_Package_getReleaseUrl___closed__8 = _init_l_Lake_Package_getReleaseUrl___closed__8();
lean_mark_persistent(l_Lake_Package_getReleaseUrl___closed__8);
l_Lake_Package_getReleaseUrl___closed__9 = _init_l_Lake_Package_getReleaseUrl___closed__9();
lean_mark_persistent(l_Lake_Package_getReleaseUrl___closed__9);
l_Lake_Package_getReleaseUrl___closed__10 = _init_l_Lake_Package_getReleaseUrl___closed__10();
lean_mark_persistent(l_Lake_Package_getReleaseUrl___closed__10);
l_Lake_Package_getReleaseUrl___closed__11 = _init_l_Lake_Package_getReleaseUrl___closed__11();
lean_mark_persistent(l_Lake_Package_getReleaseUrl___closed__11);
l_Lake_Package_getReleaseUrl___closed__12 = _init_l_Lake_Package_getReleaseUrl___closed__12();
lean_mark_persistent(l_Lake_Package_getReleaseUrl___closed__12);
l_Lake_Package_getReleaseUrl___closed__13 = _init_l_Lake_Package_getReleaseUrl___closed__13();
lean_mark_persistent(l_Lake_Package_getReleaseUrl___closed__13);
l_Lake_Package_getReleaseUrl___closed__14 = _init_l_Lake_Package_getReleaseUrl___closed__14();
lean_mark_persistent(l_Lake_Package_getReleaseUrl___closed__14);
l_Lake_Package_fetchBuildArchive___closed__1 = _init_l_Lake_Package_fetchBuildArchive___closed__1();
lean_mark_persistent(l_Lake_Package_fetchBuildArchive___closed__1);
l_Lake_Package_fetchBuildArchive___closed__2 = _init_l_Lake_Package_fetchBuildArchive___closed__2();
lean_mark_persistent(l_Lake_Package_fetchBuildArchive___closed__2);
l_Lake_Package_fetchBuildArchive___closed__3 = _init_l_Lake_Package_fetchBuildArchive___closed__3();
lean_mark_persistent(l_Lake_Package_fetchBuildArchive___closed__3);
l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__1 = _init_l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__1();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__1);
l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__2 = _init_l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__2();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__2);
l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__3 = _init_l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__3();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__3);
l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__4 = _init_l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__4();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__4);
l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__5 = _init_l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__5();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2___closed__5);
l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__5___closed__1 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__5___closed__1();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__5___closed__1);
l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__7___closed__1 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__7___closed__1();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__7___closed__1);
l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__7___closed__2 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__7___closed__2();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__7___closed__2);
l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___closed__1 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___closed__1();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___closed__1);
l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1___closed__1 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1___closed__1();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1___closed__1);
l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___closed__1 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___closed__1();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___closed__1);
l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__1 = _init_l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__1();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__1);
l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__2 = _init_l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__2();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__2);
l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__3 = _init_l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__3();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__3);
l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__4 = _init_l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__4();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__4);
l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__5 = _init_l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__5();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__5);
l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__6 = _init_l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__6();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig___elambda__2___lambda__1___closed__6);
l_Lake_Package_buildCacheFacetConfig___elambda__2___closed__1 = _init_l_Lake_Package_buildCacheFacetConfig___elambda__2___closed__1();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig___elambda__2___closed__1);
l_Lake_Package_buildCacheFacetConfig___elambda__2___closed__2 = _init_l_Lake_Package_buildCacheFacetConfig___elambda__2___closed__2();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig___elambda__2___closed__2);
l_Lake_Package_buildCacheFacetConfig___elambda__2___closed__3 = _init_l_Lake_Package_buildCacheFacetConfig___elambda__2___closed__3();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig___elambda__2___closed__3);
l_Lake_Package_buildCacheFacetConfig___closed__1 = _init_l_Lake_Package_buildCacheFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig___closed__1);
l_Lake_Package_buildCacheFacetConfig___closed__2 = _init_l_Lake_Package_buildCacheFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig___closed__2);
l_Lake_Package_buildCacheFacetConfig___closed__3 = _init_l_Lake_Package_buildCacheFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig___closed__3);
l_Lake_Package_buildCacheFacetConfig = _init_l_Lake_Package_buildCacheFacetConfig();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig);
l_Lake_Package_optBarrelFacetConfig___elambda__2___lambda__1___closed__1 = _init_l_Lake_Package_optBarrelFacetConfig___elambda__2___lambda__1___closed__1();
lean_mark_persistent(l_Lake_Package_optBarrelFacetConfig___elambda__2___lambda__1___closed__1);
l_Lake_Package_optBarrelFacetConfig___closed__1 = _init_l_Lake_Package_optBarrelFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Package_optBarrelFacetConfig___closed__1);
l_Lake_Package_optBarrelFacetConfig___closed__2 = _init_l_Lake_Package_optBarrelFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Package_optBarrelFacetConfig___closed__2);
l_Lake_Package_optBarrelFacetConfig___closed__3 = _init_l_Lake_Package_optBarrelFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Package_optBarrelFacetConfig___closed__3);
l_Lake_Package_optBarrelFacetConfig = _init_l_Lake_Package_optBarrelFacetConfig();
lean_mark_persistent(l_Lake_Package_optBarrelFacetConfig);
l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__1 = _init_l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__1();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__1);
l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__2 = _init_l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__2();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__2);
l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__3 = _init_l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__3();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__3);
l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__4 = _init_l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__4();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__4);
l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__5 = _init_l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__5();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__5);
l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__6 = _init_l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__6();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig___elambda__2___lambda__1___closed__6);
l_Lake_Package_barrelFacetConfig___elambda__2___closed__1 = _init_l_Lake_Package_barrelFacetConfig___elambda__2___closed__1();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig___elambda__2___closed__1);
l_Lake_Package_barrelFacetConfig___elambda__2___closed__2 = _init_l_Lake_Package_barrelFacetConfig___elambda__2___closed__2();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig___elambda__2___closed__2);
l_Lake_Package_barrelFacetConfig___elambda__2___closed__3 = _init_l_Lake_Package_barrelFacetConfig___elambda__2___closed__3();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig___elambda__2___closed__3);
l_Lake_Package_barrelFacetConfig___closed__1 = _init_l_Lake_Package_barrelFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig___closed__1);
l_Lake_Package_barrelFacetConfig___closed__2 = _init_l_Lake_Package_barrelFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig___closed__2);
l_Lake_Package_barrelFacetConfig___closed__3 = _init_l_Lake_Package_barrelFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig___closed__3);
l_Lake_Package_barrelFacetConfig = _init_l_Lake_Package_barrelFacetConfig();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig);
l_Lake_Package_optGitHubReleaseFacetConfig___closed__1 = _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Package_optGitHubReleaseFacetConfig___closed__1);
l_Lake_Package_optGitHubReleaseFacetConfig___closed__2 = _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Package_optGitHubReleaseFacetConfig___closed__2);
l_Lake_Package_optGitHubReleaseFacetConfig___closed__3 = _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Package_optGitHubReleaseFacetConfig___closed__3);
l_Lake_Package_optGitHubReleaseFacetConfig = _init_l_Lake_Package_optGitHubReleaseFacetConfig();
lean_mark_persistent(l_Lake_Package_optGitHubReleaseFacetConfig);
l_Lake_Package_optReleaseFacetConfig = _init_l_Lake_Package_optReleaseFacetConfig();
lean_mark_persistent(l_Lake_Package_optReleaseFacetConfig);
l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__1 = _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__1();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__1);
l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__2 = _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__2();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__2);
l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__3 = _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__3();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__3);
l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__4 = _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__4();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__4);
l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__5 = _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__5();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__5);
l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__6 = _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__6();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___lambda__1___closed__6);
l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___closed__1 = _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___closed__1();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___closed__1);
l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___closed__2 = _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___closed__2();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___closed__2);
l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___closed__3 = _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___closed__3();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig___elambda__2___closed__3);
l_Lake_Package_gitHubReleaseFacetConfig___closed__1 = _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig___closed__1);
l_Lake_Package_gitHubReleaseFacetConfig___closed__2 = _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig___closed__2);
l_Lake_Package_gitHubReleaseFacetConfig___closed__3 = _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig___closed__3);
l_Lake_Package_gitHubReleaseFacetConfig = _init_l_Lake_Package_gitHubReleaseFacetConfig();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig);
l_Lake_Package_releaseFacetConfig = _init_l_Lake_Package_releaseFacetConfig();
lean_mark_persistent(l_Lake_Package_releaseFacetConfig);
l_Lake_initPackageFacetConfigs___closed__1 = _init_l_Lake_initPackageFacetConfigs___closed__1();
lean_mark_persistent(l_Lake_initPackageFacetConfigs___closed__1);
l_Lake_initPackageFacetConfigs___closed__2 = _init_l_Lake_initPackageFacetConfigs___closed__2();
lean_mark_persistent(l_Lake_initPackageFacetConfigs___closed__2);
l_Lake_initPackageFacetConfigs___closed__3 = _init_l_Lake_initPackageFacetConfigs___closed__3();
lean_mark_persistent(l_Lake_initPackageFacetConfigs___closed__3);
l_Lake_initPackageFacetConfigs___closed__4 = _init_l_Lake_initPackageFacetConfigs___closed__4();
lean_mark_persistent(l_Lake_initPackageFacetConfigs___closed__4);
l_Lake_initPackageFacetConfigs___closed__5 = _init_l_Lake_initPackageFacetConfigs___closed__5();
lean_mark_persistent(l_Lake_initPackageFacetConfigs___closed__5);
l_Lake_initPackageFacetConfigs___closed__6 = _init_l_Lake_initPackageFacetConfigs___closed__6();
lean_mark_persistent(l_Lake_initPackageFacetConfigs___closed__6);
l_Lake_initPackageFacetConfigs___closed__7 = _init_l_Lake_initPackageFacetConfigs___closed__7();
lean_mark_persistent(l_Lake_initPackageFacetConfigs___closed__7);
l_Lake_initPackageFacetConfigs___closed__8 = _init_l_Lake_initPackageFacetConfigs___closed__8();
lean_mark_persistent(l_Lake_initPackageFacetConfigs___closed__8);
l_Lake_initPackageFacetConfigs___closed__9 = _init_l_Lake_initPackageFacetConfigs___closed__9();
lean_mark_persistent(l_Lake_initPackageFacetConfigs___closed__9);
l_Lake_initPackageFacetConfigs = _init_l_Lake_initPackageFacetConfigs();
lean_mark_persistent(l_Lake_initPackageFacetConfigs);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

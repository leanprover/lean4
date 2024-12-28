// Lean compiler output
// Module: Lake.Build.Package
// Imports: Lake.Util.Git Lake.Util.Sugar Lake.Build.Common Lake.Build.Targets Lake.Reservoir
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
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initPackageFacetConfigs___closed__5;
lean_object* l_Lake_Package_fetchTargetJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterBuildCacheSync___spec__6(lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___lambda__1___closed__2;
static lean_object* l_Lake_Package_optBuildCacheFacetConfig___closed__6;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_afterBuildCacheSync___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__2;
static lean_object* l_Lake_Package_depsFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_initPackageFacetConfigs;
static lean_object* l_Lake_Package_maybeFetchBuildCache___closed__6;
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__6;
static lean_object* l_Lake_Package_getReleaseUrl___closed__11;
static lean_object* l_Lake_Package_getBarrelUrl___lambda__2___closed__10;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__7;
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static lean_object* l_Lake_Package_getReleaseUrl___closed__12;
static lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__6;
static lean_object* l_Lake_Package_getReleaseUrl___closed__9;
static lean_object* l_Lake_Package_fetchBuildArchive___closed__2;
static lean_object* l_Lake_Package_getReleaseUrl___closed__2;
static lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
static lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_afterBuildCacheSync___spec__1(lean_object*);
static lean_object* l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__4;
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
static lean_object* l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__5;
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_recBuildExtraDepTargets___closed__3;
static lean_object* l_Lake_Package_depsFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_optBarrelFacetConfig___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_Package_barrelFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_getReleaseUrl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lake_Build_Job_0__Lake_Job_toOpaqueImpl___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_afterBuildCacheSync___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCache___closed__5;
static lean_object* l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__2;
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Package_afterBuildCacheSync___spec__4(lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCache___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig;
lean_object* l_Lake_Job_mix___rarg(lean_object*, lean_object*);
lean_object* l_Lake_download(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_buildUnlessUpToDate_x3f_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_checkHashUpToDate___at_Lake_buildFileUnlessUpToDate_x27___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getReleaseUrl___closed__10;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
extern lean_object* l_Lake_Reservoir_lakeHeaders;
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate_x27___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_barrelFacetConfig___closed__1;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__4;
lean_object* l_Lake_Job_add___rarg(lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate_x27___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___rarg___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_getReleaseUrl___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__9;
extern lean_object* l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
static lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__5;
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
static lean_object* l_Lake_Package_buildCacheFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig;
lean_object* l_Lake_readTraceFile_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___lambda__2___closed__11;
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initPackageFacetConfigs___closed__3;
static lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__2;
static lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__5;
static lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__6;
static lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__1___closed__3;
static lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___elambda__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_optBuildCacheFacetConfig___closed__4;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__1;
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_Package_recBuildExtraDepTargets___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCache___closed__3;
LEAN_EXPORT lean_object* l_Lake_Package_fetchBuildArchive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_optBuildCacheFacetConfig___closed__5;
lean_object* lean_task_pure(lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__6___closed__1;
static lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__1___closed__2;
uint8_t l_instDecidableNot___rarg(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___lambda__2___closed__4;
lean_object* l_Lake_captureProc_x3f(lean_object*, lean_object*);
static lean_object* l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__5;
static lean_object* l_Lake_Package_getBarrelUrl___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__7(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_Package_gitHubReleaseFacetConfig___closed__2;
static lean_object* l_Lake_Package_getBarrelUrl___lambda__2___closed__5;
static lean_object* l_Lake_Package_getBarrelUrl___lambda__2___closed__15;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_to_int(lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchBuildArchive___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildInfo_fetch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___lambda__1(lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__4;
static lean_object* l_Lake_Package_optBuildCacheFacetConfig___closed__2;
static lean_object* l_Lake_initPackageFacetConfigs___closed__8;
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_withRegisterJob___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___lambda__2___closed__9;
static lean_object* l_Lake_Package_getBarrelUrl___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_Package_recComputeDeps___spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___lambda__2___closed__8;
static lean_object* l_Lake_Package_getReleaseUrl___closed__3;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseAsync(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_buildCacheFacetConfig___closed__1;
static lean_object* l_Lake_initPackageFacetConfigs___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseSync___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getReleaseUrl___closed__7;
static lean_object* l_Lake_Package_gitHubReleaseFacetConfig___closed__1;
static lean_object* l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lake_Job_mapM___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_barrelFacetConfig___elambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optReleaseFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseSync(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Package_recComputeDeps___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchBuildArchive___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_String_fromUTF8_x21___spec__1(lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_getReleaseUrl(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_optBuildCacheFacetConfig___closed__1;
static lean_object* l_Lake_Package_optBarrelFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchBuildArchive___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Task_Priority_default;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Package_recComputeDeps___spec__2(lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__1;
static lean_object* l_Lake_Package_getReleaseUrl___closed__6;
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterBuildCacheSync___spec__5(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__4;
static lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_BuildTrace_nil;
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___elambda__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
static lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___closed__3;
static lean_object* l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__1;
extern lean_object* l_Lake_defaultLakeDir;
lean_object* lean_string_from_utf8_unchecked(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchBuildArchive___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_barrelFacetConfig___elambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___lambda__1___boxed(lean_object*);
lean_object* l_Lake_untar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCache___closed__4;
extern lean_object* l_Lake_Git_defaultRemote;
LEAN_EXPORT lean_object* l_Lake_Package_releaseFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__10;
static lean_object* l_Lake_Package_recComputeDeps___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig;
lean_object* l_Lake_Job_bindM___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___lambda__2___closed__1;
static lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__5;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__4___closed__1;
uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_depsFacetConfig;
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterBuildCacheSync___spec__2(lean_object*);
lean_object* l_Lake_EquipT_lift___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterBuildCacheSync___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCache___closed__1;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__3;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__4;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_Package_getReleaseUrl___closed__5;
LEAN_EXPORT lean_object* l_Lake_EquipT_map___at_Lake_Package_recBuildExtraDepTargets___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_optBuildCacheFacetConfig___closed__3;
static lean_object* l_Lake_Package_getBarrelUrl___closed__1;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__5;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_extraDepFacetConfig___closed__2;
static lean_object* l_Lake_Package_extraDepFacetConfig___closed__3;
static lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterBuildCacheSync___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_barrelFacetConfig___elambda__1___closed__2;
static lean_object* l_Lake_Package_getReleaseUrl___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__3;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_Package_recComputeDeps___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterBuildCacheSync___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___lambda__2___closed__3;
static lean_object* l_Lake_Package_extraDepFacetConfig___closed__4;
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig;
static lean_object* l_Lake_Package_getReleaseUrl___closed__4;
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
static lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__4;
lean_object* l_Lake_uriEncode(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Package_fetchOptRelease(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instHashablePackage___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___closed__2;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__3;
static lean_object* l_Lake_Package_getReleaseUrl___closed__13;
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_fetchBuildArchive___closed__3;
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Lake_initPackageFacetConfigs___closed__4;
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseAsync___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_Package_recComputeDeps___spec__5(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_fetchBuildArchive___closed__1;
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterBuildCacheSync___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_JobAction_merge(uint8_t, uint8_t);
static lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_recBuildExtraDepTargets___closed__2;
size_t lean_usize_sub(size_t, size_t);
static lean_object* l_Lake_Package_getBarrelUrl___lambda__2___closed__13;
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___lambda__2___closed__12;
static lean_object* l_Lake_Package_recBuildExtraDepTargets___closed__4;
static lean_object* l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__6;
static lean_object* l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__1;
static lean_object* l_Lake_initPackageFacetConfigs___closed__7;
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_Package_recBuildExtraDepTargets___spec__3(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lake_Package_getReleaseUrl___closed__8;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Env_toolchain(lean_object*);
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__2;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__1;
lean_object* l_Lean_RBNode_insert___at_Lake_Workspace_addPackageFacetConfig___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCache___closed__7;
lean_object* l_Lake_instBEqPackage___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterBuildCacheSync___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__4;
static lean_object* l_Lake_Package_extraDepFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getReleaseUrl___lambda__1___closed__1;
static lean_object* l_Lake_initPackageFacetConfigs___closed__1;
static lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__3;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate_x27___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initPackageFacetConfigs___closed__6;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__8;
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getReleaseUrl___closed__14;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_optBarrelFacetConfig___closed__1;
static lean_object* l_Lake_Package_getBarrelUrl___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_recComputeDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___lambda__2___closed__14;
static lean_object* l_Lake_Package_getBarrelUrl___lambda__2___closed__6;
static lean_object* l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1___closed__1;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_EquipT_map___at_Lake_Package_recBuildExtraDepTargets___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_Package_recComputeDeps___spec__5___at_Lake_Package_recComputeDeps___spec__6(lean_object*, lean_object*);
static lean_object* l_Lake_Package_getBarrelUrl___lambda__2___closed__7;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__4;
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__6;
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Package_afterBuildCacheSync___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Reservoir_pkgApiUrl(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Package_recComputeDeps___spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_Package_recComputeDeps___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_Package_recComputeDeps___spec__5___at_Lake_Package_recComputeDeps___spec__6(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_Package_recComputeDeps___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_Package_recComputeDeps___spec__5___at_Lake_Package_recComputeDeps___spec__6(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_Package_recComputeDeps___spec__3(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_Package_recComputeDeps___spec__4(x_7, x_1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instHashablePackage___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instBEqPackage___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_23 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Package_recComputeDeps___spec__2(x_2, x_22);
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
x_37 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_Package_recComputeDeps___spec__3(x_30);
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
x_58 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Package_recComputeDeps___spec__2(x_2, x_57);
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
x_72 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_Package_recComputeDeps___spec__3(x_65);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(x_4, x_6);
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
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": package not found for dependency '", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' (this is likely a bug in Lake)", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("deps", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_37; 
x_37 = lean_usize_dec_eq(x_3, x_4);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_array_uget(x_2, x_3);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_ctor_get(x_8, 1);
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
x_46 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__1;
x_47 = l_Lean_Name_toString(x_44, x_45, x_46);
x_48 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_49 = lean_string_append(x_48, x_47);
lean_dec(x_47);
x_50 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__3;
x_51 = lean_string_append(x_49, x_50);
x_52 = l_Lean_Name_toString(x_39, x_45, x_46);
x_53 = lean_string_append(x_51, x_52);
lean_dec(x_52);
x_54 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__4;
x_55 = lean_string_append(x_53, x_54);
x_56 = 3;
x_57 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_56);
x_58 = lean_array_get_size(x_9);
x_59 = lean_array_push(x_9, x_57);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_10);
x_12 = x_61;
x_13 = x_11;
goto block_36;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_39);
x_62 = lean_ctor_get(x_42, 0);
lean_inc(x_62);
lean_dec(x_42);
x_63 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__6;
lean_inc(x_62);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
lean_inc(x_6);
lean_inc(x_8);
lean_inc(x_7);
x_65 = lean_apply_6(x_6, x_64, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_69 = !lean_is_exclusive(x_66);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_66, 0);
lean_dec(x_70);
x_71 = !lean_is_exclusive(x_67);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_67, 0);
x_73 = lean_array_get_size(x_72);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_nat_dec_lt(x_74, x_73);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_73);
lean_dec(x_72);
x_76 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(x_5, x_62);
lean_ctor_set(x_67, 0, x_76);
x_12 = x_66;
x_13 = x_68;
goto block_36;
}
else
{
uint8_t x_77; 
x_77 = lean_nat_dec_le(x_73, x_73);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_73);
lean_dec(x_72);
x_78 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(x_5, x_62);
lean_ctor_set(x_67, 0, x_78);
x_12 = x_66;
x_13 = x_68;
goto block_36;
}
else
{
size_t x_79; size_t x_80; lean_object* x_81; lean_object* x_82; 
x_79 = 0;
x_80 = lean_usize_of_nat(x_73);
lean_dec(x_73);
x_81 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__7(x_72, x_79, x_80, x_5);
lean_dec(x_72);
x_82 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(x_81, x_62);
lean_ctor_set(x_67, 0, x_82);
x_12 = x_66;
x_13 = x_68;
goto block_36;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_83 = lean_ctor_get(x_67, 0);
x_84 = lean_ctor_get(x_67, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_67);
x_85 = lean_array_get_size(x_83);
x_86 = lean_unsigned_to_nat(0u);
x_87 = lean_nat_dec_lt(x_86, x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_85);
lean_dec(x_83);
x_88 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(x_5, x_62);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_84);
lean_ctor_set(x_66, 0, x_89);
x_12 = x_66;
x_13 = x_68;
goto block_36;
}
else
{
uint8_t x_90; 
x_90 = lean_nat_dec_le(x_85, x_85);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_85);
lean_dec(x_83);
x_91 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(x_5, x_62);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_84);
lean_ctor_set(x_66, 0, x_92);
x_12 = x_66;
x_13 = x_68;
goto block_36;
}
else
{
size_t x_93; size_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = 0;
x_94 = lean_usize_of_nat(x_85);
lean_dec(x_85);
x_95 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__7(x_83, x_93, x_94, x_5);
lean_dec(x_83);
x_96 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(x_95, x_62);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_84);
lean_ctor_set(x_66, 0, x_97);
x_12 = x_66;
x_13 = x_68;
goto block_36;
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_98 = lean_ctor_get(x_66, 1);
lean_inc(x_98);
lean_dec(x_66);
x_99 = lean_ctor_get(x_67, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_67, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_101 = x_67;
} else {
 lean_dec_ref(x_67);
 x_101 = lean_box(0);
}
x_102 = lean_array_get_size(x_99);
x_103 = lean_unsigned_to_nat(0u);
x_104 = lean_nat_dec_lt(x_103, x_102);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_102);
lean_dec(x_99);
x_105 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(x_5, x_62);
if (lean_is_scalar(x_101)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_101;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_100);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_98);
x_12 = x_107;
x_13 = x_68;
goto block_36;
}
else
{
uint8_t x_108; 
x_108 = lean_nat_dec_le(x_102, x_102);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_102);
lean_dec(x_99);
x_109 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(x_5, x_62);
if (lean_is_scalar(x_101)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_101;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_100);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_98);
x_12 = x_111;
x_13 = x_68;
goto block_36;
}
else
{
size_t x_112; size_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_112 = 0;
x_113 = lean_usize_of_nat(x_102);
lean_dec(x_102);
x_114 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__7(x_99, x_112, x_113, x_5);
lean_dec(x_99);
x_115 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(x_114, x_62);
if (lean_is_scalar(x_101)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_101;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_100);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_98);
x_12 = x_117;
x_13 = x_68;
goto block_36;
}
}
}
}
else
{
lean_object* x_118; uint8_t x_119; 
lean_dec(x_62);
lean_dec(x_5);
x_118 = lean_ctor_get(x_65, 1);
lean_inc(x_118);
lean_dec(x_65);
x_119 = !lean_is_exclusive(x_66);
if (x_119 == 0)
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_ctor_get(x_66, 0);
lean_dec(x_120);
x_121 = !lean_is_exclusive(x_67);
if (x_121 == 0)
{
x_12 = x_66;
x_13 = x_118;
goto block_36;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_67, 0);
x_123 = lean_ctor_get(x_67, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_67);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
lean_ctor_set(x_66, 0, x_124);
x_12 = x_66;
x_13 = x_118;
goto block_36;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_125 = lean_ctor_get(x_66, 1);
lean_inc(x_125);
lean_dec(x_66);
x_126 = lean_ctor_get(x_67, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_67, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_128 = x_67;
} else {
 lean_dec_ref(x_67);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_125);
x_12 = x_130;
x_13 = x_118;
goto block_36;
}
}
}
else
{
uint8_t x_131; 
lean_dec(x_62);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_131 = !lean_is_exclusive(x_65);
if (x_131 == 0)
{
return x_65;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_65, 0);
x_133 = lean_ctor_get(x_65, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_65);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_5);
lean_ctor_set(x_135, 1, x_9);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_10);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_11);
return x_137;
}
block_36:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_5 = x_16;
x_9 = x_17;
x_10 = x_15;
x_11 = x_13;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_12, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_13);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_12, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_12);
lean_ctor_set(x_28, 1, x_13);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_dec(x_12);
x_30 = lean_ctor_get(x_14, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_32 = x_14;
} else {
 lean_dec_ref(x_14);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(1, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_13);
return x_35;
}
}
}
}
}
static lean_object* _init_l_Lake_Package_recComputeDeps___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recComputeDeps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lake_Package_recComputeDeps___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
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
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_9, x_9);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lake_Package_recComputeDeps___closed__1;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_6);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_23 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_24 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8(x_1, x_8, x_21, x_22, x_23, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_8);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_24, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_25, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
lean_ctor_set(x_26, 0, x_33);
return x_24;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_26, 0);
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_26);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_25, 0, x_37);
return x_24;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_25, 1);
lean_inc(x_38);
lean_dec(x_25);
x_39 = lean_ctor_get(x_26, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_26, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_41 = x_26;
} else {
 lean_dec_ref(x_26);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_38);
lean_ctor_set(x_24, 0, x_44);
return x_24;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_45 = lean_ctor_get(x_24, 1);
lean_inc(x_45);
lean_dec(x_24);
x_46 = lean_ctor_get(x_25, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_47 = x_25;
} else {
 lean_dec_ref(x_25);
 x_47 = lean_box(0);
}
x_48 = lean_ctor_get(x_26, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_50 = x_26;
} else {
 lean_dec_ref(x_26);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
if (lean_is_scalar(x_47)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_47;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_46);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_45);
return x_54;
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_24);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_24, 0);
lean_dec(x_56);
x_57 = !lean_is_exclusive(x_25);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_25, 0);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_26);
if (x_59 == 0)
{
return x_24;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_26, 0);
x_61 = lean_ctor_get(x_26, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_26);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_25, 0, x_62);
return x_24;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_25, 1);
lean_inc(x_63);
lean_dec(x_25);
x_64 = lean_ctor_get(x_26, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_26, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_66 = x_26;
} else {
 lean_dec_ref(x_26);
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
lean_ctor_set(x_24, 0, x_68);
return x_24;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_69 = lean_ctor_get(x_24, 1);
lean_inc(x_69);
lean_dec(x_24);
x_70 = lean_ctor_get(x_25, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_71 = x_25;
} else {
 lean_dec_ref(x_25);
 x_71 = lean_box(0);
}
x_72 = lean_ctor_get(x_26, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_26, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_74 = x_26;
} else {
 lean_dec_ref(x_26);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
if (lean_is_scalar(x_71)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_71;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_70);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_69);
return x_77;
}
}
}
else
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_24);
if (x_78 == 0)
{
return x_24;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_24, 0);
x_80 = lean_ctor_get(x_24, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_24);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Package_recComputeDeps___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Package_recComputeDeps___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__7(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
static lean_object* _init_l_Lake_Package_depsFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_recComputeDeps), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_depsFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_depsFacetConfig___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_depsFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_depsFacetConfig___closed__2;
return x_1;
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
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_1 = lean_alloc_closure((void*)(l___private_Lake_Build_Job_0__Lake_Job_toOpaqueImpl___rarg___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_optBuildCacheFacetConfig___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optCache", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_optBuildCacheFacetConfig___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_optBuildCacheFacetConfig___elambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_optBuildCacheFacetConfig___closed__5;
x_2 = l_Lake_Package_optBuildCacheFacetConfig___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_optBuildCacheFacetConfig___closed__6;
return x_1;
}
}
static lean_object* _init_l_Lake_Package_maybeFetchBuildCache___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_maybeFetchBuildCache___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Package_maybeFetchBuildCache___closed__1;
x_2 = 0;
x_3 = l_Lake_BuildTrace_nil;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_maybeFetchBuildCache___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lake_Package_maybeFetchBuildCache___closed__2;
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_maybeFetchBuildCache___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_maybeFetchBuildCache___closed__3;
x_2 = lean_task_pure(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_maybeFetchBuildCache___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lake_Package_maybeFetchBuildCache___closed__4;
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_maybeFetchBuildCache___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("leanprover", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_maybeFetchBuildCache___closed__7() {
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
lean_object* x_8; lean_object* x_9; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_4, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_ctor_get_uint8(x_63, sizeof(void*)*11);
lean_dec(x_63);
if (x_64 == 0)
{
uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = 1;
x_66 = lean_box(x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_5);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_6);
x_8 = x_68;
x_9 = x_7;
goto block_61;
}
else
{
uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = 0;
x_70 = lean_box(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_5);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_6);
x_8 = x_72;
x_9 = x_7;
goto block_61;
}
block_61:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_30; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_12 = x_8;
} else {
 lean_dec_ref(x_8);
 x_12 = lean_box(0);
}
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_15 = x_10;
} else {
 lean_dec_ref(x_10);
 x_15 = lean_box(0);
}
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 8);
lean_inc(x_18);
x_19 = l_System_FilePath_join(x_16, x_18);
lean_dec(x_18);
x_20 = l_System_FilePath_pathExists(x_19, x_9);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_23 = x_20;
} else {
 lean_dec_ref(x_20);
 x_23 = lean_box(0);
}
x_30 = lean_unbox(x_13);
lean_dec(x_13);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_box(0);
x_24 = x_31;
goto block_29;
}
else
{
uint8_t x_32; 
x_32 = lean_unbox(x_21);
lean_dec(x_21);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = lean_ctor_get_uint8(x_17, sizeof(void*)*29 + 1);
lean_dec(x_17);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_4, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lake_Env_toolchain(x_35);
lean_dec(x_35);
x_37 = lean_ctor_get(x_1, 5);
lean_inc(x_37);
x_38 = l_Lake_Package_maybeFetchBuildCache___closed__6;
x_39 = lean_string_dec_eq(x_37, x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = l_Lake_Package_maybeFetchBuildCache___closed__7;
x_41 = lean_string_dec_eq(x_37, x_40);
lean_dec(x_37);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_36);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = lean_box(0);
x_24 = x_42;
goto block_29;
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_string_utf8_byte_size(x_36);
lean_dec(x_36);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_nat_dec_eq(x_43, x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_12);
x_46 = l_Lake_Package_optBuildCacheFacetConfig___closed__4;
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_apply_6(x_2, x_47, x_3, x_4, x_14, x_11, x_22);
return x_48;
}
else
{
lean_object* x_49; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_box(0);
x_24 = x_49;
goto block_29;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_37);
x_50 = lean_string_utf8_byte_size(x_36);
lean_dec(x_36);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_nat_dec_eq(x_50, x_51);
lean_dec(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_12);
x_53 = l_Lake_Package_optBuildCacheFacetConfig___closed__4;
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_1);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_apply_6(x_2, x_54, x_3, x_4, x_14, x_11, x_22);
return x_55;
}
else
{
lean_object* x_56; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = lean_box(0);
x_24 = x_56;
goto block_29;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_12);
x_57 = l_Lake_Package_optBuildCacheFacetConfig___closed__4;
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_1);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_apply_6(x_2, x_58, x_3, x_4, x_14, x_11, x_22);
return x_59;
}
}
else
{
lean_object* x_60; 
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = lean_box(0);
x_24 = x_60;
goto block_29;
}
}
block_29:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_24);
x_25 = l_Lake_Package_maybeFetchBuildCache___closed__5;
if (lean_is_scalar(x_15)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_15;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_14);
if (lean_is_scalar(x_12)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_12;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_11);
if (lean_is_scalar(x_23)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_23;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_22);
return x_28;
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_dec(x_1);
x_10 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__1;
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
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_dec(x_13);
x_15 = 1;
x_16 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__1;
x_17 = l_Lean_Name_toString(x_14, x_15, x_16);
x_18 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__2;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_21 = lean_string_append(x_19, x_20);
x_22 = l_Lean_Name_toString(x_2, x_15, x_16);
x_23 = lean_string_append(x_21, x_22);
lean_dec(x_22);
x_24 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__4;
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
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
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
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
x_3 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__1;
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
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
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
x_3 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__1;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (x_2 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*29 + 1);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 3);
x_10 = 2;
x_11 = l_Lake_instDecidableEqVerbosity(x_9, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__4;
x_15 = lean_array_push(x_13, x_14);
lean_ctor_set(x_4, 0, x_15);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
lean_inc(x_19);
lean_dec(x_4);
x_22 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__4;
x_23 = lean_array_push(x_19, x_22);
x_24 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_5);
return x_27;
}
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; uint8_t x_46; 
x_28 = lean_ctor_get(x_6, 2);
lean_inc(x_28);
lean_dec(x_6);
x_29 = 1;
x_30 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__1;
x_31 = l_Lean_Name_toString(x_28, x_29, x_30);
x_32 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__2;
x_33 = lean_string_append(x_32, x_31);
lean_dec(x_31);
x_34 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_35 = lean_string_append(x_33, x_34);
x_36 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__5;
x_37 = lean_string_append(x_35, x_36);
x_38 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__4;
x_39 = lean_string_append(x_37, x_38);
x_40 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__1;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_42 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_43 = lean_string_append(x_41, x_42);
x_44 = 0;
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_44);
x_46 = !lean_is_exclusive(x_4);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_4, 0);
x_48 = lean_array_push(x_47, x_45);
lean_ctor_set(x_4, 0, x_48);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_4);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_5);
return x_51;
}
else
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_4, 0);
x_53 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_54 = lean_ctor_get(x_4, 1);
lean_inc(x_54);
lean_inc(x_52);
lean_dec(x_4);
x_55 = lean_array_push(x_52, x_45);
x_56 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*2, x_53);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_5);
return x_59;
}
}
}
else
{
lean_object* x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_3, 0);
x_61 = lean_ctor_get_uint8(x_60, sizeof(void*)*1 + 3);
x_62 = 2;
x_63 = l_Lake_instDecidableEqVerbosity(x_61, x_62);
if (x_63 == 0)
{
uint8_t x_64; 
lean_dec(x_6);
x_64 = !lean_is_exclusive(x_4);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_4, 0);
x_66 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__9;
x_67 = lean_array_push(x_65, x_66);
lean_ctor_set(x_4, 0, x_67);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_4);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_5);
return x_70;
}
else
{
lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_71 = lean_ctor_get(x_4, 0);
x_72 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_73 = lean_ctor_get(x_4, 1);
lean_inc(x_73);
lean_inc(x_71);
lean_dec(x_4);
x_74 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__9;
x_75 = lean_array_push(x_71, x_74);
x_76 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
lean_ctor_set_uint8(x_76, sizeof(void*)*2, x_72);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_5);
return x_79;
}
}
else
{
lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; uint8_t x_98; 
x_80 = lean_ctor_get(x_6, 2);
lean_inc(x_80);
lean_dec(x_6);
x_81 = 1;
x_82 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__1;
x_83 = l_Lean_Name_toString(x_80, x_81, x_82);
x_84 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__2;
x_85 = lean_string_append(x_84, x_83);
lean_dec(x_83);
x_86 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_87 = lean_string_append(x_85, x_86);
x_88 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__10;
x_89 = lean_string_append(x_87, x_88);
x_90 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__4;
x_91 = lean_string_append(x_89, x_90);
x_92 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__6;
x_93 = lean_string_append(x_92, x_91);
lean_dec(x_91);
x_94 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_95 = lean_string_append(x_93, x_94);
x_96 = 2;
x_97 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set_uint8(x_97, sizeof(void*)*1, x_96);
x_98 = !lean_is_exclusive(x_4);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_4, 0);
x_100 = lean_array_push(x_99, x_97);
lean_ctor_set(x_4, 0, x_100);
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_4);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_5);
return x_103;
}
else
{
lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_104 = lean_ctor_get(x_4, 0);
x_105 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_106 = lean_ctor_get(x_4, 1);
lean_inc(x_106);
lean_inc(x_104);
lean_dec(x_4);
x_107 = lean_array_push(x_104, x_97);
x_108 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
lean_ctor_set_uint8(x_108, sizeof(void*)*2, x_105);
x_109 = lean_box(0);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_5);
return x_111;
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_1);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_4);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_5);
return x_114;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_4);
lean_inc(x_1);
x_8 = l_Lake_Package_maybeFetchBuildCache(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_9, 1);
x_14 = lean_ctor_get(x_9, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
x_18 = lean_alloc_closure((void*)(l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___boxed), 5, 1);
lean_closure_set(x_18, 0, x_1);
x_19 = l_Task_Priority_default;
x_20 = 0;
x_21 = l_Lake_BuildTrace_nil;
x_22 = l_Lake_Job_mapM___rarg(x_16, x_18, x_19, x_20, x_4, x_21, x_11);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_ctor_set(x_10, 0, x_24);
lean_ctor_set(x_22, 0, x_9);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_22);
lean_ctor_set(x_10, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_9);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_free_object(x_10);
lean_dec(x_17);
lean_free_object(x_9);
lean_dec(x_13);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
return x_22;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_22, 0);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_22);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_10, 0);
x_33 = lean_ctor_get(x_10, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_10);
x_34 = lean_alloc_closure((void*)(l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___boxed), 5, 1);
lean_closure_set(x_34, 0, x_1);
x_35 = l_Task_Priority_default;
x_36 = 0;
x_37 = l_Lake_BuildTrace_nil;
x_38 = l_Lake_Job_mapM___rarg(x_32, x_34, x_35, x_36, x_4, x_37, x_11);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
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
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_33);
lean_ctor_set(x_9, 0, x_42);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_9);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_33);
lean_free_object(x_9);
lean_dec(x_13);
x_44 = lean_ctor_get(x_38, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_46 = x_38;
} else {
 lean_dec_ref(x_38);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; 
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
x_52 = lean_alloc_closure((void*)(l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___boxed), 5, 1);
lean_closure_set(x_52, 0, x_1);
x_53 = l_Task_Priority_default;
x_54 = 0;
x_55 = l_Lake_BuildTrace_nil;
x_56 = l_Lake_Job_mapM___rarg(x_49, x_52, x_53, x_54, x_4, x_55, x_11);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
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
if (lean_is_scalar(x_51)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_51;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_50);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_48);
if (lean_is_scalar(x_59)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_59;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_58);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_48);
x_63 = lean_ctor_get(x_56, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_56, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_65 = x_56;
} else {
 lean_dec_ref(x_56);
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
uint8_t x_67; 
lean_dec(x_4);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_8);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_8, 0);
lean_dec(x_68);
x_69 = !lean_is_exclusive(x_9);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_9, 0);
lean_dec(x_70);
x_71 = !lean_is_exclusive(x_10);
if (x_71 == 0)
{
return x_8;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_10, 0);
x_73 = lean_ctor_get(x_10, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_10);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_9, 0, x_74);
return x_8;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_9, 1);
lean_inc(x_75);
lean_dec(x_9);
x_76 = lean_ctor_get(x_10, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_10, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_78 = x_10;
} else {
 lean_dec_ref(x_10);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_75);
lean_ctor_set(x_8, 0, x_80);
return x_8;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_81 = lean_ctor_get(x_8, 1);
lean_inc(x_81);
lean_dec(x_8);
x_82 = lean_ctor_get(x_9, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_83 = x_9;
} else {
 lean_dec_ref(x_9);
 x_83 = lean_box(0);
}
x_84 = lean_ctor_get(x_10, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_10, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_86 = x_10;
} else {
 lean_dec_ref(x_10);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
if (lean_is_scalar(x_83)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_83;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_82);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_81);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_4);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_8);
if (x_90 == 0)
{
return x_8;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_8, 0);
x_92 = lean_ctor_get(x_8, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_8);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_3);
return x_7;
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
LEAN_EXPORT lean_object* l_Lake_EquipT_map___at_Lake_Package_recBuildExtraDepTargets___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_apply_1(x_1, x_17);
lean_ctor_set(x_11, 0, x_18);
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_apply_1(x_1, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_10, 0, x_22);
return x_9;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_26 = x_11;
} else {
 lean_dec_ref(x_11);
 x_26 = lean_box(0);
}
x_27 = lean_apply_1(x_1, x_24);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_23);
lean_ctor_set(x_9, 0, x_29);
return x_9;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
lean_dec(x_9);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_32 = x_10;
} else {
 lean_dec_ref(x_10);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get(x_11, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_35 = x_11;
} else {
 lean_dec_ref(x_11);
 x_35 = lean_box(0);
}
x_36 = lean_apply_1(x_1, x_33);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
if (lean_is_scalar(x_32)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_32;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_31);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_30);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_9);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_9, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_10);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_10, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_11);
if (x_44 == 0)
{
return x_9;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_11, 0);
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_11);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_10, 0, x_47);
return x_9;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_10, 1);
lean_inc(x_48);
lean_dec(x_10);
x_49 = lean_ctor_get(x_11, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_11, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_51 = x_11;
} else {
 lean_dec_ref(x_11);
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
lean_ctor_set(x_9, 0, x_53);
return x_9;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_54 = lean_ctor_get(x_9, 1);
lean_inc(x_54);
lean_dec(x_9);
x_55 = lean_ctor_get(x_10, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_56 = x_10;
} else {
 lean_dec_ref(x_10);
 x_56 = lean_box(0);
}
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
if (lean_is_scalar(x_56)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_56;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_55);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_54);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_9);
if (x_63 == 0)
{
return x_9;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_9, 0);
x_65 = lean_ctor_get(x_9, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_9);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EquipT_map___at_Lake_Package_recBuildExtraDepTargets___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_EquipT_map___at_Lake_Package_recBuildExtraDepTargets___spec__1___rarg), 8, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_57; 
x_57 = lean_usize_dec_lt(x_6, x_5);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_7);
lean_ctor_set(x_58, 1, x_11);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_12);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_13);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_array_uget(x_4, x_6);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_62 = l_Lake_Package_fetchTargetJob(x_1, x_61, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = !lean_is_exclusive(x_63);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_63, 0);
lean_dec(x_67);
x_68 = !lean_is_exclusive(x_64);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_64, 0);
x_70 = l_Lake_Job_mix___rarg(x_7, x_69);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_64, 0, x_71);
x_14 = x_63;
x_15 = x_65;
goto block_56;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_64, 0);
x_73 = lean_ctor_get(x_64, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_64);
x_74 = l_Lake_Job_mix___rarg(x_7, x_72);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
lean_ctor_set(x_63, 0, x_76);
x_14 = x_63;
x_15 = x_65;
goto block_56;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_77 = lean_ctor_get(x_63, 1);
lean_inc(x_77);
lean_dec(x_63);
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
x_81 = l_Lake_Job_mix___rarg(x_7, x_78);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
if (lean_is_scalar(x_80)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_80;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_79);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_77);
x_14 = x_84;
x_15 = x_65;
goto block_56;
}
}
else
{
lean_object* x_85; uint8_t x_86; 
lean_dec(x_7);
x_85 = lean_ctor_get(x_62, 1);
lean_inc(x_85);
lean_dec(x_62);
x_86 = !lean_is_exclusive(x_63);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_63, 0);
lean_dec(x_87);
x_88 = !lean_is_exclusive(x_64);
if (x_88 == 0)
{
x_14 = x_63;
x_15 = x_85;
goto block_56;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_64, 0);
x_90 = lean_ctor_get(x_64, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_64);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_63, 0, x_91);
x_14 = x_63;
x_15 = x_85;
goto block_56;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_92 = lean_ctor_get(x_63, 1);
lean_inc(x_92);
lean_dec(x_63);
x_93 = lean_ctor_get(x_64, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_64, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_95 = x_64;
} else {
 lean_dec_ref(x_64);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_92);
x_14 = x_97;
x_15 = x_85;
goto block_56;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_62);
if (x_98 == 0)
{
return x_62;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_62, 0);
x_100 = lean_ctor_get(x_62, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_62);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
block_56:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_14, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
lean_ctor_set(x_16, 0, x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_15);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_14, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_15);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_30 = x_16;
} else {
 lean_dec_ref(x_16);
 x_30 = lean_box(0);
}
x_31 = lean_ctor_get(x_17, 0);
lean_inc(x_31);
lean_dec(x_17);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_15);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; 
x_35 = lean_ctor_get(x_14, 1);
lean_inc(x_35);
lean_dec(x_14);
x_36 = lean_ctor_get(x_16, 1);
lean_inc(x_36);
lean_dec(x_16);
x_37 = lean_ctor_get(x_17, 0);
lean_inc(x_37);
lean_dec(x_17);
x_38 = 1;
x_39 = lean_usize_add(x_6, x_38);
x_6 = x_39;
x_7 = x_37;
x_11 = x_36;
x_12 = x_35;
x_13 = x_15;
goto _start;
}
}
else
{
uint8_t x_41; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_14);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_14, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_16);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_14);
lean_ctor_set(x_44, 1, x_15);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_16, 0);
x_46 = lean_ctor_get(x_16, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_16);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_14, 0, x_47);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_14);
lean_ctor_set(x_48, 1, x_15);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_14, 1);
lean_inc(x_49);
lean_dec(x_14);
x_50 = lean_ctor_get(x_16, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_16, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_52 = x_16;
} else {
 lean_dec_ref(x_16);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_49);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_15);
return x_55;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_Package_recBuildExtraDepTargets___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
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
x_16 = lean_apply_7(x_2, x_14, x_3, x_4, x_5, x_15, x_13, x_12);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_9, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_10, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_10, 0, x_24);
return x_9;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_dec(x_10);
x_26 = lean_ctor_get(x_11, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_28 = x_11;
} else {
 lean_dec_ref(x_11);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(1, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
lean_ctor_set(x_9, 0, x_30);
return x_9;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
lean_dec(x_9);
x_32 = lean_ctor_get(x_10, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_33 = x_10;
} else {
 lean_dec_ref(x_10);
 x_33 = lean_box(0);
}
x_34 = lean_ctor_get(x_11, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_36 = x_11;
} else {
 lean_dec_ref(x_11);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
if (lean_is_scalar(x_33)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_33;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_32);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_31);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_9);
if (x_40 == 0)
{
return x_9;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_9, 0);
x_42 = lean_ctor_get(x_9, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_9);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_Package_recBuildExtraDepTargets___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Package_recBuildExtraDepTargets___spec__3___rarg), 8, 0);
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
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
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
x_15 = l_Array_forIn_x27Unsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__2(x_2, x_11, x_12, x_11, x_13, x_14, x_3, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_16, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_16, 0, x_25);
return x_15;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_29 = x_17;
} else {
 lean_dec_ref(x_17);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
lean_ctor_set(x_15, 0, x_31);
return x_15;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_dec(x_15);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_34 = x_16;
} else {
 lean_dec_ref(x_16);
 x_34 = lean_box(0);
}
x_35 = lean_ctor_get(x_17, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_17, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_37 = x_17;
} else {
 lean_dec_ref(x_17);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
if (lean_is_scalar(x_34)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_34;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_33);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_32);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_15);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_15, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_16);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_16, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_17);
if (x_45 == 0)
{
return x_15;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_17, 0);
x_47 = lean_ctor_get(x_17, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_17);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_16, 0, x_48);
return x_15;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_16, 1);
lean_inc(x_49);
lean_dec(x_16);
x_50 = lean_ctor_get(x_17, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_17, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_52 = x_17;
} else {
 lean_dec_ref(x_17);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_49);
lean_ctor_set(x_15, 0, x_54);
return x_15;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_55 = lean_ctor_get(x_15, 1);
lean_inc(x_55);
lean_dec(x_15);
x_56 = lean_ctor_get(x_16, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_57 = x_16;
} else {
 lean_dec_ref(x_16);
 x_57 = lean_box(0);
}
x_58 = lean_ctor_get(x_17, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_17, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_60 = x_17;
} else {
 lean_dec_ref(x_17);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
if (lean_is_scalar(x_57)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_57;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_56);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_55);
return x_63;
}
}
}
else
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_15);
if (x_64 == 0)
{
return x_15;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_15, 0);
x_66 = lean_ctor_get(x_15, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_15);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_maybeFetchBuildCache___closed__2;
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
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
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
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_19 = l_Lake_Package_maybeFetchBuildCacheWithWarning(x_2, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
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
x_26 = l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__3;
x_27 = l_Lake_Job_add___rarg(x_26, x_24);
x_28 = lean_box(0);
x_29 = l_Lake_Package_recBuildExtraDepTargets___lambda__3(x_1, x_2, x_27, x_28, x_5, x_6, x_7, x_25, x_23, x_22);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_19);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_19, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_20, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_21);
if (x_34 == 0)
{
return x_19;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_21, 0);
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_21);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_20, 0, x_37);
return x_19;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_20, 1);
lean_inc(x_38);
lean_dec(x_20);
x_39 = lean_ctor_get(x_21, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_41 = x_21;
} else {
 lean_dec_ref(x_21);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_38);
lean_ctor_set(x_19, 0, x_43);
return x_19;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_19, 1);
lean_inc(x_44);
lean_dec(x_19);
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_46 = x_20;
} else {
 lean_dec_ref(x_20);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_21, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_21, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_49 = x_21;
} else {
 lean_dec_ref(x_21);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
if (lean_is_scalar(x_46)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_46;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_45);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_44);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_19);
if (x_53 == 0)
{
return x_19;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_19, 0);
x_55 = lean_ctor_get(x_19, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_19);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
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
x_1 = lean_alloc_closure((void*)(l_Lake_Package_recBuildExtraDepTargets___lambda__2___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_recBuildExtraDepTargets___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_recBuildExtraDepTargets___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
x_10 = 1;
x_11 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__1;
lean_inc(x_9);
x_12 = l_Lean_Name_toString(x_9, x_10, x_11);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_Lake_Package_recBuildExtraDepTargets___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lake_Package_recBuildExtraDepTargets___closed__4;
x_18 = l_Lake_Package_recBuildExtraDepTargets___closed__3;
x_19 = lean_alloc_closure((void*)(l_Lake_EquipT_map___at_Lake_Package_recBuildExtraDepTargets___spec__1___rarg), 8, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lake_Package_recBuildExtraDepTargets___lambda__4___boxed), 10, 3);
lean_closure_set(x_20, 0, x_8);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_9);
x_21 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Package_recBuildExtraDepTargets___spec__3___rarg), 8, 2);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_20);
x_22 = 0;
x_23 = l_Lake_withRegisterJob___rarg(x_16, x_21, x_22, x_2, x_3, x_4, x_5, x_6, x_7);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__2(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Package_recBuildExtraDepTargets___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_extraDepFacetConfig___closed__3;
x_2 = l_Lake_Package_optBuildCacheFacetConfig___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_extraDepFacetConfig___closed__4;
return x_1;
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
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_9 = lean_string_append(x_8, x_3);
x_10 = l_Lake_Package_getBarrelUrl___lambda__1___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_1);
x_13 = l_Lake_Package_getBarrelUrl___lambda__1___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_Lake_Env_toolchain(x_2);
x_16 = l_Lake_uriEncode(x_15);
lean_dec(x_15);
x_17 = lean_string_append(x_14, x_16);
lean_dec(x_16);
x_18 = lean_string_append(x_17, x_8);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_6);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
return x_20;
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
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 5);
lean_inc(x_8);
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_6);
x_14 = l_Lake_Package_getBarrelUrl___lambda__2___closed__10;
x_15 = l_Lake_Package_getBarrelUrl___lambda__2___closed__11;
x_16 = l_Lake_Package_getBarrelUrl___lambda__2___closed__9;
x_17 = l_Lake_Package_maybeFetchBuildCache___closed__1;
x_18 = 0;
x_19 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_13);
lean_ctor_set(x_19, 4, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*5, x_18);
x_20 = l_Lake_captureProc_x3f(x_19, x_5);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec(x_7);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_array_get_size(x_10);
x_25 = l_Lake_Package_getBarrelUrl___lambda__2___closed__13;
x_26 = lean_array_push(x_10, x_25);
lean_ctor_set(x_4, 0, x_26);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_4);
lean_ctor_set(x_20, 0, x_27);
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_array_get_size(x_10);
x_30 = l_Lake_Package_getBarrelUrl___lambda__2___closed__13;
x_31 = lean_array_push(x_10, x_30);
lean_ctor_set(x_4, 0, x_31);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_4);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_35 = lean_ctor_get(x_20, 1);
x_36 = lean_ctor_get(x_20, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_21, 0);
lean_inc(x_37);
lean_dec(x_21);
lean_inc(x_12);
lean_inc(x_10);
x_38 = lean_ctor_get(x_7, 2);
lean_inc(x_38);
lean_dec(x_7);
x_39 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__1;
x_40 = l_Lean_Name_toString(x_38, x_18, x_39);
x_41 = lean_ctor_get(x_3, 1);
x_42 = lean_ctor_get(x_41, 1);
x_43 = l_Lake_Reservoir_pkgApiUrl(x_42, x_8, x_40);
lean_dec(x_40);
lean_dec(x_8);
x_44 = l_Lake_Env_toolchain(x_42);
x_45 = lean_string_utf8_byte_size(x_44);
lean_dec(x_44);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_nat_dec_eq(x_45, x_46);
lean_dec(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_free_object(x_20);
lean_dec(x_12);
lean_dec(x_10);
x_48 = lean_box(0);
x_49 = l_Lake_Package_getBarrelUrl___lambda__1(x_37, x_42, x_43, x_48, x_3, x_4, x_35);
lean_dec(x_43);
lean_dec(x_37);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_43);
lean_dec(x_4);
lean_dec(x_37);
x_50 = lean_array_get_size(x_10);
x_51 = l_Lake_Package_getBarrelUrl___lambda__2___closed__15;
x_52 = lean_array_push(x_10, x_51);
x_53 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_12);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_11);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_20, 0, x_54);
return x_20;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_55 = lean_ctor_get(x_20, 1);
lean_inc(x_55);
lean_dec(x_20);
x_56 = lean_ctor_get(x_21, 0);
lean_inc(x_56);
lean_dec(x_21);
lean_inc(x_12);
lean_inc(x_10);
x_57 = lean_ctor_get(x_7, 2);
lean_inc(x_57);
lean_dec(x_7);
x_58 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__1;
x_59 = l_Lean_Name_toString(x_57, x_18, x_58);
x_60 = lean_ctor_get(x_3, 1);
x_61 = lean_ctor_get(x_60, 1);
x_62 = l_Lake_Reservoir_pkgApiUrl(x_61, x_8, x_59);
lean_dec(x_59);
lean_dec(x_8);
x_63 = l_Lake_Env_toolchain(x_61);
x_64 = lean_string_utf8_byte_size(x_63);
lean_dec(x_63);
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_nat_dec_eq(x_64, x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_12);
lean_dec(x_10);
x_67 = lean_box(0);
x_68 = l_Lake_Package_getBarrelUrl___lambda__1(x_56, x_61, x_62, x_67, x_3, x_4, x_55);
lean_dec(x_62);
lean_dec(x_56);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_62);
lean_dec(x_4);
lean_dec(x_56);
x_69 = lean_array_get_size(x_10);
x_70 = l_Lake_Package_getBarrelUrl___lambda__2___closed__15;
x_71 = lean_array_push(x_10, x_70);
x_72 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_12);
lean_ctor_set_uint8(x_72, sizeof(void*)*2, x_11);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_55);
return x_74;
}
}
}
}
else
{
lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_75 = lean_ctor_get(x_4, 0);
x_76 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_77 = lean_ctor_get(x_4, 1);
lean_inc(x_77);
lean_inc(x_75);
lean_dec(x_4);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_6);
x_79 = l_Lake_Package_getBarrelUrl___lambda__2___closed__10;
x_80 = l_Lake_Package_getBarrelUrl___lambda__2___closed__11;
x_81 = l_Lake_Package_getBarrelUrl___lambda__2___closed__9;
x_82 = l_Lake_Package_maybeFetchBuildCache___closed__1;
x_83 = 0;
x_84 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_80);
lean_ctor_set(x_84, 2, x_81);
lean_ctor_set(x_84, 3, x_78);
lean_ctor_set(x_84, 4, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*5, x_83);
x_85 = l_Lake_captureProc_x3f(x_84, x_5);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_8);
lean_dec(x_7);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_88 = x_85;
} else {
 lean_dec_ref(x_85);
 x_88 = lean_box(0);
}
x_89 = lean_array_get_size(x_75);
x_90 = l_Lake_Package_getBarrelUrl___lambda__2___closed__13;
x_91 = lean_array_push(x_75, x_90);
x_92 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_77);
lean_ctor_set_uint8(x_92, sizeof(void*)*2, x_76);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_89);
lean_ctor_set(x_93, 1, x_92);
if (lean_is_scalar(x_88)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_88;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_87);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_95 = lean_ctor_get(x_85, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_96 = x_85;
} else {
 lean_dec_ref(x_85);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_86, 0);
lean_inc(x_97);
lean_dec(x_86);
lean_inc(x_77);
lean_inc(x_75);
x_98 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_98, 0, x_75);
lean_ctor_set(x_98, 1, x_77);
lean_ctor_set_uint8(x_98, sizeof(void*)*2, x_76);
x_99 = lean_ctor_get(x_7, 2);
lean_inc(x_99);
lean_dec(x_7);
x_100 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__1;
x_101 = l_Lean_Name_toString(x_99, x_83, x_100);
x_102 = lean_ctor_get(x_3, 1);
x_103 = lean_ctor_get(x_102, 1);
x_104 = l_Lake_Reservoir_pkgApiUrl(x_103, x_8, x_101);
lean_dec(x_101);
lean_dec(x_8);
x_105 = l_Lake_Env_toolchain(x_103);
x_106 = lean_string_utf8_byte_size(x_105);
lean_dec(x_105);
x_107 = lean_unsigned_to_nat(0u);
x_108 = lean_nat_dec_eq(x_106, x_107);
lean_dec(x_106);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_96);
lean_dec(x_77);
lean_dec(x_75);
x_109 = lean_box(0);
x_110 = l_Lake_Package_getBarrelUrl___lambda__1(x_97, x_103, x_104, x_109, x_3, x_98, x_95);
lean_dec(x_104);
lean_dec(x_97);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_104);
lean_dec(x_98);
lean_dec(x_97);
x_111 = lean_array_get_size(x_75);
x_112 = l_Lake_Package_getBarrelUrl___lambda__2___closed__15;
x_113 = lean_array_push(x_75, x_112);
x_114 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_77);
lean_ctor_set_uint8(x_114, sizeof(void*)*2, x_76);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_111);
lean_ctor_set(x_115, 1, x_114);
if (lean_is_scalar(x_96)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_96;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_95);
return x_116;
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
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 5);
lean_inc(x_5);
x_6 = lean_string_utf8_byte_size(x_5);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lake_Package_getBarrelUrl___lambda__2(x_1, x_9, x_2, x_3, x_4);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_array_get_size(x_12);
x_14 = l_Lake_Package_getBarrelUrl___closed__2;
x_15 = lean_array_push(x_12, x_14);
lean_ctor_set(x_3, 0, x_15);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_3);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
lean_inc(x_18);
lean_dec(x_3);
x_21 = lean_array_get_size(x_18);
x_22 = l_Lake_Package_getBarrelUrl___closed__2;
x_23 = lean_array_push(x_18, x_22);
x_24 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_19);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_4);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Package_getBarrelUrl___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Package_getBarrelUrl___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Package_getBarrelUrl(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
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
LEAN_EXPORT lean_object* l_Lake_Package_getReleaseUrl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = l_Lake_Package_getReleaseUrl___lambda__1___closed__1;
x_6 = lean_string_append(x_5, x_1);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_8 = lean_string_append(x_6, x_7);
x_9 = 3;
x_10 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_9);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_array_get_size(x_12);
x_14 = lean_array_push(x_12, x_10);
lean_ctor_set(x_3, 0, x_14);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_3);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
lean_inc(x_17);
lean_dec(x_3);
x_20 = lean_array_get_size(x_17);
x_21 = lean_array_push(x_17, x_10);
x_22 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_18);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_4);
return x_24;
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
x_1 = lean_alloc_closure((void*)(l_Lake_Package_getReleaseUrl___lambda__1___boxed), 4, 0);
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
LEAN_EXPORT lean_object* l_Lake_Package_getReleaseUrl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 6);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_6, 14);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_12 = x_3;
} else {
 lean_dec_ref(x_3);
 x_12 = lean_box(0);
}
x_13 = l_Lake_Git_defaultRemote;
lean_inc(x_5);
x_14 = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(x_13, x_5, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_6, 13);
lean_inc(x_137);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_138 = lean_string_utf8_byte_size(x_7);
x_139 = lean_unsigned_to_nat(0u);
x_140 = lean_nat_dec_eq(x_138, x_139);
lean_dec(x_138);
if (x_140 == 0)
{
lean_object* x_141; 
lean_dec(x_7);
x_141 = lean_box(0);
x_15 = x_141;
goto block_136;
}
else
{
lean_object* x_142; 
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_7);
x_15 = x_142;
goto block_136;
}
}
else
{
uint8_t x_143; 
lean_dec(x_7);
x_143 = !lean_is_exclusive(x_137);
if (x_143 == 0)
{
x_15 = x_137;
goto block_136;
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_137, 0);
lean_inc(x_144);
lean_dec(x_137);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_144);
x_15 = x_145;
goto block_136;
}
}
}
else
{
uint8_t x_146; 
lean_dec(x_7);
x_146 = !lean_is_exclusive(x_8);
if (x_146 == 0)
{
x_15 = x_8;
goto block_136;
}
else
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_8, 0);
lean_inc(x_147);
lean_dec(x_8);
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_147);
x_15 = x_148;
goto block_136;
}
}
block_136:
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
if (lean_obj_tag(x_15) == 0)
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_76 = lean_array_get_size(x_9);
x_77 = l_Lake_Package_getReleaseUrl___closed__14;
x_78 = lean_array_push(x_9, x_77);
x_79 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_11);
lean_ctor_set_uint8(x_79, sizeof(void*)*2, x_10);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set(x_14, 0, x_80);
return x_14;
}
else
{
lean_object* x_81; 
lean_free_object(x_14);
x_81 = lean_ctor_get(x_17, 0);
lean_inc(x_81);
lean_dec(x_17);
x_19 = x_81;
goto block_75;
}
}
else
{
lean_object* x_82; 
lean_free_object(x_14);
lean_dec(x_17);
x_82 = lean_ctor_get(x_15, 0);
lean_inc(x_82);
lean_dec(x_15);
x_19 = x_82;
goto block_75;
}
block_75:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_5);
x_21 = l_Lake_Package_getBarrelUrl___lambda__2___closed__10;
x_22 = l_Lake_Package_getBarrelUrl___lambda__2___closed__11;
x_23 = l_Lake_Package_getReleaseUrl___closed__7;
x_24 = l_Lake_Package_maybeFetchBuildCache___closed__1;
x_25 = 0;
lean_inc(x_20);
x_26 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_26, 2, x_23);
lean_ctor_set(x_26, 3, x_20);
lean_ctor_set(x_26, 4, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*5, x_25);
x_27 = l_Lake_captureProc_x3f(x_26, x_18);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_19);
lean_dec(x_6);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lake_Package_getReleaseUrl___closed__8;
x_31 = l_Lake_Package_getBarrelUrl___lambda__2___closed__9;
x_32 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_32, 0, x_21);
lean_ctor_set(x_32, 1, x_22);
lean_ctor_set(x_32, 2, x_31);
lean_ctor_set(x_32, 3, x_20);
lean_ctor_set(x_32, 4, x_24);
lean_ctor_set_uint8(x_32, sizeof(void*)*5, x_25);
x_33 = l_Lake_captureProc_x3f(x_32, x_29);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
if (lean_is_scalar(x_12)) {
 x_36 = lean_alloc_ctor(0, 2, 1);
} else {
 x_36 = x_12;
}
lean_ctor_set(x_36, 0, x_9);
lean_ctor_set(x_36, 1, x_11);
lean_ctor_set_uint8(x_36, sizeof(void*)*2, x_10);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_38 = lean_apply_4(x_30, x_37, x_2, x_36, x_35);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_34, 0);
lean_inc(x_39);
lean_dec(x_34);
x_40 = l_Lake_Package_getReleaseUrl___closed__9;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_42 = l_Lake_Package_getReleaseUrl___closed__10;
x_43 = lean_string_append(x_41, x_42);
x_44 = lean_apply_4(x_30, x_43, x_2, x_36, x_35);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_20);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_27);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_46 = lean_ctor_get(x_27, 0);
lean_dec(x_46);
x_47 = lean_ctor_get(x_28, 0);
lean_inc(x_47);
lean_dec(x_28);
if (lean_is_scalar(x_12)) {
 x_48 = lean_alloc_ctor(0, 2, 1);
} else {
 x_48 = x_12;
}
lean_ctor_set(x_48, 0, x_9);
lean_ctor_set(x_48, 1, x_11);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_10);
x_49 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_50 = lean_string_append(x_49, x_19);
lean_dec(x_19);
x_51 = l_Lake_Package_getReleaseUrl___closed__11;
x_52 = lean_string_append(x_50, x_51);
x_53 = lean_string_append(x_52, x_47);
lean_dec(x_47);
x_54 = l_Lake_Package_getReleaseUrl___closed__12;
x_55 = lean_string_append(x_53, x_54);
x_56 = lean_ctor_get(x_6, 16);
lean_inc(x_56);
lean_dec(x_6);
x_57 = lean_string_append(x_55, x_56);
lean_dec(x_56);
x_58 = lean_string_append(x_57, x_49);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_48);
lean_ctor_set(x_27, 0, x_59);
return x_27;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_60 = lean_ctor_get(x_27, 1);
lean_inc(x_60);
lean_dec(x_27);
x_61 = lean_ctor_get(x_28, 0);
lean_inc(x_61);
lean_dec(x_28);
if (lean_is_scalar(x_12)) {
 x_62 = lean_alloc_ctor(0, 2, 1);
} else {
 x_62 = x_12;
}
lean_ctor_set(x_62, 0, x_9);
lean_ctor_set(x_62, 1, x_11);
lean_ctor_set_uint8(x_62, sizeof(void*)*2, x_10);
x_63 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_64 = lean_string_append(x_63, x_19);
lean_dec(x_19);
x_65 = l_Lake_Package_getReleaseUrl___closed__11;
x_66 = lean_string_append(x_64, x_65);
x_67 = lean_string_append(x_66, x_61);
lean_dec(x_61);
x_68 = l_Lake_Package_getReleaseUrl___closed__12;
x_69 = lean_string_append(x_67, x_68);
x_70 = lean_ctor_get(x_6, 16);
lean_inc(x_70);
lean_dec(x_6);
x_71 = lean_string_append(x_69, x_70);
lean_dec(x_70);
x_72 = lean_string_append(x_71, x_63);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_62);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_60);
return x_74;
}
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_14, 0);
x_84 = lean_ctor_get(x_14, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_128 = lean_array_get_size(x_9);
x_129 = l_Lake_Package_getReleaseUrl___closed__14;
x_130 = lean_array_push(x_9, x_129);
x_131 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_11);
lean_ctor_set_uint8(x_131, sizeof(void*)*2, x_10);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_128);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_84);
return x_133;
}
else
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_83, 0);
lean_inc(x_134);
lean_dec(x_83);
x_85 = x_134;
goto block_127;
}
}
else
{
lean_object* x_135; 
lean_dec(x_83);
x_135 = lean_ctor_get(x_15, 0);
lean_inc(x_135);
lean_dec(x_15);
x_85 = x_135;
goto block_127;
}
block_127:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_5);
x_87 = l_Lake_Package_getBarrelUrl___lambda__2___closed__10;
x_88 = l_Lake_Package_getBarrelUrl___lambda__2___closed__11;
x_89 = l_Lake_Package_getReleaseUrl___closed__7;
x_90 = l_Lake_Package_maybeFetchBuildCache___closed__1;
x_91 = 0;
lean_inc(x_86);
x_92 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_92, 0, x_87);
lean_ctor_set(x_92, 1, x_88);
lean_ctor_set(x_92, 2, x_89);
lean_ctor_set(x_92, 3, x_86);
lean_ctor_set(x_92, 4, x_90);
lean_ctor_set_uint8(x_92, sizeof(void*)*5, x_91);
x_93 = l_Lake_captureProc_x3f(x_92, x_84);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_85);
lean_dec(x_6);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = l_Lake_Package_getReleaseUrl___closed__8;
x_97 = l_Lake_Package_getBarrelUrl___lambda__2___closed__9;
x_98 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_98, 0, x_87);
lean_ctor_set(x_98, 1, x_88);
lean_ctor_set(x_98, 2, x_97);
lean_ctor_set(x_98, 3, x_86);
lean_ctor_set(x_98, 4, x_90);
lean_ctor_set_uint8(x_98, sizeof(void*)*5, x_91);
x_99 = l_Lake_captureProc_x3f(x_98, x_95);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
if (lean_is_scalar(x_12)) {
 x_102 = lean_alloc_ctor(0, 2, 1);
} else {
 x_102 = x_12;
}
lean_ctor_set(x_102, 0, x_9);
lean_ctor_set(x_102, 1, x_11);
lean_ctor_set_uint8(x_102, sizeof(void*)*2, x_10);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_104 = lean_apply_4(x_96, x_103, x_2, x_102, x_101);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_105 = lean_ctor_get(x_100, 0);
lean_inc(x_105);
lean_dec(x_100);
x_106 = l_Lake_Package_getReleaseUrl___closed__9;
x_107 = lean_string_append(x_106, x_105);
lean_dec(x_105);
x_108 = l_Lake_Package_getReleaseUrl___closed__10;
x_109 = lean_string_append(x_107, x_108);
x_110 = lean_apply_4(x_96, x_109, x_2, x_102, x_101);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_86);
lean_dec(x_2);
x_111 = lean_ctor_get(x_93, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_112 = x_93;
} else {
 lean_dec_ref(x_93);
 x_112 = lean_box(0);
}
x_113 = lean_ctor_get(x_94, 0);
lean_inc(x_113);
lean_dec(x_94);
if (lean_is_scalar(x_12)) {
 x_114 = lean_alloc_ctor(0, 2, 1);
} else {
 x_114 = x_12;
}
lean_ctor_set(x_114, 0, x_9);
lean_ctor_set(x_114, 1, x_11);
lean_ctor_set_uint8(x_114, sizeof(void*)*2, x_10);
x_115 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_116 = lean_string_append(x_115, x_85);
lean_dec(x_85);
x_117 = l_Lake_Package_getReleaseUrl___closed__11;
x_118 = lean_string_append(x_116, x_117);
x_119 = lean_string_append(x_118, x_113);
lean_dec(x_113);
x_120 = l_Lake_Package_getReleaseUrl___closed__12;
x_121 = lean_string_append(x_119, x_120);
x_122 = lean_ctor_get(x_6, 16);
lean_inc(x_122);
lean_dec(x_6);
x_123 = lean_string_append(x_121, x_122);
lean_dec(x_122);
x_124 = lean_string_append(x_123, x_115);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_114);
if (lean_is_scalar(x_112)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_112;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_111);
return x_126;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_getReleaseUrl___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Package_getReleaseUrl___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchBuildArchive___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = l_Lake_download(x_1, x_2, x_3, x_8, x_6);
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
lean_object* x_14; 
x_14 = lean_ctor_get(x_10, 1);
lean_ctor_set(x_5, 0, x_14);
lean_ctor_set(x_10, 1, x_5);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
lean_ctor_set(x_5, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_5);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_21 = x_10;
} else {
 lean_dec_ref(x_10);
 x_21 = lean_box(0);
}
lean_ctor_set(x_5, 0, x_20);
if (lean_is_scalar(x_21)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_21;
}
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_5);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_9, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_10, 1);
lean_ctor_set(x_5, 0, x_27);
lean_ctor_set(x_10, 1, x_5);
return x_9;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_10, 0);
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_10);
lean_ctor_set(x_5, 0, x_29);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_5);
lean_ctor_set(x_9, 0, x_30);
return x_9;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
lean_dec(x_9);
x_32 = lean_ctor_get(x_10, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_10, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_34 = x_10;
} else {
 lean_dec_ref(x_10);
 x_34 = lean_box(0);
}
lean_ctor_set(x_5, 0, x_33);
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_5);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
return x_36;
}
}
}
else
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_5, 0);
x_38 = lean_ctor_get_uint8(x_5, sizeof(void*)*2);
x_39 = lean_ctor_get(x_5, 1);
lean_inc(x_39);
lean_inc(x_37);
lean_dec(x_5);
x_40 = l_Lake_download(x_1, x_2, x_3, x_37, x_6);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
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
x_44 = lean_ctor_get(x_41, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_46 = x_41;
} else {
 lean_dec_ref(x_41);
 x_46 = lean_box(0);
}
x_47 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_39);
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_38);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_47);
if (lean_is_scalar(x_43)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_43;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_42);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_51 = x_40;
} else {
 lean_dec_ref(x_40);
 x_51 = lean_box(0);
}
x_52 = lean_ctor_get(x_41, 0);
lean_inc(x_52);
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
x_55 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_39);
lean_ctor_set_uint8(x_55, sizeof(void*)*2, x_38);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_55);
if (lean_is_scalar(x_51)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_51;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_50);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchBuildArchive___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_268; 
x_12 = lean_alloc_closure((void*)(l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchBuildArchive___spec__1___lambda__1___boxed), 6, 3);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
x_268 = !lean_is_exclusive(x_10);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; 
x_269 = lean_ctor_get(x_10, 0);
x_270 = l_System_FilePath_pathExists(x_6, x_11);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_unbox(x_271);
lean_dec(x_271);
if (x_272 == 0)
{
uint8_t x_273; 
lean_dec(x_8);
x_273 = !lean_is_exclusive(x_270);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_274 = lean_ctor_get(x_270, 1);
x_275 = lean_ctor_get(x_270, 0);
lean_dec(x_275);
x_276 = lean_ctor_get(x_5, 1);
lean_inc(x_276);
x_277 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate_x27___spec__3(x_4, x_276, x_274);
x_278 = !lean_is_exclusive(x_277);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; uint8_t x_281; 
x_279 = lean_ctor_get(x_277, 0);
x_280 = lean_ctor_get(x_277, 1);
x_281 = lean_unbox(x_279);
lean_dec(x_279);
if (x_281 == 0)
{
lean_object* x_282; 
lean_free_object(x_277);
lean_free_object(x_270);
x_282 = l_Lake_buildUnlessUpToDate_x3f_go(x_5, x_6, x_12, x_7, x_9, x_10, x_280);
return x_282;
}
else
{
uint8_t x_283; lean_object* x_284; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_5);
x_283 = 1;
x_284 = lean_box(x_283);
lean_ctor_set(x_270, 1, x_10);
lean_ctor_set(x_270, 0, x_284);
lean_ctor_set(x_277, 0, x_270);
return x_277;
}
}
else
{
lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_285 = lean_ctor_get(x_277, 0);
x_286 = lean_ctor_get(x_277, 1);
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_277);
x_287 = lean_unbox(x_285);
lean_dec(x_285);
if (x_287 == 0)
{
lean_object* x_288; 
lean_free_object(x_270);
x_288 = l_Lake_buildUnlessUpToDate_x3f_go(x_5, x_6, x_12, x_7, x_9, x_10, x_286);
return x_288;
}
else
{
uint8_t x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_5);
x_289 = 1;
x_290 = lean_box(x_289);
lean_ctor_set(x_270, 1, x_10);
lean_ctor_set(x_270, 0, x_290);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_270);
lean_ctor_set(x_291, 1, x_286);
return x_291;
}
}
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; 
x_292 = lean_ctor_get(x_270, 1);
lean_inc(x_292);
lean_dec(x_270);
x_293 = lean_ctor_get(x_5, 1);
lean_inc(x_293);
x_294 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate_x27___spec__3(x_4, x_293, x_292);
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_294, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 lean_ctor_release(x_294, 1);
 x_297 = x_294;
} else {
 lean_dec_ref(x_294);
 x_297 = lean_box(0);
}
x_298 = lean_unbox(x_295);
lean_dec(x_295);
if (x_298 == 0)
{
lean_object* x_299; 
lean_dec(x_297);
x_299 = l_Lake_buildUnlessUpToDate_x3f_go(x_5, x_6, x_12, x_7, x_9, x_10, x_296);
return x_299;
}
else
{
uint8_t x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_5);
x_300 = 1;
x_301 = lean_box(x_300);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_10);
if (lean_is_scalar(x_297)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_297;
}
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_296);
return x_303;
}
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; 
x_304 = lean_ctor_get(x_270, 1);
lean_inc(x_304);
lean_dec(x_270);
x_305 = l_Lake_readTraceFile_x3f(x_6, x_269, x_304);
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_305, 1);
lean_inc(x_307);
lean_dec(x_305);
x_308 = !lean_is_exclusive(x_306);
if (x_308 == 0)
{
lean_object* x_309; 
x_309 = lean_ctor_get(x_306, 1);
lean_ctor_set(x_10, 0, x_309);
lean_ctor_set(x_306, 1, x_10);
x_13 = x_306;
x_14 = x_307;
goto block_267;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_310 = lean_ctor_get(x_306, 0);
x_311 = lean_ctor_get(x_306, 1);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_306);
lean_ctor_set(x_10, 0, x_311);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_310);
lean_ctor_set(x_312, 1, x_10);
x_13 = x_312;
x_14 = x_307;
goto block_267;
}
}
}
else
{
lean_object* x_313; uint8_t x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; 
x_313 = lean_ctor_get(x_10, 0);
x_314 = lean_ctor_get_uint8(x_10, sizeof(void*)*2);
x_315 = lean_ctor_get(x_10, 1);
lean_inc(x_315);
lean_inc(x_313);
lean_dec(x_10);
x_316 = l_System_FilePath_pathExists(x_6, x_11);
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_unbox(x_317);
lean_dec(x_317);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
lean_dec(x_8);
x_319 = lean_ctor_get(x_316, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 lean_ctor_release(x_316, 1);
 x_320 = x_316;
} else {
 lean_dec_ref(x_316);
 x_320 = lean_box(0);
}
x_321 = lean_ctor_get(x_5, 1);
lean_inc(x_321);
x_322 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate_x27___spec__3(x_4, x_321, x_319);
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_322, 1);
lean_inc(x_324);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 x_325 = x_322;
} else {
 lean_dec_ref(x_322);
 x_325 = lean_box(0);
}
x_326 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_326, 0, x_313);
lean_ctor_set(x_326, 1, x_315);
lean_ctor_set_uint8(x_326, sizeof(void*)*2, x_314);
x_327 = lean_unbox(x_323);
lean_dec(x_323);
if (x_327 == 0)
{
lean_object* x_328; 
lean_dec(x_325);
lean_dec(x_320);
x_328 = l_Lake_buildUnlessUpToDate_x3f_go(x_5, x_6, x_12, x_7, x_9, x_326, x_324);
return x_328;
}
else
{
uint8_t x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_5);
x_329 = 1;
x_330 = lean_box(x_329);
if (lean_is_scalar(x_320)) {
 x_331 = lean_alloc_ctor(0, 2, 0);
} else {
 x_331 = x_320;
}
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_326);
if (lean_is_scalar(x_325)) {
 x_332 = lean_alloc_ctor(0, 2, 0);
} else {
 x_332 = x_325;
}
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_324);
return x_332;
}
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_333 = lean_ctor_get(x_316, 1);
lean_inc(x_333);
lean_dec(x_316);
x_334 = l_Lake_readTraceFile_x3f(x_6, x_313, x_333);
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
lean_dec(x_334);
x_337 = lean_ctor_get(x_335, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_335, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 x_339 = x_335;
} else {
 lean_dec_ref(x_335);
 x_339 = lean_box(0);
}
x_340 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_340, 0, x_338);
lean_ctor_set(x_340, 1, x_315);
lean_ctor_set_uint8(x_340, sizeof(void*)*2, x_314);
if (lean_is_scalar(x_339)) {
 x_341 = lean_alloc_ctor(0, 2, 0);
} else {
 x_341 = x_339;
}
lean_ctor_set(x_341, 0, x_337);
lean_ctor_set(x_341, 1, x_340);
x_13 = x_341;
x_14 = x_336;
goto block_267;
}
}
block_267:
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*1);
lean_dec(x_19);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate_x27___spec__3(x_4, x_8, x_14);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
if (x_20 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_free_object(x_22);
lean_dec(x_24);
lean_free_object(x_13);
x_26 = l_Lake_buildUnlessUpToDate_x3f_go(x_5, x_6, x_12, x_7, x_9, x_17, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = lean_ctor_get(x_22, 1);
x_29 = lean_unbox(x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_free_object(x_22);
lean_free_object(x_13);
x_30 = l_Lake_buildUnlessUpToDate_x3f_go(x_5, x_6, x_12, x_7, x_9, x_17, x_28);
return x_30;
}
else
{
uint8_t x_31; lean_object* x_32; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_5);
x_31 = 1;
x_32 = lean_box(x_31);
lean_ctor_set(x_13, 0, x_32);
lean_ctor_set(x_22, 0, x_13);
return x_22;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_22, 0);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_22);
if (x_20 == 0)
{
lean_object* x_35; 
lean_dec(x_33);
lean_free_object(x_13);
x_35 = l_Lake_buildUnlessUpToDate_x3f_go(x_5, x_6, x_12, x_7, x_9, x_17, x_34);
return x_35;
}
else
{
uint8_t x_36; 
x_36 = lean_unbox(x_33);
lean_dec(x_33);
if (x_36 == 0)
{
lean_object* x_37; 
lean_free_object(x_13);
x_37 = l_Lake_buildUnlessUpToDate_x3f_go(x_5, x_6, x_12, x_7, x_9, x_17, x_34);
return x_37;
}
else
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_5);
x_38 = 1;
x_39 = lean_box(x_38);
lean_ctor_set(x_13, 0, x_39);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_13);
lean_ctor_set(x_40, 1, x_34);
return x_40;
}
}
}
}
else
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_41 = lean_ctor_get(x_17, 0);
x_42 = lean_ctor_get_uint8(x_17, sizeof(void*)*2);
x_43 = lean_ctor_get(x_17, 1);
lean_inc(x_43);
lean_inc(x_41);
lean_dec(x_17);
x_44 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate_x27___spec__3(x_4, x_8, x_14);
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
x_48 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_43);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_42);
if (x_20 == 0)
{
lean_object* x_49; 
lean_dec(x_47);
lean_dec(x_45);
lean_free_object(x_13);
x_49 = l_Lake_buildUnlessUpToDate_x3f_go(x_5, x_6, x_12, x_7, x_9, x_48, x_46);
return x_49;
}
else
{
uint8_t x_50; 
x_50 = lean_unbox(x_45);
lean_dec(x_45);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_47);
lean_free_object(x_13);
x_51 = l_Lake_buildUnlessUpToDate_x3f_go(x_5, x_6, x_12, x_7, x_9, x_48, x_46);
return x_51;
}
else
{
uint8_t x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_5);
x_52 = 1;
x_53 = lean_box(x_52);
lean_ctor_set(x_13, 1, x_48);
lean_ctor_set(x_13, 0, x_53);
if (lean_is_scalar(x_47)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_47;
}
lean_ctor_set(x_54, 0, x_13);
lean_ctor_set(x_54, 1, x_46);
return x_54;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_55 = lean_ctor_get(x_13, 1);
lean_inc(x_55);
lean_dec(x_13);
x_56 = lean_ctor_get(x_9, 0);
lean_inc(x_56);
x_57 = lean_ctor_get_uint8(x_56, sizeof(void*)*1);
lean_dec(x_56);
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
x_59 = lean_ctor_get_uint8(x_55, sizeof(void*)*2);
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_61 = x_55;
} else {
 lean_dec_ref(x_55);
 x_61 = lean_box(0);
}
x_62 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate_x27___spec__3(x_4, x_8, x_14);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_66 = lean_alloc_ctor(0, 2, 1);
} else {
 x_66 = x_61;
}
lean_ctor_set(x_66, 0, x_58);
lean_ctor_set(x_66, 1, x_60);
lean_ctor_set_uint8(x_66, sizeof(void*)*2, x_59);
if (x_57 == 0)
{
lean_object* x_67; 
lean_dec(x_65);
lean_dec(x_63);
x_67 = l_Lake_buildUnlessUpToDate_x3f_go(x_5, x_6, x_12, x_7, x_9, x_66, x_64);
return x_67;
}
else
{
uint8_t x_68; 
x_68 = lean_unbox(x_63);
lean_dec(x_63);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec(x_65);
x_69 = l_Lake_buildUnlessUpToDate_x3f_go(x_5, x_6, x_12, x_7, x_9, x_66, x_64);
return x_69;
}
else
{
uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_5);
x_70 = 1;
x_71 = lean_box(x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_66);
if (lean_is_scalar(x_65)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_65;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_64);
return x_73;
}
}
}
}
else
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_15);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_75 = lean_ctor_get(x_15, 0);
x_76 = lean_ctor_get(x_13, 1);
lean_inc(x_76);
lean_dec(x_13);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
lean_ctor_set(x_15, 0, x_77);
lean_inc(x_5);
x_79 = l_Lake_checkHashUpToDate___at_Lake_buildFileUnlessUpToDate_x27___spec__4(x_4, x_5, x_15, x_8, x_9, x_76, x_14);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_unbox(x_81);
lean_dec(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_78);
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
lean_dec(x_79);
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
lean_dec(x_80);
x_85 = l_Lake_buildUnlessUpToDate_x3f_go(x_5, x_6, x_12, x_7, x_9, x_84, x_83);
return x_85;
}
else
{
uint8_t x_86; 
lean_dec(x_12);
lean_dec(x_5);
x_86 = !lean_is_exclusive(x_80);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_ctor_get(x_80, 1);
x_88 = lean_ctor_get(x_80, 0);
lean_dec(x_88);
x_89 = !lean_is_exclusive(x_79);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_90 = lean_ctor_get(x_79, 1);
x_91 = lean_ctor_get(x_79, 0);
lean_dec(x_91);
x_92 = !lean_is_exclusive(x_87);
if (x_92 == 0)
{
uint8_t x_93; uint8_t x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_93 = lean_ctor_get_uint8(x_87, sizeof(void*)*2);
x_94 = 1;
x_95 = l_Lake_JobAction_merge(x_93, x_94);
lean_ctor_set_uint8(x_87, sizeof(void*)*2, x_95);
x_96 = lean_array_get_size(x_78);
x_97 = lean_unsigned_to_nat(0u);
x_98 = lean_nat_dec_lt(x_97, x_96);
if (x_98 == 0)
{
uint8_t x_99; lean_object* x_100; 
lean_dec(x_96);
lean_dec(x_78);
lean_dec(x_9);
x_99 = 1;
x_100 = lean_box(x_99);
lean_ctor_set(x_80, 0, x_100);
return x_79;
}
else
{
uint8_t x_101; 
x_101 = lean_nat_dec_le(x_96, x_96);
if (x_101 == 0)
{
uint8_t x_102; lean_object* x_103; 
lean_dec(x_96);
lean_dec(x_78);
lean_dec(x_9);
x_102 = 1;
x_103 = lean_box(x_102);
lean_ctor_set(x_80, 0, x_103);
return x_79;
}
else
{
size_t x_104; size_t x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
lean_free_object(x_79);
lean_free_object(x_80);
x_104 = 0;
x_105 = lean_usize_of_nat(x_96);
lean_dec(x_96);
x_106 = lean_box(0);
x_107 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate_x27___spec__6(x_78, x_104, x_105, x_106, x_9, x_87, x_90);
lean_dec(x_9);
lean_dec(x_78);
x_108 = !lean_is_exclusive(x_107);
if (x_108 == 0)
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_ctor_get(x_107, 0);
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; uint8_t x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_109, 0);
lean_dec(x_111);
x_112 = 1;
x_113 = lean_box(x_112);
lean_ctor_set(x_109, 0, x_113);
return x_107;
}
else
{
lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_109, 1);
lean_inc(x_114);
lean_dec(x_109);
x_115 = 1;
x_116 = lean_box(x_115);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_114);
lean_ctor_set(x_107, 0, x_117);
return x_107;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_118 = lean_ctor_get(x_107, 0);
x_119 = lean_ctor_get(x_107, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_107);
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
x_122 = 1;
x_123 = lean_box(x_122);
if (lean_is_scalar(x_121)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_121;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_120);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_119);
return x_125;
}
}
}
}
else
{
lean_object* x_126; uint8_t x_127; lean_object* x_128; uint8_t x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_126 = lean_ctor_get(x_87, 0);
x_127 = lean_ctor_get_uint8(x_87, sizeof(void*)*2);
x_128 = lean_ctor_get(x_87, 1);
lean_inc(x_128);
lean_inc(x_126);
lean_dec(x_87);
x_129 = 1;
x_130 = l_Lake_JobAction_merge(x_127, x_129);
x_131 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_131, 0, x_126);
lean_ctor_set(x_131, 1, x_128);
lean_ctor_set_uint8(x_131, sizeof(void*)*2, x_130);
x_132 = lean_array_get_size(x_78);
x_133 = lean_unsigned_to_nat(0u);
x_134 = lean_nat_dec_lt(x_133, x_132);
if (x_134 == 0)
{
uint8_t x_135; lean_object* x_136; 
lean_dec(x_132);
lean_dec(x_78);
lean_dec(x_9);
x_135 = 1;
x_136 = lean_box(x_135);
lean_ctor_set(x_80, 1, x_131);
lean_ctor_set(x_80, 0, x_136);
return x_79;
}
else
{
uint8_t x_137; 
x_137 = lean_nat_dec_le(x_132, x_132);
if (x_137 == 0)
{
uint8_t x_138; lean_object* x_139; 
lean_dec(x_132);
lean_dec(x_78);
lean_dec(x_9);
x_138 = 1;
x_139 = lean_box(x_138);
lean_ctor_set(x_80, 1, x_131);
lean_ctor_set(x_80, 0, x_139);
return x_79;
}
else
{
size_t x_140; size_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_free_object(x_79);
lean_free_object(x_80);
x_140 = 0;
x_141 = lean_usize_of_nat(x_132);
lean_dec(x_132);
x_142 = lean_box(0);
x_143 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate_x27___spec__6(x_78, x_140, x_141, x_142, x_9, x_131, x_90);
lean_dec(x_9);
lean_dec(x_78);
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
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_148 = x_144;
} else {
 lean_dec_ref(x_144);
 x_148 = lean_box(0);
}
x_149 = 1;
x_150 = lean_box(x_149);
if (lean_is_scalar(x_148)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_148;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_147);
if (lean_is_scalar(x_146)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_146;
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_145);
return x_152;
}
}
}
}
else
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_153 = lean_ctor_get(x_79, 1);
lean_inc(x_153);
lean_dec(x_79);
x_154 = lean_ctor_get(x_87, 0);
lean_inc(x_154);
x_155 = lean_ctor_get_uint8(x_87, sizeof(void*)*2);
x_156 = lean_ctor_get(x_87, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_157 = x_87;
} else {
 lean_dec_ref(x_87);
 x_157 = lean_box(0);
}
x_158 = 1;
x_159 = l_Lake_JobAction_merge(x_155, x_158);
if (lean_is_scalar(x_157)) {
 x_160 = lean_alloc_ctor(0, 2, 1);
} else {
 x_160 = x_157;
}
lean_ctor_set(x_160, 0, x_154);
lean_ctor_set(x_160, 1, x_156);
lean_ctor_set_uint8(x_160, sizeof(void*)*2, x_159);
x_161 = lean_array_get_size(x_78);
x_162 = lean_unsigned_to_nat(0u);
x_163 = lean_nat_dec_lt(x_162, x_161);
if (x_163 == 0)
{
uint8_t x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_161);
lean_dec(x_78);
lean_dec(x_9);
x_164 = 1;
x_165 = lean_box(x_164);
lean_ctor_set(x_80, 1, x_160);
lean_ctor_set(x_80, 0, x_165);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_80);
lean_ctor_set(x_166, 1, x_153);
return x_166;
}
else
{
uint8_t x_167; 
x_167 = lean_nat_dec_le(x_161, x_161);
if (x_167 == 0)
{
uint8_t x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_161);
lean_dec(x_78);
lean_dec(x_9);
x_168 = 1;
x_169 = lean_box(x_168);
lean_ctor_set(x_80, 1, x_160);
lean_ctor_set(x_80, 0, x_169);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_80);
lean_ctor_set(x_170, 1, x_153);
return x_170;
}
else
{
size_t x_171; size_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_free_object(x_80);
x_171 = 0;
x_172 = lean_usize_of_nat(x_161);
lean_dec(x_161);
x_173 = lean_box(0);
x_174 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate_x27___spec__6(x_78, x_171, x_172, x_173, x_9, x_160, x_153);
lean_dec(x_9);
lean_dec(x_78);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
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
x_178 = lean_ctor_get(x_175, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_179 = x_175;
} else {
 lean_dec_ref(x_175);
 x_179 = lean_box(0);
}
x_180 = 1;
x_181 = lean_box(x_180);
if (lean_is_scalar(x_179)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_179;
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_178);
if (lean_is_scalar(x_177)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_177;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_176);
return x_183;
}
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; uint8_t x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_184 = lean_ctor_get(x_80, 1);
lean_inc(x_184);
lean_dec(x_80);
x_185 = lean_ctor_get(x_79, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_186 = x_79;
} else {
 lean_dec_ref(x_79);
 x_186 = lean_box(0);
}
x_187 = lean_ctor_get(x_184, 0);
lean_inc(x_187);
x_188 = lean_ctor_get_uint8(x_184, sizeof(void*)*2);
x_189 = lean_ctor_get(x_184, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_190 = x_184;
} else {
 lean_dec_ref(x_184);
 x_190 = lean_box(0);
}
x_191 = 1;
x_192 = l_Lake_JobAction_merge(x_188, x_191);
if (lean_is_scalar(x_190)) {
 x_193 = lean_alloc_ctor(0, 2, 1);
} else {
 x_193 = x_190;
}
lean_ctor_set(x_193, 0, x_187);
lean_ctor_set(x_193, 1, x_189);
lean_ctor_set_uint8(x_193, sizeof(void*)*2, x_192);
x_194 = lean_array_get_size(x_78);
x_195 = lean_unsigned_to_nat(0u);
x_196 = lean_nat_dec_lt(x_195, x_194);
if (x_196 == 0)
{
uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_194);
lean_dec(x_78);
lean_dec(x_9);
x_197 = 1;
x_198 = lean_box(x_197);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_193);
if (lean_is_scalar(x_186)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_186;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_185);
return x_200;
}
else
{
uint8_t x_201; 
x_201 = lean_nat_dec_le(x_194, x_194);
if (x_201 == 0)
{
uint8_t x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_194);
lean_dec(x_78);
lean_dec(x_9);
x_202 = 1;
x_203 = lean_box(x_202);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_193);
if (lean_is_scalar(x_186)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_186;
}
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_185);
return x_205;
}
else
{
size_t x_206; size_t x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_186);
x_206 = 0;
x_207 = lean_usize_of_nat(x_194);
lean_dec(x_194);
x_208 = lean_box(0);
x_209 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate_x27___spec__6(x_78, x_206, x_207, x_208, x_9, x_193, x_185);
lean_dec(x_9);
lean_dec(x_78);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_212 = x_209;
} else {
 lean_dec_ref(x_209);
 x_212 = lean_box(0);
}
x_213 = lean_ctor_get(x_210, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_214 = x_210;
} else {
 lean_dec_ref(x_210);
 x_214 = lean_box(0);
}
x_215 = 1;
x_216 = lean_box(x_215);
if (lean_is_scalar(x_214)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_214;
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_213);
if (lean_is_scalar(x_212)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_212;
}
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_211);
return x_218;
}
}
}
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
x_219 = lean_ctor_get(x_15, 0);
lean_inc(x_219);
lean_dec(x_15);
x_220 = lean_ctor_get(x_13, 1);
lean_inc(x_220);
lean_dec(x_13);
x_221 = lean_ctor_get(x_219, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_219, 1);
lean_inc(x_222);
lean_dec(x_219);
x_223 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_223, 0, x_221);
lean_inc(x_5);
x_224 = l_Lake_checkHashUpToDate___at_Lake_buildFileUnlessUpToDate_x27___spec__4(x_4, x_5, x_223, x_8, x_9, x_220, x_14);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_unbox(x_226);
lean_dec(x_226);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_222);
x_228 = lean_ctor_get(x_224, 1);
lean_inc(x_228);
lean_dec(x_224);
x_229 = lean_ctor_get(x_225, 1);
lean_inc(x_229);
lean_dec(x_225);
x_230 = l_Lake_buildUnlessUpToDate_x3f_go(x_5, x_6, x_12, x_7, x_9, x_229, x_228);
return x_230;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; uint8_t x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; 
lean_dec(x_12);
lean_dec(x_5);
x_231 = lean_ctor_get(x_225, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_232 = x_225;
} else {
 lean_dec_ref(x_225);
 x_232 = lean_box(0);
}
x_233 = lean_ctor_get(x_224, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_234 = x_224;
} else {
 lean_dec_ref(x_224);
 x_234 = lean_box(0);
}
x_235 = lean_ctor_get(x_231, 0);
lean_inc(x_235);
x_236 = lean_ctor_get_uint8(x_231, sizeof(void*)*2);
x_237 = lean_ctor_get(x_231, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_238 = x_231;
} else {
 lean_dec_ref(x_231);
 x_238 = lean_box(0);
}
x_239 = 1;
x_240 = l_Lake_JobAction_merge(x_236, x_239);
if (lean_is_scalar(x_238)) {
 x_241 = lean_alloc_ctor(0, 2, 1);
} else {
 x_241 = x_238;
}
lean_ctor_set(x_241, 0, x_235);
lean_ctor_set(x_241, 1, x_237);
lean_ctor_set_uint8(x_241, sizeof(void*)*2, x_240);
x_242 = lean_array_get_size(x_222);
x_243 = lean_unsigned_to_nat(0u);
x_244 = lean_nat_dec_lt(x_243, x_242);
if (x_244 == 0)
{
uint8_t x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_242);
lean_dec(x_222);
lean_dec(x_9);
x_245 = 1;
x_246 = lean_box(x_245);
if (lean_is_scalar(x_232)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_232;
}
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_241);
if (lean_is_scalar(x_234)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_234;
}
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_233);
return x_248;
}
else
{
uint8_t x_249; 
x_249 = lean_nat_dec_le(x_242, x_242);
if (x_249 == 0)
{
uint8_t x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_242);
lean_dec(x_222);
lean_dec(x_9);
x_250 = 1;
x_251 = lean_box(x_250);
if (lean_is_scalar(x_232)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_232;
}
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_241);
if (lean_is_scalar(x_234)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_234;
}
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_233);
return x_253;
}
else
{
size_t x_254; size_t x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_234);
lean_dec(x_232);
x_254 = 0;
x_255 = lean_usize_of_nat(x_242);
lean_dec(x_242);
x_256 = lean_box(0);
x_257 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate_x27___spec__6(x_222, x_254, x_255, x_256, x_9, x_241, x_233);
lean_dec(x_9);
lean_dec(x_222);
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_260 = x_257;
} else {
 lean_dec_ref(x_257);
 x_260 = lean_box(0);
}
x_261 = lean_ctor_get(x_258, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 x_262 = x_258;
} else {
 lean_dec_ref(x_258);
 x_262 = lean_box(0);
}
x_263 = 1;
x_264 = lean_box(x_263);
if (lean_is_scalar(x_262)) {
 x_265 = lean_alloc_ctor(0, 2, 0);
} else {
 x_265 = x_262;
}
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_261);
if (lean_is_scalar(x_260)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_260;
}
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_259);
return x_266;
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
LEAN_EXPORT lean_object* l_Lake_Package_fetchBuildArchive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint64_t x_8; uint64_t x_9; uint64_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_8 = lean_string_hash(x_2);
x_9 = 1723;
x_10 = lean_uint64_mix_hash(x_9, x_8);
x_11 = l_Lake_Package_fetchBuildArchive___closed__1;
lean_inc(x_3);
x_12 = l_System_FilePath_addExtension(x_3, x_11);
x_13 = l_Lake_Package_fetchBuildArchive___closed__3;
x_14 = lean_box_uint64(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = 2;
lean_inc(x_3);
x_17 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchBuildArchive___spec__1(x_2, x_3, x_4, x_3, x_15, x_12, x_16, x_13, x_5, x_6, x_7);
lean_dec(x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 1);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 2);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_ctor_get(x_24, 8);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_System_FilePath_join(x_23, x_25);
lean_dec(x_25);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get_uint8(x_22, sizeof(void*)*2);
x_30 = l_System_FilePath_pathExists(x_26, x_19);
x_31 = lean_unbox(x_21);
lean_dec(x_21);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
lean_free_object(x_18);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lake_JobAction_merge(x_29, x_16);
x_34 = 1;
x_35 = l_Lake_untar(x_3, x_26, x_34, x_28, x_32);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_35, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_36, 1);
lean_ctor_set(x_22, 0, x_40);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_33);
lean_ctor_set(x_36, 1, x_22);
return x_35;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_36, 0);
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_36);
lean_ctor_set(x_22, 0, x_42);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_33);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_22);
lean_ctor_set(x_35, 0, x_43);
return x_35;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_35, 1);
lean_inc(x_44);
lean_dec(x_35);
x_45 = lean_ctor_get(x_36, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_36, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_47 = x_36;
} else {
 lean_dec_ref(x_36);
 x_47 = lean_box(0);
}
lean_ctor_set(x_22, 0, x_46);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_33);
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_22);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_44);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_35);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_35, 0);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_36);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_36, 1);
lean_ctor_set(x_22, 0, x_53);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_33);
lean_ctor_set(x_36, 1, x_22);
return x_35;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_36, 0);
x_55 = lean_ctor_get(x_36, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_36);
lean_ctor_set(x_22, 0, x_55);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_33);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_22);
lean_ctor_set(x_35, 0, x_56);
return x_35;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_35, 1);
lean_inc(x_57);
lean_dec(x_35);
x_58 = lean_ctor_get(x_36, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_36, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_60 = x_36;
} else {
 lean_dec_ref(x_36);
 x_60 = lean_box(0);
}
lean_ctor_set(x_22, 0, x_59);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_33);
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_22);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
return x_62;
}
}
}
else
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_30, 0);
lean_inc(x_63);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; 
lean_free_object(x_18);
x_65 = lean_ctor_get(x_30, 1);
lean_inc(x_65);
lean_dec(x_30);
x_66 = l_Lake_JobAction_merge(x_29, x_16);
x_67 = 1;
x_68 = l_Lake_untar(x_3, x_26, x_67, x_28, x_65);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_68);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_68, 0);
lean_dec(x_71);
x_72 = !lean_is_exclusive(x_69);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_69, 1);
lean_ctor_set(x_22, 0, x_73);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_66);
lean_ctor_set(x_69, 1, x_22);
return x_68;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_69, 0);
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_69);
lean_ctor_set(x_22, 0, x_75);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_66);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_22);
lean_ctor_set(x_68, 0, x_76);
return x_68;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_68, 1);
lean_inc(x_77);
lean_dec(x_68);
x_78 = lean_ctor_get(x_69, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_69, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_80 = x_69;
} else {
 lean_dec_ref(x_69);
 x_80 = lean_box(0);
}
lean_ctor_set(x_22, 0, x_79);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_66);
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_22);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_77);
return x_82;
}
}
else
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_68);
if (x_83 == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_68, 0);
lean_dec(x_84);
x_85 = !lean_is_exclusive(x_69);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_69, 1);
lean_ctor_set(x_22, 0, x_86);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_66);
lean_ctor_set(x_69, 1, x_22);
return x_68;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_69, 0);
x_88 = lean_ctor_get(x_69, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_69);
lean_ctor_set(x_22, 0, x_88);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_66);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_22);
lean_ctor_set(x_68, 0, x_89);
return x_68;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_90 = lean_ctor_get(x_68, 1);
lean_inc(x_90);
lean_dec(x_68);
x_91 = lean_ctor_get(x_69, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_69, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_93 = x_69;
} else {
 lean_dec_ref(x_69);
 x_93 = lean_box(0);
}
lean_ctor_set(x_22, 0, x_92);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_66);
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_22);
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
lean_dec(x_26);
lean_dec(x_3);
x_96 = !lean_is_exclusive(x_30);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_30, 0);
lean_dec(x_97);
x_98 = lean_box(0);
lean_ctor_set(x_18, 0, x_98);
lean_ctor_set(x_30, 0, x_18);
return x_30;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_30, 1);
lean_inc(x_99);
lean_dec(x_30);
x_100 = lean_box(0);
lean_ctor_set(x_18, 0, x_100);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_18);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
}
}
else
{
lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_102 = lean_ctor_get(x_22, 0);
x_103 = lean_ctor_get_uint8(x_22, sizeof(void*)*2);
x_104 = lean_ctor_get(x_22, 1);
lean_inc(x_104);
lean_inc(x_102);
lean_dec(x_22);
x_105 = l_System_FilePath_pathExists(x_26, x_19);
x_106 = lean_unbox(x_21);
lean_dec(x_21);
if (x_106 == 0)
{
lean_object* x_107; uint8_t x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; 
lean_free_object(x_18);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = l_Lake_JobAction_merge(x_103, x_16);
x_109 = 1;
x_110 = l_Lake_untar(x_3, x_26, x_109, x_102, x_107);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_113 = x_110;
} else {
 lean_dec_ref(x_110);
 x_113 = lean_box(0);
}
x_114 = lean_ctor_get(x_111, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_111, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_116 = x_111;
} else {
 lean_dec_ref(x_111);
 x_116 = lean_box(0);
}
x_117 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_104);
lean_ctor_set_uint8(x_117, sizeof(void*)*2, x_108);
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_114);
lean_ctor_set(x_118, 1, x_117);
if (lean_is_scalar(x_113)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_113;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_112);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_120 = lean_ctor_get(x_110, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_121 = x_110;
} else {
 lean_dec_ref(x_110);
 x_121 = lean_box(0);
}
x_122 = lean_ctor_get(x_111, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_111, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_124 = x_111;
} else {
 lean_dec_ref(x_111);
 x_124 = lean_box(0);
}
x_125 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_104);
lean_ctor_set_uint8(x_125, sizeof(void*)*2, x_108);
if (lean_is_scalar(x_124)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_124;
}
lean_ctor_set(x_126, 0, x_122);
lean_ctor_set(x_126, 1, x_125);
if (lean_is_scalar(x_121)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_121;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_120);
return x_127;
}
}
else
{
lean_object* x_128; uint8_t x_129; 
x_128 = lean_ctor_get(x_105, 0);
lean_inc(x_128);
x_129 = lean_unbox(x_128);
lean_dec(x_128);
if (x_129 == 0)
{
lean_object* x_130; uint8_t x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; 
lean_free_object(x_18);
x_130 = lean_ctor_get(x_105, 1);
lean_inc(x_130);
lean_dec(x_105);
x_131 = l_Lake_JobAction_merge(x_103, x_16);
x_132 = 1;
x_133 = l_Lake_untar(x_3, x_26, x_132, x_102, x_130);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
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
x_137 = lean_ctor_get(x_134, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_134, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_139 = x_134;
} else {
 lean_dec_ref(x_134);
 x_139 = lean_box(0);
}
x_140 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_104);
lean_ctor_set_uint8(x_140, sizeof(void*)*2, x_131);
if (lean_is_scalar(x_139)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_139;
}
lean_ctor_set(x_141, 0, x_137);
lean_ctor_set(x_141, 1, x_140);
if (lean_is_scalar(x_136)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_136;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_135);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_143 = lean_ctor_get(x_133, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_144 = x_133;
} else {
 lean_dec_ref(x_133);
 x_144 = lean_box(0);
}
x_145 = lean_ctor_get(x_134, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_134, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_147 = x_134;
} else {
 lean_dec_ref(x_134);
 x_147 = lean_box(0);
}
x_148 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_104);
lean_ctor_set_uint8(x_148, sizeof(void*)*2, x_131);
if (lean_is_scalar(x_147)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_147;
}
lean_ctor_set(x_149, 0, x_145);
lean_ctor_set(x_149, 1, x_148);
if (lean_is_scalar(x_144)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_144;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_143);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_26);
lean_dec(x_3);
x_151 = lean_ctor_get(x_105, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_152 = x_105;
} else {
 lean_dec_ref(x_105);
 x_152 = lean_box(0);
}
x_153 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_153, 0, x_102);
lean_ctor_set(x_153, 1, x_104);
lean_ctor_set_uint8(x_153, sizeof(void*)*2, x_103);
x_154 = lean_box(0);
lean_ctor_set(x_18, 1, x_153);
lean_ctor_set(x_18, 0, x_154);
if (lean_is_scalar(x_152)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_152;
}
lean_ctor_set(x_155, 0, x_18);
lean_ctor_set(x_155, 1, x_151);
return x_155;
}
}
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_156 = lean_ctor_get(x_18, 0);
x_157 = lean_ctor_get(x_18, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_18);
x_158 = lean_ctor_get(x_1, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_1, 2);
lean_inc(x_159);
lean_dec(x_1);
x_160 = lean_ctor_get(x_159, 8);
lean_inc(x_160);
lean_dec(x_159);
x_161 = l_System_FilePath_join(x_158, x_160);
lean_dec(x_160);
x_162 = lean_ctor_get(x_157, 0);
lean_inc(x_162);
x_163 = lean_ctor_get_uint8(x_157, sizeof(void*)*2);
x_164 = lean_ctor_get(x_157, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_165 = x_157;
} else {
 lean_dec_ref(x_157);
 x_165 = lean_box(0);
}
x_166 = l_System_FilePath_pathExists(x_161, x_19);
x_167 = lean_unbox(x_156);
lean_dec(x_156);
if (x_167 == 0)
{
lean_object* x_168; uint8_t x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; 
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = l_Lake_JobAction_merge(x_163, x_16);
x_170 = 1;
x_171 = l_Lake_untar(x_3, x_161, x_170, x_162, x_168);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_174 = x_171;
} else {
 lean_dec_ref(x_171);
 x_174 = lean_box(0);
}
x_175 = lean_ctor_get(x_172, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_172, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_177 = x_172;
} else {
 lean_dec_ref(x_172);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_178 = lean_alloc_ctor(0, 2, 1);
} else {
 x_178 = x_165;
}
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_164);
lean_ctor_set_uint8(x_178, sizeof(void*)*2, x_169);
if (lean_is_scalar(x_177)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_177;
}
lean_ctor_set(x_179, 0, x_175);
lean_ctor_set(x_179, 1, x_178);
if (lean_is_scalar(x_174)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_174;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_173);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_181 = lean_ctor_get(x_171, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_182 = x_171;
} else {
 lean_dec_ref(x_171);
 x_182 = lean_box(0);
}
x_183 = lean_ctor_get(x_172, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_172, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_185 = x_172;
} else {
 lean_dec_ref(x_172);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_186 = lean_alloc_ctor(0, 2, 1);
} else {
 x_186 = x_165;
}
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_164);
lean_ctor_set_uint8(x_186, sizeof(void*)*2, x_169);
if (lean_is_scalar(x_185)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_185;
}
lean_ctor_set(x_187, 0, x_183);
lean_ctor_set(x_187, 1, x_186);
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
else
{
lean_object* x_189; uint8_t x_190; 
x_189 = lean_ctor_get(x_166, 0);
lean_inc(x_189);
x_190 = lean_unbox(x_189);
lean_dec(x_189);
if (x_190 == 0)
{
lean_object* x_191; uint8_t x_192; uint8_t x_193; lean_object* x_194; lean_object* x_195; 
x_191 = lean_ctor_get(x_166, 1);
lean_inc(x_191);
lean_dec(x_166);
x_192 = l_Lake_JobAction_merge(x_163, x_16);
x_193 = 1;
x_194 = l_Lake_untar(x_3, x_161, x_193, x_162, x_191);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_197 = x_194;
} else {
 lean_dec_ref(x_194);
 x_197 = lean_box(0);
}
x_198 = lean_ctor_get(x_195, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_195, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_200 = x_195;
} else {
 lean_dec_ref(x_195);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_201 = lean_alloc_ctor(0, 2, 1);
} else {
 x_201 = x_165;
}
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_164);
lean_ctor_set_uint8(x_201, sizeof(void*)*2, x_192);
if (lean_is_scalar(x_200)) {
 x_202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_202 = x_200;
}
lean_ctor_set(x_202, 0, x_198);
lean_ctor_set(x_202, 1, x_201);
if (lean_is_scalar(x_197)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_197;
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_196);
return x_203;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_204 = lean_ctor_get(x_194, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_205 = x_194;
} else {
 lean_dec_ref(x_194);
 x_205 = lean_box(0);
}
x_206 = lean_ctor_get(x_195, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_195, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_208 = x_195;
} else {
 lean_dec_ref(x_195);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_209 = lean_alloc_ctor(0, 2, 1);
} else {
 x_209 = x_165;
}
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_164);
lean_ctor_set_uint8(x_209, sizeof(void*)*2, x_192);
if (lean_is_scalar(x_208)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_208;
}
lean_ctor_set(x_210, 0, x_206);
lean_ctor_set(x_210, 1, x_209);
if (lean_is_scalar(x_205)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_205;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_204);
return x_211;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_161);
lean_dec(x_3);
x_212 = lean_ctor_get(x_166, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_213 = x_166;
} else {
 lean_dec_ref(x_166);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_214 = lean_alloc_ctor(0, 2, 1);
} else {
 x_214 = x_165;
}
lean_ctor_set(x_214, 0, x_162);
lean_ctor_set(x_214, 1, x_164);
lean_ctor_set_uint8(x_214, sizeof(void*)*2, x_163);
x_215 = lean_box(0);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_214);
if (lean_is_scalar(x_213)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_213;
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_212);
return x_217;
}
}
}
}
else
{
uint8_t x_218; 
lean_dec(x_3);
lean_dec(x_1);
x_218 = !lean_is_exclusive(x_17);
if (x_218 == 0)
{
lean_object* x_219; uint8_t x_220; 
x_219 = lean_ctor_get(x_17, 0);
lean_dec(x_219);
x_220 = !lean_is_exclusive(x_18);
if (x_220 == 0)
{
return x_17;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_18, 0);
x_222 = lean_ctor_get(x_18, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_18);
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
lean_ctor_set(x_17, 0, x_223);
return x_17;
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_224 = lean_ctor_get(x_17, 1);
lean_inc(x_224);
lean_dec(x_17);
x_225 = lean_ctor_get(x_18, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_18, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_227 = x_18;
} else {
 lean_dec_ref(x_18);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_226);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_224);
return x_229;
}
}
}
else
{
uint8_t x_230; 
lean_dec(x_3);
lean_dec(x_1);
x_230 = !lean_is_exclusive(x_17);
if (x_230 == 0)
{
return x_17;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_17, 0);
x_232 = lean_ctor_get(x_17, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_17);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchBuildArchive___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchBuildArchive___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchBuildArchive___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_7);
lean_dec(x_7);
x_13 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchBuildArchive___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_12, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_28; 
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_ctor_get(x_4, 1);
x_31 = lean_get_set_stdout(x_1, x_5);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_3(x_2, x_3, x_4, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_36, 0);
x_43 = lean_ctor_get(x_36, 1);
x_44 = lean_get_set_stdout(x_32, x_37);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_39);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_35, 0, x_47);
x_6 = x_35;
x_7 = x_45;
goto block_27;
}
else
{
uint8_t x_48; 
lean_free_object(x_36);
lean_dec(x_43);
lean_dec(x_42);
lean_free_object(x_35);
lean_dec(x_39);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_44, 0);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_44);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_36, 0);
x_53 = lean_ctor_get_uint8(x_36, sizeof(void*)*2);
x_54 = lean_ctor_get(x_36, 1);
lean_inc(x_54);
lean_inc(x_52);
lean_dec(x_36);
x_55 = lean_get_set_stdout(x_32, x_37);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_53);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_39);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_35, 1, x_57);
lean_ctor_set(x_35, 0, x_59);
x_6 = x_35;
x_7 = x_56;
goto block_27;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_54);
lean_dec(x_52);
lean_free_object(x_35);
lean_dec(x_39);
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_62 = x_55;
} else {
 lean_dec_ref(x_55);
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
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_35, 0);
lean_inc(x_64);
lean_dec(x_35);
x_65 = lean_ctor_get(x_36, 0);
lean_inc(x_65);
x_66 = lean_ctor_get_uint8(x_36, sizeof(void*)*2);
x_67 = lean_ctor_get(x_36, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_68 = x_36;
} else {
 lean_dec_ref(x_36);
 x_68 = lean_box(0);
}
x_69 = lean_get_set_stdout(x_32, x_37);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
if (lean_is_scalar(x_68)) {
 x_71 = lean_alloc_ctor(0, 2, 1);
} else {
 x_71 = x_68;
}
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_67);
lean_ctor_set_uint8(x_71, sizeof(void*)*2, x_66);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_64);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
x_6 = x_74;
x_7 = x_70;
goto block_27;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_64);
x_75 = lean_ctor_get(x_69, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_69, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_77 = x_69;
} else {
 lean_dec_ref(x_69);
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
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_ctor_get(x_35, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_34, 1);
lean_inc(x_80);
lean_dec(x_34);
x_81 = !lean_is_exclusive(x_35);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_35, 0);
x_83 = lean_ctor_get(x_35, 1);
lean_dec(x_83);
x_84 = !lean_is_exclusive(x_79);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_79, 0);
x_86 = lean_ctor_get(x_79, 1);
x_87 = lean_get_set_stdout(x_32, x_80);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_6 = x_35;
x_7 = x_88;
goto block_27;
}
else
{
uint8_t x_89; 
lean_free_object(x_79);
lean_dec(x_86);
lean_dec(x_85);
lean_free_object(x_35);
lean_dec(x_82);
x_89 = !lean_is_exclusive(x_87);
if (x_89 == 0)
{
return x_87;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_87, 0);
x_91 = lean_ctor_get(x_87, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_87);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_79, 0);
x_94 = lean_ctor_get_uint8(x_79, sizeof(void*)*2);
x_95 = lean_ctor_get(x_79, 1);
lean_inc(x_95);
lean_inc(x_93);
lean_dec(x_79);
x_96 = lean_get_set_stdout(x_32, x_80);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_98 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_98, 0, x_93);
lean_ctor_set(x_98, 1, x_95);
lean_ctor_set_uint8(x_98, sizeof(void*)*2, x_94);
lean_ctor_set(x_35, 1, x_98);
x_6 = x_35;
x_7 = x_97;
goto block_27;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_95);
lean_dec(x_93);
lean_free_object(x_35);
lean_dec(x_82);
x_99 = lean_ctor_get(x_96, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_101 = x_96;
} else {
 lean_dec_ref(x_96);
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
lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = lean_ctor_get(x_35, 0);
lean_inc(x_103);
lean_dec(x_35);
x_104 = lean_ctor_get(x_79, 0);
lean_inc(x_104);
x_105 = lean_ctor_get_uint8(x_79, sizeof(void*)*2);
x_106 = lean_ctor_get(x_79, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_107 = x_79;
} else {
 lean_dec_ref(x_79);
 x_107 = lean_box(0);
}
x_108 = lean_get_set_stdout(x_32, x_80);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
if (lean_is_scalar(x_107)) {
 x_110 = lean_alloc_ctor(0, 2, 1);
} else {
 x_110 = x_107;
}
lean_ctor_set(x_110, 0, x_104);
lean_ctor_set(x_110, 1, x_106);
lean_ctor_set_uint8(x_110, sizeof(void*)*2, x_105);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_103);
lean_ctor_set(x_111, 1, x_110);
x_6 = x_111;
x_7 = x_109;
goto block_27;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_104);
lean_dec(x_103);
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
}
}
else
{
uint8_t x_116; 
lean_dec(x_32);
x_116 = !lean_is_exclusive(x_34);
if (x_116 == 0)
{
return x_34;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_34, 0);
x_118 = lean_ctor_get(x_34, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_34);
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
lean_free_object(x_4);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_120 = !lean_is_exclusive(x_31);
if (x_120 == 0)
{
return x_31;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_31, 0);
x_122 = lean_ctor_get(x_31, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_31);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_4, 0);
x_125 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_126 = lean_ctor_get(x_4, 1);
lean_inc(x_126);
lean_inc(x_124);
lean_dec(x_4);
x_127 = lean_get_set_stdout(x_1, x_5);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_130, 0, x_124);
lean_ctor_set(x_130, 1, x_126);
lean_ctor_set_uint8(x_130, sizeof(void*)*2, x_125);
x_131 = lean_apply_3(x_2, x_3, x_130, x_129);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_dec(x_131);
x_135 = lean_ctor_get(x_132, 0);
lean_inc(x_135);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_136 = x_132;
} else {
 lean_dec_ref(x_132);
 x_136 = lean_box(0);
}
x_137 = lean_ctor_get(x_133, 0);
lean_inc(x_137);
x_138 = lean_ctor_get_uint8(x_133, sizeof(void*)*2);
x_139 = lean_ctor_get(x_133, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_140 = x_133;
} else {
 lean_dec_ref(x_133);
 x_140 = lean_box(0);
}
x_141 = lean_get_set_stdout(x_128, x_134);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_dec(x_141);
if (lean_is_scalar(x_140)) {
 x_143 = lean_alloc_ctor(0, 2, 1);
} else {
 x_143 = x_140;
}
lean_ctor_set(x_143, 0, x_137);
lean_ctor_set(x_143, 1, x_139);
lean_ctor_set_uint8(x_143, sizeof(void*)*2, x_138);
x_144 = lean_box(0);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_135);
lean_ctor_set(x_145, 1, x_144);
if (lean_is_scalar(x_136)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_136;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_143);
x_6 = x_146;
x_7 = x_142;
goto block_27;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
x_147 = lean_ctor_get(x_141, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_141, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_149 = x_141;
} else {
 lean_dec_ref(x_141);
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
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_151 = lean_ctor_get(x_132, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_131, 1);
lean_inc(x_152);
lean_dec(x_131);
x_153 = lean_ctor_get(x_132, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_154 = x_132;
} else {
 lean_dec_ref(x_132);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_151, 0);
lean_inc(x_155);
x_156 = lean_ctor_get_uint8(x_151, sizeof(void*)*2);
x_157 = lean_ctor_get(x_151, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_158 = x_151;
} else {
 lean_dec_ref(x_151);
 x_158 = lean_box(0);
}
x_159 = lean_get_set_stdout(x_128, x_152);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
lean_dec(x_159);
if (lean_is_scalar(x_158)) {
 x_161 = lean_alloc_ctor(0, 2, 1);
} else {
 x_161 = x_158;
}
lean_ctor_set(x_161, 0, x_155);
lean_ctor_set(x_161, 1, x_157);
lean_ctor_set_uint8(x_161, sizeof(void*)*2, x_156);
if (lean_is_scalar(x_154)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_154;
}
lean_ctor_set(x_162, 0, x_153);
lean_ctor_set(x_162, 1, x_161);
x_6 = x_162;
x_7 = x_160;
goto block_27;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
x_163 = lean_ctor_get(x_159, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_159, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_165 = x_159;
} else {
 lean_dec_ref(x_159);
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
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_128);
x_167 = lean_ctor_get(x_131, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_131, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_169 = x_131;
} else {
 lean_dec_ref(x_131);
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
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_3);
lean_dec(x_2);
x_171 = lean_ctor_get(x_127, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_127, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_173 = x_127;
} else {
 lean_dec_ref(x_127);
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
block_27:
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_dec(x_12);
lean_ctor_set(x_6, 0, x_11);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 0, x_6);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
lean_ctor_set(x_6, 0, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_16);
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_6);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_7);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_6);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_7);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_28; 
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_ctor_get(x_4, 1);
x_31 = lean_get_set_stdin(x_1, x_5);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_3(x_2, x_3, x_4, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_36, 0);
x_43 = lean_ctor_get(x_36, 1);
x_44 = lean_get_set_stdin(x_32, x_37);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_39);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_35, 0, x_47);
x_6 = x_35;
x_7 = x_45;
goto block_27;
}
else
{
uint8_t x_48; 
lean_free_object(x_36);
lean_dec(x_43);
lean_dec(x_42);
lean_free_object(x_35);
lean_dec(x_39);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_44, 0);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_44);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_36, 0);
x_53 = lean_ctor_get_uint8(x_36, sizeof(void*)*2);
x_54 = lean_ctor_get(x_36, 1);
lean_inc(x_54);
lean_inc(x_52);
lean_dec(x_36);
x_55 = lean_get_set_stdin(x_32, x_37);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_53);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_39);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_35, 1, x_57);
lean_ctor_set(x_35, 0, x_59);
x_6 = x_35;
x_7 = x_56;
goto block_27;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_54);
lean_dec(x_52);
lean_free_object(x_35);
lean_dec(x_39);
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_62 = x_55;
} else {
 lean_dec_ref(x_55);
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
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_35, 0);
lean_inc(x_64);
lean_dec(x_35);
x_65 = lean_ctor_get(x_36, 0);
lean_inc(x_65);
x_66 = lean_ctor_get_uint8(x_36, sizeof(void*)*2);
x_67 = lean_ctor_get(x_36, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_68 = x_36;
} else {
 lean_dec_ref(x_36);
 x_68 = lean_box(0);
}
x_69 = lean_get_set_stdin(x_32, x_37);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
if (lean_is_scalar(x_68)) {
 x_71 = lean_alloc_ctor(0, 2, 1);
} else {
 x_71 = x_68;
}
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_67);
lean_ctor_set_uint8(x_71, sizeof(void*)*2, x_66);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_64);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
x_6 = x_74;
x_7 = x_70;
goto block_27;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_64);
x_75 = lean_ctor_get(x_69, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_69, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_77 = x_69;
} else {
 lean_dec_ref(x_69);
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
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_ctor_get(x_35, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_34, 1);
lean_inc(x_80);
lean_dec(x_34);
x_81 = !lean_is_exclusive(x_35);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_35, 0);
x_83 = lean_ctor_get(x_35, 1);
lean_dec(x_83);
x_84 = !lean_is_exclusive(x_79);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_79, 0);
x_86 = lean_ctor_get(x_79, 1);
x_87 = lean_get_set_stdin(x_32, x_80);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_6 = x_35;
x_7 = x_88;
goto block_27;
}
else
{
uint8_t x_89; 
lean_free_object(x_79);
lean_dec(x_86);
lean_dec(x_85);
lean_free_object(x_35);
lean_dec(x_82);
x_89 = !lean_is_exclusive(x_87);
if (x_89 == 0)
{
return x_87;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_87, 0);
x_91 = lean_ctor_get(x_87, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_87);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_79, 0);
x_94 = lean_ctor_get_uint8(x_79, sizeof(void*)*2);
x_95 = lean_ctor_get(x_79, 1);
lean_inc(x_95);
lean_inc(x_93);
lean_dec(x_79);
x_96 = lean_get_set_stdin(x_32, x_80);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_98 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_98, 0, x_93);
lean_ctor_set(x_98, 1, x_95);
lean_ctor_set_uint8(x_98, sizeof(void*)*2, x_94);
lean_ctor_set(x_35, 1, x_98);
x_6 = x_35;
x_7 = x_97;
goto block_27;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_95);
lean_dec(x_93);
lean_free_object(x_35);
lean_dec(x_82);
x_99 = lean_ctor_get(x_96, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_101 = x_96;
} else {
 lean_dec_ref(x_96);
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
lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = lean_ctor_get(x_35, 0);
lean_inc(x_103);
lean_dec(x_35);
x_104 = lean_ctor_get(x_79, 0);
lean_inc(x_104);
x_105 = lean_ctor_get_uint8(x_79, sizeof(void*)*2);
x_106 = lean_ctor_get(x_79, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_107 = x_79;
} else {
 lean_dec_ref(x_79);
 x_107 = lean_box(0);
}
x_108 = lean_get_set_stdin(x_32, x_80);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
if (lean_is_scalar(x_107)) {
 x_110 = lean_alloc_ctor(0, 2, 1);
} else {
 x_110 = x_107;
}
lean_ctor_set(x_110, 0, x_104);
lean_ctor_set(x_110, 1, x_106);
lean_ctor_set_uint8(x_110, sizeof(void*)*2, x_105);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_103);
lean_ctor_set(x_111, 1, x_110);
x_6 = x_111;
x_7 = x_109;
goto block_27;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_104);
lean_dec(x_103);
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
}
}
else
{
uint8_t x_116; 
lean_dec(x_32);
x_116 = !lean_is_exclusive(x_34);
if (x_116 == 0)
{
return x_34;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_34, 0);
x_118 = lean_ctor_get(x_34, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_34);
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
lean_free_object(x_4);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_120 = !lean_is_exclusive(x_31);
if (x_120 == 0)
{
return x_31;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_31, 0);
x_122 = lean_ctor_get(x_31, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_31);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_4, 0);
x_125 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_126 = lean_ctor_get(x_4, 1);
lean_inc(x_126);
lean_inc(x_124);
lean_dec(x_4);
x_127 = lean_get_set_stdin(x_1, x_5);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_130, 0, x_124);
lean_ctor_set(x_130, 1, x_126);
lean_ctor_set_uint8(x_130, sizeof(void*)*2, x_125);
x_131 = lean_apply_3(x_2, x_3, x_130, x_129);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_dec(x_131);
x_135 = lean_ctor_get(x_132, 0);
lean_inc(x_135);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_136 = x_132;
} else {
 lean_dec_ref(x_132);
 x_136 = lean_box(0);
}
x_137 = lean_ctor_get(x_133, 0);
lean_inc(x_137);
x_138 = lean_ctor_get_uint8(x_133, sizeof(void*)*2);
x_139 = lean_ctor_get(x_133, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_140 = x_133;
} else {
 lean_dec_ref(x_133);
 x_140 = lean_box(0);
}
x_141 = lean_get_set_stdin(x_128, x_134);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_dec(x_141);
if (lean_is_scalar(x_140)) {
 x_143 = lean_alloc_ctor(0, 2, 1);
} else {
 x_143 = x_140;
}
lean_ctor_set(x_143, 0, x_137);
lean_ctor_set(x_143, 1, x_139);
lean_ctor_set_uint8(x_143, sizeof(void*)*2, x_138);
x_144 = lean_box(0);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_135);
lean_ctor_set(x_145, 1, x_144);
if (lean_is_scalar(x_136)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_136;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_143);
x_6 = x_146;
x_7 = x_142;
goto block_27;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
x_147 = lean_ctor_get(x_141, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_141, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_149 = x_141;
} else {
 lean_dec_ref(x_141);
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
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_151 = lean_ctor_get(x_132, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_131, 1);
lean_inc(x_152);
lean_dec(x_131);
x_153 = lean_ctor_get(x_132, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_154 = x_132;
} else {
 lean_dec_ref(x_132);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_151, 0);
lean_inc(x_155);
x_156 = lean_ctor_get_uint8(x_151, sizeof(void*)*2);
x_157 = lean_ctor_get(x_151, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_158 = x_151;
} else {
 lean_dec_ref(x_151);
 x_158 = lean_box(0);
}
x_159 = lean_get_set_stdin(x_128, x_152);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
lean_dec(x_159);
if (lean_is_scalar(x_158)) {
 x_161 = lean_alloc_ctor(0, 2, 1);
} else {
 x_161 = x_158;
}
lean_ctor_set(x_161, 0, x_155);
lean_ctor_set(x_161, 1, x_157);
lean_ctor_set_uint8(x_161, sizeof(void*)*2, x_156);
if (lean_is_scalar(x_154)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_154;
}
lean_ctor_set(x_162, 0, x_153);
lean_ctor_set(x_162, 1, x_161);
x_6 = x_162;
x_7 = x_160;
goto block_27;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
x_163 = lean_ctor_get(x_159, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_159, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_165 = x_159;
} else {
 lean_dec_ref(x_159);
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
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_128);
x_167 = lean_ctor_get(x_131, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_131, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_169 = x_131;
} else {
 lean_dec_ref(x_131);
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
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_3);
lean_dec(x_2);
x_171 = lean_ctor_get(x_127, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_127, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_173 = x_127;
} else {
 lean_dec_ref(x_127);
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
block_27:
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_dec(x_12);
lean_ctor_set(x_6, 0, x_11);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 0, x_6);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
lean_ctor_set(x_6, 0, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_16);
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_6);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_7);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_6);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_7);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_28; 
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_ctor_get(x_4, 1);
x_31 = lean_get_set_stderr(x_1, x_5);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_3(x_2, x_3, x_4, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_36, 0);
x_43 = lean_ctor_get(x_36, 1);
x_44 = lean_get_set_stderr(x_32, x_37);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_39);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_35, 0, x_47);
x_6 = x_35;
x_7 = x_45;
goto block_27;
}
else
{
uint8_t x_48; 
lean_free_object(x_36);
lean_dec(x_43);
lean_dec(x_42);
lean_free_object(x_35);
lean_dec(x_39);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_44, 0);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_44);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_36, 0);
x_53 = lean_ctor_get_uint8(x_36, sizeof(void*)*2);
x_54 = lean_ctor_get(x_36, 1);
lean_inc(x_54);
lean_inc(x_52);
lean_dec(x_36);
x_55 = lean_get_set_stderr(x_32, x_37);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_53);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_39);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_35, 1, x_57);
lean_ctor_set(x_35, 0, x_59);
x_6 = x_35;
x_7 = x_56;
goto block_27;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_54);
lean_dec(x_52);
lean_free_object(x_35);
lean_dec(x_39);
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_62 = x_55;
} else {
 lean_dec_ref(x_55);
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
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_35, 0);
lean_inc(x_64);
lean_dec(x_35);
x_65 = lean_ctor_get(x_36, 0);
lean_inc(x_65);
x_66 = lean_ctor_get_uint8(x_36, sizeof(void*)*2);
x_67 = lean_ctor_get(x_36, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_68 = x_36;
} else {
 lean_dec_ref(x_36);
 x_68 = lean_box(0);
}
x_69 = lean_get_set_stderr(x_32, x_37);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
if (lean_is_scalar(x_68)) {
 x_71 = lean_alloc_ctor(0, 2, 1);
} else {
 x_71 = x_68;
}
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_67);
lean_ctor_set_uint8(x_71, sizeof(void*)*2, x_66);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_64);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
x_6 = x_74;
x_7 = x_70;
goto block_27;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_64);
x_75 = lean_ctor_get(x_69, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_69, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_77 = x_69;
} else {
 lean_dec_ref(x_69);
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
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_ctor_get(x_35, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_34, 1);
lean_inc(x_80);
lean_dec(x_34);
x_81 = !lean_is_exclusive(x_35);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_35, 0);
x_83 = lean_ctor_get(x_35, 1);
lean_dec(x_83);
x_84 = !lean_is_exclusive(x_79);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_79, 0);
x_86 = lean_ctor_get(x_79, 1);
x_87 = lean_get_set_stderr(x_32, x_80);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_6 = x_35;
x_7 = x_88;
goto block_27;
}
else
{
uint8_t x_89; 
lean_free_object(x_79);
lean_dec(x_86);
lean_dec(x_85);
lean_free_object(x_35);
lean_dec(x_82);
x_89 = !lean_is_exclusive(x_87);
if (x_89 == 0)
{
return x_87;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_87, 0);
x_91 = lean_ctor_get(x_87, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_87);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_79, 0);
x_94 = lean_ctor_get_uint8(x_79, sizeof(void*)*2);
x_95 = lean_ctor_get(x_79, 1);
lean_inc(x_95);
lean_inc(x_93);
lean_dec(x_79);
x_96 = lean_get_set_stderr(x_32, x_80);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_98 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_98, 0, x_93);
lean_ctor_set(x_98, 1, x_95);
lean_ctor_set_uint8(x_98, sizeof(void*)*2, x_94);
lean_ctor_set(x_35, 1, x_98);
x_6 = x_35;
x_7 = x_97;
goto block_27;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_95);
lean_dec(x_93);
lean_free_object(x_35);
lean_dec(x_82);
x_99 = lean_ctor_get(x_96, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_101 = x_96;
} else {
 lean_dec_ref(x_96);
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
lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = lean_ctor_get(x_35, 0);
lean_inc(x_103);
lean_dec(x_35);
x_104 = lean_ctor_get(x_79, 0);
lean_inc(x_104);
x_105 = lean_ctor_get_uint8(x_79, sizeof(void*)*2);
x_106 = lean_ctor_get(x_79, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_107 = x_79;
} else {
 lean_dec_ref(x_79);
 x_107 = lean_box(0);
}
x_108 = lean_get_set_stderr(x_32, x_80);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
if (lean_is_scalar(x_107)) {
 x_110 = lean_alloc_ctor(0, 2, 1);
} else {
 x_110 = x_107;
}
lean_ctor_set(x_110, 0, x_104);
lean_ctor_set(x_110, 1, x_106);
lean_ctor_set_uint8(x_110, sizeof(void*)*2, x_105);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_103);
lean_ctor_set(x_111, 1, x_110);
x_6 = x_111;
x_7 = x_109;
goto block_27;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_104);
lean_dec(x_103);
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
}
}
else
{
uint8_t x_116; 
lean_dec(x_32);
x_116 = !lean_is_exclusive(x_34);
if (x_116 == 0)
{
return x_34;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_34, 0);
x_118 = lean_ctor_get(x_34, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_34);
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
lean_free_object(x_4);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_120 = !lean_is_exclusive(x_31);
if (x_120 == 0)
{
return x_31;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_31, 0);
x_122 = lean_ctor_get(x_31, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_31);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_4, 0);
x_125 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_126 = lean_ctor_get(x_4, 1);
lean_inc(x_126);
lean_inc(x_124);
lean_dec(x_4);
x_127 = lean_get_set_stderr(x_1, x_5);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_130, 0, x_124);
lean_ctor_set(x_130, 1, x_126);
lean_ctor_set_uint8(x_130, sizeof(void*)*2, x_125);
x_131 = lean_apply_3(x_2, x_3, x_130, x_129);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_dec(x_131);
x_135 = lean_ctor_get(x_132, 0);
lean_inc(x_135);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_136 = x_132;
} else {
 lean_dec_ref(x_132);
 x_136 = lean_box(0);
}
x_137 = lean_ctor_get(x_133, 0);
lean_inc(x_137);
x_138 = lean_ctor_get_uint8(x_133, sizeof(void*)*2);
x_139 = lean_ctor_get(x_133, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_140 = x_133;
} else {
 lean_dec_ref(x_133);
 x_140 = lean_box(0);
}
x_141 = lean_get_set_stderr(x_128, x_134);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_dec(x_141);
if (lean_is_scalar(x_140)) {
 x_143 = lean_alloc_ctor(0, 2, 1);
} else {
 x_143 = x_140;
}
lean_ctor_set(x_143, 0, x_137);
lean_ctor_set(x_143, 1, x_139);
lean_ctor_set_uint8(x_143, sizeof(void*)*2, x_138);
x_144 = lean_box(0);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_135);
lean_ctor_set(x_145, 1, x_144);
if (lean_is_scalar(x_136)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_136;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_143);
x_6 = x_146;
x_7 = x_142;
goto block_27;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
x_147 = lean_ctor_get(x_141, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_141, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_149 = x_141;
} else {
 lean_dec_ref(x_141);
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
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_151 = lean_ctor_get(x_132, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_131, 1);
lean_inc(x_152);
lean_dec(x_131);
x_153 = lean_ctor_get(x_132, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_154 = x_132;
} else {
 lean_dec_ref(x_132);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_151, 0);
lean_inc(x_155);
x_156 = lean_ctor_get_uint8(x_151, sizeof(void*)*2);
x_157 = lean_ctor_get(x_151, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_158 = x_151;
} else {
 lean_dec_ref(x_151);
 x_158 = lean_box(0);
}
x_159 = lean_get_set_stderr(x_128, x_152);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
lean_dec(x_159);
if (lean_is_scalar(x_158)) {
 x_161 = lean_alloc_ctor(0, 2, 1);
} else {
 x_161 = x_158;
}
lean_ctor_set(x_161, 0, x_155);
lean_ctor_set(x_161, 1, x_157);
lean_ctor_set_uint8(x_161, sizeof(void*)*2, x_156);
if (lean_is_scalar(x_154)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_154;
}
lean_ctor_set(x_162, 0, x_153);
lean_ctor_set(x_162, 1, x_161);
x_6 = x_162;
x_7 = x_160;
goto block_27;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
x_163 = lean_ctor_get(x_159, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_159, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_165 = x_159;
} else {
 lean_dec_ref(x_159);
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
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_128);
x_167 = lean_ctor_get(x_131, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_131, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_169 = x_131;
} else {
 lean_dec_ref(x_131);
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
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_3);
lean_dec(x_2);
x_171 = lean_ctor_get(x_127, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_127, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_173 = x_127;
} else {
 lean_dec_ref(x_127);
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
block_27:
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_dec(x_12);
lean_ctor_set(x_6, 0, x_11);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 0, x_6);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
lean_ctor_set(x_6, 0, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_16);
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_6);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_7);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_6);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_7);
return x_26;
}
}
}
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__1() {
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
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.String.Extra", 22, 22);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String.fromUTF8!", 16, 16);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid UTF-8 string", 20, 20);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__2;
x_2 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__3;
x_3 = lean_unsigned_to_nat(100u);
x_4 = lean_unsigned_to_nat(47u);
x_5 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__1;
x_10 = lean_st_mk_ref(x_9, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_mk_ref(x_9, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_IO_FS_Stream_ofBuffer(x_11);
lean_inc(x_14);
x_17 = l_IO_FS_Stream_ofBuffer(x_14);
if (x_2 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_closure((void*)(l_IO_withStdout___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2), 5, 2);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_1);
x_19 = l_IO_withStdin___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__3(x_16, x_18, x_3, x_4, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
x_29 = lean_st_ref_get(x_14, x_22);
lean_dec(x_14);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_string_validate_utf8(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_32);
x_34 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__5;
x_35 = l_panic___at_String_fromUTF8_x21___spec__1(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_24);
lean_ctor_set(x_20, 0, x_36);
lean_ctor_set(x_29, 0, x_20);
return x_29;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_string_from_utf8_unchecked(x_32);
lean_dec(x_32);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_24);
lean_ctor_set(x_20, 0, x_38);
lean_ctor_set(x_29, 0, x_20);
return x_29;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_29, 0);
x_40 = lean_ctor_get(x_29, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_29);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_string_validate_utf8(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_41);
x_43 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__5;
x_44 = l_panic___at_String_fromUTF8_x21___spec__1(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_24);
lean_ctor_set(x_20, 0, x_45);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_20);
lean_ctor_set(x_46, 1, x_40);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_string_from_utf8_unchecked(x_41);
lean_dec(x_41);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_24);
lean_ctor_set(x_20, 0, x_48);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_20);
lean_ctor_set(x_49, 1, x_40);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_free_object(x_21);
lean_dec(x_28);
lean_dec(x_27);
lean_free_object(x_20);
lean_dec(x_24);
x_50 = !lean_is_exclusive(x_29);
if (x_50 == 0)
{
return x_29;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_29, 0);
x_52 = lean_ctor_get(x_29, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_29);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_21, 0);
x_55 = lean_ctor_get_uint8(x_21, sizeof(void*)*2);
x_56 = lean_ctor_get(x_21, 1);
lean_inc(x_56);
lean_inc(x_54);
lean_dec(x_21);
x_57 = lean_st_ref_get(x_14, x_22);
lean_dec(x_14);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
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
x_61 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_61, 0, x_54);
lean_ctor_set(x_61, 1, x_56);
lean_ctor_set_uint8(x_61, sizeof(void*)*2, x_55);
x_62 = lean_ctor_get(x_58, 0);
lean_inc(x_62);
lean_dec(x_58);
x_63 = lean_string_validate_utf8(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__5;
x_65 = l_panic___at_String_fromUTF8_x21___spec__1(x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_24);
lean_ctor_set(x_20, 1, x_61);
lean_ctor_set(x_20, 0, x_66);
if (lean_is_scalar(x_60)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_60;
}
lean_ctor_set(x_67, 0, x_20);
lean_ctor_set(x_67, 1, x_59);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_string_from_utf8_unchecked(x_62);
lean_dec(x_62);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_24);
lean_ctor_set(x_20, 1, x_61);
lean_ctor_set(x_20, 0, x_69);
if (lean_is_scalar(x_60)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_60;
}
lean_ctor_set(x_70, 0, x_20);
lean_ctor_set(x_70, 1, x_59);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_56);
lean_dec(x_54);
lean_free_object(x_20);
lean_dec(x_24);
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_57, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_73 = x_57;
} else {
 lean_dec_ref(x_57);
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
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_20, 0);
lean_inc(x_75);
lean_dec(x_20);
x_76 = lean_ctor_get(x_21, 0);
lean_inc(x_76);
x_77 = lean_ctor_get_uint8(x_21, sizeof(void*)*2);
x_78 = lean_ctor_get(x_21, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_79 = x_21;
} else {
 lean_dec_ref(x_21);
 x_79 = lean_box(0);
}
x_80 = lean_st_ref_get(x_14, x_22);
lean_dec(x_14);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_83 = x_80;
} else {
 lean_dec_ref(x_80);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_84 = lean_alloc_ctor(0, 2, 1);
} else {
 x_84 = x_79;
}
lean_ctor_set(x_84, 0, x_76);
lean_ctor_set(x_84, 1, x_78);
lean_ctor_set_uint8(x_84, sizeof(void*)*2, x_77);
x_85 = lean_ctor_get(x_81, 0);
lean_inc(x_85);
lean_dec(x_81);
x_86 = lean_string_validate_utf8(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_85);
x_87 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__5;
x_88 = l_panic___at_String_fromUTF8_x21___spec__1(x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_75);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_84);
if (lean_is_scalar(x_83)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_83;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_82);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_string_from_utf8_unchecked(x_85);
lean_dec(x_85);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_75);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_84);
if (lean_is_scalar(x_83)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_83;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_82);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_76);
lean_dec(x_75);
x_96 = lean_ctor_get(x_80, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_80, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_98 = x_80;
} else {
 lean_dec_ref(x_80);
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
}
else
{
uint8_t x_100; 
lean_dec(x_14);
x_100 = !lean_is_exclusive(x_19);
if (x_100 == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_19, 0);
lean_dec(x_101);
x_102 = !lean_is_exclusive(x_20);
if (x_102 == 0)
{
return x_19;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_20, 0);
x_104 = lean_ctor_get(x_20, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_20);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_19, 0, x_105);
return x_19;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_19, 1);
lean_inc(x_106);
lean_dec(x_19);
x_107 = lean_ctor_get(x_20, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_20, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_109 = x_20;
} else {
 lean_dec_ref(x_20);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_106);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_14);
x_112 = !lean_is_exclusive(x_19);
if (x_112 == 0)
{
return x_19;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_19, 0);
x_114 = lean_ctor_get(x_19, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_19);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_inc(x_17);
x_116 = lean_alloc_closure((void*)(l_IO_withStderr___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__4), 5, 2);
lean_closure_set(x_116, 0, x_17);
lean_closure_set(x_116, 1, x_1);
x_117 = lean_alloc_closure((void*)(l_IO_withStdout___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2), 5, 2);
lean_closure_set(x_117, 0, x_17);
lean_closure_set(x_117, 1, x_116);
x_118 = l_IO_withStdin___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__3(x_16, x_117, x_3, x_4, x_15);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_dec(x_118);
x_122 = !lean_is_exclusive(x_119);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get(x_119, 0);
x_124 = lean_ctor_get(x_119, 1);
lean_dec(x_124);
x_125 = !lean_is_exclusive(x_120);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_120, 0);
x_127 = lean_ctor_get(x_120, 1);
x_128 = lean_st_ref_get(x_14, x_121);
lean_dec(x_14);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_130 = lean_ctor_get(x_128, 0);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
lean_dec(x_130);
x_132 = lean_string_validate_utf8(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_131);
x_133 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__5;
x_134 = l_panic___at_String_fromUTF8_x21___spec__1(x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_123);
lean_ctor_set(x_119, 0, x_135);
lean_ctor_set(x_128, 0, x_119);
return x_128;
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_string_from_utf8_unchecked(x_131);
lean_dec(x_131);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_123);
lean_ctor_set(x_119, 0, x_137);
lean_ctor_set(x_128, 0, x_119);
return x_128;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_138 = lean_ctor_get(x_128, 0);
x_139 = lean_ctor_get(x_128, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_128);
x_140 = lean_ctor_get(x_138, 0);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_string_validate_utf8(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_140);
x_142 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__5;
x_143 = l_panic___at_String_fromUTF8_x21___spec__1(x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_123);
lean_ctor_set(x_119, 0, x_144);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_119);
lean_ctor_set(x_145, 1, x_139);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_string_from_utf8_unchecked(x_140);
lean_dec(x_140);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_123);
lean_ctor_set(x_119, 0, x_147);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_119);
lean_ctor_set(x_148, 1, x_139);
return x_148;
}
}
}
else
{
uint8_t x_149; 
lean_free_object(x_120);
lean_dec(x_127);
lean_dec(x_126);
lean_free_object(x_119);
lean_dec(x_123);
x_149 = !lean_is_exclusive(x_128);
if (x_149 == 0)
{
return x_128;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_128, 0);
x_151 = lean_ctor_get(x_128, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_128);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
else
{
lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; 
x_153 = lean_ctor_get(x_120, 0);
x_154 = lean_ctor_get_uint8(x_120, sizeof(void*)*2);
x_155 = lean_ctor_get(x_120, 1);
lean_inc(x_155);
lean_inc(x_153);
lean_dec(x_120);
x_156 = lean_st_ref_get(x_14, x_121);
lean_dec(x_14);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_159 = x_156;
} else {
 lean_dec_ref(x_156);
 x_159 = lean_box(0);
}
x_160 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_160, 0, x_153);
lean_ctor_set(x_160, 1, x_155);
lean_ctor_set_uint8(x_160, sizeof(void*)*2, x_154);
x_161 = lean_ctor_get(x_157, 0);
lean_inc(x_161);
lean_dec(x_157);
x_162 = lean_string_validate_utf8(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_161);
x_163 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__5;
x_164 = l_panic___at_String_fromUTF8_x21___spec__1(x_163);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_123);
lean_ctor_set(x_119, 1, x_160);
lean_ctor_set(x_119, 0, x_165);
if (lean_is_scalar(x_159)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_159;
}
lean_ctor_set(x_166, 0, x_119);
lean_ctor_set(x_166, 1, x_158);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_string_from_utf8_unchecked(x_161);
lean_dec(x_161);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_123);
lean_ctor_set(x_119, 1, x_160);
lean_ctor_set(x_119, 0, x_168);
if (lean_is_scalar(x_159)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_159;
}
lean_ctor_set(x_169, 0, x_119);
lean_ctor_set(x_169, 1, x_158);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_155);
lean_dec(x_153);
lean_free_object(x_119);
lean_dec(x_123);
x_170 = lean_ctor_get(x_156, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_156, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_172 = x_156;
} else {
 lean_dec_ref(x_156);
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
}
else
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_174 = lean_ctor_get(x_119, 0);
lean_inc(x_174);
lean_dec(x_119);
x_175 = lean_ctor_get(x_120, 0);
lean_inc(x_175);
x_176 = lean_ctor_get_uint8(x_120, sizeof(void*)*2);
x_177 = lean_ctor_get(x_120, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_178 = x_120;
} else {
 lean_dec_ref(x_120);
 x_178 = lean_box(0);
}
x_179 = lean_st_ref_get(x_14, x_121);
lean_dec(x_14);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
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
if (lean_is_scalar(x_178)) {
 x_183 = lean_alloc_ctor(0, 2, 1);
} else {
 x_183 = x_178;
}
lean_ctor_set(x_183, 0, x_175);
lean_ctor_set(x_183, 1, x_177);
lean_ctor_set_uint8(x_183, sizeof(void*)*2, x_176);
x_184 = lean_ctor_get(x_180, 0);
lean_inc(x_184);
lean_dec(x_180);
x_185 = lean_string_validate_utf8(x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_184);
x_186 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__5;
x_187 = l_panic___at_String_fromUTF8_x21___spec__1(x_186);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_174);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_183);
if (lean_is_scalar(x_182)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_182;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_181);
return x_190;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_191 = lean_string_from_utf8_unchecked(x_184);
lean_dec(x_184);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_174);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_183);
if (lean_is_scalar(x_182)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_182;
}
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_181);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_175);
lean_dec(x_174);
x_195 = lean_ctor_get(x_179, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_179, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_197 = x_179;
} else {
 lean_dec_ref(x_179);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
return x_198;
}
}
}
else
{
uint8_t x_199; 
lean_dec(x_14);
x_199 = !lean_is_exclusive(x_118);
if (x_199 == 0)
{
lean_object* x_200; uint8_t x_201; 
x_200 = lean_ctor_get(x_118, 0);
lean_dec(x_200);
x_201 = !lean_is_exclusive(x_119);
if (x_201 == 0)
{
return x_118;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_119, 0);
x_203 = lean_ctor_get(x_119, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_119);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
lean_ctor_set(x_118, 0, x_204);
return x_118;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_205 = lean_ctor_get(x_118, 1);
lean_inc(x_205);
lean_dec(x_118);
x_206 = lean_ctor_get(x_119, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_119, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_208 = x_119;
} else {
 lean_dec_ref(x_119);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_207);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_205);
return x_210;
}
}
}
else
{
uint8_t x_211; 
lean_dec(x_14);
x_211 = !lean_is_exclusive(x_118);
if (x_211 == 0)
{
return x_118;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_118, 0);
x_213 = lean_ctor_get(x_118, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_118);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
}
}
else
{
uint8_t x_215; 
lean_dec(x_11);
lean_free_object(x_4);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_215 = !lean_is_exclusive(x_13);
if (x_215 == 0)
{
return x_13;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_13, 0);
x_217 = lean_ctor_get(x_13, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_13);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
else
{
uint8_t x_219; 
lean_free_object(x_4);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_219 = !lean_is_exclusive(x_10);
if (x_219 == 0)
{
return x_10;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_10, 0);
x_221 = lean_ctor_get(x_10, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_10);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
}
}
else
{
lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_223 = lean_ctor_get(x_4, 0);
x_224 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_225 = lean_ctor_get(x_4, 1);
lean_inc(x_225);
lean_inc(x_223);
lean_dec(x_4);
x_226 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__1;
x_227 = lean_st_mk_ref(x_226, x_5);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = lean_st_mk_ref(x_226, x_229);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_233, 0, x_223);
lean_ctor_set(x_233, 1, x_225);
lean_ctor_set_uint8(x_233, sizeof(void*)*2, x_224);
x_234 = l_IO_FS_Stream_ofBuffer(x_228);
lean_inc(x_231);
x_235 = l_IO_FS_Stream_ofBuffer(x_231);
if (x_2 == 0)
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_alloc_closure((void*)(l_IO_withStdout___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2), 5, 2);
lean_closure_set(x_236, 0, x_235);
lean_closure_set(x_236, 1, x_1);
x_237 = l_IO_withStdin___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__3(x_234, x_236, x_3, x_233, x_232);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_239 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
x_240 = lean_ctor_get(x_237, 1);
lean_inc(x_240);
lean_dec(x_237);
x_241 = lean_ctor_get(x_238, 0);
lean_inc(x_241);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_242 = x_238;
} else {
 lean_dec_ref(x_238);
 x_242 = lean_box(0);
}
x_243 = lean_ctor_get(x_239, 0);
lean_inc(x_243);
x_244 = lean_ctor_get_uint8(x_239, sizeof(void*)*2);
x_245 = lean_ctor_get(x_239, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_246 = x_239;
} else {
 lean_dec_ref(x_239);
 x_246 = lean_box(0);
}
x_247 = lean_st_ref_get(x_231, x_240);
lean_dec(x_231);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_250 = x_247;
} else {
 lean_dec_ref(x_247);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_251 = lean_alloc_ctor(0, 2, 1);
} else {
 x_251 = x_246;
}
lean_ctor_set(x_251, 0, x_243);
lean_ctor_set(x_251, 1, x_245);
lean_ctor_set_uint8(x_251, sizeof(void*)*2, x_244);
x_252 = lean_ctor_get(x_248, 0);
lean_inc(x_252);
lean_dec(x_248);
x_253 = lean_string_validate_utf8(x_252);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_252);
x_254 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__5;
x_255 = l_panic___at_String_fromUTF8_x21___spec__1(x_254);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_241);
if (lean_is_scalar(x_242)) {
 x_257 = lean_alloc_ctor(0, 2, 0);
} else {
 x_257 = x_242;
}
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_251);
if (lean_is_scalar(x_250)) {
 x_258 = lean_alloc_ctor(0, 2, 0);
} else {
 x_258 = x_250;
}
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_249);
return x_258;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_259 = lean_string_from_utf8_unchecked(x_252);
lean_dec(x_252);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_241);
if (lean_is_scalar(x_242)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_242;
}
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_251);
if (lean_is_scalar(x_250)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_250;
}
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_249);
return x_262;
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
x_263 = lean_ctor_get(x_247, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_247, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_265 = x_247;
} else {
 lean_dec_ref(x_247);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_263);
lean_ctor_set(x_266, 1, x_264);
return x_266;
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_231);
x_267 = lean_ctor_get(x_237, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_268 = x_237;
} else {
 lean_dec_ref(x_237);
 x_268 = lean_box(0);
}
x_269 = lean_ctor_get(x_238, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_238, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_271 = x_238;
} else {
 lean_dec_ref(x_238);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(1, 2, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_269);
lean_ctor_set(x_272, 1, x_270);
if (lean_is_scalar(x_268)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_268;
}
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_267);
return x_273;
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_231);
x_274 = lean_ctor_get(x_237, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_237, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_276 = x_237;
} else {
 lean_dec_ref(x_237);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(1, 2, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_274);
lean_ctor_set(x_277, 1, x_275);
return x_277;
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_inc(x_235);
x_278 = lean_alloc_closure((void*)(l_IO_withStderr___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__4), 5, 2);
lean_closure_set(x_278, 0, x_235);
lean_closure_set(x_278, 1, x_1);
x_279 = lean_alloc_closure((void*)(l_IO_withStdout___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__2), 5, 2);
lean_closure_set(x_279, 0, x_235);
lean_closure_set(x_279, 1, x_278);
x_280 = l_IO_withStdin___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__3(x_234, x_279, x_3, x_233, x_232);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_282 = lean_ctor_get(x_281, 1);
lean_inc(x_282);
x_283 = lean_ctor_get(x_280, 1);
lean_inc(x_283);
lean_dec(x_280);
x_284 = lean_ctor_get(x_281, 0);
lean_inc(x_284);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_285 = x_281;
} else {
 lean_dec_ref(x_281);
 x_285 = lean_box(0);
}
x_286 = lean_ctor_get(x_282, 0);
lean_inc(x_286);
x_287 = lean_ctor_get_uint8(x_282, sizeof(void*)*2);
x_288 = lean_ctor_get(x_282, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_289 = x_282;
} else {
 lean_dec_ref(x_282);
 x_289 = lean_box(0);
}
x_290 = lean_st_ref_get(x_231, x_283);
lean_dec(x_231);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; 
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 x_293 = x_290;
} else {
 lean_dec_ref(x_290);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_289)) {
 x_294 = lean_alloc_ctor(0, 2, 1);
} else {
 x_294 = x_289;
}
lean_ctor_set(x_294, 0, x_286);
lean_ctor_set(x_294, 1, x_288);
lean_ctor_set_uint8(x_294, sizeof(void*)*2, x_287);
x_295 = lean_ctor_get(x_291, 0);
lean_inc(x_295);
lean_dec(x_291);
x_296 = lean_string_validate_utf8(x_295);
if (x_296 == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_295);
x_297 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__5;
x_298 = l_panic___at_String_fromUTF8_x21___spec__1(x_297);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_284);
if (lean_is_scalar(x_285)) {
 x_300 = lean_alloc_ctor(0, 2, 0);
} else {
 x_300 = x_285;
}
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_294);
if (lean_is_scalar(x_293)) {
 x_301 = lean_alloc_ctor(0, 2, 0);
} else {
 x_301 = x_293;
}
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_292);
return x_301;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_302 = lean_string_from_utf8_unchecked(x_295);
lean_dec(x_295);
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_284);
if (lean_is_scalar(x_285)) {
 x_304 = lean_alloc_ctor(0, 2, 0);
} else {
 x_304 = x_285;
}
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_294);
if (lean_is_scalar(x_293)) {
 x_305 = lean_alloc_ctor(0, 2, 0);
} else {
 x_305 = x_293;
}
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_292);
return x_305;
}
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_286);
lean_dec(x_285);
lean_dec(x_284);
x_306 = lean_ctor_get(x_290, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_290, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 x_308 = x_290;
} else {
 lean_dec_ref(x_290);
 x_308 = lean_box(0);
}
if (lean_is_scalar(x_308)) {
 x_309 = lean_alloc_ctor(1, 2, 0);
} else {
 x_309 = x_308;
}
lean_ctor_set(x_309, 0, x_306);
lean_ctor_set(x_309, 1, x_307);
return x_309;
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_dec(x_231);
x_310 = lean_ctor_get(x_280, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_311 = x_280;
} else {
 lean_dec_ref(x_280);
 x_311 = lean_box(0);
}
x_312 = lean_ctor_get(x_281, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_281, 1);
lean_inc(x_313);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_314 = x_281;
} else {
 lean_dec_ref(x_281);
 x_314 = lean_box(0);
}
if (lean_is_scalar(x_314)) {
 x_315 = lean_alloc_ctor(1, 2, 0);
} else {
 x_315 = x_314;
}
lean_ctor_set(x_315, 0, x_312);
lean_ctor_set(x_315, 1, x_313);
if (lean_is_scalar(x_311)) {
 x_316 = lean_alloc_ctor(0, 2, 0);
} else {
 x_316 = x_311;
}
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_310);
return x_316;
}
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_231);
x_317 = lean_ctor_get(x_280, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_280, 1);
lean_inc(x_318);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_319 = x_280;
} else {
 lean_dec_ref(x_280);
 x_319 = lean_box(0);
}
if (lean_is_scalar(x_319)) {
 x_320 = lean_alloc_ctor(1, 2, 0);
} else {
 x_320 = x_319;
}
lean_ctor_set(x_320, 0, x_317);
lean_ctor_set(x_320, 1, x_318);
return x_320;
}
}
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_228);
lean_dec(x_225);
lean_dec(x_223);
lean_dec(x_3);
lean_dec(x_1);
x_321 = lean_ctor_get(x_230, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_230, 1);
lean_inc(x_322);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_323 = x_230;
} else {
 lean_dec_ref(x_230);
 x_323 = lean_box(0);
}
if (lean_is_scalar(x_323)) {
 x_324 = lean_alloc_ctor(1, 2, 0);
} else {
 x_324 = x_323;
}
lean_ctor_set(x_324, 0, x_321);
lean_ctor_set(x_324, 1, x_322);
return x_324;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_225);
lean_dec(x_223);
lean_dec(x_3);
lean_dec(x_1);
x_325 = lean_ctor_get(x_227, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_227, 1);
lean_inc(x_326);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_327 = x_227;
} else {
 lean_dec_ref(x_227);
 x_327 = lean_box(0);
}
if (lean_is_scalar(x_327)) {
 x_328 = lean_alloc_ctor(1, 2, 0);
} else {
 x_328 = x_327;
}
lean_ctor_set(x_328, 0, x_325);
lean_ctor_set(x_328, 1, x_326);
return x_328;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_43; 
lean_inc(x_5);
lean_inc(x_2);
x_43 = lean_apply_4(x_1, x_2, x_5, x_6, x_7);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
lean_inc(x_2);
x_48 = lean_apply_1(x_3, x_2);
x_49 = l_Lake_Package_fetchBuildArchive(x_2, x_46, x_48, x_4, x_5, x_47, x_45);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = !lean_is_exclusive(x_50);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_50, 0);
lean_dec(x_53);
x_54 = 1;
x_55 = lean_box(x_54);
lean_ctor_set(x_50, 0, x_55);
x_8 = x_50;
x_9 = x_51;
goto block_42;
}
else
{
lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_dec(x_50);
x_57 = 1;
x_58 = lean_box(x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
x_8 = x_59;
x_9 = x_51;
goto block_42;
}
}
else
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_49, 1);
lean_inc(x_60);
lean_dec(x_49);
x_61 = !lean_is_exclusive(x_50);
if (x_61 == 0)
{
x_8 = x_50;
x_9 = x_60;
goto block_42;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_50, 0);
x_63 = lean_ctor_get(x_50, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_50);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_8 = x_64;
x_9 = x_60;
goto block_42;
}
}
}
else
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_49);
if (x_65 == 0)
{
return x_49;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_49, 0);
x_67 = lean_ctor_get(x_49, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_49);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; uint8_t x_70; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = lean_ctor_get(x_43, 1);
lean_inc(x_69);
lean_dec(x_43);
x_70 = !lean_is_exclusive(x_44);
if (x_70 == 0)
{
x_8 = x_44;
x_9 = x_69;
goto block_42;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_44, 0);
x_72 = lean_ctor_get(x_44, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_44);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_8 = x_73;
x_9 = x_69;
goto block_42;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_43);
if (x_74 == 0)
{
return x_43;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_43, 0);
x_76 = lean_ctor_get(x_43, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_43);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
block_42:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_8, 1);
x_13 = lean_ctor_get(x_8, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get_uint8(x_12, sizeof(void*)*2);
x_16 = 2;
x_17 = l_Lake_JobAction_merge(x_15, x_16);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_17);
x_18 = 0;
x_19 = lean_box(x_18);
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 0, x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_9);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get_uint8(x_12, sizeof(void*)*2);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_21);
lean_dec(x_12);
x_24 = 2;
x_25 = l_Lake_JobAction_merge(x_22, x_24);
x_26 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_25);
x_27 = 0;
x_28 = lean_box(x_27);
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 1, x_26);
lean_ctor_set(x_8, 0, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_8);
lean_ctor_set(x_29, 1, x_9);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_30 = lean_ctor_get(x_8, 1);
lean_inc(x_30);
lean_dec(x_8);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_30, sizeof(void*)*2);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_34 = x_30;
} else {
 lean_dec_ref(x_30);
 x_34 = lean_box(0);
}
x_35 = 2;
x_36 = l_Lake_JobAction_merge(x_32, x_35);
if (lean_is_scalar(x_34)) {
 x_37 = lean_alloc_ctor(0, 2, 1);
} else {
 x_37 = x_34;
}
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_36);
x_38 = 0;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_9);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 1;
lean_inc(x_2);
x_6 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1(x_1, x_5, x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_string_utf8_byte_size(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; 
x_16 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_11, x_13, x_14);
x_17 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_11, x_16, x_13);
x_18 = lean_string_utf8_extract(x_11, x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
x_19 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__4___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_22 = lean_string_append(x_20, x_21);
x_23 = 1;
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_array_push(x_26, x_24);
lean_ctor_set(x_10, 0, x_27);
x_28 = lean_box(0);
x_29 = lean_unbox(x_12);
lean_dec(x_12);
x_30 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__3(x_29, x_28, x_2, x_10, x_9);
lean_dec(x_2);
return x_30;
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_10, 0);
x_32 = lean_ctor_get_uint8(x_10, sizeof(void*)*2);
x_33 = lean_ctor_get(x_10, 1);
lean_inc(x_33);
lean_inc(x_31);
lean_dec(x_10);
x_34 = lean_array_push(x_31, x_24);
x_35 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_32);
x_36 = lean_box(0);
x_37 = lean_unbox(x_12);
lean_dec(x_12);
x_38 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__3(x_37, x_36, x_2, x_35, x_9);
lean_dec(x_2);
return x_38;
}
}
else
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; 
lean_dec(x_13);
lean_dec(x_11);
x_39 = lean_box(0);
x_40 = lean_unbox(x_12);
lean_dec(x_12);
x_41 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__3(x_40, x_39, x_2, x_10, x_9);
lean_dec(x_2);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_6);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_6, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_7);
if (x_44 == 0)
{
return x_6;
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
lean_ctor_set(x_6, 0, x_47);
return x_6;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_6, 1);
lean_inc(x_48);
lean_dec(x_6);
x_49 = lean_ctor_get(x_7, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_7, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_51 = x_7;
} else {
 lean_dec_ref(x_7);
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
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_6);
if (x_54 == 0)
{
return x_6;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_6, 0);
x_56 = lean_ctor_get(x_6, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_6);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lake_Package_maybeFetchBuildCache___closed__2;
x_8 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__4), 4, 3);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_3);
lean_closure_set(x_8, 2, x_7);
x_9 = l_Task_Priority_default;
x_10 = lean_io_as_task(x_8, x_9, x_6);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_14 = 0;
x_15 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
lean_ctor_set(x_10, 0, x_17);
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_21 = 0;
x_22 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_4);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_5);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
return x_10;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__2___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_12 = lean_ctor_get(x_5, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
x_14 = 1;
x_15 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__1;
x_16 = l_Lean_Name_toString(x_13, x_14, x_15);
x_17 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Lean_Name_toString(x_1, x_14, x_15);
x_22 = lean_string_append(x_20, x_21);
lean_dec(x_21);
x_23 = lean_string_append(x_22, x_17);
x_24 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__1), 7, 4);
lean_closure_set(x_24, 0, x_2);
lean_closure_set(x_24, 1, x_5);
lean_closure_set(x_24, 2, x_3);
lean_closure_set(x_24, 3, x_4);
x_25 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__6___closed__1;
x_26 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate_x27___spec__1___rarg), 5, 2);
lean_closure_set(x_26, 0, x_24);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__5___boxed), 6, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = l_Lake_withRegisterJob___rarg(x_23, x_28, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
return x_29;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__6), 11, 4);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_3);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_4);
x_7 = l_Lake_Package_optBuildCacheFacetConfig___closed__2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__2(x_5, x_2, x_3, x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__3(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_5 == 0)
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get_uint8(x_9, sizeof(void*)*1 + 3);
x_11 = 2;
x_12 = l_Lake_instDecidableEqVerbosity(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_4);
lean_dec(x_3);
x_13 = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1___closed__1;
x_14 = lean_string_append(x_13, x_1);
x_15 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_15);
x_20 = 3;
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = !lean_is_exclusive(x_7);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_array_get_size(x_23);
x_25 = lean_array_push(x_23, x_21);
lean_ctor_set(x_7, 0, x_25);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_7);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_8);
return x_27;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_7, 0);
x_29 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_30 = lean_ctor_get(x_7, 1);
lean_inc(x_30);
lean_inc(x_28);
lean_dec(x_7);
x_31 = lean_array_get_size(x_28);
x_32 = lean_array_push(x_28, x_21);
x_33 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_29);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_8);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; uint8_t x_53; 
x_36 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__2;
x_37 = lean_string_append(x_36, x_2);
x_38 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_39 = lean_string_append(x_37, x_38);
x_40 = 1;
x_41 = l_Lean_Name_toString(x_3, x_40, x_4);
x_42 = lean_string_append(x_39, x_41);
lean_dec(x_41);
x_43 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__4;
x_44 = lean_string_append(x_42, x_43);
x_45 = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1___closed__1;
x_46 = lean_string_append(x_45, x_1);
x_47 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_string_append(x_48, x_44);
lean_dec(x_44);
x_50 = lean_string_append(x_49, x_47);
x_51 = 3;
x_52 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_51);
x_53 = !lean_is_exclusive(x_7);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_7, 0);
x_55 = lean_array_get_size(x_54);
x_56 = lean_array_push(x_54, x_52);
lean_ctor_set(x_7, 0, x_56);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_7);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_8);
return x_58;
}
else
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_7, 0);
x_60 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_61 = lean_ctor_get(x_7, 1);
lean_inc(x_61);
lean_inc(x_59);
lean_dec(x_7);
x_62 = lean_array_get_size(x_59);
x_63 = lean_array_push(x_59, x_52);
x_64 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
lean_ctor_set_uint8(x_64, sizeof(void*)*2, x_60);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_8);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_4);
lean_dec(x_3);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_7);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_8);
return x_69;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1___boxed), 8, 4);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
x_13 = l_Task_Priority_default;
x_14 = 0;
x_15 = l_Lake_BuildTrace_nil;
x_16 = l_Lake_Job_mapM___rarg(x_5, x_12, x_13, x_14, x_8, x_15, x_11);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_9);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_10);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_9);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_10);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_10);
lean_dec(x_9);
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
x_14 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__1;
x_15 = l_Lean_Name_toString(x_12, x_13, x_14);
x_16 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
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
x_25 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__2___boxed), 11, 4);
lean_closure_set(x_25, 0, x_3);
lean_closure_set(x_25, 1, x_15);
lean_closure_set(x_25, 2, x_2);
lean_closure_set(x_25, 3, x_14);
x_26 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Package_recBuildExtraDepTargets___spec__3___rarg), 8, 2);
lean_closure_set(x_26, 0, x_24);
lean_closure_set(x_26, 1, x_25);
x_27 = 0;
x_28 = l_Lake_withRegisterJob___rarg(x_22, x_26, x_27, x_5, x_6, x_7, x_8, x_9, x_10);
return x_28;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__3), 10, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_3);
x_7 = l_Lake_Package_optBuildCacheFacetConfig___closed__2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_6);
return x_12;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("build cache", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1___closed__1;
x_2 = l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__2;
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__3;
x_2 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__4;
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 3;
x_2 = l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__5;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (x_4 == 0)
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 3);
x_10 = 2;
x_11 = l_Lake_instDecidableEqVerbosity(x_9, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_array_get_size(x_13);
x_15 = l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__6;
x_16 = lean_array_push(x_13, x_15);
lean_ctor_set(x_6, 0, x_16);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_6);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_7);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_6, 0);
x_20 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_inc(x_19);
lean_dec(x_6);
x_22 = lean_array_get_size(x_19);
x_23 = l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__6;
x_24 = lean_array_push(x_19, x_23);
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_20);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_7);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; uint8_t x_43; 
x_28 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__2;
x_29 = lean_string_append(x_28, x_1);
x_30 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_31 = lean_string_append(x_29, x_30);
x_32 = 1;
x_33 = l_Lean_Name_toString(x_2, x_32, x_3);
x_34 = lean_string_append(x_31, x_33);
lean_dec(x_33);
x_35 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__4;
x_36 = lean_string_append(x_34, x_35);
x_37 = l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__3;
x_38 = lean_string_append(x_37, x_36);
lean_dec(x_36);
x_39 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_40 = lean_string_append(x_38, x_39);
x_41 = 3;
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = !lean_is_exclusive(x_6);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_6, 0);
x_45 = lean_array_get_size(x_44);
x_46 = lean_array_push(x_44, x_42);
lean_ctor_set(x_6, 0, x_46);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_6);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_7);
return x_48;
}
else
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_6, 0);
x_50 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_51 = lean_ctor_get(x_6, 1);
lean_inc(x_51);
lean_inc(x_49);
lean_dec(x_6);
x_52 = lean_array_get_size(x_49);
x_53 = lean_array_push(x_49, x_42);
x_54 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
lean_ctor_set_uint8(x_54, sizeof(void*)*2, x_50);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_7);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_3);
lean_dec(x_2);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_6);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_7);
return x_59;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___boxed), 7, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
x_12 = l_Task_Priority_default;
x_13 = 0;
x_14 = l_Lake_BuildTrace_nil;
x_15 = l_Lake_Job_mapM___rarg(x_4, x_11, x_12, x_13, x_7, x_14, x_10);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_9);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_8);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_9);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_8);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cache", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_buildCacheFacetConfig___elambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___elambda__1___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Package_buildCacheFacetConfig___elambda__1___closed__2;
x_2 = 1;
x_3 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__1;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = 1;
x_11 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__1;
x_12 = l_Lean_Name_toString(x_9, x_10, x_11);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_14 = lean_string_append(x_13, x_12);
x_15 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lake_Package_buildCacheFacetConfig___elambda__1___closed__3;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_13);
x_20 = l_Lake_Package_optBuildCacheFacetConfig___closed__4;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, lean_box(0));
x_23 = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__2___boxed), 10, 3);
lean_closure_set(x_23, 0, x_12);
lean_closure_set(x_23, 1, x_20);
lean_closure_set(x_23, 2, x_11);
x_24 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Package_recBuildExtraDepTargets___spec__3___rarg), 8, 2);
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
x_1 = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___elambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_buildCacheFacetConfig___closed__1;
x_2 = l_Lake_Package_optBuildCacheFacetConfig___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_buildCacheFacetConfig___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("build.barrel", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_40; lean_object* x_41; 
lean_inc(x_1);
x_40 = l_Lake_Package_getBarrelUrl(x_1, x_2, x_3, x_4);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_ctor_get(x_1, 0);
lean_inc(x_45);
x_46 = l_Lake_defaultLakeDir;
x_47 = l_System_FilePath_join(x_45, x_46);
x_48 = l_Lake_Package_optBarrelFacetConfig___lambda__1___closed__1;
x_49 = l_System_FilePath_join(x_47, x_48);
x_50 = l_Lake_Reservoir_lakeHeaders;
x_51 = l_Lake_Package_fetchBuildArchive(x_1, x_43, x_49, x_50, x_2, x_44, x_42);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
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
lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_52, 0);
lean_dec(x_55);
x_56 = 1;
x_57 = lean_box(x_56);
lean_ctor_set(x_52, 0, x_57);
x_5 = x_52;
x_6 = x_53;
goto block_39;
}
else
{
lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_dec(x_52);
x_59 = 1;
x_60 = lean_box(x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
x_5 = x_61;
x_6 = x_53;
goto block_39;
}
}
else
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_51, 1);
lean_inc(x_62);
lean_dec(x_51);
x_63 = !lean_is_exclusive(x_52);
if (x_63 == 0)
{
x_5 = x_52;
x_6 = x_62;
goto block_39;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_52, 0);
x_65 = lean_ctor_get(x_52, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_52);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_5 = x_66;
x_6 = x_62;
goto block_39;
}
}
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_51);
if (x_67 == 0)
{
return x_51;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_51, 0);
x_69 = lean_ctor_get(x_51, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_51);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; uint8_t x_72; 
lean_dec(x_2);
lean_dec(x_1);
x_71 = lean_ctor_get(x_40, 1);
lean_inc(x_71);
lean_dec(x_40);
x_72 = !lean_is_exclusive(x_41);
if (x_72 == 0)
{
x_5 = x_41;
x_6 = x_71;
goto block_39;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_41, 0);
x_74 = lean_ctor_get(x_41, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_41);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_5 = x_75;
x_6 = x_71;
goto block_39;
}
}
block_39:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_5, 0);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_13 = 2;
x_14 = l_Lake_JobAction_merge(x_12, x_13);
lean_ctor_set_uint8(x_9, sizeof(void*)*2, x_14);
x_15 = 0;
x_16 = lean_box(x_15);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_18);
lean_dec(x_9);
x_21 = 2;
x_22 = l_Lake_JobAction_merge(x_19, x_21);
x_23 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_22);
x_24 = 0;
x_25 = lean_box(x_24);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 1, x_23);
lean_ctor_set(x_5, 0, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_6);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_dec(x_5);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get_uint8(x_27, sizeof(void*)*2);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_31 = x_27;
} else {
 lean_dec_ref(x_27);
 x_31 = lean_box(0);
}
x_32 = 2;
x_33 = l_Lake_JobAction_merge(x_29, x_32);
if (lean_is_scalar(x_31)) {
 x_34 = lean_alloc_ctor(0, 2, 1);
} else {
 x_34 = x_31;
}
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_33);
x_35 = 0;
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_6);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = 1;
x_11 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__1;
x_12 = l_Lean_Name_toString(x_9, x_10, x_11);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__5;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_13);
x_20 = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lambda__1), 4, 1);
lean_closure_set(x_20, 0, x_1);
x_21 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__6___closed__1;
x_22 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate_x27___spec__1___rarg), 5, 2);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__5___boxed), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = l_Lake_withRegisterJob___rarg(x_19, x_24, x_10, x_2, x_3, x_4, x_5, x_6, x_7);
return x_25;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lambda__2), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_optBarrelFacetConfig___closed__1;
x_2 = l_Lake_Package_optBuildCacheFacetConfig___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_optBarrelFacetConfig___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Reservoir build", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1___closed__1;
x_2 = l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__2;
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__3;
x_2 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__4;
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 3;
x_2 = l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__5;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (x_4 == 0)
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 3);
x_10 = 2;
x_11 = l_Lake_instDecidableEqVerbosity(x_9, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_array_get_size(x_13);
x_15 = l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__6;
x_16 = lean_array_push(x_13, x_15);
lean_ctor_set(x_6, 0, x_16);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_6);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_7);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_6, 0);
x_20 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_inc(x_19);
lean_dec(x_6);
x_22 = lean_array_get_size(x_19);
x_23 = l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__6;
x_24 = lean_array_push(x_19, x_23);
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_20);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_7);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; uint8_t x_43; 
x_28 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__2;
x_29 = lean_string_append(x_28, x_1);
x_30 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_31 = lean_string_append(x_29, x_30);
x_32 = 1;
x_33 = l_Lean_Name_toString(x_2, x_32, x_3);
x_34 = lean_string_append(x_31, x_33);
lean_dec(x_33);
x_35 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__4;
x_36 = lean_string_append(x_34, x_35);
x_37 = l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__3;
x_38 = lean_string_append(x_37, x_36);
lean_dec(x_36);
x_39 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_40 = lean_string_append(x_38, x_39);
x_41 = 3;
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = !lean_is_exclusive(x_6);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_6, 0);
x_45 = lean_array_get_size(x_44);
x_46 = lean_array_push(x_44, x_42);
lean_ctor_set(x_6, 0, x_46);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_6);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_7);
return x_48;
}
else
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_6, 0);
x_50 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_51 = lean_ctor_get(x_6, 1);
lean_inc(x_51);
lean_inc(x_49);
lean_dec(x_6);
x_52 = lean_array_get_size(x_49);
x_53 = lean_array_push(x_49, x_42);
x_54 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
lean_ctor_set_uint8(x_54, sizeof(void*)*2, x_50);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_7);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_3);
lean_dec(x_2);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_6);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_7);
return x_59;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___elambda__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___boxed), 7, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
x_12 = l_Task_Priority_default;
x_13 = 0;
x_14 = l_Lake_BuildTrace_nil;
x_15 = l_Lake_Job_mapM___rarg(x_4, x_11, x_12, x_13, x_7, x_14, x_10);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_9);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_8);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_9);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_8);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("barrel", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_barrelFacetConfig___elambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___elambda__1___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Package_barrelFacetConfig___elambda__1___closed__2;
x_2 = 1;
x_3 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__1;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = 1;
x_11 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__1;
x_12 = l_Lean_Name_toString(x_9, x_10, x_11);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_14 = lean_string_append(x_13, x_12);
x_15 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lake_Package_barrelFacetConfig___elambda__1___closed__3;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_13);
x_20 = l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__2;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, lean_box(0));
x_23 = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___elambda__1___lambda__2___boxed), 10, 3);
lean_closure_set(x_23, 0, x_12);
lean_closure_set(x_23, 1, x_20);
lean_closure_set(x_23, 2, x_11);
x_24 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Package_recBuildExtraDepTargets___spec__3___rarg), 8, 2);
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
x_1 = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___elambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_barrelFacetConfig___closed__1;
x_2 = l_Lake_Package_optBuildCacheFacetConfig___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_barrelFacetConfig___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___elambda__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_Package_barrelFacetConfig___elambda__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_42; 
lean_inc(x_4);
lean_inc(x_1);
x_42 = l_Lake_Package_getReleaseUrl(x_1, x_4, x_5, x_6);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
x_48 = l_Lake_defaultLakeDir;
x_49 = l_System_FilePath_join(x_47, x_48);
x_50 = lean_ctor_get(x_2, 16);
x_51 = l_System_FilePath_join(x_49, x_50);
x_52 = l_Lake_Package_fetchBuildArchive(x_1, x_45, x_51, x_3, x_4, x_46, x_44);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = !lean_is_exclusive(x_53);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_53, 0);
lean_dec(x_56);
x_57 = 1;
x_58 = lean_box(x_57);
lean_ctor_set(x_53, 0, x_58);
x_7 = x_53;
x_8 = x_54;
goto block_41;
}
else
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
lean_dec(x_53);
x_60 = 1;
x_61 = lean_box(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
x_7 = x_62;
x_8 = x_54;
goto block_41;
}
}
else
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_52, 1);
lean_inc(x_63);
lean_dec(x_52);
x_64 = !lean_is_exclusive(x_53);
if (x_64 == 0)
{
x_7 = x_53;
x_8 = x_63;
goto block_41;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_53, 0);
x_66 = lean_ctor_get(x_53, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_7 = x_67;
x_8 = x_63;
goto block_41;
}
}
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_52);
if (x_68 == 0)
{
return x_52;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_52, 0);
x_70 = lean_ctor_get(x_52, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_52);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; uint8_t x_73; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_72 = lean_ctor_get(x_42, 1);
lean_inc(x_72);
lean_dec(x_42);
x_73 = !lean_is_exclusive(x_43);
if (x_73 == 0)
{
x_7 = x_43;
x_8 = x_72;
goto block_41;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_43, 0);
x_75 = lean_ctor_get(x_43, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_43);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_7 = x_76;
x_8 = x_72;
goto block_41;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_42);
if (x_77 == 0)
{
return x_42;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_42, 0);
x_79 = lean_ctor_get(x_42, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_42);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
block_41:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_ctor_get(x_7, 0);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
x_15 = 2;
x_16 = l_Lake_JobAction_merge(x_14, x_15);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_16);
x_17 = 0;
x_18 = lean_box(x_17);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_18);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_8);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_20);
lean_dec(x_11);
x_23 = 2;
x_24 = l_Lake_JobAction_merge(x_21, x_23);
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_24);
x_26 = 0;
x_27 = lean_box(x_26);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_7);
lean_ctor_set(x_28, 1, x_8);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_29 = lean_ctor_get(x_7, 1);
lean_inc(x_29);
lean_dec(x_7);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get_uint8(x_29, sizeof(void*)*2);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_33 = x_29;
} else {
 lean_dec_ref(x_29);
 x_33 = lean_box(0);
}
x_34 = 2;
x_35 = l_Lake_JobAction_merge(x_31, x_34);
if (lean_is_scalar(x_33)) {
 x_36 = lean_alloc_ctor(0, 2, 1);
} else {
 x_36 = x_33;
}
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set_uint8(x_36, sizeof(void*)*2, x_35);
x_37 = 0;
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_8);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = 0;
x_9 = l_Lake_BuildTrace_nil;
x_10 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_8);
x_11 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__4), 4, 3);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_4);
lean_closure_set(x_11, 2, x_10);
x_12 = l_Task_Priority_default;
x_13 = lean_io_as_task(x_11, x_12, x_7);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_17 = 0;
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
lean_ctor_set(x_13, 0, x_20);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_24 = 0;
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_5);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_6);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_22);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_6);
lean_dec(x_5);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
return x_13;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
x_11 = 1;
x_12 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__1;
x_13 = l_Lean_Name_toString(x_10, x_11, x_12);
x_14 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_17 = lean_string_append(x_15, x_16);
x_18 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lambda__1___closed__10;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_14);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lambda__1___boxed), 6, 3);
lean_closure_set(x_21, 0, x_2);
lean_closure_set(x_21, 1, x_9);
lean_closure_set(x_21, 2, x_1);
x_22 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__6___closed__1;
x_23 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate_x27___spec__1___rarg), 5, 2);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lambda__2___boxed), 7, 2);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = l_Lake_withRegisterJob___rarg(x_20, x_25, x_11, x_3, x_4, x_5, x_6, x_7, x_8);
return x_26;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Package_maybeFetchBuildCache___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lambda__3), 8, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lake_Package_optBuildCacheFacetConfig___closed__2;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Package_optGitHubReleaseFacetConfig___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Package_optGitHubReleaseFacetConfig___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
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
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("GitHub release", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1___closed__1;
x_2 = l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__2;
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__3;
x_2 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__4;
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 3;
x_2 = l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__5;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (x_4 == 0)
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 3);
x_10 = 2;
x_11 = l_Lake_instDecidableEqVerbosity(x_9, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_array_get_size(x_13);
x_15 = l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__6;
x_16 = lean_array_push(x_13, x_15);
lean_ctor_set(x_6, 0, x_16);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_6);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_7);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_6, 0);
x_20 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_inc(x_19);
lean_dec(x_6);
x_22 = lean_array_get_size(x_19);
x_23 = l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__6;
x_24 = lean_array_push(x_19, x_23);
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_20);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_7);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; uint8_t x_43; 
x_28 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__2;
x_29 = lean_string_append(x_28, x_1);
x_30 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_31 = lean_string_append(x_29, x_30);
x_32 = 1;
x_33 = l_Lean_Name_toString(x_2, x_32, x_3);
x_34 = lean_string_append(x_31, x_33);
lean_dec(x_33);
x_35 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__4;
x_36 = lean_string_append(x_34, x_35);
x_37 = l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__3;
x_38 = lean_string_append(x_37, x_36);
lean_dec(x_36);
x_39 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_40 = lean_string_append(x_38, x_39);
x_41 = 3;
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = !lean_is_exclusive(x_6);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_6, 0);
x_45 = lean_array_get_size(x_44);
x_46 = lean_array_push(x_44, x_42);
lean_ctor_set(x_6, 0, x_46);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_6);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_7);
return x_48;
}
else
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_6, 0);
x_50 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_51 = lean_ctor_get(x_6, 1);
lean_inc(x_51);
lean_inc(x_49);
lean_dec(x_6);
x_52 = lean_array_get_size(x_49);
x_53 = lean_array_push(x_49, x_42);
x_54 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
lean_ctor_set_uint8(x_54, sizeof(void*)*2, x_50);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_7);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_3);
lean_dec(x_2);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_6);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_7);
return x_59;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___boxed), 7, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
x_12 = l_Task_Priority_default;
x_13 = 0;
x_14 = l_Lake_BuildTrace_nil;
x_15 = l_Lake_Job_mapM___rarg(x_4, x_11, x_12, x_13, x_7, x_14, x_10);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_9);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_8);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_9);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_8);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("release", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___closed__2;
x_2 = 1;
x_3 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__1;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = 1;
x_11 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__1;
x_12 = l_Lean_Name_toString(x_9, x_10, x_11);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_14 = lean_string_append(x_13, x_12);
x_15 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___closed__3;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___closed__3;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_13);
x_20 = l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__4;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, lean_box(0));
x_23 = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__2___boxed), 10, 3);
lean_closure_set(x_23, 0, x_12);
lean_closure_set(x_23, 1, x_20);
lean_closure_set(x_23, 2, x_11);
x_24 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Package_recBuildExtraDepTargets___spec__3___rarg), 8, 2);
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
x_1 = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___elambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_gitHubReleaseFacetConfig___closed__1;
x_2 = l_Lake_Package_optBuildCacheFacetConfig___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_gitHubReleaseFacetConfig___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
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
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___rarg___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 1);
lean_dec(x_7);
x_8 = l_Lake_BuildTrace_nil;
lean_ctor_set(x_4, 1, x_8);
x_9 = lean_apply_3(x_1, x_3, x_4, x_5);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
lean_inc(x_10);
lean_dec(x_4);
x_12 = l_Lake_BuildTrace_nil;
x_13 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_11);
x_14 = lean_apply_3(x_1, x_3, x_13, x_5);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_5, 1);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_17 = 0;
x_18 = l_Lake_BuildTrace_nil;
x_19 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_17);
x_20 = lean_apply_3(x_2, x_5, x_19, x_8);
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
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
lean_ctor_set(x_21, 1, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_7);
lean_ctor_set(x_20, 0, x_27);
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_7);
lean_ctor_set(x_20, 0, x_32);
return x_20;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_dec(x_20);
x_34 = lean_ctor_get(x_21, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_36 = x_21;
} else {
 lean_dec_ref(x_21);
 x_36 = lean_box(0);
}
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_7);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_33);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_20);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_20, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_21);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_21, 1);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
lean_ctor_set(x_21, 1, x_45);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_21);
lean_ctor_set(x_46, 1, x_7);
lean_ctor_set(x_20, 0, x_46);
return x_20;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_21, 0);
x_48 = lean_ctor_get(x_21, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_21);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_7);
lean_ctor_set(x_20, 0, x_51);
return x_20;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_20, 1);
lean_inc(x_52);
lean_dec(x_20);
x_53 = lean_ctor_get(x_21, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_21, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_55 = x_21;
} else {
 lean_dec_ref(x_21);
 x_55 = lean_box(0);
}
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec(x_54);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_7);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_52);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_7);
x_60 = !lean_is_exclusive(x_20);
if (x_60 == 0)
{
return x_20;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_20, 0);
x_62 = lean_ctor_get(x_20, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_20);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; 
lean_inc(x_5);
x_64 = l_Lake_Package_maybeFetchBuildCache(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = !lean_is_exclusive(x_65);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_65, 1);
x_70 = lean_ctor_get(x_65, 0);
lean_dec(x_70);
x_71 = !lean_is_exclusive(x_66);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_ctor_get(x_66, 0);
x_73 = lean_ctor_get(x_66, 1);
x_74 = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheAsync___rarg___lambda__1___boxed), 5, 1);
lean_closure_set(x_74, 0, x_2);
x_75 = l_Task_Priority_default;
x_76 = 0;
x_77 = l_Lake_BuildTrace_nil;
x_78 = l_Lake_Job_bindM___rarg(x_72, x_74, x_75, x_76, x_5, x_77, x_67);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_78, 0);
lean_ctor_set(x_66, 0, x_80);
lean_ctor_set(x_78, 0, x_65);
return x_78;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_78, 0);
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_78);
lean_ctor_set(x_66, 0, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_65);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
uint8_t x_84; 
lean_free_object(x_66);
lean_dec(x_73);
lean_free_object(x_65);
lean_dec(x_69);
x_84 = !lean_is_exclusive(x_78);
if (x_84 == 0)
{
return x_78;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_78, 0);
x_86 = lean_ctor_get(x_78, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_78);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; 
x_88 = lean_ctor_get(x_66, 0);
x_89 = lean_ctor_get(x_66, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_66);
x_90 = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheAsync___rarg___lambda__1___boxed), 5, 1);
lean_closure_set(x_90, 0, x_2);
x_91 = l_Task_Priority_default;
x_92 = 0;
x_93 = l_Lake_BuildTrace_nil;
x_94 = l_Lake_Job_bindM___rarg(x_88, x_90, x_91, x_92, x_5, x_93, x_67);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_97 = x_94;
} else {
 lean_dec_ref(x_94);
 x_97 = lean_box(0);
}
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_89);
lean_ctor_set(x_65, 0, x_98);
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_97;
}
lean_ctor_set(x_99, 0, x_65);
lean_ctor_set(x_99, 1, x_96);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_89);
lean_free_object(x_65);
lean_dec(x_69);
x_100 = lean_ctor_get(x_94, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_94, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_102 = x_94;
} else {
 lean_dec_ref(x_94);
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
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; 
x_104 = lean_ctor_get(x_65, 1);
lean_inc(x_104);
lean_dec(x_65);
x_105 = lean_ctor_get(x_66, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_66, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_107 = x_66;
} else {
 lean_dec_ref(x_66);
 x_107 = lean_box(0);
}
x_108 = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheAsync___rarg___lambda__1___boxed), 5, 1);
lean_closure_set(x_108, 0, x_2);
x_109 = l_Task_Priority_default;
x_110 = 0;
x_111 = l_Lake_BuildTrace_nil;
x_112 = l_Lake_Job_bindM___rarg(x_105, x_108, x_109, x_110, x_5, x_111, x_67);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
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
if (lean_is_scalar(x_107)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_107;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_106);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_104);
if (lean_is_scalar(x_115)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_115;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_114);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_104);
x_119 = lean_ctor_get(x_112, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_112, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_121 = x_112;
} else {
 lean_dec_ref(x_112);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_5);
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_64);
if (x_123 == 0)
{
lean_object* x_124; uint8_t x_125; 
x_124 = lean_ctor_get(x_64, 0);
lean_dec(x_124);
x_125 = !lean_is_exclusive(x_65);
if (x_125 == 0)
{
lean_object* x_126; uint8_t x_127; 
x_126 = lean_ctor_get(x_65, 0);
lean_dec(x_126);
x_127 = !lean_is_exclusive(x_66);
if (x_127 == 0)
{
return x_64;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_66, 0);
x_129 = lean_ctor_get(x_66, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_66);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
lean_ctor_set(x_65, 0, x_130);
return x_64;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_131 = lean_ctor_get(x_65, 1);
lean_inc(x_131);
lean_dec(x_65);
x_132 = lean_ctor_get(x_66, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_66, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_134 = x_66;
} else {
 lean_dec_ref(x_66);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_131);
lean_ctor_set(x_64, 0, x_136);
return x_64;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_137 = lean_ctor_get(x_64, 1);
lean_inc(x_137);
lean_dec(x_64);
x_138 = lean_ctor_get(x_65, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_139 = x_65;
} else {
 lean_dec_ref(x_65);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_66, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_66, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_142 = x_66;
} else {
 lean_dec_ref(x_66);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
if (lean_is_scalar(x_139)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_139;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_138);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_137);
return x_145;
}
}
}
else
{
uint8_t x_146; 
lean_dec(x_5);
lean_dec(x_2);
x_146 = !lean_is_exclusive(x_64);
if (x_146 == 0)
{
return x_64;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_64, 0);
x_148 = lean_ctor_get(x_64, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_64);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
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
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lake_Package_afterBuildCacheAsync___rarg___lambda__1(x_1, x_6, x_3, x_4, x_5);
return x_7;
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
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterBuildCacheSync___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_28; 
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_ctor_get(x_4, 1);
x_31 = lean_get_set_stdout(x_1, x_5);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_3(x_2, x_3, x_4, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_36, 0);
x_43 = lean_ctor_get(x_36, 1);
x_44 = lean_get_set_stdout(x_32, x_37);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_39);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_35, 0, x_47);
x_6 = x_35;
x_7 = x_45;
goto block_27;
}
else
{
uint8_t x_48; 
lean_free_object(x_36);
lean_dec(x_43);
lean_dec(x_42);
lean_free_object(x_35);
lean_dec(x_39);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_44, 0);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_44);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_36, 0);
x_53 = lean_ctor_get_uint8(x_36, sizeof(void*)*2);
x_54 = lean_ctor_get(x_36, 1);
lean_inc(x_54);
lean_inc(x_52);
lean_dec(x_36);
x_55 = lean_get_set_stdout(x_32, x_37);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_53);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_39);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_35, 1, x_57);
lean_ctor_set(x_35, 0, x_59);
x_6 = x_35;
x_7 = x_56;
goto block_27;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_54);
lean_dec(x_52);
lean_free_object(x_35);
lean_dec(x_39);
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_62 = x_55;
} else {
 lean_dec_ref(x_55);
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
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_35, 0);
lean_inc(x_64);
lean_dec(x_35);
x_65 = lean_ctor_get(x_36, 0);
lean_inc(x_65);
x_66 = lean_ctor_get_uint8(x_36, sizeof(void*)*2);
x_67 = lean_ctor_get(x_36, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_68 = x_36;
} else {
 lean_dec_ref(x_36);
 x_68 = lean_box(0);
}
x_69 = lean_get_set_stdout(x_32, x_37);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
if (lean_is_scalar(x_68)) {
 x_71 = lean_alloc_ctor(0, 2, 1);
} else {
 x_71 = x_68;
}
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_67);
lean_ctor_set_uint8(x_71, sizeof(void*)*2, x_66);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_64);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
x_6 = x_74;
x_7 = x_70;
goto block_27;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_64);
x_75 = lean_ctor_get(x_69, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_69, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_77 = x_69;
} else {
 lean_dec_ref(x_69);
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
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_ctor_get(x_35, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_34, 1);
lean_inc(x_80);
lean_dec(x_34);
x_81 = !lean_is_exclusive(x_35);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_35, 0);
x_83 = lean_ctor_get(x_35, 1);
lean_dec(x_83);
x_84 = !lean_is_exclusive(x_79);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_79, 0);
x_86 = lean_ctor_get(x_79, 1);
x_87 = lean_get_set_stdout(x_32, x_80);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_6 = x_35;
x_7 = x_88;
goto block_27;
}
else
{
uint8_t x_89; 
lean_free_object(x_79);
lean_dec(x_86);
lean_dec(x_85);
lean_free_object(x_35);
lean_dec(x_82);
x_89 = !lean_is_exclusive(x_87);
if (x_89 == 0)
{
return x_87;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_87, 0);
x_91 = lean_ctor_get(x_87, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_87);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_79, 0);
x_94 = lean_ctor_get_uint8(x_79, sizeof(void*)*2);
x_95 = lean_ctor_get(x_79, 1);
lean_inc(x_95);
lean_inc(x_93);
lean_dec(x_79);
x_96 = lean_get_set_stdout(x_32, x_80);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_98 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_98, 0, x_93);
lean_ctor_set(x_98, 1, x_95);
lean_ctor_set_uint8(x_98, sizeof(void*)*2, x_94);
lean_ctor_set(x_35, 1, x_98);
x_6 = x_35;
x_7 = x_97;
goto block_27;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_95);
lean_dec(x_93);
lean_free_object(x_35);
lean_dec(x_82);
x_99 = lean_ctor_get(x_96, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_101 = x_96;
} else {
 lean_dec_ref(x_96);
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
lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = lean_ctor_get(x_35, 0);
lean_inc(x_103);
lean_dec(x_35);
x_104 = lean_ctor_get(x_79, 0);
lean_inc(x_104);
x_105 = lean_ctor_get_uint8(x_79, sizeof(void*)*2);
x_106 = lean_ctor_get(x_79, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_107 = x_79;
} else {
 lean_dec_ref(x_79);
 x_107 = lean_box(0);
}
x_108 = lean_get_set_stdout(x_32, x_80);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
if (lean_is_scalar(x_107)) {
 x_110 = lean_alloc_ctor(0, 2, 1);
} else {
 x_110 = x_107;
}
lean_ctor_set(x_110, 0, x_104);
lean_ctor_set(x_110, 1, x_106);
lean_ctor_set_uint8(x_110, sizeof(void*)*2, x_105);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_103);
lean_ctor_set(x_111, 1, x_110);
x_6 = x_111;
x_7 = x_109;
goto block_27;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_104);
lean_dec(x_103);
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
}
}
else
{
uint8_t x_116; 
lean_dec(x_32);
x_116 = !lean_is_exclusive(x_34);
if (x_116 == 0)
{
return x_34;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_34, 0);
x_118 = lean_ctor_get(x_34, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_34);
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
lean_free_object(x_4);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_120 = !lean_is_exclusive(x_31);
if (x_120 == 0)
{
return x_31;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_31, 0);
x_122 = lean_ctor_get(x_31, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_31);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_4, 0);
x_125 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_126 = lean_ctor_get(x_4, 1);
lean_inc(x_126);
lean_inc(x_124);
lean_dec(x_4);
x_127 = lean_get_set_stdout(x_1, x_5);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_130, 0, x_124);
lean_ctor_set(x_130, 1, x_126);
lean_ctor_set_uint8(x_130, sizeof(void*)*2, x_125);
x_131 = lean_apply_3(x_2, x_3, x_130, x_129);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_dec(x_131);
x_135 = lean_ctor_get(x_132, 0);
lean_inc(x_135);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_136 = x_132;
} else {
 lean_dec_ref(x_132);
 x_136 = lean_box(0);
}
x_137 = lean_ctor_get(x_133, 0);
lean_inc(x_137);
x_138 = lean_ctor_get_uint8(x_133, sizeof(void*)*2);
x_139 = lean_ctor_get(x_133, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_140 = x_133;
} else {
 lean_dec_ref(x_133);
 x_140 = lean_box(0);
}
x_141 = lean_get_set_stdout(x_128, x_134);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_dec(x_141);
if (lean_is_scalar(x_140)) {
 x_143 = lean_alloc_ctor(0, 2, 1);
} else {
 x_143 = x_140;
}
lean_ctor_set(x_143, 0, x_137);
lean_ctor_set(x_143, 1, x_139);
lean_ctor_set_uint8(x_143, sizeof(void*)*2, x_138);
x_144 = lean_box(0);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_135);
lean_ctor_set(x_145, 1, x_144);
if (lean_is_scalar(x_136)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_136;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_143);
x_6 = x_146;
x_7 = x_142;
goto block_27;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
x_147 = lean_ctor_get(x_141, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_141, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_149 = x_141;
} else {
 lean_dec_ref(x_141);
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
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_151 = lean_ctor_get(x_132, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_131, 1);
lean_inc(x_152);
lean_dec(x_131);
x_153 = lean_ctor_get(x_132, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_154 = x_132;
} else {
 lean_dec_ref(x_132);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_151, 0);
lean_inc(x_155);
x_156 = lean_ctor_get_uint8(x_151, sizeof(void*)*2);
x_157 = lean_ctor_get(x_151, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_158 = x_151;
} else {
 lean_dec_ref(x_151);
 x_158 = lean_box(0);
}
x_159 = lean_get_set_stdout(x_128, x_152);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
lean_dec(x_159);
if (lean_is_scalar(x_158)) {
 x_161 = lean_alloc_ctor(0, 2, 1);
} else {
 x_161 = x_158;
}
lean_ctor_set(x_161, 0, x_155);
lean_ctor_set(x_161, 1, x_157);
lean_ctor_set_uint8(x_161, sizeof(void*)*2, x_156);
if (lean_is_scalar(x_154)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_154;
}
lean_ctor_set(x_162, 0, x_153);
lean_ctor_set(x_162, 1, x_161);
x_6 = x_162;
x_7 = x_160;
goto block_27;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
x_163 = lean_ctor_get(x_159, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_159, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_165 = x_159;
} else {
 lean_dec_ref(x_159);
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
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_128);
x_167 = lean_ctor_get(x_131, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_131, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_169 = x_131;
} else {
 lean_dec_ref(x_131);
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
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_3);
lean_dec(x_2);
x_171 = lean_ctor_get(x_127, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_127, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_173 = x_127;
} else {
 lean_dec_ref(x_127);
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
block_27:
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_dec(x_12);
lean_ctor_set(x_6, 0, x_11);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 0, x_6);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
lean_ctor_set(x_6, 0, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_16);
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_6);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_7);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_6);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_7);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterBuildCacheSync___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_afterBuildCacheSync___spec__2___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterBuildCacheSync___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_28; 
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_ctor_get(x_4, 1);
x_31 = lean_get_set_stdin(x_1, x_5);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_3(x_2, x_3, x_4, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_36, 0);
x_43 = lean_ctor_get(x_36, 1);
x_44 = lean_get_set_stdin(x_32, x_37);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_39);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_35, 0, x_47);
x_6 = x_35;
x_7 = x_45;
goto block_27;
}
else
{
uint8_t x_48; 
lean_free_object(x_36);
lean_dec(x_43);
lean_dec(x_42);
lean_free_object(x_35);
lean_dec(x_39);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_44, 0);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_44);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_36, 0);
x_53 = lean_ctor_get_uint8(x_36, sizeof(void*)*2);
x_54 = lean_ctor_get(x_36, 1);
lean_inc(x_54);
lean_inc(x_52);
lean_dec(x_36);
x_55 = lean_get_set_stdin(x_32, x_37);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_53);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_39);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_35, 1, x_57);
lean_ctor_set(x_35, 0, x_59);
x_6 = x_35;
x_7 = x_56;
goto block_27;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_54);
lean_dec(x_52);
lean_free_object(x_35);
lean_dec(x_39);
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_62 = x_55;
} else {
 lean_dec_ref(x_55);
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
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_35, 0);
lean_inc(x_64);
lean_dec(x_35);
x_65 = lean_ctor_get(x_36, 0);
lean_inc(x_65);
x_66 = lean_ctor_get_uint8(x_36, sizeof(void*)*2);
x_67 = lean_ctor_get(x_36, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_68 = x_36;
} else {
 lean_dec_ref(x_36);
 x_68 = lean_box(0);
}
x_69 = lean_get_set_stdin(x_32, x_37);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
if (lean_is_scalar(x_68)) {
 x_71 = lean_alloc_ctor(0, 2, 1);
} else {
 x_71 = x_68;
}
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_67);
lean_ctor_set_uint8(x_71, sizeof(void*)*2, x_66);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_64);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
x_6 = x_74;
x_7 = x_70;
goto block_27;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_64);
x_75 = lean_ctor_get(x_69, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_69, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_77 = x_69;
} else {
 lean_dec_ref(x_69);
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
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_ctor_get(x_35, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_34, 1);
lean_inc(x_80);
lean_dec(x_34);
x_81 = !lean_is_exclusive(x_35);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_35, 0);
x_83 = lean_ctor_get(x_35, 1);
lean_dec(x_83);
x_84 = !lean_is_exclusive(x_79);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_79, 0);
x_86 = lean_ctor_get(x_79, 1);
x_87 = lean_get_set_stdin(x_32, x_80);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_6 = x_35;
x_7 = x_88;
goto block_27;
}
else
{
uint8_t x_89; 
lean_free_object(x_79);
lean_dec(x_86);
lean_dec(x_85);
lean_free_object(x_35);
lean_dec(x_82);
x_89 = !lean_is_exclusive(x_87);
if (x_89 == 0)
{
return x_87;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_87, 0);
x_91 = lean_ctor_get(x_87, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_87);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_79, 0);
x_94 = lean_ctor_get_uint8(x_79, sizeof(void*)*2);
x_95 = lean_ctor_get(x_79, 1);
lean_inc(x_95);
lean_inc(x_93);
lean_dec(x_79);
x_96 = lean_get_set_stdin(x_32, x_80);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_98 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_98, 0, x_93);
lean_ctor_set(x_98, 1, x_95);
lean_ctor_set_uint8(x_98, sizeof(void*)*2, x_94);
lean_ctor_set(x_35, 1, x_98);
x_6 = x_35;
x_7 = x_97;
goto block_27;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_95);
lean_dec(x_93);
lean_free_object(x_35);
lean_dec(x_82);
x_99 = lean_ctor_get(x_96, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_101 = x_96;
} else {
 lean_dec_ref(x_96);
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
lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = lean_ctor_get(x_35, 0);
lean_inc(x_103);
lean_dec(x_35);
x_104 = lean_ctor_get(x_79, 0);
lean_inc(x_104);
x_105 = lean_ctor_get_uint8(x_79, sizeof(void*)*2);
x_106 = lean_ctor_get(x_79, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_107 = x_79;
} else {
 lean_dec_ref(x_79);
 x_107 = lean_box(0);
}
x_108 = lean_get_set_stdin(x_32, x_80);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
if (lean_is_scalar(x_107)) {
 x_110 = lean_alloc_ctor(0, 2, 1);
} else {
 x_110 = x_107;
}
lean_ctor_set(x_110, 0, x_104);
lean_ctor_set(x_110, 1, x_106);
lean_ctor_set_uint8(x_110, sizeof(void*)*2, x_105);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_103);
lean_ctor_set(x_111, 1, x_110);
x_6 = x_111;
x_7 = x_109;
goto block_27;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_104);
lean_dec(x_103);
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
}
}
else
{
uint8_t x_116; 
lean_dec(x_32);
x_116 = !lean_is_exclusive(x_34);
if (x_116 == 0)
{
return x_34;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_34, 0);
x_118 = lean_ctor_get(x_34, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_34);
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
lean_free_object(x_4);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_120 = !lean_is_exclusive(x_31);
if (x_120 == 0)
{
return x_31;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_31, 0);
x_122 = lean_ctor_get(x_31, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_31);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_4, 0);
x_125 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_126 = lean_ctor_get(x_4, 1);
lean_inc(x_126);
lean_inc(x_124);
lean_dec(x_4);
x_127 = lean_get_set_stdin(x_1, x_5);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_130, 0, x_124);
lean_ctor_set(x_130, 1, x_126);
lean_ctor_set_uint8(x_130, sizeof(void*)*2, x_125);
x_131 = lean_apply_3(x_2, x_3, x_130, x_129);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_dec(x_131);
x_135 = lean_ctor_get(x_132, 0);
lean_inc(x_135);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_136 = x_132;
} else {
 lean_dec_ref(x_132);
 x_136 = lean_box(0);
}
x_137 = lean_ctor_get(x_133, 0);
lean_inc(x_137);
x_138 = lean_ctor_get_uint8(x_133, sizeof(void*)*2);
x_139 = lean_ctor_get(x_133, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_140 = x_133;
} else {
 lean_dec_ref(x_133);
 x_140 = lean_box(0);
}
x_141 = lean_get_set_stdin(x_128, x_134);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_dec(x_141);
if (lean_is_scalar(x_140)) {
 x_143 = lean_alloc_ctor(0, 2, 1);
} else {
 x_143 = x_140;
}
lean_ctor_set(x_143, 0, x_137);
lean_ctor_set(x_143, 1, x_139);
lean_ctor_set_uint8(x_143, sizeof(void*)*2, x_138);
x_144 = lean_box(0);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_135);
lean_ctor_set(x_145, 1, x_144);
if (lean_is_scalar(x_136)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_136;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_143);
x_6 = x_146;
x_7 = x_142;
goto block_27;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
x_147 = lean_ctor_get(x_141, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_141, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_149 = x_141;
} else {
 lean_dec_ref(x_141);
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
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_151 = lean_ctor_get(x_132, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_131, 1);
lean_inc(x_152);
lean_dec(x_131);
x_153 = lean_ctor_get(x_132, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_154 = x_132;
} else {
 lean_dec_ref(x_132);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_151, 0);
lean_inc(x_155);
x_156 = lean_ctor_get_uint8(x_151, sizeof(void*)*2);
x_157 = lean_ctor_get(x_151, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_158 = x_151;
} else {
 lean_dec_ref(x_151);
 x_158 = lean_box(0);
}
x_159 = lean_get_set_stdin(x_128, x_152);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
lean_dec(x_159);
if (lean_is_scalar(x_158)) {
 x_161 = lean_alloc_ctor(0, 2, 1);
} else {
 x_161 = x_158;
}
lean_ctor_set(x_161, 0, x_155);
lean_ctor_set(x_161, 1, x_157);
lean_ctor_set_uint8(x_161, sizeof(void*)*2, x_156);
if (lean_is_scalar(x_154)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_154;
}
lean_ctor_set(x_162, 0, x_153);
lean_ctor_set(x_162, 1, x_161);
x_6 = x_162;
x_7 = x_160;
goto block_27;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
x_163 = lean_ctor_get(x_159, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_159, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_165 = x_159;
} else {
 lean_dec_ref(x_159);
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
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_128);
x_167 = lean_ctor_get(x_131, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_131, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_169 = x_131;
} else {
 lean_dec_ref(x_131);
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
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_3);
lean_dec(x_2);
x_171 = lean_ctor_get(x_127, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_127, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_173 = x_127;
} else {
 lean_dec_ref(x_127);
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
block_27:
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_dec(x_12);
lean_ctor_set(x_6, 0, x_11);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 0, x_6);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
lean_ctor_set(x_6, 0, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_16);
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_6);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_7);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_6);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_7);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterBuildCacheSync___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdin___at_Lake_Package_afterBuildCacheSync___spec__3___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Package_afterBuildCacheSync___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_28; 
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_ctor_get(x_4, 1);
x_31 = lean_get_set_stderr(x_1, x_5);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_3(x_2, x_3, x_4, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_36, 0);
x_43 = lean_ctor_get(x_36, 1);
x_44 = lean_get_set_stderr(x_32, x_37);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_39);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_35, 0, x_47);
x_6 = x_35;
x_7 = x_45;
goto block_27;
}
else
{
uint8_t x_48; 
lean_free_object(x_36);
lean_dec(x_43);
lean_dec(x_42);
lean_free_object(x_35);
lean_dec(x_39);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_44, 0);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_44);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_36, 0);
x_53 = lean_ctor_get_uint8(x_36, sizeof(void*)*2);
x_54 = lean_ctor_get(x_36, 1);
lean_inc(x_54);
lean_inc(x_52);
lean_dec(x_36);
x_55 = lean_get_set_stderr(x_32, x_37);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_53);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_39);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_35, 1, x_57);
lean_ctor_set(x_35, 0, x_59);
x_6 = x_35;
x_7 = x_56;
goto block_27;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_54);
lean_dec(x_52);
lean_free_object(x_35);
lean_dec(x_39);
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_62 = x_55;
} else {
 lean_dec_ref(x_55);
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
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_35, 0);
lean_inc(x_64);
lean_dec(x_35);
x_65 = lean_ctor_get(x_36, 0);
lean_inc(x_65);
x_66 = lean_ctor_get_uint8(x_36, sizeof(void*)*2);
x_67 = lean_ctor_get(x_36, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_68 = x_36;
} else {
 lean_dec_ref(x_36);
 x_68 = lean_box(0);
}
x_69 = lean_get_set_stderr(x_32, x_37);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
if (lean_is_scalar(x_68)) {
 x_71 = lean_alloc_ctor(0, 2, 1);
} else {
 x_71 = x_68;
}
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_67);
lean_ctor_set_uint8(x_71, sizeof(void*)*2, x_66);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_64);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
x_6 = x_74;
x_7 = x_70;
goto block_27;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_64);
x_75 = lean_ctor_get(x_69, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_69, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_77 = x_69;
} else {
 lean_dec_ref(x_69);
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
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_ctor_get(x_35, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_34, 1);
lean_inc(x_80);
lean_dec(x_34);
x_81 = !lean_is_exclusive(x_35);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_35, 0);
x_83 = lean_ctor_get(x_35, 1);
lean_dec(x_83);
x_84 = !lean_is_exclusive(x_79);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_79, 0);
x_86 = lean_ctor_get(x_79, 1);
x_87 = lean_get_set_stderr(x_32, x_80);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_6 = x_35;
x_7 = x_88;
goto block_27;
}
else
{
uint8_t x_89; 
lean_free_object(x_79);
lean_dec(x_86);
lean_dec(x_85);
lean_free_object(x_35);
lean_dec(x_82);
x_89 = !lean_is_exclusive(x_87);
if (x_89 == 0)
{
return x_87;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_87, 0);
x_91 = lean_ctor_get(x_87, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_87);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_79, 0);
x_94 = lean_ctor_get_uint8(x_79, sizeof(void*)*2);
x_95 = lean_ctor_get(x_79, 1);
lean_inc(x_95);
lean_inc(x_93);
lean_dec(x_79);
x_96 = lean_get_set_stderr(x_32, x_80);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_98 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_98, 0, x_93);
lean_ctor_set(x_98, 1, x_95);
lean_ctor_set_uint8(x_98, sizeof(void*)*2, x_94);
lean_ctor_set(x_35, 1, x_98);
x_6 = x_35;
x_7 = x_97;
goto block_27;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_95);
lean_dec(x_93);
lean_free_object(x_35);
lean_dec(x_82);
x_99 = lean_ctor_get(x_96, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_101 = x_96;
} else {
 lean_dec_ref(x_96);
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
lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = lean_ctor_get(x_35, 0);
lean_inc(x_103);
lean_dec(x_35);
x_104 = lean_ctor_get(x_79, 0);
lean_inc(x_104);
x_105 = lean_ctor_get_uint8(x_79, sizeof(void*)*2);
x_106 = lean_ctor_get(x_79, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_107 = x_79;
} else {
 lean_dec_ref(x_79);
 x_107 = lean_box(0);
}
x_108 = lean_get_set_stderr(x_32, x_80);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
if (lean_is_scalar(x_107)) {
 x_110 = lean_alloc_ctor(0, 2, 1);
} else {
 x_110 = x_107;
}
lean_ctor_set(x_110, 0, x_104);
lean_ctor_set(x_110, 1, x_106);
lean_ctor_set_uint8(x_110, sizeof(void*)*2, x_105);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_103);
lean_ctor_set(x_111, 1, x_110);
x_6 = x_111;
x_7 = x_109;
goto block_27;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_104);
lean_dec(x_103);
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
}
}
else
{
uint8_t x_116; 
lean_dec(x_32);
x_116 = !lean_is_exclusive(x_34);
if (x_116 == 0)
{
return x_34;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_34, 0);
x_118 = lean_ctor_get(x_34, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_34);
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
lean_free_object(x_4);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_120 = !lean_is_exclusive(x_31);
if (x_120 == 0)
{
return x_31;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_31, 0);
x_122 = lean_ctor_get(x_31, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_31);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_4, 0);
x_125 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_126 = lean_ctor_get(x_4, 1);
lean_inc(x_126);
lean_inc(x_124);
lean_dec(x_4);
x_127 = lean_get_set_stderr(x_1, x_5);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_130, 0, x_124);
lean_ctor_set(x_130, 1, x_126);
lean_ctor_set_uint8(x_130, sizeof(void*)*2, x_125);
x_131 = lean_apply_3(x_2, x_3, x_130, x_129);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_dec(x_131);
x_135 = lean_ctor_get(x_132, 0);
lean_inc(x_135);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_136 = x_132;
} else {
 lean_dec_ref(x_132);
 x_136 = lean_box(0);
}
x_137 = lean_ctor_get(x_133, 0);
lean_inc(x_137);
x_138 = lean_ctor_get_uint8(x_133, sizeof(void*)*2);
x_139 = lean_ctor_get(x_133, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_140 = x_133;
} else {
 lean_dec_ref(x_133);
 x_140 = lean_box(0);
}
x_141 = lean_get_set_stderr(x_128, x_134);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_dec(x_141);
if (lean_is_scalar(x_140)) {
 x_143 = lean_alloc_ctor(0, 2, 1);
} else {
 x_143 = x_140;
}
lean_ctor_set(x_143, 0, x_137);
lean_ctor_set(x_143, 1, x_139);
lean_ctor_set_uint8(x_143, sizeof(void*)*2, x_138);
x_144 = lean_box(0);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_135);
lean_ctor_set(x_145, 1, x_144);
if (lean_is_scalar(x_136)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_136;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_143);
x_6 = x_146;
x_7 = x_142;
goto block_27;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
x_147 = lean_ctor_get(x_141, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_141, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_149 = x_141;
} else {
 lean_dec_ref(x_141);
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
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_151 = lean_ctor_get(x_132, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_131, 1);
lean_inc(x_152);
lean_dec(x_131);
x_153 = lean_ctor_get(x_132, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_154 = x_132;
} else {
 lean_dec_ref(x_132);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_151, 0);
lean_inc(x_155);
x_156 = lean_ctor_get_uint8(x_151, sizeof(void*)*2);
x_157 = lean_ctor_get(x_151, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_158 = x_151;
} else {
 lean_dec_ref(x_151);
 x_158 = lean_box(0);
}
x_159 = lean_get_set_stderr(x_128, x_152);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
lean_dec(x_159);
if (lean_is_scalar(x_158)) {
 x_161 = lean_alloc_ctor(0, 2, 1);
} else {
 x_161 = x_158;
}
lean_ctor_set(x_161, 0, x_155);
lean_ctor_set(x_161, 1, x_157);
lean_ctor_set_uint8(x_161, sizeof(void*)*2, x_156);
if (lean_is_scalar(x_154)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_154;
}
lean_ctor_set(x_162, 0, x_153);
lean_ctor_set(x_162, 1, x_161);
x_6 = x_162;
x_7 = x_160;
goto block_27;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
x_163 = lean_ctor_get(x_159, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_159, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_165 = x_159;
} else {
 lean_dec_ref(x_159);
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
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_128);
x_167 = lean_ctor_get(x_131, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_131, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_169 = x_131;
} else {
 lean_dec_ref(x_131);
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
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_3);
lean_dec(x_2);
x_171 = lean_ctor_get(x_127, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_127, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_173 = x_127;
} else {
 lean_dec_ref(x_127);
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
block_27:
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_dec(x_12);
lean_ctor_set(x_6, 0, x_11);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 0, x_6);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
lean_ctor_set(x_6, 0, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_16);
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_6);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_7);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_6);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_7);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Package_afterBuildCacheSync___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_Package_afterBuildCacheSync___spec__4___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterBuildCacheSync___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_28; 
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_ctor_get(x_4, 1);
x_31 = lean_get_set_stdout(x_1, x_5);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_3(x_2, x_3, x_4, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_36, 0);
x_43 = lean_ctor_get(x_36, 1);
x_44 = lean_get_set_stdout(x_32, x_37);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_39);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_35, 0, x_47);
x_6 = x_35;
x_7 = x_45;
goto block_27;
}
else
{
uint8_t x_48; 
lean_free_object(x_36);
lean_dec(x_43);
lean_dec(x_42);
lean_free_object(x_35);
lean_dec(x_39);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_44, 0);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_44);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_36, 0);
x_53 = lean_ctor_get_uint8(x_36, sizeof(void*)*2);
x_54 = lean_ctor_get(x_36, 1);
lean_inc(x_54);
lean_inc(x_52);
lean_dec(x_36);
x_55 = lean_get_set_stdout(x_32, x_37);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_53);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_39);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_35, 1, x_57);
lean_ctor_set(x_35, 0, x_59);
x_6 = x_35;
x_7 = x_56;
goto block_27;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_54);
lean_dec(x_52);
lean_free_object(x_35);
lean_dec(x_39);
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_62 = x_55;
} else {
 lean_dec_ref(x_55);
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
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_35, 0);
lean_inc(x_64);
lean_dec(x_35);
x_65 = lean_ctor_get(x_36, 0);
lean_inc(x_65);
x_66 = lean_ctor_get_uint8(x_36, sizeof(void*)*2);
x_67 = lean_ctor_get(x_36, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_68 = x_36;
} else {
 lean_dec_ref(x_36);
 x_68 = lean_box(0);
}
x_69 = lean_get_set_stdout(x_32, x_37);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
if (lean_is_scalar(x_68)) {
 x_71 = lean_alloc_ctor(0, 2, 1);
} else {
 x_71 = x_68;
}
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_67);
lean_ctor_set_uint8(x_71, sizeof(void*)*2, x_66);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_64);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
x_6 = x_74;
x_7 = x_70;
goto block_27;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_64);
x_75 = lean_ctor_get(x_69, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_69, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_77 = x_69;
} else {
 lean_dec_ref(x_69);
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
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_ctor_get(x_35, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_34, 1);
lean_inc(x_80);
lean_dec(x_34);
x_81 = !lean_is_exclusive(x_35);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_35, 0);
x_83 = lean_ctor_get(x_35, 1);
lean_dec(x_83);
x_84 = !lean_is_exclusive(x_79);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_79, 0);
x_86 = lean_ctor_get(x_79, 1);
x_87 = lean_get_set_stdout(x_32, x_80);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_6 = x_35;
x_7 = x_88;
goto block_27;
}
else
{
uint8_t x_89; 
lean_free_object(x_79);
lean_dec(x_86);
lean_dec(x_85);
lean_free_object(x_35);
lean_dec(x_82);
x_89 = !lean_is_exclusive(x_87);
if (x_89 == 0)
{
return x_87;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_87, 0);
x_91 = lean_ctor_get(x_87, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_87);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_79, 0);
x_94 = lean_ctor_get_uint8(x_79, sizeof(void*)*2);
x_95 = lean_ctor_get(x_79, 1);
lean_inc(x_95);
lean_inc(x_93);
lean_dec(x_79);
x_96 = lean_get_set_stdout(x_32, x_80);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_98 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_98, 0, x_93);
lean_ctor_set(x_98, 1, x_95);
lean_ctor_set_uint8(x_98, sizeof(void*)*2, x_94);
lean_ctor_set(x_35, 1, x_98);
x_6 = x_35;
x_7 = x_97;
goto block_27;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_95);
lean_dec(x_93);
lean_free_object(x_35);
lean_dec(x_82);
x_99 = lean_ctor_get(x_96, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_101 = x_96;
} else {
 lean_dec_ref(x_96);
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
lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = lean_ctor_get(x_35, 0);
lean_inc(x_103);
lean_dec(x_35);
x_104 = lean_ctor_get(x_79, 0);
lean_inc(x_104);
x_105 = lean_ctor_get_uint8(x_79, sizeof(void*)*2);
x_106 = lean_ctor_get(x_79, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_107 = x_79;
} else {
 lean_dec_ref(x_79);
 x_107 = lean_box(0);
}
x_108 = lean_get_set_stdout(x_32, x_80);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
if (lean_is_scalar(x_107)) {
 x_110 = lean_alloc_ctor(0, 2, 1);
} else {
 x_110 = x_107;
}
lean_ctor_set(x_110, 0, x_104);
lean_ctor_set(x_110, 1, x_106);
lean_ctor_set_uint8(x_110, sizeof(void*)*2, x_105);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_103);
lean_ctor_set(x_111, 1, x_110);
x_6 = x_111;
x_7 = x_109;
goto block_27;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_104);
lean_dec(x_103);
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
}
}
else
{
uint8_t x_116; 
lean_dec(x_32);
x_116 = !lean_is_exclusive(x_34);
if (x_116 == 0)
{
return x_34;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_34, 0);
x_118 = lean_ctor_get(x_34, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_34);
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
lean_free_object(x_4);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_120 = !lean_is_exclusive(x_31);
if (x_120 == 0)
{
return x_31;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_31, 0);
x_122 = lean_ctor_get(x_31, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_31);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_4, 0);
x_125 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_126 = lean_ctor_get(x_4, 1);
lean_inc(x_126);
lean_inc(x_124);
lean_dec(x_4);
x_127 = lean_get_set_stdout(x_1, x_5);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_130, 0, x_124);
lean_ctor_set(x_130, 1, x_126);
lean_ctor_set_uint8(x_130, sizeof(void*)*2, x_125);
x_131 = lean_apply_3(x_2, x_3, x_130, x_129);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_dec(x_131);
x_135 = lean_ctor_get(x_132, 0);
lean_inc(x_135);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_136 = x_132;
} else {
 lean_dec_ref(x_132);
 x_136 = lean_box(0);
}
x_137 = lean_ctor_get(x_133, 0);
lean_inc(x_137);
x_138 = lean_ctor_get_uint8(x_133, sizeof(void*)*2);
x_139 = lean_ctor_get(x_133, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_140 = x_133;
} else {
 lean_dec_ref(x_133);
 x_140 = lean_box(0);
}
x_141 = lean_get_set_stdout(x_128, x_134);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_dec(x_141);
if (lean_is_scalar(x_140)) {
 x_143 = lean_alloc_ctor(0, 2, 1);
} else {
 x_143 = x_140;
}
lean_ctor_set(x_143, 0, x_137);
lean_ctor_set(x_143, 1, x_139);
lean_ctor_set_uint8(x_143, sizeof(void*)*2, x_138);
x_144 = lean_box(0);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_135);
lean_ctor_set(x_145, 1, x_144);
if (lean_is_scalar(x_136)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_136;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_143);
x_6 = x_146;
x_7 = x_142;
goto block_27;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
x_147 = lean_ctor_get(x_141, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_141, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_149 = x_141;
} else {
 lean_dec_ref(x_141);
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
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_151 = lean_ctor_get(x_132, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_131, 1);
lean_inc(x_152);
lean_dec(x_131);
x_153 = lean_ctor_get(x_132, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_154 = x_132;
} else {
 lean_dec_ref(x_132);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_151, 0);
lean_inc(x_155);
x_156 = lean_ctor_get_uint8(x_151, sizeof(void*)*2);
x_157 = lean_ctor_get(x_151, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_158 = x_151;
} else {
 lean_dec_ref(x_151);
 x_158 = lean_box(0);
}
x_159 = lean_get_set_stdout(x_128, x_152);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
lean_dec(x_159);
if (lean_is_scalar(x_158)) {
 x_161 = lean_alloc_ctor(0, 2, 1);
} else {
 x_161 = x_158;
}
lean_ctor_set(x_161, 0, x_155);
lean_ctor_set(x_161, 1, x_157);
lean_ctor_set_uint8(x_161, sizeof(void*)*2, x_156);
if (lean_is_scalar(x_154)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_154;
}
lean_ctor_set(x_162, 0, x_153);
lean_ctor_set(x_162, 1, x_161);
x_6 = x_162;
x_7 = x_160;
goto block_27;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
x_163 = lean_ctor_get(x_159, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_159, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_165 = x_159;
} else {
 lean_dec_ref(x_159);
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
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_128);
x_167 = lean_ctor_get(x_131, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_131, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_169 = x_131;
} else {
 lean_dec_ref(x_131);
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
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_3);
lean_dec(x_2);
x_171 = lean_ctor_get(x_127, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_127, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_173 = x_127;
} else {
 lean_dec_ref(x_127);
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
block_27:
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_dec(x_12);
lean_ctor_set(x_6, 0, x_11);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 0, x_6);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
lean_ctor_set(x_6, 0, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_16);
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_6);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_7);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_6);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_7);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterBuildCacheSync___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_afterBuildCacheSync___spec__5___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterBuildCacheSync___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_28; 
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_ctor_get(x_4, 1);
x_31 = lean_get_set_stdin(x_1, x_5);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_3(x_2, x_3, x_4, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_36, 0);
x_43 = lean_ctor_get(x_36, 1);
x_44 = lean_get_set_stdin(x_32, x_37);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_39);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_35, 0, x_47);
x_6 = x_35;
x_7 = x_45;
goto block_27;
}
else
{
uint8_t x_48; 
lean_free_object(x_36);
lean_dec(x_43);
lean_dec(x_42);
lean_free_object(x_35);
lean_dec(x_39);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_44, 0);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_44);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_36, 0);
x_53 = lean_ctor_get_uint8(x_36, sizeof(void*)*2);
x_54 = lean_ctor_get(x_36, 1);
lean_inc(x_54);
lean_inc(x_52);
lean_dec(x_36);
x_55 = lean_get_set_stdin(x_32, x_37);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_53);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_39);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_35, 1, x_57);
lean_ctor_set(x_35, 0, x_59);
x_6 = x_35;
x_7 = x_56;
goto block_27;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_54);
lean_dec(x_52);
lean_free_object(x_35);
lean_dec(x_39);
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_62 = x_55;
} else {
 lean_dec_ref(x_55);
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
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_35, 0);
lean_inc(x_64);
lean_dec(x_35);
x_65 = lean_ctor_get(x_36, 0);
lean_inc(x_65);
x_66 = lean_ctor_get_uint8(x_36, sizeof(void*)*2);
x_67 = lean_ctor_get(x_36, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_68 = x_36;
} else {
 lean_dec_ref(x_36);
 x_68 = lean_box(0);
}
x_69 = lean_get_set_stdin(x_32, x_37);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
if (lean_is_scalar(x_68)) {
 x_71 = lean_alloc_ctor(0, 2, 1);
} else {
 x_71 = x_68;
}
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_67);
lean_ctor_set_uint8(x_71, sizeof(void*)*2, x_66);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_64);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
x_6 = x_74;
x_7 = x_70;
goto block_27;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_64);
x_75 = lean_ctor_get(x_69, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_69, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_77 = x_69;
} else {
 lean_dec_ref(x_69);
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
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_ctor_get(x_35, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_34, 1);
lean_inc(x_80);
lean_dec(x_34);
x_81 = !lean_is_exclusive(x_35);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_35, 0);
x_83 = lean_ctor_get(x_35, 1);
lean_dec(x_83);
x_84 = !lean_is_exclusive(x_79);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_79, 0);
x_86 = lean_ctor_get(x_79, 1);
x_87 = lean_get_set_stdin(x_32, x_80);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_6 = x_35;
x_7 = x_88;
goto block_27;
}
else
{
uint8_t x_89; 
lean_free_object(x_79);
lean_dec(x_86);
lean_dec(x_85);
lean_free_object(x_35);
lean_dec(x_82);
x_89 = !lean_is_exclusive(x_87);
if (x_89 == 0)
{
return x_87;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_87, 0);
x_91 = lean_ctor_get(x_87, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_87);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_79, 0);
x_94 = lean_ctor_get_uint8(x_79, sizeof(void*)*2);
x_95 = lean_ctor_get(x_79, 1);
lean_inc(x_95);
lean_inc(x_93);
lean_dec(x_79);
x_96 = lean_get_set_stdin(x_32, x_80);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_98 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_98, 0, x_93);
lean_ctor_set(x_98, 1, x_95);
lean_ctor_set_uint8(x_98, sizeof(void*)*2, x_94);
lean_ctor_set(x_35, 1, x_98);
x_6 = x_35;
x_7 = x_97;
goto block_27;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_95);
lean_dec(x_93);
lean_free_object(x_35);
lean_dec(x_82);
x_99 = lean_ctor_get(x_96, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_101 = x_96;
} else {
 lean_dec_ref(x_96);
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
lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = lean_ctor_get(x_35, 0);
lean_inc(x_103);
lean_dec(x_35);
x_104 = lean_ctor_get(x_79, 0);
lean_inc(x_104);
x_105 = lean_ctor_get_uint8(x_79, sizeof(void*)*2);
x_106 = lean_ctor_get(x_79, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_107 = x_79;
} else {
 lean_dec_ref(x_79);
 x_107 = lean_box(0);
}
x_108 = lean_get_set_stdin(x_32, x_80);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
if (lean_is_scalar(x_107)) {
 x_110 = lean_alloc_ctor(0, 2, 1);
} else {
 x_110 = x_107;
}
lean_ctor_set(x_110, 0, x_104);
lean_ctor_set(x_110, 1, x_106);
lean_ctor_set_uint8(x_110, sizeof(void*)*2, x_105);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_103);
lean_ctor_set(x_111, 1, x_110);
x_6 = x_111;
x_7 = x_109;
goto block_27;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_104);
lean_dec(x_103);
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
}
}
else
{
uint8_t x_116; 
lean_dec(x_32);
x_116 = !lean_is_exclusive(x_34);
if (x_116 == 0)
{
return x_34;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_34, 0);
x_118 = lean_ctor_get(x_34, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_34);
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
lean_free_object(x_4);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_120 = !lean_is_exclusive(x_31);
if (x_120 == 0)
{
return x_31;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_31, 0);
x_122 = lean_ctor_get(x_31, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_31);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_4, 0);
x_125 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_126 = lean_ctor_get(x_4, 1);
lean_inc(x_126);
lean_inc(x_124);
lean_dec(x_4);
x_127 = lean_get_set_stdin(x_1, x_5);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_130, 0, x_124);
lean_ctor_set(x_130, 1, x_126);
lean_ctor_set_uint8(x_130, sizeof(void*)*2, x_125);
x_131 = lean_apply_3(x_2, x_3, x_130, x_129);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_dec(x_131);
x_135 = lean_ctor_get(x_132, 0);
lean_inc(x_135);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_136 = x_132;
} else {
 lean_dec_ref(x_132);
 x_136 = lean_box(0);
}
x_137 = lean_ctor_get(x_133, 0);
lean_inc(x_137);
x_138 = lean_ctor_get_uint8(x_133, sizeof(void*)*2);
x_139 = lean_ctor_get(x_133, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_140 = x_133;
} else {
 lean_dec_ref(x_133);
 x_140 = lean_box(0);
}
x_141 = lean_get_set_stdin(x_128, x_134);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_dec(x_141);
if (lean_is_scalar(x_140)) {
 x_143 = lean_alloc_ctor(0, 2, 1);
} else {
 x_143 = x_140;
}
lean_ctor_set(x_143, 0, x_137);
lean_ctor_set(x_143, 1, x_139);
lean_ctor_set_uint8(x_143, sizeof(void*)*2, x_138);
x_144 = lean_box(0);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_135);
lean_ctor_set(x_145, 1, x_144);
if (lean_is_scalar(x_136)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_136;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_143);
x_6 = x_146;
x_7 = x_142;
goto block_27;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
x_147 = lean_ctor_get(x_141, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_141, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_149 = x_141;
} else {
 lean_dec_ref(x_141);
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
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_151 = lean_ctor_get(x_132, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_131, 1);
lean_inc(x_152);
lean_dec(x_131);
x_153 = lean_ctor_get(x_132, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_154 = x_132;
} else {
 lean_dec_ref(x_132);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_151, 0);
lean_inc(x_155);
x_156 = lean_ctor_get_uint8(x_151, sizeof(void*)*2);
x_157 = lean_ctor_get(x_151, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_158 = x_151;
} else {
 lean_dec_ref(x_151);
 x_158 = lean_box(0);
}
x_159 = lean_get_set_stdin(x_128, x_152);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
lean_dec(x_159);
if (lean_is_scalar(x_158)) {
 x_161 = lean_alloc_ctor(0, 2, 1);
} else {
 x_161 = x_158;
}
lean_ctor_set(x_161, 0, x_155);
lean_ctor_set(x_161, 1, x_157);
lean_ctor_set_uint8(x_161, sizeof(void*)*2, x_156);
if (lean_is_scalar(x_154)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_154;
}
lean_ctor_set(x_162, 0, x_153);
lean_ctor_set(x_162, 1, x_161);
x_6 = x_162;
x_7 = x_160;
goto block_27;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
x_163 = lean_ctor_get(x_159, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_159, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_165 = x_159;
} else {
 lean_dec_ref(x_159);
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
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_128);
x_167 = lean_ctor_get(x_131, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_131, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_169 = x_131;
} else {
 lean_dec_ref(x_131);
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
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_3);
lean_dec(x_2);
x_171 = lean_ctor_get(x_127, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_127, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_173 = x_127;
} else {
 lean_dec_ref(x_127);
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
block_27:
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_dec(x_12);
lean_ctor_set(x_6, 0, x_11);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 0, x_6);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
lean_ctor_set(x_6, 0, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_16);
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_6);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_7);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_6);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_7);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterBuildCacheSync___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdin___at_Lake_Package_afterBuildCacheSync___spec__6___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_afterBuildCacheSync___spec__1___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__1;
x_10 = lean_st_mk_ref(x_9, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_mk_ref(x_9, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_IO_FS_Stream_ofBuffer(x_11);
lean_inc(x_14);
x_17 = l_IO_FS_Stream_ofBuffer(x_14);
if (x_2 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_afterBuildCacheSync___spec__2___rarg), 5, 2);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_1);
x_19 = l_IO_withStdin___at_Lake_Package_afterBuildCacheSync___spec__3___rarg(x_16, x_18, x_3, x_4, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
x_29 = lean_st_ref_get(x_14, x_22);
lean_dec(x_14);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_string_validate_utf8(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_32);
x_34 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__5;
x_35 = l_panic___at_String_fromUTF8_x21___spec__1(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_24);
lean_ctor_set(x_20, 0, x_36);
lean_ctor_set(x_29, 0, x_20);
return x_29;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_string_from_utf8_unchecked(x_32);
lean_dec(x_32);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_24);
lean_ctor_set(x_20, 0, x_38);
lean_ctor_set(x_29, 0, x_20);
return x_29;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_29, 0);
x_40 = lean_ctor_get(x_29, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_29);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_string_validate_utf8(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_41);
x_43 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__5;
x_44 = l_panic___at_String_fromUTF8_x21___spec__1(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_24);
lean_ctor_set(x_20, 0, x_45);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_20);
lean_ctor_set(x_46, 1, x_40);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_string_from_utf8_unchecked(x_41);
lean_dec(x_41);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_24);
lean_ctor_set(x_20, 0, x_48);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_20);
lean_ctor_set(x_49, 1, x_40);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_free_object(x_21);
lean_dec(x_28);
lean_dec(x_27);
lean_free_object(x_20);
lean_dec(x_24);
x_50 = !lean_is_exclusive(x_29);
if (x_50 == 0)
{
return x_29;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_29, 0);
x_52 = lean_ctor_get(x_29, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_29);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_21, 0);
x_55 = lean_ctor_get_uint8(x_21, sizeof(void*)*2);
x_56 = lean_ctor_get(x_21, 1);
lean_inc(x_56);
lean_inc(x_54);
lean_dec(x_21);
x_57 = lean_st_ref_get(x_14, x_22);
lean_dec(x_14);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
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
x_61 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_61, 0, x_54);
lean_ctor_set(x_61, 1, x_56);
lean_ctor_set_uint8(x_61, sizeof(void*)*2, x_55);
x_62 = lean_ctor_get(x_58, 0);
lean_inc(x_62);
lean_dec(x_58);
x_63 = lean_string_validate_utf8(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__5;
x_65 = l_panic___at_String_fromUTF8_x21___spec__1(x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_24);
lean_ctor_set(x_20, 1, x_61);
lean_ctor_set(x_20, 0, x_66);
if (lean_is_scalar(x_60)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_60;
}
lean_ctor_set(x_67, 0, x_20);
lean_ctor_set(x_67, 1, x_59);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_string_from_utf8_unchecked(x_62);
lean_dec(x_62);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_24);
lean_ctor_set(x_20, 1, x_61);
lean_ctor_set(x_20, 0, x_69);
if (lean_is_scalar(x_60)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_60;
}
lean_ctor_set(x_70, 0, x_20);
lean_ctor_set(x_70, 1, x_59);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_56);
lean_dec(x_54);
lean_free_object(x_20);
lean_dec(x_24);
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_57, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_73 = x_57;
} else {
 lean_dec_ref(x_57);
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
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_20, 0);
lean_inc(x_75);
lean_dec(x_20);
x_76 = lean_ctor_get(x_21, 0);
lean_inc(x_76);
x_77 = lean_ctor_get_uint8(x_21, sizeof(void*)*2);
x_78 = lean_ctor_get(x_21, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_79 = x_21;
} else {
 lean_dec_ref(x_21);
 x_79 = lean_box(0);
}
x_80 = lean_st_ref_get(x_14, x_22);
lean_dec(x_14);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_83 = x_80;
} else {
 lean_dec_ref(x_80);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_84 = lean_alloc_ctor(0, 2, 1);
} else {
 x_84 = x_79;
}
lean_ctor_set(x_84, 0, x_76);
lean_ctor_set(x_84, 1, x_78);
lean_ctor_set_uint8(x_84, sizeof(void*)*2, x_77);
x_85 = lean_ctor_get(x_81, 0);
lean_inc(x_85);
lean_dec(x_81);
x_86 = lean_string_validate_utf8(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_85);
x_87 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__5;
x_88 = l_panic___at_String_fromUTF8_x21___spec__1(x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_75);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_84);
if (lean_is_scalar(x_83)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_83;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_82);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_string_from_utf8_unchecked(x_85);
lean_dec(x_85);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_75);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_84);
if (lean_is_scalar(x_83)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_83;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_82);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_76);
lean_dec(x_75);
x_96 = lean_ctor_get(x_80, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_80, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_98 = x_80;
} else {
 lean_dec_ref(x_80);
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
}
else
{
uint8_t x_100; 
lean_dec(x_14);
x_100 = !lean_is_exclusive(x_19);
if (x_100 == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_19, 0);
lean_dec(x_101);
x_102 = !lean_is_exclusive(x_20);
if (x_102 == 0)
{
return x_19;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_20, 0);
x_104 = lean_ctor_get(x_20, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_20);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_19, 0, x_105);
return x_19;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_19, 1);
lean_inc(x_106);
lean_dec(x_19);
x_107 = lean_ctor_get(x_20, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_20, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_109 = x_20;
} else {
 lean_dec_ref(x_20);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_106);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_14);
x_112 = !lean_is_exclusive(x_19);
if (x_112 == 0)
{
return x_19;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_19, 0);
x_114 = lean_ctor_get(x_19, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_19);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_inc(x_17);
x_116 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_Package_afterBuildCacheSync___spec__4___rarg), 5, 2);
lean_closure_set(x_116, 0, x_17);
lean_closure_set(x_116, 1, x_1);
x_117 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_afterBuildCacheSync___spec__5___rarg), 5, 2);
lean_closure_set(x_117, 0, x_17);
lean_closure_set(x_117, 1, x_116);
x_118 = l_IO_withStdin___at_Lake_Package_afterBuildCacheSync___spec__6___rarg(x_16, x_117, x_3, x_4, x_15);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_dec(x_118);
x_122 = !lean_is_exclusive(x_119);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get(x_119, 0);
x_124 = lean_ctor_get(x_119, 1);
lean_dec(x_124);
x_125 = !lean_is_exclusive(x_120);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_120, 0);
x_127 = lean_ctor_get(x_120, 1);
x_128 = lean_st_ref_get(x_14, x_121);
lean_dec(x_14);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_130 = lean_ctor_get(x_128, 0);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
lean_dec(x_130);
x_132 = lean_string_validate_utf8(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_131);
x_133 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__5;
x_134 = l_panic___at_String_fromUTF8_x21___spec__1(x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_123);
lean_ctor_set(x_119, 0, x_135);
lean_ctor_set(x_128, 0, x_119);
return x_128;
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_string_from_utf8_unchecked(x_131);
lean_dec(x_131);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_123);
lean_ctor_set(x_119, 0, x_137);
lean_ctor_set(x_128, 0, x_119);
return x_128;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_138 = lean_ctor_get(x_128, 0);
x_139 = lean_ctor_get(x_128, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_128);
x_140 = lean_ctor_get(x_138, 0);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_string_validate_utf8(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_140);
x_142 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__5;
x_143 = l_panic___at_String_fromUTF8_x21___spec__1(x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_123);
lean_ctor_set(x_119, 0, x_144);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_119);
lean_ctor_set(x_145, 1, x_139);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_string_from_utf8_unchecked(x_140);
lean_dec(x_140);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_123);
lean_ctor_set(x_119, 0, x_147);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_119);
lean_ctor_set(x_148, 1, x_139);
return x_148;
}
}
}
else
{
uint8_t x_149; 
lean_free_object(x_120);
lean_dec(x_127);
lean_dec(x_126);
lean_free_object(x_119);
lean_dec(x_123);
x_149 = !lean_is_exclusive(x_128);
if (x_149 == 0)
{
return x_128;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_128, 0);
x_151 = lean_ctor_get(x_128, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_128);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
else
{
lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; 
x_153 = lean_ctor_get(x_120, 0);
x_154 = lean_ctor_get_uint8(x_120, sizeof(void*)*2);
x_155 = lean_ctor_get(x_120, 1);
lean_inc(x_155);
lean_inc(x_153);
lean_dec(x_120);
x_156 = lean_st_ref_get(x_14, x_121);
lean_dec(x_14);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_159 = x_156;
} else {
 lean_dec_ref(x_156);
 x_159 = lean_box(0);
}
x_160 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_160, 0, x_153);
lean_ctor_set(x_160, 1, x_155);
lean_ctor_set_uint8(x_160, sizeof(void*)*2, x_154);
x_161 = lean_ctor_get(x_157, 0);
lean_inc(x_161);
lean_dec(x_157);
x_162 = lean_string_validate_utf8(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_161);
x_163 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__5;
x_164 = l_panic___at_String_fromUTF8_x21___spec__1(x_163);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_123);
lean_ctor_set(x_119, 1, x_160);
lean_ctor_set(x_119, 0, x_165);
if (lean_is_scalar(x_159)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_159;
}
lean_ctor_set(x_166, 0, x_119);
lean_ctor_set(x_166, 1, x_158);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_string_from_utf8_unchecked(x_161);
lean_dec(x_161);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_123);
lean_ctor_set(x_119, 1, x_160);
lean_ctor_set(x_119, 0, x_168);
if (lean_is_scalar(x_159)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_159;
}
lean_ctor_set(x_169, 0, x_119);
lean_ctor_set(x_169, 1, x_158);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_155);
lean_dec(x_153);
lean_free_object(x_119);
lean_dec(x_123);
x_170 = lean_ctor_get(x_156, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_156, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_172 = x_156;
} else {
 lean_dec_ref(x_156);
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
}
else
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_174 = lean_ctor_get(x_119, 0);
lean_inc(x_174);
lean_dec(x_119);
x_175 = lean_ctor_get(x_120, 0);
lean_inc(x_175);
x_176 = lean_ctor_get_uint8(x_120, sizeof(void*)*2);
x_177 = lean_ctor_get(x_120, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_178 = x_120;
} else {
 lean_dec_ref(x_120);
 x_178 = lean_box(0);
}
x_179 = lean_st_ref_get(x_14, x_121);
lean_dec(x_14);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
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
if (lean_is_scalar(x_178)) {
 x_183 = lean_alloc_ctor(0, 2, 1);
} else {
 x_183 = x_178;
}
lean_ctor_set(x_183, 0, x_175);
lean_ctor_set(x_183, 1, x_177);
lean_ctor_set_uint8(x_183, sizeof(void*)*2, x_176);
x_184 = lean_ctor_get(x_180, 0);
lean_inc(x_184);
lean_dec(x_180);
x_185 = lean_string_validate_utf8(x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_184);
x_186 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__5;
x_187 = l_panic___at_String_fromUTF8_x21___spec__1(x_186);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_174);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_183);
if (lean_is_scalar(x_182)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_182;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_181);
return x_190;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_191 = lean_string_from_utf8_unchecked(x_184);
lean_dec(x_184);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_174);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_183);
if (lean_is_scalar(x_182)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_182;
}
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_181);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_175);
lean_dec(x_174);
x_195 = lean_ctor_get(x_179, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_179, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_197 = x_179;
} else {
 lean_dec_ref(x_179);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
return x_198;
}
}
}
else
{
uint8_t x_199; 
lean_dec(x_14);
x_199 = !lean_is_exclusive(x_118);
if (x_199 == 0)
{
lean_object* x_200; uint8_t x_201; 
x_200 = lean_ctor_get(x_118, 0);
lean_dec(x_200);
x_201 = !lean_is_exclusive(x_119);
if (x_201 == 0)
{
return x_118;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_119, 0);
x_203 = lean_ctor_get(x_119, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_119);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
lean_ctor_set(x_118, 0, x_204);
return x_118;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_205 = lean_ctor_get(x_118, 1);
lean_inc(x_205);
lean_dec(x_118);
x_206 = lean_ctor_get(x_119, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_119, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_208 = x_119;
} else {
 lean_dec_ref(x_119);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_207);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_205);
return x_210;
}
}
}
else
{
uint8_t x_211; 
lean_dec(x_14);
x_211 = !lean_is_exclusive(x_118);
if (x_211 == 0)
{
return x_118;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_118, 0);
x_213 = lean_ctor_get(x_118, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_118);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
}
}
else
{
uint8_t x_215; 
lean_dec(x_11);
lean_free_object(x_4);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_215 = !lean_is_exclusive(x_13);
if (x_215 == 0)
{
return x_13;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_13, 0);
x_217 = lean_ctor_get(x_13, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_13);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
else
{
uint8_t x_219; 
lean_free_object(x_4);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_219 = !lean_is_exclusive(x_10);
if (x_219 == 0)
{
return x_10;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_10, 0);
x_221 = lean_ctor_get(x_10, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_10);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
}
}
else
{
lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_223 = lean_ctor_get(x_4, 0);
x_224 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_225 = lean_ctor_get(x_4, 1);
lean_inc(x_225);
lean_inc(x_223);
lean_dec(x_4);
x_226 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__1;
x_227 = lean_st_mk_ref(x_226, x_5);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = lean_st_mk_ref(x_226, x_229);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_233, 0, x_223);
lean_ctor_set(x_233, 1, x_225);
lean_ctor_set_uint8(x_233, sizeof(void*)*2, x_224);
x_234 = l_IO_FS_Stream_ofBuffer(x_228);
lean_inc(x_231);
x_235 = l_IO_FS_Stream_ofBuffer(x_231);
if (x_2 == 0)
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_afterBuildCacheSync___spec__2___rarg), 5, 2);
lean_closure_set(x_236, 0, x_235);
lean_closure_set(x_236, 1, x_1);
x_237 = l_IO_withStdin___at_Lake_Package_afterBuildCacheSync___spec__3___rarg(x_234, x_236, x_3, x_233, x_232);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_239 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
x_240 = lean_ctor_get(x_237, 1);
lean_inc(x_240);
lean_dec(x_237);
x_241 = lean_ctor_get(x_238, 0);
lean_inc(x_241);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_242 = x_238;
} else {
 lean_dec_ref(x_238);
 x_242 = lean_box(0);
}
x_243 = lean_ctor_get(x_239, 0);
lean_inc(x_243);
x_244 = lean_ctor_get_uint8(x_239, sizeof(void*)*2);
x_245 = lean_ctor_get(x_239, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_246 = x_239;
} else {
 lean_dec_ref(x_239);
 x_246 = lean_box(0);
}
x_247 = lean_st_ref_get(x_231, x_240);
lean_dec(x_231);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_250 = x_247;
} else {
 lean_dec_ref(x_247);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_251 = lean_alloc_ctor(0, 2, 1);
} else {
 x_251 = x_246;
}
lean_ctor_set(x_251, 0, x_243);
lean_ctor_set(x_251, 1, x_245);
lean_ctor_set_uint8(x_251, sizeof(void*)*2, x_244);
x_252 = lean_ctor_get(x_248, 0);
lean_inc(x_252);
lean_dec(x_248);
x_253 = lean_string_validate_utf8(x_252);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_252);
x_254 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__5;
x_255 = l_panic___at_String_fromUTF8_x21___spec__1(x_254);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_241);
if (lean_is_scalar(x_242)) {
 x_257 = lean_alloc_ctor(0, 2, 0);
} else {
 x_257 = x_242;
}
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_251);
if (lean_is_scalar(x_250)) {
 x_258 = lean_alloc_ctor(0, 2, 0);
} else {
 x_258 = x_250;
}
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_249);
return x_258;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_259 = lean_string_from_utf8_unchecked(x_252);
lean_dec(x_252);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_241);
if (lean_is_scalar(x_242)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_242;
}
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_251);
if (lean_is_scalar(x_250)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_250;
}
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_249);
return x_262;
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
x_263 = lean_ctor_get(x_247, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_247, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_265 = x_247;
} else {
 lean_dec_ref(x_247);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_263);
lean_ctor_set(x_266, 1, x_264);
return x_266;
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_231);
x_267 = lean_ctor_get(x_237, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_268 = x_237;
} else {
 lean_dec_ref(x_237);
 x_268 = lean_box(0);
}
x_269 = lean_ctor_get(x_238, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_238, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_271 = x_238;
} else {
 lean_dec_ref(x_238);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(1, 2, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_269);
lean_ctor_set(x_272, 1, x_270);
if (lean_is_scalar(x_268)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_268;
}
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_267);
return x_273;
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_231);
x_274 = lean_ctor_get(x_237, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_237, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_276 = x_237;
} else {
 lean_dec_ref(x_237);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(1, 2, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_274);
lean_ctor_set(x_277, 1, x_275);
return x_277;
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_inc(x_235);
x_278 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_Package_afterBuildCacheSync___spec__4___rarg), 5, 2);
lean_closure_set(x_278, 0, x_235);
lean_closure_set(x_278, 1, x_1);
x_279 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_afterBuildCacheSync___spec__5___rarg), 5, 2);
lean_closure_set(x_279, 0, x_235);
lean_closure_set(x_279, 1, x_278);
x_280 = l_IO_withStdin___at_Lake_Package_afterBuildCacheSync___spec__6___rarg(x_234, x_279, x_3, x_233, x_232);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_282 = lean_ctor_get(x_281, 1);
lean_inc(x_282);
x_283 = lean_ctor_get(x_280, 1);
lean_inc(x_283);
lean_dec(x_280);
x_284 = lean_ctor_get(x_281, 0);
lean_inc(x_284);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_285 = x_281;
} else {
 lean_dec_ref(x_281);
 x_285 = lean_box(0);
}
x_286 = lean_ctor_get(x_282, 0);
lean_inc(x_286);
x_287 = lean_ctor_get_uint8(x_282, sizeof(void*)*2);
x_288 = lean_ctor_get(x_282, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_289 = x_282;
} else {
 lean_dec_ref(x_282);
 x_289 = lean_box(0);
}
x_290 = lean_st_ref_get(x_231, x_283);
lean_dec(x_231);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; 
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 x_293 = x_290;
} else {
 lean_dec_ref(x_290);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_289)) {
 x_294 = lean_alloc_ctor(0, 2, 1);
} else {
 x_294 = x_289;
}
lean_ctor_set(x_294, 0, x_286);
lean_ctor_set(x_294, 1, x_288);
lean_ctor_set_uint8(x_294, sizeof(void*)*2, x_287);
x_295 = lean_ctor_get(x_291, 0);
lean_inc(x_295);
lean_dec(x_291);
x_296 = lean_string_validate_utf8(x_295);
if (x_296 == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_295);
x_297 = l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__5;
x_298 = l_panic___at_String_fromUTF8_x21___spec__1(x_297);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_284);
if (lean_is_scalar(x_285)) {
 x_300 = lean_alloc_ctor(0, 2, 0);
} else {
 x_300 = x_285;
}
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_294);
if (lean_is_scalar(x_293)) {
 x_301 = lean_alloc_ctor(0, 2, 0);
} else {
 x_301 = x_293;
}
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_292);
return x_301;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_302 = lean_string_from_utf8_unchecked(x_295);
lean_dec(x_295);
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_284);
if (lean_is_scalar(x_285)) {
 x_304 = lean_alloc_ctor(0, 2, 0);
} else {
 x_304 = x_285;
}
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_294);
if (lean_is_scalar(x_293)) {
 x_305 = lean_alloc_ctor(0, 2, 0);
} else {
 x_305 = x_293;
}
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_292);
return x_305;
}
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_286);
lean_dec(x_285);
lean_dec(x_284);
x_306 = lean_ctor_get(x_290, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_290, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 x_308 = x_290;
} else {
 lean_dec_ref(x_290);
 x_308 = lean_box(0);
}
if (lean_is_scalar(x_308)) {
 x_309 = lean_alloc_ctor(1, 2, 0);
} else {
 x_309 = x_308;
}
lean_ctor_set(x_309, 0, x_306);
lean_ctor_set(x_309, 1, x_307);
return x_309;
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_dec(x_231);
x_310 = lean_ctor_get(x_280, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_311 = x_280;
} else {
 lean_dec_ref(x_280);
 x_311 = lean_box(0);
}
x_312 = lean_ctor_get(x_281, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_281, 1);
lean_inc(x_313);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_314 = x_281;
} else {
 lean_dec_ref(x_281);
 x_314 = lean_box(0);
}
if (lean_is_scalar(x_314)) {
 x_315 = lean_alloc_ctor(1, 2, 0);
} else {
 x_315 = x_314;
}
lean_ctor_set(x_315, 0, x_312);
lean_ctor_set(x_315, 1, x_313);
if (lean_is_scalar(x_311)) {
 x_316 = lean_alloc_ctor(0, 2, 0);
} else {
 x_316 = x_311;
}
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_310);
return x_316;
}
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_231);
x_317 = lean_ctor_get(x_280, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_280, 1);
lean_inc(x_318);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_319 = x_280;
} else {
 lean_dec_ref(x_280);
 x_319 = lean_box(0);
}
if (lean_is_scalar(x_319)) {
 x_320 = lean_alloc_ctor(1, 2, 0);
} else {
 x_320 = x_319;
}
lean_ctor_set(x_320, 0, x_317);
lean_ctor_set(x_320, 1, x_318);
return x_320;
}
}
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_228);
lean_dec(x_225);
lean_dec(x_223);
lean_dec(x_3);
lean_dec(x_1);
x_321 = lean_ctor_get(x_230, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_230, 1);
lean_inc(x_322);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_323 = x_230;
} else {
 lean_dec_ref(x_230);
 x_323 = lean_box(0);
}
if (lean_is_scalar(x_323)) {
 x_324 = lean_alloc_ctor(1, 2, 0);
} else {
 x_324 = x_323;
}
lean_ctor_set(x_324, 0, x_321);
lean_ctor_set(x_324, 1, x_322);
return x_324;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_225);
lean_dec(x_223);
lean_dec(x_3);
lean_dec(x_1);
x_325 = lean_ctor_get(x_227, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_227, 1);
lean_inc(x_326);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_327 = x_227;
} else {
 lean_dec_ref(x_227);
 x_327 = lean_box(0);
}
if (lean_is_scalar(x_327)) {
 x_328 = lean_alloc_ctor(1, 2, 0);
} else {
 x_328 = x_327;
}
lean_ctor_set(x_328, 0, x_325);
lean_ctor_set(x_328, 1, x_326);
return x_328;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_afterBuildCacheSync___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___at_Lake_Package_afterBuildCacheSync___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 1;
lean_inc(x_2);
x_6 = l_IO_FS_withIsolatedStreams___at_Lake_Package_afterBuildCacheSync___spec__1___rarg(x_1, x_5, x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_string_utf8_byte_size(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; 
x_16 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_11, x_13, x_14);
x_17 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_11, x_16, x_13);
x_18 = lean_string_utf8_extract(x_11, x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
x_19 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__4___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_22 = lean_string_append(x_20, x_21);
x_23 = 1;
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_array_push(x_26, x_24);
lean_ctor_set(x_10, 0, x_27);
x_28 = lean_box(0);
x_29 = l_Lake_Package_afterBuildCacheSync___rarg___lambda__1(x_12, x_28, x_2, x_10, x_9);
lean_dec(x_2);
return x_29;
}
else
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_10, 0);
x_31 = lean_ctor_get_uint8(x_10, sizeof(void*)*2);
x_32 = lean_ctor_get(x_10, 1);
lean_inc(x_32);
lean_inc(x_30);
lean_dec(x_10);
x_33 = lean_array_push(x_30, x_24);
x_34 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_31);
x_35 = lean_box(0);
x_36 = l_Lake_Package_afterBuildCacheSync___rarg___lambda__1(x_12, x_35, x_2, x_34, x_9);
lean_dec(x_2);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_13);
lean_dec(x_11);
x_37 = lean_box(0);
x_38 = l_Lake_Package_afterBuildCacheSync___rarg___lambda__1(x_12, x_37, x_2, x_10, x_9);
lean_dec(x_2);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_6);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_6, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_7);
if (x_41 == 0)
{
return x_6;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_7, 0);
x_43 = lean_ctor_get(x_7, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_7);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_6, 0, x_44);
return x_6;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_6, 1);
lean_inc(x_45);
lean_dec(x_6);
x_46 = lean_ctor_get(x_7, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_7, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_48 = x_7;
} else {
 lean_dec_ref(x_7);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_45);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_6);
if (x_51 == 0)
{
return x_6;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_6, 0);
x_53 = lean_ctor_get(x_6, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_6);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_5, 1);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_17 = l_Lake_Package_maybeFetchBuildCache___closed__2;
x_18 = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheSync___rarg___lambda__2), 4, 3);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_5);
lean_closure_set(x_18, 2, x_17);
x_19 = l_Task_Priority_default;
x_20 = lean_io_as_task(x_18, x_19, x_8);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_24 = 0;
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_6);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_7);
lean_ctor_set(x_20, 0, x_27);
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
x_30 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2;
x_31 = 0;
x_32 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_6);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_7);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_29);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_7);
lean_dec(x_6);
x_36 = !lean_is_exclusive(x_20);
if (x_36 == 0)
{
return x_20;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_20, 0);
x_38 = lean_ctor_get(x_20, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_20);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; 
lean_inc(x_5);
x_40 = l_Lake_Package_maybeFetchBuildCache(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_41, 1);
x_46 = lean_ctor_get(x_41, 0);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_42);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_42, 0);
x_49 = lean_ctor_get(x_42, 1);
x_50 = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheAsync___rarg___lambda__1___boxed), 5, 1);
lean_closure_set(x_50, 0, x_2);
x_51 = l_Task_Priority_default;
x_52 = 0;
x_53 = l_Lake_BuildTrace_nil;
x_54 = l_Lake_Job_mapM___rarg(x_48, x_50, x_51, x_52, x_5, x_53, x_43);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
lean_ctor_set(x_42, 0, x_56);
lean_ctor_set(x_54, 0, x_41);
return x_54;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_54, 0);
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_54);
lean_ctor_set(x_42, 0, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_41);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_free_object(x_42);
lean_dec(x_49);
lean_free_object(x_41);
lean_dec(x_45);
x_60 = !lean_is_exclusive(x_54);
if (x_60 == 0)
{
return x_54;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_54, 0);
x_62 = lean_ctor_get(x_54, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_54);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_42, 0);
x_65 = lean_ctor_get(x_42, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_42);
x_66 = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheAsync___rarg___lambda__1___boxed), 5, 1);
lean_closure_set(x_66, 0, x_2);
x_67 = l_Task_Priority_default;
x_68 = 0;
x_69 = l_Lake_BuildTrace_nil;
x_70 = l_Lake_Job_mapM___rarg(x_64, x_66, x_67, x_68, x_5, x_69, x_43);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_65);
lean_ctor_set(x_41, 0, x_74);
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_41);
lean_ctor_set(x_75, 1, x_72);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_65);
lean_free_object(x_41);
lean_dec(x_45);
x_76 = lean_ctor_get(x_70, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_70, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_78 = x_70;
} else {
 lean_dec_ref(x_70);
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
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; 
x_80 = lean_ctor_get(x_41, 1);
lean_inc(x_80);
lean_dec(x_41);
x_81 = lean_ctor_get(x_42, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_42, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_83 = x_42;
} else {
 lean_dec_ref(x_42);
 x_83 = lean_box(0);
}
x_84 = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheAsync___rarg___lambda__1___boxed), 5, 1);
lean_closure_set(x_84, 0, x_2);
x_85 = l_Task_Priority_default;
x_86 = 0;
x_87 = l_Lake_BuildTrace_nil;
x_88 = l_Lake_Job_mapM___rarg(x_81, x_84, x_85, x_86, x_5, x_87, x_43);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
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
if (lean_is_scalar(x_83)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_83;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_82);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_80);
if (lean_is_scalar(x_91)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_91;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_90);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_80);
x_95 = lean_ctor_get(x_88, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_88, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_97 = x_88;
} else {
 lean_dec_ref(x_88);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_5);
lean_dec(x_2);
x_99 = !lean_is_exclusive(x_40);
if (x_99 == 0)
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_ctor_get(x_40, 0);
lean_dec(x_100);
x_101 = !lean_is_exclusive(x_41);
if (x_101 == 0)
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_ctor_get(x_41, 0);
lean_dec(x_102);
x_103 = !lean_is_exclusive(x_42);
if (x_103 == 0)
{
return x_40;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_42, 0);
x_105 = lean_ctor_get(x_42, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_42);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_41, 0, x_106);
return x_40;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_107 = lean_ctor_get(x_41, 1);
lean_inc(x_107);
lean_dec(x_41);
x_108 = lean_ctor_get(x_42, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_42, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_110 = x_42;
} else {
 lean_dec_ref(x_42);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_107);
lean_ctor_set(x_40, 0, x_112);
return x_40;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_113 = lean_ctor_get(x_40, 1);
lean_inc(x_113);
lean_dec(x_40);
x_114 = lean_ctor_get(x_41, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_115 = x_41;
} else {
 lean_dec_ref(x_41);
 x_115 = lean_box(0);
}
x_116 = lean_ctor_get(x_42, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_42, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_118 = x_42;
} else {
 lean_dec_ref(x_42);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
if (lean_is_scalar(x_115)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_115;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_114);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_113);
return x_121;
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_5);
lean_dec(x_2);
x_122 = !lean_is_exclusive(x_40);
if (x_122 == 0)
{
return x_40;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_40, 0);
x_124 = lean_ctor_get(x_40, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_40);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
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
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_afterBuildCacheSync___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_IO_FS_withIsolatedStreams___at_Lake_Package_afterBuildCacheSync___spec__1___rarg(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Package_afterBuildCacheSync___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
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
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__6;
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
x_2 = l_Lake_Package_extraDepFacetConfig___closed__2;
x_3 = l_Lake_Package_extraDepFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addPackageFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initPackageFacetConfigs___closed__2;
x_2 = l_Lake_Package_optBuildCacheFacetConfig___closed__4;
x_3 = l_Lake_Package_optBuildCacheFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addPackageFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initPackageFacetConfigs___closed__3;
x_2 = l_Lake_Package_buildCacheFacetConfig___elambda__1___closed__2;
x_3 = l_Lake_Package_buildCacheFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addPackageFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initPackageFacetConfigs___closed__4;
x_2 = l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__2;
x_3 = l_Lake_Package_optBarrelFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addPackageFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initPackageFacetConfigs___closed__5;
x_2 = l_Lake_Package_barrelFacetConfig___elambda__1___closed__2;
x_3 = l_Lake_Package_barrelFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addPackageFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initPackageFacetConfigs___closed__6;
x_2 = l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__4;
x_3 = l_Lake_Package_optGitHubReleaseFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addPackageFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initPackageFacetConfigs___closed__7;
x_2 = l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___closed__2;
x_3 = l_Lake_Package_gitHubReleaseFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addPackageFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_initPackageFacetConfigs___closed__8;
return x_1;
}
}
lean_object* initialize_Lake_Util_Git(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Sugar(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Common(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Targets(uint8_t builtin, lean_object*);
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
res = initialize_Lake_Reservoir(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1___closed__1 = _init_l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1___closed__1();
lean_mark_persistent(l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1___closed__1);
l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1___closed__2 = _init_l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1___closed__2();
lean_mark_persistent(l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1___closed__2);
l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__1);
l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__2);
l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__3 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__3();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__3);
l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__4 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__4();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__4);
l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__5 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__5();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__5);
l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__6 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__6();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__8___closed__6);
l_Lake_Package_recComputeDeps___closed__1 = _init_l_Lake_Package_recComputeDeps___closed__1();
lean_mark_persistent(l_Lake_Package_recComputeDeps___closed__1);
l_Lake_Package_depsFacetConfig___closed__1 = _init_l_Lake_Package_depsFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Package_depsFacetConfig___closed__1);
l_Lake_Package_depsFacetConfig___closed__2 = _init_l_Lake_Package_depsFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Package_depsFacetConfig___closed__2);
l_Lake_Package_depsFacetConfig = _init_l_Lake_Package_depsFacetConfig();
lean_mark_persistent(l_Lake_Package_depsFacetConfig);
l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__1 = _init_l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__1();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__1);
l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__2 = _init_l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__2();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__2);
l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__3 = _init_l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__3();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__3);
l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__4 = _init_l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__4();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___closed__4);
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
l_Lake_Package_optBuildCacheFacetConfig___closed__6 = _init_l_Lake_Package_optBuildCacheFacetConfig___closed__6();
lean_mark_persistent(l_Lake_Package_optBuildCacheFacetConfig___closed__6);
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
l_Lake_Package_maybeFetchBuildCache___closed__6 = _init_l_Lake_Package_maybeFetchBuildCache___closed__6();
lean_mark_persistent(l_Lake_Package_maybeFetchBuildCache___closed__6);
l_Lake_Package_maybeFetchBuildCache___closed__7 = _init_l_Lake_Package_maybeFetchBuildCache___closed__7();
lean_mark_persistent(l_Lake_Package_maybeFetchBuildCache___closed__7);
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
l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__1 = _init_l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__1();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__1);
l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__2 = _init_l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__2();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__2);
l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__3 = _init_l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__3();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__3);
l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__4 = _init_l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__4();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__4);
l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__5 = _init_l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__5();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___spec__1___closed__5);
l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__4___closed__1 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__4___closed__1();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__4___closed__1);
l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__6___closed__1 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__6___closed__1();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___lambda__6___closed__1);
l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1___closed__1 = _init_l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1___closed__1();
lean_mark_persistent(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___lambda__1___closed__1);
l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__1 = _init_l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__1();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__1);
l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__2 = _init_l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__2();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__2);
l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__3 = _init_l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__3();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__3);
l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__4 = _init_l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__4();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__4);
l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__5 = _init_l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__5();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__5);
l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__6 = _init_l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__6();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig___elambda__1___lambda__1___closed__6);
l_Lake_Package_buildCacheFacetConfig___elambda__1___closed__1 = _init_l_Lake_Package_buildCacheFacetConfig___elambda__1___closed__1();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig___elambda__1___closed__1);
l_Lake_Package_buildCacheFacetConfig___elambda__1___closed__2 = _init_l_Lake_Package_buildCacheFacetConfig___elambda__1___closed__2();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig___elambda__1___closed__2);
l_Lake_Package_buildCacheFacetConfig___elambda__1___closed__3 = _init_l_Lake_Package_buildCacheFacetConfig___elambda__1___closed__3();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig___elambda__1___closed__3);
l_Lake_Package_buildCacheFacetConfig___closed__1 = _init_l_Lake_Package_buildCacheFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig___closed__1);
l_Lake_Package_buildCacheFacetConfig___closed__2 = _init_l_Lake_Package_buildCacheFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig___closed__2);
l_Lake_Package_buildCacheFacetConfig = _init_l_Lake_Package_buildCacheFacetConfig();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig);
l_Lake_Package_optBarrelFacetConfig___lambda__1___closed__1 = _init_l_Lake_Package_optBarrelFacetConfig___lambda__1___closed__1();
lean_mark_persistent(l_Lake_Package_optBarrelFacetConfig___lambda__1___closed__1);
l_Lake_Package_optBarrelFacetConfig___closed__1 = _init_l_Lake_Package_optBarrelFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Package_optBarrelFacetConfig___closed__1);
l_Lake_Package_optBarrelFacetConfig___closed__2 = _init_l_Lake_Package_optBarrelFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Package_optBarrelFacetConfig___closed__2);
l_Lake_Package_optBarrelFacetConfig = _init_l_Lake_Package_optBarrelFacetConfig();
lean_mark_persistent(l_Lake_Package_optBarrelFacetConfig);
l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__1 = _init_l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__1();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__1);
l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__2 = _init_l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__2();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__2);
l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__3 = _init_l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__3();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__3);
l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__4 = _init_l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__4();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__4);
l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__5 = _init_l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__5();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__5);
l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__6 = _init_l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__6();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig___elambda__1___lambda__1___closed__6);
l_Lake_Package_barrelFacetConfig___elambda__1___closed__1 = _init_l_Lake_Package_barrelFacetConfig___elambda__1___closed__1();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig___elambda__1___closed__1);
l_Lake_Package_barrelFacetConfig___elambda__1___closed__2 = _init_l_Lake_Package_barrelFacetConfig___elambda__1___closed__2();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig___elambda__1___closed__2);
l_Lake_Package_barrelFacetConfig___elambda__1___closed__3 = _init_l_Lake_Package_barrelFacetConfig___elambda__1___closed__3();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig___elambda__1___closed__3);
l_Lake_Package_barrelFacetConfig___closed__1 = _init_l_Lake_Package_barrelFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig___closed__1);
l_Lake_Package_barrelFacetConfig___closed__2 = _init_l_Lake_Package_barrelFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig___closed__2);
l_Lake_Package_barrelFacetConfig = _init_l_Lake_Package_barrelFacetConfig();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig);
l_Lake_Package_optGitHubReleaseFacetConfig = _init_l_Lake_Package_optGitHubReleaseFacetConfig();
lean_mark_persistent(l_Lake_Package_optGitHubReleaseFacetConfig);
l_Lake_Package_optReleaseFacetConfig = _init_l_Lake_Package_optReleaseFacetConfig();
lean_mark_persistent(l_Lake_Package_optReleaseFacetConfig);
l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__1 = _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__1();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__1);
l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__2 = _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__2();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__2);
l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__3 = _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__3();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__3);
l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__4 = _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__4();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__4);
l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__5 = _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__5();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__5);
l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__6 = _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__6();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___lambda__1___closed__6);
l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___closed__1 = _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___closed__1();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___closed__1);
l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___closed__2 = _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___closed__2();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___closed__2);
l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___closed__3 = _init_l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___closed__3();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig___elambda__1___closed__3);
l_Lake_Package_gitHubReleaseFacetConfig___closed__1 = _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig___closed__1);
l_Lake_Package_gitHubReleaseFacetConfig___closed__2 = _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig___closed__2);
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
l_Lake_initPackageFacetConfigs = _init_l_Lake_initPackageFacetConfigs();
lean_mark_persistent(l_Lake_initPackageFacetConfigs);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

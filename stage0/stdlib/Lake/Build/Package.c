// Lean compiler output
// Module: Lake.Build.Package
// Imports: Init Lake.Util.Git Lake.Util.Sugar Lake.Build.Common Lake.Build.Targets
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
static lean_object* l_Lake_Package_recBuildExtraDepTargets___closed__1;
static lean_object* l_Lake_Package_releaseFacetConfig___elambda__1___lambda__2___closed__1;
lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_fetchTargetJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_afterReleaseSync___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
static lean_object* l_Lake_Package_depsFacetConfig___closed__2;
static lean_object* l_Lake_Package_fetchOptRelease___lambda__3___closed__9;
LEAN_EXPORT lean_object* l_Lake_initPackageFacetConfigs;
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterReleaseSync___spec__8(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_Package_fetchOptRelease___lambda__3___closed__16;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static lean_object* l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___closed__1;
lean_object* l_Lake_BuildJob_add___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterReleaseSync___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Package_afterReleaseSync___spec__10(lean_object*);
static lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__5;
static lean_object* l_Lake_Package_fetchOptRelease___lambda__3___closed__1;
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_Package_fetchOptRelease___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_hashset_mk_idx(lean_object*, uint64_t);
static uint8_t l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1___lambda__2___closed__1;
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_Package_optReleaseFacetConfig___spec__1___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Package_fetchOptRelease___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_recBuildExtraDepTargets___closed__3;
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseSync___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_depsFacetConfig___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_HashSetImp_contains___at_Lake_Package_recComputeDeps___spec__2(lean_object*, lean_object*);
static lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__4;
LEAN_EXPORT uint8_t l_List_elem___at_Lake_Package_recComputeDeps___spec__3(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_recBuildExtraDepTargets___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lake_Package_fetchOptRelease___lambda__3___closed__14;
lean_object* l_Lake_download(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_fetchOptRelease___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_afterReleaseSync___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__2;
extern lean_object* l_Lake_instOrdJobAction;
static lean_object* l_Lake_Package_fetchOptRelease___lambda__3___closed__4;
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterReleaseSync___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterReleaseSync___spec__9(lean_object*);
static lean_object* l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___closed__2;
static lean_object* l_Lake_Package_fetchOptRelease___lambda__3___closed__10;
static lean_object* l_Lake_Package_releaseFacetConfig___elambda__1___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_HashSetImp_contains___at_Lake_Package_recComputeDeps___spec__2___boxed(lean_object*, lean_object*);
extern lean_object* l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
lean_object* l_Lake_readTraceFile_x3f(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_fetchOptRelease___lambda__2___closed__1;
uint8_t lean_string_validate_utf8(lean_object*);
static lean_object* l_Lake_Package_fetchOptRelease___lambda__3___closed__17;
static lean_object* l_Lake_initPackageFacetConfigs___closed__3;
static lean_object* l_Lake_Package_recBuildExtraDepTargets___closed__8;
LEAN_EXPORT lean_object* l_Lake_Package_fetchOptRelease___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseSync___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__2;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_fetchOptRelease___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_String_isEmpty(lean_object*);
lean_object* lean_task_pure(lean_object*);
uint8_t l_instDecidableNot___rarg(uint8_t);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11___closed__2;
static lean_object* l_Lake_Package_recBuildExtraDepTargets___closed__9;
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_captureProc_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_afterReleaseSync___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterReleaseSync___spec__12(lean_object*);
LEAN_EXPORT lean_object* l_List_replace___at_Lake_Package_recComputeDeps___spec__9(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
extern lean_object* l_ByteArray_empty;
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
static lean_object* l_Lake_Package_recBuildExtraDepTargets___closed__5;
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterReleaseSync___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Package_recBuildExtraDepTargets___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1___closed__2;
static lean_object* l_Lake_Package_optReleaseFacetConfig___closed__3;
lean_object* l_Lake_BuildInfo_fetch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_releaseFacetConfig___elambda__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_withRegisterJob___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_optReleaseFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_fetchOptRelease___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_afterReleaseSync___spec__7___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseAsync(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lake_Package_optReleaseFacetConfig___closed__1;
static lean_object* l_Lake_initPackageFacetConfigs___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseSync___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseAsync___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_releaseFacetConfig___closed__3;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lake_Package_fetchOptRelease___lambda__3___closed__7;
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__4;
LEAN_EXPORT lean_object* l_Lake_Package_optReleaseFacetConfig;
static lean_object* l_Lake_Package_recBuildExtraDepTargets___closed__6;
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseSync(lean_object*);
static lean_object* l_Lake_Package_fetchOptRelease___lambda__3___closed__22;
lean_object* l_Lake_JobState_merge(lean_object*, lean_object*);
lean_object* l_Lake_checkHashUpToDate___at_Lake_buildFileUnlessUpToDate___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_releaseFacetConfig___closed__1;
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_panic___at_String_fromUTF8_x21___spec__1(lean_object*);
static lean_object* l_Lake_Package_fetchOptRelease___lambda__3___closed__12;
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterReleaseSync___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_fetchOptRelease___lambda__3___closed__13;
static lean_object* l_Lake_Package_fetchOptRelease___lambda__3___closed__11;
LEAN_EXPORT lean_object* l_Lake_Package_releaseFacetConfig___elambda__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_afterReleaseSync___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Task_Priority_default;
static lean_object* l_Functor_discard___at_Lake_Package_optReleaseFacetConfig___spec__1___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_fetchOptRelease___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_Package_recComputeDeps___spec__7___at_Lake_Package_recComputeDeps___spec__8(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildJob_mix___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterReleaseSync___spec__11(lean_object*);
extern lean_object* l_Lake_BuildTrace_nil;
LEAN_EXPORT lean_object* l_Lake_Package_fetchOptRelease___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseAsync___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lake_EResult_map___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_releaseFacetConfig___elambda__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Package_afterReleaseSync___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___closed__1;
extern lean_object* l_Lake_defaultLakeDir;
lean_object* lean_string_from_utf8(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___closed__2;
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterReleaseSync___spec__12___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_untar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lake_Git_defaultRemote;
LEAN_EXPORT lean_object* l_Lake_Package_optReleaseFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_releaseFacetConfig;
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterReleaseSync___spec__6(lean_object*);
lean_object* l_ReaderT_pure___at_Lake_buildStaticLib___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_releaseFacetConfig___elambda__1___closed__2;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_afterReleaseSync___spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_fetchOptRelease___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_recComputeDeps___closed__1;
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterReleaseSync___spec__9___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_deps___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_depsFacetConfig;
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Package_afterReleaseSync___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_fetchOptRelease___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_releaseFacetConfig___elambda__1___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterReleaseSync___spec__11___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__10(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_Package_fetchOptRelease___lambda__3___closed__21;
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterReleaseSync___spec__3(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_Package_extraDepFacetConfig___closed__2;
static lean_object* l_Lake_Package_recBuildExtraDepTargets___closed__7;
static lean_object* l_Lake_Package_extraDepFacetConfig___closed__3;
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterReleaseSync___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_releaseFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_releaseFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_fetchOptRelease___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_extraDepFacetConfig___closed__4;
uint64_t l_Lean_Name_hash___override(lean_object*);
static lean_object* l_Lake_Package_fetchOptRelease___lambda__3___closed__3;
lean_object* lean_io_exit(uint8_t, lean_object*);
uint8_t l_instDecidableRelLe___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Package_fetchOptRelease(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instHashablePackage___boxed(lean_object*);
static lean_object* l_Lake_Package_releaseFacetConfig___closed__4;
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_recBuildExtraDepTargets___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_Package_recComputeDeps___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lake_initPackageFacetConfigs___closed__4;
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___lambda__1(lean_object*);
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseAsync___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_fetchOptRelease___lambda__3___closed__5;
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_Package_optReleaseFacetConfig___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at_Lake_Package_recComputeDeps___spec__3___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Package_fetchOptRelease___lambda__3___closed__6;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11___closed__1;
static lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__3;
static lean_object* l_Lake_Package_recBuildExtraDepTargets___closed__2;
static lean_object* l_Lake_Package_recBuildExtraDepTargets___closed__4;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_releaseFacetConfig___elambda__1___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__1;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert___at_Lake_Package_recComputeDeps___spec__4(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lake_Package_fetchOptRelease___lambda__3___closed__18;
static lean_object* l_Lake_Package_fetchOptRelease___lambda__3___closed__2;
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_Package_recBuildExtraDepTargets___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lake_Workspace_addPackageFacetConfig___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optReleaseFacetConfig___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_fetchOptRelease___lambda__3___closed__20;
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterReleaseSync___spec__2(lean_object*);
lean_object* l_Lake_instBEqPackage___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_writeTraceFile(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__5(lean_object*, lean_object*, lean_object*);
extern uint32_t l_Lake_noBuildCode;
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterReleaseSync___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries___at_Lake_Package_recComputeDeps___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lake_Package_fetchOptRelease___lambda__3___closed__19;
static lean_object* l_Lake_Package_extraDepFacetConfig___closed__1;
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__3;
static lean_object* l_Lake_initPackageFacetConfigs___closed__1;
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand___at_Lake_Package_recComputeDeps___spec__5(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lake_Package_releaseFacetConfig___elambda__1___closed__1;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lake_Package_fetchOptRelease___lambda__3___closed__15;
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_fetchOptRelease___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__1;
static lean_object* l_Lake_Package_fetchOptRelease___lambda__3___closed__8;
LEAN_EXPORT lean_object* l_Lake_Package_recComputeDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_Package_recBuildExtraDepTargets___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_releaseFacetConfig___elambda__1___lambda__1___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__1(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_optReleaseFacetConfig___closed__4;
lean_object* l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_fetchOptRelease___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Functor_discard___at_Lake_Package_optReleaseFacetConfig___spec__1___closed__1;
LEAN_EXPORT lean_object* l_List_replace___at_Lake_Package_recComputeDeps___spec__9___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_fetchOptRelease___lambda__3___closed__23;
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Package_afterReleaseSync___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at_Lake_Package_recComputeDeps___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_ctor_get(x_2, 1);
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
LEAN_EXPORT uint8_t l_Lean_HashSetImp_contains___at_Lake_Package_recComputeDeps___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_5, 2);
x_7 = l_Lean_Name_hash___override(x_6);
x_8 = lean_hashset_mk_idx(x_4, x_7);
x_9 = lean_array_uget(x_3, x_8);
x_10 = l_List_elem___at_Lake_Package_recComputeDeps___spec__3(x_2, x_9);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_Package_recComputeDeps___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = lean_hashset_mk_idx(x_7, x_9);
x_11 = lean_array_uget(x_2, x_10);
lean_ctor_set(x_3, 1, x_11);
x_12 = lean_array_uset(x_2, x_10, x_3);
x_2 = x_12;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_14);
x_17 = lean_apply_1(x_1, x_14);
x_18 = lean_unbox_uint64(x_17);
lean_dec(x_17);
x_19 = lean_hashset_mk_idx(x_16, x_18);
x_20 = lean_array_uget(x_2, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_uset(x_2, x_19, x_21);
x_2 = x_22;
x_3 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_Package_recComputeDeps___spec__7___at_Lake_Package_recComputeDeps___spec__8(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_1);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Name_hash___override(x_8);
lean_dec(x_8);
x_10 = lean_hashset_mk_idx(x_6, x_9);
x_11 = lean_array_uget(x_1, x_10);
lean_ctor_set(x_2, 1, x_11);
x_12 = lean_array_uset(x_1, x_10, x_2);
x_1 = x_12;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_16 = lean_array_get_size(x_1);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Name_hash___override(x_18);
lean_dec(x_18);
x_20 = lean_hashset_mk_idx(x_16, x_19);
x_21 = lean_array_uget(x_1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_array_uset(x_1, x_20, x_22);
x_1 = x_23;
x_2 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries___at_Lake_Package_recComputeDeps___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_List_foldl___at_Lake_Package_recComputeDeps___spec__7___at_Lake_Package_recComputeDeps___spec__8(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand___at_Lake_Package_recComputeDeps___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Lean_HashSetImp_moveEntries___at_Lake_Package_recComputeDeps___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_replace___at_Lake_Package_recComputeDeps___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_3);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_6, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_10, 2);
x_12 = lean_name_eq(x_9, x_11);
lean_dec(x_9);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_List_replace___at_Lake_Package_recComputeDeps___spec__9(x_7, x_2, x_3);
lean_ctor_set(x_1, 1, x_13);
return x_1;
}
else
{
lean_dec(x_6);
lean_ctor_set(x_1, 0, x_3);
return x_1;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_16 = lean_ctor_get(x_14, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_2, 2);
x_19 = lean_ctor_get(x_18, 2);
x_20 = lean_name_eq(x_17, x_19);
lean_dec(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_List_replace___at_Lake_Package_recComputeDeps___spec__9(x_15, x_2, x_3);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_15);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert___at_Lake_Package_recComputeDeps___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Name_hash___override(x_8);
lean_dec(x_8);
lean_inc(x_6);
x_10 = lean_hashset_mk_idx(x_6, x_9);
x_11 = lean_array_uget(x_5, x_10);
x_12 = l_List_elem___at_Lake_Package_recComputeDeps___spec__3(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_11);
x_16 = lean_array_uset(x_5, x_10, x_15);
x_17 = lean_nat_dec_le(x_14, x_6);
lean_dec(x_6);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_1);
x_18 = l_Lean_HashSetImp_expand___at_Lake_Package_recComputeDeps___spec__5(x_14, x_16);
return x_18;
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
x_19 = lean_box(0);
x_20 = lean_array_uset(x_5, x_10, x_19);
lean_inc(x_2);
x_21 = l_List_replace___at_Lake_Package_recComputeDeps___spec__9(x_11, x_2, x_2);
lean_dec(x_2);
x_22 = lean_array_uset(x_20, x_10, x_21);
lean_ctor_set(x_1, 1, x_22);
return x_1;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; size_t x_29; lean_object* x_30; uint8_t x_31; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
x_25 = lean_array_get_size(x_24);
x_26 = lean_ctor_get(x_2, 2);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 2);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_Name_hash___override(x_27);
lean_dec(x_27);
lean_inc(x_25);
x_29 = lean_hashset_mk_idx(x_25, x_28);
x_30 = lean_array_uget(x_24, x_29);
x_31 = l_List_elem___at_Lake_Package_recComputeDeps___spec__3(x_2, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_23, x_32);
lean_dec(x_23);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_2);
lean_ctor_set(x_34, 1, x_30);
x_35 = lean_array_uset(x_24, x_29, x_34);
x_36 = lean_nat_dec_le(x_33, x_25);
lean_dec(x_25);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l_Lean_HashSetImp_expand___at_Lake_Package_recComputeDeps___spec__5(x_33, x_35);
return x_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_25);
x_39 = lean_box(0);
x_40 = lean_array_uset(x_24, x_29, x_39);
lean_inc(x_2);
x_41 = l_List_replace___at_Lake_Package_recComputeDeps___spec__9(x_30, x_2, x_2);
lean_dec(x_2);
x_42 = lean_array_uset(x_40, x_29, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_23);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
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
x_4 = l_Lean_HashSetImp_contains___at_Lake_Package_recComputeDeps___spec__2(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
lean_inc(x_2);
x_6 = lean_array_push(x_5, x_2);
x_7 = l_Lean_HashSetImp_insert___at_Lake_Package_recComputeDeps___spec__4(x_3, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("deps", 4);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_36; 
x_36 = lean_usize_dec_eq(x_2, x_3);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_array_uget(x_1, x_2);
x_38 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11___closed__2;
lean_inc(x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_inc(x_5);
lean_inc(x_7);
lean_inc(x_6);
x_40 = lean_apply_6(x_5, x_39, x_6, x_7, x_8, x_9, x_10);
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
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_41, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_array_get_size(x_47);
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_nat_dec_lt(x_49, x_48);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_48);
lean_dec(x_47);
x_51 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(x_4, x_37);
lean_ctor_set(x_42, 0, x_51);
x_11 = x_41;
x_12 = x_43;
goto block_35;
}
else
{
uint8_t x_52; 
x_52 = lean_nat_dec_le(x_48, x_48);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_48);
lean_dec(x_47);
x_53 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(x_4, x_37);
lean_ctor_set(x_42, 0, x_53);
x_11 = x_41;
x_12 = x_43;
goto block_35;
}
else
{
size_t x_54; size_t x_55; lean_object* x_56; lean_object* x_57; 
x_54 = 0;
x_55 = lean_usize_of_nat(x_48);
lean_dec(x_48);
x_56 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__10(x_47, x_54, x_55, x_4);
lean_dec(x_47);
x_57 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(x_56, x_37);
lean_ctor_set(x_42, 0, x_57);
x_11 = x_41;
x_12 = x_43;
goto block_35;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_42, 0);
x_59 = lean_ctor_get(x_42, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_42);
x_60 = lean_array_get_size(x_58);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_nat_dec_lt(x_61, x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_60);
lean_dec(x_58);
x_63 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(x_4, x_37);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_59);
lean_ctor_set(x_41, 0, x_64);
x_11 = x_41;
x_12 = x_43;
goto block_35;
}
else
{
uint8_t x_65; 
x_65 = lean_nat_dec_le(x_60, x_60);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_60);
lean_dec(x_58);
x_66 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(x_4, x_37);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_59);
lean_ctor_set(x_41, 0, x_67);
x_11 = x_41;
x_12 = x_43;
goto block_35;
}
else
{
size_t x_68; size_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = 0;
x_69 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_70 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__10(x_58, x_68, x_69, x_4);
lean_dec(x_58);
x_71 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(x_70, x_37);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_59);
lean_ctor_set(x_41, 0, x_72);
x_11 = x_41;
x_12 = x_43;
goto block_35;
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_73 = lean_ctor_get(x_41, 1);
lean_inc(x_73);
lean_dec(x_41);
x_74 = lean_ctor_get(x_42, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_42, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_76 = x_42;
} else {
 lean_dec_ref(x_42);
 x_76 = lean_box(0);
}
x_77 = lean_array_get_size(x_74);
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_nat_dec_lt(x_78, x_77);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_77);
lean_dec(x_74);
x_80 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(x_4, x_37);
if (lean_is_scalar(x_76)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_76;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_75);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_73);
x_11 = x_82;
x_12 = x_43;
goto block_35;
}
else
{
uint8_t x_83; 
x_83 = lean_nat_dec_le(x_77, x_77);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_77);
lean_dec(x_74);
x_84 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(x_4, x_37);
if (lean_is_scalar(x_76)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_76;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_75);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_73);
x_11 = x_86;
x_12 = x_43;
goto block_35;
}
else
{
size_t x_87; size_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_87 = 0;
x_88 = lean_usize_of_nat(x_77);
lean_dec(x_77);
x_89 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__10(x_74, x_87, x_88, x_4);
lean_dec(x_74);
x_90 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(x_89, x_37);
if (lean_is_scalar(x_76)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_76;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_75);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_73);
x_11 = x_92;
x_12 = x_43;
goto block_35;
}
}
}
}
else
{
lean_object* x_93; uint8_t x_94; 
lean_dec(x_37);
lean_dec(x_4);
x_93 = lean_ctor_get(x_40, 1);
lean_inc(x_93);
lean_dec(x_40);
x_94 = !lean_is_exclusive(x_41);
if (x_94 == 0)
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_ctor_get(x_41, 0);
lean_dec(x_95);
x_96 = !lean_is_exclusive(x_42);
if (x_96 == 0)
{
x_11 = x_41;
x_12 = x_93;
goto block_35;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_42, 0);
x_98 = lean_ctor_get(x_42, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_42);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set(x_41, 0, x_99);
x_11 = x_41;
x_12 = x_93;
goto block_35;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_100 = lean_ctor_get(x_41, 1);
lean_inc(x_100);
lean_dec(x_41);
x_101 = lean_ctor_get(x_42, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_42, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_103 = x_42;
} else {
 lean_dec_ref(x_42);
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
x_11 = x_105;
x_12 = x_93;
goto block_35;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_37);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_106 = !lean_is_exclusive(x_40);
if (x_106 == 0)
{
return x_40;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_40, 0);
x_108 = lean_ctor_get(x_40, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_40);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_4);
lean_ctor_set(x_110, 1, x_8);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_9);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_10);
return x_112;
}
block_35:
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_2 = x_18;
x_4 = x_15;
x_8 = x_16;
x_9 = x_14;
x_10 = x_12;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_11, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_12);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_11, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_11);
lean_ctor_set(x_27, 1, x_12);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
lean_dec(x_11);
x_29 = lean_ctor_get(x_13, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_31 = x_13;
} else {
 lean_dec_ref(x_13);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(1, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_12);
return x_34;
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
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_1, 6);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_array_get_size(x_8);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at_Lake_Package_deps___spec__1(x_10, x_11, x_8);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = l_Lake_Package_recComputeDeps___closed__1;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_6);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_13, x_13);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = l_Lake_Package_recComputeDeps___closed__1;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_5);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_7);
return x_24;
}
else
{
size_t x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_26 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_27 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11(x_12, x_11, x_25, x_26, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_12);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_27, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_28, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
lean_ctor_set(x_29, 0, x_36);
return x_27;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_29, 0);
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_29);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_28, 0, x_40);
return x_27;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_28, 1);
lean_inc(x_41);
lean_dec(x_28);
x_42 = lean_ctor_get(x_29, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_29, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_44 = x_29;
} else {
 lean_dec_ref(x_29);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
lean_ctor_set(x_27, 0, x_47);
return x_27;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_48 = lean_ctor_get(x_27, 1);
lean_inc(x_48);
lean_dec(x_27);
x_49 = lean_ctor_get(x_28, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_50 = x_28;
} else {
 lean_dec_ref(x_28);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_29, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_29, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_53 = x_29;
} else {
 lean_dec_ref(x_29);
 x_53 = lean_box(0);
}
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
if (lean_is_scalar(x_50)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_50;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_49);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_48);
return x_57;
}
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_27);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_27, 0);
lean_dec(x_59);
x_60 = !lean_is_exclusive(x_28);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_28, 0);
lean_dec(x_61);
x_62 = !lean_is_exclusive(x_29);
if (x_62 == 0)
{
return x_27;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_29, 0);
x_64 = lean_ctor_get(x_29, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_29);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_28, 0, x_65);
return x_27;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_28, 1);
lean_inc(x_66);
lean_dec(x_28);
x_67 = lean_ctor_get(x_29, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_29, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_69 = x_29;
} else {
 lean_dec_ref(x_29);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_66);
lean_ctor_set(x_27, 0, x_71);
return x_27;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_72 = lean_ctor_get(x_27, 1);
lean_inc(x_72);
lean_dec(x_27);
x_73 = lean_ctor_get(x_28, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_74 = x_28;
} else {
 lean_dec_ref(x_28);
 x_74 = lean_box(0);
}
x_75 = lean_ctor_get(x_29, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_29, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_77 = x_29;
} else {
 lean_dec_ref(x_29);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
if (lean_is_scalar(x_74)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_74;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_73);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_72);
return x_80;
}
}
}
else
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_27);
if (x_81 == 0)
{
return x_27;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_27, 0);
x_83 = lean_ctor_get(x_27, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_27);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at_Lake_Package_recComputeDeps___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at_Lake_Package_recComputeDeps___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_contains___at_Lake_Package_recComputeDeps___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_HashSetImp_contains___at_Lake_Package_recComputeDeps___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_replace___at_Lake_Package_recComputeDeps___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_replace___at_Lake_Package_recComputeDeps___spec__9(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__10(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
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
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("extraDep", 8);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_54; 
x_54 = lean_usize_dec_lt(x_3, x_2);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_4);
lean_ctor_set(x_55, 1, x_8);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_9);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_10);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_array_uget(x_1, x_3);
x_59 = l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___closed__2;
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
lean_inc(x_5);
lean_inc(x_7);
lean_inc(x_6);
x_61 = lean_apply_6(x_5, x_60, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = !lean_is_exclusive(x_62);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_62, 0);
lean_dec(x_66);
x_67 = !lean_is_exclusive(x_63);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_63, 0);
x_69 = l_Lake_BuildJob_mix___rarg(x_4, x_68);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_63, 0, x_70);
x_11 = x_62;
x_12 = x_64;
goto block_53;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_63, 0);
x_72 = lean_ctor_get(x_63, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_63);
x_73 = l_Lake_BuildJob_mix___rarg(x_4, x_71);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_72);
lean_ctor_set(x_62, 0, x_75);
x_11 = x_62;
x_12 = x_64;
goto block_53;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_76 = lean_ctor_get(x_62, 1);
lean_inc(x_76);
lean_dec(x_62);
x_77 = lean_ctor_get(x_63, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_63, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_79 = x_63;
} else {
 lean_dec_ref(x_63);
 x_79 = lean_box(0);
}
x_80 = l_Lake_BuildJob_mix___rarg(x_4, x_77);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
if (lean_is_scalar(x_79)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_79;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_78);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_76);
x_11 = x_83;
x_12 = x_64;
goto block_53;
}
}
else
{
lean_object* x_84; uint8_t x_85; 
lean_dec(x_4);
x_84 = lean_ctor_get(x_61, 1);
lean_inc(x_84);
lean_dec(x_61);
x_85 = !lean_is_exclusive(x_62);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_62, 0);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_63);
if (x_87 == 0)
{
x_11 = x_62;
x_12 = x_84;
goto block_53;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_63, 0);
x_89 = lean_ctor_get(x_63, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_63);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_62, 0, x_90);
x_11 = x_62;
x_12 = x_84;
goto block_53;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_91 = lean_ctor_get(x_62, 1);
lean_inc(x_91);
lean_dec(x_62);
x_92 = lean_ctor_get(x_63, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_63, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_94 = x_63;
} else {
 lean_dec_ref(x_63);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_91);
x_11 = x_96;
x_12 = x_84;
goto block_53;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_97 = !lean_is_exclusive(x_61);
if (x_97 == 0)
{
return x_61;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_61, 0);
x_99 = lean_ctor_get(x_61, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_61);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
block_53:
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
lean_ctor_set(x_13, 0, x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_11, 0, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_12);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_dec(x_11);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_27 = x_13;
} else {
 lean_dec_ref(x_13);
 x_27 = lean_box(0);
}
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_12);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; 
x_32 = lean_ctor_get(x_11, 1);
lean_inc(x_32);
lean_dec(x_11);
x_33 = lean_ctor_get(x_13, 1);
lean_inc(x_33);
lean_dec(x_13);
x_34 = lean_ctor_get(x_14, 0);
lean_inc(x_34);
lean_dec(x_14);
x_35 = 1;
x_36 = lean_usize_add(x_3, x_35);
x_3 = x_36;
x_4 = x_34;
x_8 = x_33;
x_9 = x_32;
x_10 = x_12;
goto _start;
}
}
else
{
uint8_t x_38; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_11);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_11, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_13);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_11);
lean_ctor_set(x_41, 1, x_12);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_13, 0);
x_43 = lean_ctor_get(x_13, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_13);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_11, 0, x_44);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_11);
lean_ctor_set(x_45, 1, x_12);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_dec(x_11);
x_47 = lean_ctor_get(x_13, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_13, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_49 = x_13;
} else {
 lean_dec_ref(x_13);
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
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_12);
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_55; 
x_55 = lean_usize_dec_lt(x_4, x_3);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_5);
lean_ctor_set(x_56, 1, x_9);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_10);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_11);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_array_uget(x_2, x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_60 = l_Lake_Package_fetchTargetJob(x_1, x_59, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = !lean_is_exclusive(x_61);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_61, 0);
lean_dec(x_65);
x_66 = !lean_is_exclusive(x_62);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_62, 0);
x_68 = l_Lake_BuildJob_mix___rarg(x_5, x_67);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_62, 0, x_69);
x_12 = x_61;
x_13 = x_63;
goto block_54;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_62, 0);
x_71 = lean_ctor_get(x_62, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_62);
x_72 = l_Lake_BuildJob_mix___rarg(x_5, x_70);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
lean_ctor_set(x_61, 0, x_74);
x_12 = x_61;
x_13 = x_63;
goto block_54;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_ctor_get(x_61, 1);
lean_inc(x_75);
lean_dec(x_61);
x_76 = lean_ctor_get(x_62, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_62, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_78 = x_62;
} else {
 lean_dec_ref(x_62);
 x_78 = lean_box(0);
}
x_79 = l_Lake_BuildJob_mix___rarg(x_5, x_76);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
if (lean_is_scalar(x_78)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_78;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_77);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_75);
x_12 = x_82;
x_13 = x_63;
goto block_54;
}
}
else
{
lean_object* x_83; uint8_t x_84; 
lean_dec(x_5);
x_83 = lean_ctor_get(x_60, 1);
lean_inc(x_83);
lean_dec(x_60);
x_84 = !lean_is_exclusive(x_61);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_61, 0);
lean_dec(x_85);
x_86 = !lean_is_exclusive(x_62);
if (x_86 == 0)
{
x_12 = x_61;
x_13 = x_83;
goto block_54;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_62, 0);
x_88 = lean_ctor_get(x_62, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_62);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_61, 0, x_89);
x_12 = x_61;
x_13 = x_83;
goto block_54;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_90 = lean_ctor_get(x_61, 1);
lean_inc(x_90);
lean_dec(x_61);
x_91 = lean_ctor_get(x_62, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_62, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_93 = x_62;
} else {
 lean_dec_ref(x_62);
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
x_12 = x_95;
x_13 = x_83;
goto block_54;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_60);
if (x_96 == 0)
{
return x_60;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_60, 0);
x_98 = lean_ctor_get(x_60, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_60);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
block_54:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
lean_ctor_set(x_14, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_13);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_12, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_13);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_dec(x_12);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_28 = x_14;
} else {
 lean_dec_ref(x_14);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get(x_15, 0);
lean_inc(x_29);
lean_dec(x_15);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_13);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; 
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_dec(x_12);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_dec(x_14);
x_35 = lean_ctor_get(x_15, 0);
lean_inc(x_35);
lean_dec(x_15);
x_36 = 1;
x_37 = lean_usize_add(x_4, x_36);
x_4 = x_37;
x_5 = x_35;
x_9 = x_34;
x_10 = x_33;
x_11 = x_13;
goto _start;
}
}
else
{
uint8_t x_39; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_12);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_12, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_14);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_12);
lean_ctor_set(x_42, 1, x_13);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_14, 0);
x_44 = lean_ctor_get(x_14, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_14);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_12, 0, x_45);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_12);
lean_ctor_set(x_46, 1, x_13);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_12, 1);
lean_inc(x_47);
lean_dec(x_12);
x_48 = lean_ctor_get(x_14, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_14, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_50 = x_14;
} else {
 lean_dec_ref(x_14);
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
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_13);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_recBuildExtraDepTargets___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_28; 
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_get_set_stdout(x_1, x_5);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_apply_3(x_2, x_3, x_4, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_get_set_stdout(x_31, x_36);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_34, 0, x_45);
x_6 = x_34;
x_7 = x_43;
goto block_27;
}
else
{
uint8_t x_46; 
lean_free_object(x_35);
lean_dec(x_41);
lean_free_object(x_34);
lean_dec(x_38);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_35, 0);
x_51 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
lean_inc(x_50);
lean_dec(x_35);
x_52 = lean_get_set_stdout(x_31, x_36);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_51);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_38);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_34, 1, x_54);
lean_ctor_set(x_34, 0, x_56);
x_6 = x_34;
x_7 = x_53;
goto block_27;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_50);
lean_free_object(x_34);
lean_dec(x_38);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
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
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
lean_dec(x_34);
x_62 = lean_ctor_get(x_35, 0);
lean_inc(x_62);
x_63 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_64 = x_35;
} else {
 lean_dec_ref(x_35);
 x_64 = lean_box(0);
}
x_65 = lean_get_set_stdout(x_31, x_36);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(0, 1, 1);
} else {
 x_67 = x_64;
}
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_63);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
x_6 = x_70;
x_7 = x_66;
goto block_27;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_73 = x_65;
} else {
 lean_dec_ref(x_65);
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
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_34, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_33, 1);
lean_inc(x_76);
lean_dec(x_33);
x_77 = !lean_is_exclusive(x_34);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_34, 0);
x_79 = lean_ctor_get(x_34, 1);
lean_dec(x_79);
x_80 = !lean_is_exclusive(x_75);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_75, 0);
x_82 = lean_get_set_stdout(x_31, x_76);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_6 = x_34;
x_7 = x_83;
goto block_27;
}
else
{
uint8_t x_84; 
lean_free_object(x_75);
lean_dec(x_81);
lean_free_object(x_34);
lean_dec(x_78);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
return x_82;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_82, 0);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_82);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_75, 0);
x_89 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
lean_inc(x_88);
lean_dec(x_75);
x_90 = lean_get_set_stdout(x_31, x_76);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_89);
lean_ctor_set(x_34, 1, x_92);
x_6 = x_34;
x_7 = x_91;
goto block_27;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_88);
lean_free_object(x_34);
lean_dec(x_78);
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_95 = x_90;
} else {
 lean_dec_ref(x_90);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_34, 0);
lean_inc(x_97);
lean_dec(x_34);
x_98 = lean_ctor_get(x_75, 0);
lean_inc(x_98);
x_99 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_100 = x_75;
} else {
 lean_dec_ref(x_75);
 x_100 = lean_box(0);
}
x_101 = lean_get_set_stdout(x_31, x_76);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(0, 1, 1);
} else {
 x_103 = x_100;
}
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_99);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_103);
x_6 = x_104;
x_7 = x_102;
goto block_27;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
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
}
}
else
{
uint8_t x_109; 
lean_dec(x_31);
x_109 = !lean_is_exclusive(x_33);
if (x_109 == 0)
{
return x_33;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_33, 0);
x_111 = lean_ctor_get(x_33, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_33);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_free_object(x_4);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_30);
if (x_113 == 0)
{
return x_30;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_30, 0);
x_115 = lean_ctor_get(x_30, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_30);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_4, 0);
x_118 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_inc(x_117);
lean_dec(x_4);
x_119 = lean_get_set_stdout(x_1, x_5);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_122, 0, x_117);
lean_ctor_set_uint8(x_122, sizeof(void*)*1, x_118);
x_123 = lean_apply_3(x_2, x_3, x_122, x_121);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; 
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_ctor_get(x_124, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_128 = x_124;
} else {
 lean_dec_ref(x_124);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_125, 0);
lean_inc(x_129);
x_130 = lean_ctor_get_uint8(x_125, sizeof(void*)*1);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_131 = x_125;
} else {
 lean_dec_ref(x_125);
 x_131 = lean_box(0);
}
x_132 = lean_get_set_stdout(x_120, x_126);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
if (lean_is_scalar(x_131)) {
 x_134 = lean_alloc_ctor(0, 1, 1);
} else {
 x_134 = x_131;
}
lean_ctor_set(x_134, 0, x_129);
lean_ctor_set_uint8(x_134, sizeof(void*)*1, x_130);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_127);
lean_ctor_set(x_136, 1, x_135);
if (lean_is_scalar(x_128)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_128;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
x_6 = x_137;
x_7 = x_133;
goto block_27;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
x_138 = lean_ctor_get(x_132, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_132, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_140 = x_132;
} else {
 lean_dec_ref(x_132);
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
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; 
x_142 = lean_ctor_get(x_124, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_123, 1);
lean_inc(x_143);
lean_dec(x_123);
x_144 = lean_ctor_get(x_124, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_145 = x_124;
} else {
 lean_dec_ref(x_124);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_142, 0);
lean_inc(x_146);
x_147 = lean_ctor_get_uint8(x_142, sizeof(void*)*1);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 x_148 = x_142;
} else {
 lean_dec_ref(x_142);
 x_148 = lean_box(0);
}
x_149 = lean_get_set_stdout(x_120, x_143);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
if (lean_is_scalar(x_148)) {
 x_151 = lean_alloc_ctor(0, 1, 1);
} else {
 x_151 = x_148;
}
lean_ctor_set(x_151, 0, x_146);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_147);
if (lean_is_scalar(x_145)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_145;
}
lean_ctor_set(x_152, 0, x_144);
lean_ctor_set(x_152, 1, x_151);
x_6 = x_152;
x_7 = x_150;
goto block_27;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
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
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_120);
x_157 = lean_ctor_get(x_123, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_123, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_159 = x_123;
} else {
 lean_dec_ref(x_123);
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
lean_dec(x_117);
lean_dec(x_3);
lean_dec(x_2);
x_161 = lean_ctor_get(x_119, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_119, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_163 = x_119;
} else {
 lean_dec_ref(x_119);
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
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_recBuildExtraDepTargets___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_28; 
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_get_set_stdin(x_1, x_5);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_apply_3(x_2, x_3, x_4, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_get_set_stdin(x_31, x_36);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_34, 0, x_45);
x_6 = x_34;
x_7 = x_43;
goto block_27;
}
else
{
uint8_t x_46; 
lean_free_object(x_35);
lean_dec(x_41);
lean_free_object(x_34);
lean_dec(x_38);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_35, 0);
x_51 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
lean_inc(x_50);
lean_dec(x_35);
x_52 = lean_get_set_stdin(x_31, x_36);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_51);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_38);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_34, 1, x_54);
lean_ctor_set(x_34, 0, x_56);
x_6 = x_34;
x_7 = x_53;
goto block_27;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_50);
lean_free_object(x_34);
lean_dec(x_38);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
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
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
lean_dec(x_34);
x_62 = lean_ctor_get(x_35, 0);
lean_inc(x_62);
x_63 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_64 = x_35;
} else {
 lean_dec_ref(x_35);
 x_64 = lean_box(0);
}
x_65 = lean_get_set_stdin(x_31, x_36);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(0, 1, 1);
} else {
 x_67 = x_64;
}
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_63);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
x_6 = x_70;
x_7 = x_66;
goto block_27;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_73 = x_65;
} else {
 lean_dec_ref(x_65);
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
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_34, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_33, 1);
lean_inc(x_76);
lean_dec(x_33);
x_77 = !lean_is_exclusive(x_34);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_34, 0);
x_79 = lean_ctor_get(x_34, 1);
lean_dec(x_79);
x_80 = !lean_is_exclusive(x_75);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_75, 0);
x_82 = lean_get_set_stdin(x_31, x_76);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_6 = x_34;
x_7 = x_83;
goto block_27;
}
else
{
uint8_t x_84; 
lean_free_object(x_75);
lean_dec(x_81);
lean_free_object(x_34);
lean_dec(x_78);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
return x_82;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_82, 0);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_82);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_75, 0);
x_89 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
lean_inc(x_88);
lean_dec(x_75);
x_90 = lean_get_set_stdin(x_31, x_76);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_89);
lean_ctor_set(x_34, 1, x_92);
x_6 = x_34;
x_7 = x_91;
goto block_27;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_88);
lean_free_object(x_34);
lean_dec(x_78);
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_95 = x_90;
} else {
 lean_dec_ref(x_90);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_34, 0);
lean_inc(x_97);
lean_dec(x_34);
x_98 = lean_ctor_get(x_75, 0);
lean_inc(x_98);
x_99 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_100 = x_75;
} else {
 lean_dec_ref(x_75);
 x_100 = lean_box(0);
}
x_101 = lean_get_set_stdin(x_31, x_76);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(0, 1, 1);
} else {
 x_103 = x_100;
}
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_99);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_103);
x_6 = x_104;
x_7 = x_102;
goto block_27;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
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
}
}
else
{
uint8_t x_109; 
lean_dec(x_31);
x_109 = !lean_is_exclusive(x_33);
if (x_109 == 0)
{
return x_33;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_33, 0);
x_111 = lean_ctor_get(x_33, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_33);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_free_object(x_4);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_30);
if (x_113 == 0)
{
return x_30;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_30, 0);
x_115 = lean_ctor_get(x_30, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_30);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_4, 0);
x_118 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_inc(x_117);
lean_dec(x_4);
x_119 = lean_get_set_stdin(x_1, x_5);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_122, 0, x_117);
lean_ctor_set_uint8(x_122, sizeof(void*)*1, x_118);
x_123 = lean_apply_3(x_2, x_3, x_122, x_121);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; 
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_ctor_get(x_124, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_128 = x_124;
} else {
 lean_dec_ref(x_124);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_125, 0);
lean_inc(x_129);
x_130 = lean_ctor_get_uint8(x_125, sizeof(void*)*1);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_131 = x_125;
} else {
 lean_dec_ref(x_125);
 x_131 = lean_box(0);
}
x_132 = lean_get_set_stdin(x_120, x_126);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
if (lean_is_scalar(x_131)) {
 x_134 = lean_alloc_ctor(0, 1, 1);
} else {
 x_134 = x_131;
}
lean_ctor_set(x_134, 0, x_129);
lean_ctor_set_uint8(x_134, sizeof(void*)*1, x_130);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_127);
lean_ctor_set(x_136, 1, x_135);
if (lean_is_scalar(x_128)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_128;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
x_6 = x_137;
x_7 = x_133;
goto block_27;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
x_138 = lean_ctor_get(x_132, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_132, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_140 = x_132;
} else {
 lean_dec_ref(x_132);
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
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; 
x_142 = lean_ctor_get(x_124, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_123, 1);
lean_inc(x_143);
lean_dec(x_123);
x_144 = lean_ctor_get(x_124, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_145 = x_124;
} else {
 lean_dec_ref(x_124);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_142, 0);
lean_inc(x_146);
x_147 = lean_ctor_get_uint8(x_142, sizeof(void*)*1);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 x_148 = x_142;
} else {
 lean_dec_ref(x_142);
 x_148 = lean_box(0);
}
x_149 = lean_get_set_stdin(x_120, x_143);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
if (lean_is_scalar(x_148)) {
 x_151 = lean_alloc_ctor(0, 1, 1);
} else {
 x_151 = x_148;
}
lean_ctor_set(x_151, 0, x_146);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_147);
if (lean_is_scalar(x_145)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_145;
}
lean_ctor_set(x_152, 0, x_144);
lean_ctor_set(x_152, 1, x_151);
x_6 = x_152;
x_7 = x_150;
goto block_27;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
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
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_120);
x_157 = lean_ctor_get(x_123, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_123, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_159 = x_123;
} else {
 lean_dec_ref(x_123);
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
lean_dec(x_117);
lean_dec(x_3);
lean_dec(x_2);
x_161 = lean_ctor_get(x_119, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_119, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_163 = x_119;
} else {
 lean_dec_ref(x_119);
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
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Package_recBuildExtraDepTargets___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_28; 
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_get_set_stderr(x_1, x_5);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_apply_3(x_2, x_3, x_4, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_get_set_stderr(x_31, x_36);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_34, 0, x_45);
x_6 = x_34;
x_7 = x_43;
goto block_27;
}
else
{
uint8_t x_46; 
lean_free_object(x_35);
lean_dec(x_41);
lean_free_object(x_34);
lean_dec(x_38);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_35, 0);
x_51 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
lean_inc(x_50);
lean_dec(x_35);
x_52 = lean_get_set_stderr(x_31, x_36);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_51);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_38);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_34, 1, x_54);
lean_ctor_set(x_34, 0, x_56);
x_6 = x_34;
x_7 = x_53;
goto block_27;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_50);
lean_free_object(x_34);
lean_dec(x_38);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
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
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
lean_dec(x_34);
x_62 = lean_ctor_get(x_35, 0);
lean_inc(x_62);
x_63 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_64 = x_35;
} else {
 lean_dec_ref(x_35);
 x_64 = lean_box(0);
}
x_65 = lean_get_set_stderr(x_31, x_36);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(0, 1, 1);
} else {
 x_67 = x_64;
}
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_63);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
x_6 = x_70;
x_7 = x_66;
goto block_27;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_73 = x_65;
} else {
 lean_dec_ref(x_65);
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
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_34, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_33, 1);
lean_inc(x_76);
lean_dec(x_33);
x_77 = !lean_is_exclusive(x_34);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_34, 0);
x_79 = lean_ctor_get(x_34, 1);
lean_dec(x_79);
x_80 = !lean_is_exclusive(x_75);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_75, 0);
x_82 = lean_get_set_stderr(x_31, x_76);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_6 = x_34;
x_7 = x_83;
goto block_27;
}
else
{
uint8_t x_84; 
lean_free_object(x_75);
lean_dec(x_81);
lean_free_object(x_34);
lean_dec(x_78);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
return x_82;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_82, 0);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_82);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_75, 0);
x_89 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
lean_inc(x_88);
lean_dec(x_75);
x_90 = lean_get_set_stderr(x_31, x_76);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_89);
lean_ctor_set(x_34, 1, x_92);
x_6 = x_34;
x_7 = x_91;
goto block_27;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_88);
lean_free_object(x_34);
lean_dec(x_78);
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_95 = x_90;
} else {
 lean_dec_ref(x_90);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_34, 0);
lean_inc(x_97);
lean_dec(x_34);
x_98 = lean_ctor_get(x_75, 0);
lean_inc(x_98);
x_99 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_100 = x_75;
} else {
 lean_dec_ref(x_75);
 x_100 = lean_box(0);
}
x_101 = lean_get_set_stderr(x_31, x_76);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(0, 1, 1);
} else {
 x_103 = x_100;
}
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_99);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_103);
x_6 = x_104;
x_7 = x_102;
goto block_27;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
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
}
}
else
{
uint8_t x_109; 
lean_dec(x_31);
x_109 = !lean_is_exclusive(x_33);
if (x_109 == 0)
{
return x_33;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_33, 0);
x_111 = lean_ctor_get(x_33, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_33);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_free_object(x_4);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_30);
if (x_113 == 0)
{
return x_30;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_30, 0);
x_115 = lean_ctor_get(x_30, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_30);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_4, 0);
x_118 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_inc(x_117);
lean_dec(x_4);
x_119 = lean_get_set_stderr(x_1, x_5);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_122, 0, x_117);
lean_ctor_set_uint8(x_122, sizeof(void*)*1, x_118);
x_123 = lean_apply_3(x_2, x_3, x_122, x_121);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; 
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_ctor_get(x_124, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_128 = x_124;
} else {
 lean_dec_ref(x_124);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_125, 0);
lean_inc(x_129);
x_130 = lean_ctor_get_uint8(x_125, sizeof(void*)*1);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_131 = x_125;
} else {
 lean_dec_ref(x_125);
 x_131 = lean_box(0);
}
x_132 = lean_get_set_stderr(x_120, x_126);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
if (lean_is_scalar(x_131)) {
 x_134 = lean_alloc_ctor(0, 1, 1);
} else {
 x_134 = x_131;
}
lean_ctor_set(x_134, 0, x_129);
lean_ctor_set_uint8(x_134, sizeof(void*)*1, x_130);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_127);
lean_ctor_set(x_136, 1, x_135);
if (lean_is_scalar(x_128)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_128;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
x_6 = x_137;
x_7 = x_133;
goto block_27;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
x_138 = lean_ctor_get(x_132, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_132, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_140 = x_132;
} else {
 lean_dec_ref(x_132);
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
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; 
x_142 = lean_ctor_get(x_124, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_123, 1);
lean_inc(x_143);
lean_dec(x_123);
x_144 = lean_ctor_get(x_124, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_145 = x_124;
} else {
 lean_dec_ref(x_124);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_142, 0);
lean_inc(x_146);
x_147 = lean_ctor_get_uint8(x_142, sizeof(void*)*1);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 x_148 = x_142;
} else {
 lean_dec_ref(x_142);
 x_148 = lean_box(0);
}
x_149 = lean_get_set_stderr(x_120, x_143);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
if (lean_is_scalar(x_148)) {
 x_151 = lean_alloc_ctor(0, 1, 1);
} else {
 x_151 = x_148;
}
lean_ctor_set(x_151, 0, x_146);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_147);
if (lean_is_scalar(x_145)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_145;
}
lean_ctor_set(x_152, 0, x_144);
lean_ctor_set(x_152, 1, x_151);
x_6 = x_152;
x_7 = x_150;
goto block_27;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
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
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_120);
x_157 = lean_ctor_get(x_123, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_123, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_159 = x_123;
} else {
 lean_dec_ref(x_123);
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
lean_dec(x_117);
lean_dec(x_3);
lean_dec(x_2);
x_161 = lean_ctor_get(x_119, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_119, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_163 = x_119;
} else {
 lean_dec_ref(x_119);
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
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__1() {
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
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Data.String.Extra", 22);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("String.fromUTF8!", 16);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid UTF-8 string", 20);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__2;
x_2 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__3;
x_3 = lean_unsigned_to_nat(92u);
x_4 = lean_unsigned_to_nat(47u);
x_5 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__1;
x_9 = lean_st_mk_ref(x_8, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_mk_ref(x_8, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_IO_FS_Stream_ofBuffer(x_10);
lean_inc(x_13);
x_16 = l_IO_FS_Stream_ofBuffer(x_13);
if (x_2 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_recBuildExtraDepTargets___spec__4), 5, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_1);
x_18 = l_IO_withStdin___at_Lake_Package_recBuildExtraDepTargets___spec__5(x_15, x_17, x_3, x_4, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_st_ref_get(x_13, x_21);
lean_dec(x_13);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_string_validate_utf8(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_30);
x_32 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_33 = l_panic___at_String_fromUTF8_x21___spec__1(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_23);
lean_ctor_set(x_19, 0, x_34);
lean_ctor_set(x_27, 0, x_19);
return x_27;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_string_from_utf8(x_30);
lean_dec(x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_23);
lean_ctor_set(x_19, 0, x_36);
lean_ctor_set(x_27, 0, x_19);
return x_27;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_27, 0);
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_27);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_string_validate_utf8(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_39);
x_41 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_42 = l_panic___at_String_fromUTF8_x21___spec__1(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_23);
lean_ctor_set(x_19, 0, x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_19);
lean_ctor_set(x_44, 1, x_38);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_string_from_utf8(x_39);
lean_dec(x_39);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_23);
lean_ctor_set(x_19, 0, x_46);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_19);
lean_ctor_set(x_47, 1, x_38);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_19);
lean_dec(x_23);
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
lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_20, 0);
x_53 = lean_ctor_get_uint8(x_20, sizeof(void*)*1);
lean_inc(x_52);
lean_dec(x_20);
x_54 = lean_st_ref_get(x_13, x_21);
lean_dec(x_13);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
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
x_58 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_53);
x_59 = lean_ctor_get(x_55, 0);
lean_inc(x_59);
lean_dec(x_55);
x_60 = lean_string_validate_utf8(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_59);
x_61 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_62 = l_panic___at_String_fromUTF8_x21___spec__1(x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_23);
lean_ctor_set(x_19, 1, x_58);
lean_ctor_set(x_19, 0, x_63);
if (lean_is_scalar(x_57)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_57;
}
lean_ctor_set(x_64, 0, x_19);
lean_ctor_set(x_64, 1, x_56);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_string_from_utf8(x_59);
lean_dec(x_59);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_23);
lean_ctor_set(x_19, 1, x_58);
lean_ctor_set(x_19, 0, x_66);
if (lean_is_scalar(x_57)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_57;
}
lean_ctor_set(x_67, 0, x_19);
lean_ctor_set(x_67, 1, x_56);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_52);
lean_free_object(x_19);
lean_dec(x_23);
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
lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_19, 0);
lean_inc(x_72);
lean_dec(x_19);
x_73 = lean_ctor_get(x_20, 0);
lean_inc(x_73);
x_74 = lean_ctor_get_uint8(x_20, sizeof(void*)*1);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_75 = x_20;
} else {
 lean_dec_ref(x_20);
 x_75 = lean_box(0);
}
x_76 = lean_st_ref_get(x_13, x_21);
lean_dec(x_13);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_80 = lean_alloc_ctor(0, 1, 1);
} else {
 x_80 = x_75;
}
lean_ctor_set(x_80, 0, x_73);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_74);
x_81 = lean_ctor_get(x_77, 0);
lean_inc(x_81);
lean_dec(x_77);
x_82 = lean_string_validate_utf8(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_81);
x_83 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_84 = l_panic___at_String_fromUTF8_x21___spec__1(x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_72);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_80);
if (lean_is_scalar(x_79)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_79;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_78);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_string_from_utf8(x_81);
lean_dec(x_81);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_72);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_80);
if (lean_is_scalar(x_79)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_79;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_78);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_72);
x_92 = lean_ctor_get(x_76, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_76, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_94 = x_76;
} else {
 lean_dec_ref(x_76);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_13);
x_96 = !lean_is_exclusive(x_18);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_18, 0);
lean_dec(x_97);
x_98 = !lean_is_exclusive(x_19);
if (x_98 == 0)
{
return x_18;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_19, 0);
x_100 = lean_ctor_get(x_19, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_19);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_18, 0, x_101);
return x_18;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_18, 1);
lean_inc(x_102);
lean_dec(x_18);
x_103 = lean_ctor_get(x_19, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_19, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_105 = x_19;
} else {
 lean_dec_ref(x_19);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_102);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_13);
x_108 = !lean_is_exclusive(x_18);
if (x_108 == 0)
{
return x_18;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_18, 0);
x_110 = lean_ctor_get(x_18, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_18);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_inc(x_16);
x_112 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_Package_recBuildExtraDepTargets___spec__6), 5, 2);
lean_closure_set(x_112, 0, x_16);
lean_closure_set(x_112, 1, x_1);
x_113 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_recBuildExtraDepTargets___spec__4), 5, 2);
lean_closure_set(x_113, 0, x_16);
lean_closure_set(x_113, 1, x_112);
x_114 = l_IO_withStdin___at_Lake_Package_recBuildExtraDepTargets___spec__5(x_15, x_113, x_3, x_4, x_14);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_dec(x_114);
x_118 = !lean_is_exclusive(x_115);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_119 = lean_ctor_get(x_115, 0);
x_120 = lean_ctor_get(x_115, 1);
lean_dec(x_120);
x_121 = !lean_is_exclusive(x_116);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_116, 0);
x_123 = lean_st_ref_get(x_13, x_117);
lean_dec(x_13);
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_125 = lean_ctor_get(x_123, 0);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_string_validate_utf8(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_126);
x_128 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_129 = l_panic___at_String_fromUTF8_x21___spec__1(x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_119);
lean_ctor_set(x_115, 0, x_130);
lean_ctor_set(x_123, 0, x_115);
return x_123;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_string_from_utf8(x_126);
lean_dec(x_126);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_119);
lean_ctor_set(x_115, 0, x_132);
lean_ctor_set(x_123, 0, x_115);
return x_123;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_133 = lean_ctor_get(x_123, 0);
x_134 = lean_ctor_get(x_123, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_123);
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_string_validate_utf8(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_135);
x_137 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_138 = l_panic___at_String_fromUTF8_x21___spec__1(x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_119);
lean_ctor_set(x_115, 0, x_139);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_115);
lean_ctor_set(x_140, 1, x_134);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_string_from_utf8(x_135);
lean_dec(x_135);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_119);
lean_ctor_set(x_115, 0, x_142);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_115);
lean_ctor_set(x_143, 1, x_134);
return x_143;
}
}
}
else
{
uint8_t x_144; 
lean_free_object(x_116);
lean_dec(x_122);
lean_free_object(x_115);
lean_dec(x_119);
x_144 = !lean_is_exclusive(x_123);
if (x_144 == 0)
{
return x_123;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_123, 0);
x_146 = lean_ctor_get(x_123, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_123);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
lean_object* x_148; uint8_t x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_116, 0);
x_149 = lean_ctor_get_uint8(x_116, sizeof(void*)*1);
lean_inc(x_148);
lean_dec(x_116);
x_150 = lean_st_ref_get(x_13, x_117);
lean_dec(x_13);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_153 = x_150;
} else {
 lean_dec_ref(x_150);
 x_153 = lean_box(0);
}
x_154 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_154, 0, x_148);
lean_ctor_set_uint8(x_154, sizeof(void*)*1, x_149);
x_155 = lean_ctor_get(x_151, 0);
lean_inc(x_155);
lean_dec(x_151);
x_156 = lean_string_validate_utf8(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_155);
x_157 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_158 = l_panic___at_String_fromUTF8_x21___spec__1(x_157);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_119);
lean_ctor_set(x_115, 1, x_154);
lean_ctor_set(x_115, 0, x_159);
if (lean_is_scalar(x_153)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_153;
}
lean_ctor_set(x_160, 0, x_115);
lean_ctor_set(x_160, 1, x_152);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_string_from_utf8(x_155);
lean_dec(x_155);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_119);
lean_ctor_set(x_115, 1, x_154);
lean_ctor_set(x_115, 0, x_162);
if (lean_is_scalar(x_153)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_153;
}
lean_ctor_set(x_163, 0, x_115);
lean_ctor_set(x_163, 1, x_152);
return x_163;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_148);
lean_free_object(x_115);
lean_dec(x_119);
x_164 = lean_ctor_get(x_150, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_150, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_166 = x_150;
} else {
 lean_dec_ref(x_150);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
}
}
else
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; 
x_168 = lean_ctor_get(x_115, 0);
lean_inc(x_168);
lean_dec(x_115);
x_169 = lean_ctor_get(x_116, 0);
lean_inc(x_169);
x_170 = lean_ctor_get_uint8(x_116, sizeof(void*)*1);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 x_171 = x_116;
} else {
 lean_dec_ref(x_116);
 x_171 = lean_box(0);
}
x_172 = lean_st_ref_get(x_13, x_117);
lean_dec(x_13);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_175 = x_172;
} else {
 lean_dec_ref(x_172);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_176 = lean_alloc_ctor(0, 1, 1);
} else {
 x_176 = x_171;
}
lean_ctor_set(x_176, 0, x_169);
lean_ctor_set_uint8(x_176, sizeof(void*)*1, x_170);
x_177 = lean_ctor_get(x_173, 0);
lean_inc(x_177);
lean_dec(x_173);
x_178 = lean_string_validate_utf8(x_177);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_177);
x_179 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_180 = l_panic___at_String_fromUTF8_x21___spec__1(x_179);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_168);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_176);
if (lean_is_scalar(x_175)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_175;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_174);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_string_from_utf8(x_177);
lean_dec(x_177);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_168);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_176);
if (lean_is_scalar(x_175)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_175;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_174);
return x_187;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_171);
lean_dec(x_169);
lean_dec(x_168);
x_188 = lean_ctor_get(x_172, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_172, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_190 = x_172;
} else {
 lean_dec_ref(x_172);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
}
else
{
uint8_t x_192; 
lean_dec(x_13);
x_192 = !lean_is_exclusive(x_114);
if (x_192 == 0)
{
lean_object* x_193; uint8_t x_194; 
x_193 = lean_ctor_get(x_114, 0);
lean_dec(x_193);
x_194 = !lean_is_exclusive(x_115);
if (x_194 == 0)
{
return x_114;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_115, 0);
x_196 = lean_ctor_get(x_115, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_115);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
lean_ctor_set(x_114, 0, x_197);
return x_114;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_198 = lean_ctor_get(x_114, 1);
lean_inc(x_198);
lean_dec(x_114);
x_199 = lean_ctor_get(x_115, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_115, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_201 = x_115;
} else {
 lean_dec_ref(x_115);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_198);
return x_203;
}
}
}
else
{
uint8_t x_204; 
lean_dec(x_13);
x_204 = !lean_is_exclusive(x_114);
if (x_204 == 0)
{
return x_114;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_114, 0);
x_206 = lean_ctor_get(x_114, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_114);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
}
}
else
{
uint8_t x_208; 
lean_dec(x_10);
lean_free_object(x_4);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_208 = !lean_is_exclusive(x_12);
if (x_208 == 0)
{
return x_12;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_12, 0);
x_210 = lean_ctor_get(x_12, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_12);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
}
else
{
uint8_t x_212; 
lean_free_object(x_4);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_212 = !lean_is_exclusive(x_9);
if (x_212 == 0)
{
return x_9;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_9, 0);
x_214 = lean_ctor_get(x_9, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_9);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
else
{
lean_object* x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; 
x_216 = lean_ctor_get(x_4, 0);
x_217 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_inc(x_216);
lean_dec(x_4);
x_218 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__1;
x_219 = lean_st_mk_ref(x_218, x_5);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_222 = lean_st_mk_ref(x_218, x_221);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
x_225 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_225, 0, x_216);
lean_ctor_set_uint8(x_225, sizeof(void*)*1, x_217);
x_226 = l_IO_FS_Stream_ofBuffer(x_220);
lean_inc(x_223);
x_227 = l_IO_FS_Stream_ofBuffer(x_223);
if (x_2 == 0)
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_recBuildExtraDepTargets___spec__4), 5, 2);
lean_closure_set(x_228, 0, x_227);
lean_closure_set(x_228, 1, x_1);
x_229 = l_IO_withStdin___at_Lake_Package_recBuildExtraDepTargets___spec__5(x_226, x_228, x_3, x_225, x_224);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; lean_object* x_238; 
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
x_232 = lean_ctor_get(x_229, 1);
lean_inc(x_232);
lean_dec(x_229);
x_233 = lean_ctor_get(x_230, 0);
lean_inc(x_233);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_234 = x_230;
} else {
 lean_dec_ref(x_230);
 x_234 = lean_box(0);
}
x_235 = lean_ctor_get(x_231, 0);
lean_inc(x_235);
x_236 = lean_ctor_get_uint8(x_231, sizeof(void*)*1);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 x_237 = x_231;
} else {
 lean_dec_ref(x_231);
 x_237 = lean_box(0);
}
x_238 = lean_st_ref_get(x_223, x_232);
lean_dec(x_223);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_241 = x_238;
} else {
 lean_dec_ref(x_238);
 x_241 = lean_box(0);
}
if (lean_is_scalar(x_237)) {
 x_242 = lean_alloc_ctor(0, 1, 1);
} else {
 x_242 = x_237;
}
lean_ctor_set(x_242, 0, x_235);
lean_ctor_set_uint8(x_242, sizeof(void*)*1, x_236);
x_243 = lean_ctor_get(x_239, 0);
lean_inc(x_243);
lean_dec(x_239);
x_244 = lean_string_validate_utf8(x_243);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_243);
x_245 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_246 = l_panic___at_String_fromUTF8_x21___spec__1(x_245);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_233);
if (lean_is_scalar(x_234)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_234;
}
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_242);
if (lean_is_scalar(x_241)) {
 x_249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_249 = x_241;
}
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_240);
return x_249;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_250 = lean_string_from_utf8(x_243);
lean_dec(x_243);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_233);
if (lean_is_scalar(x_234)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_234;
}
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_242);
if (lean_is_scalar(x_241)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_241;
}
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_240);
return x_253;
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_237);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_233);
x_254 = lean_ctor_get(x_238, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_238, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_256 = x_238;
} else {
 lean_dec_ref(x_238);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_255);
return x_257;
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_223);
x_258 = lean_ctor_get(x_229, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_259 = x_229;
} else {
 lean_dec_ref(x_229);
 x_259 = lean_box(0);
}
x_260 = lean_ctor_get(x_230, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_230, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_262 = x_230;
} else {
 lean_dec_ref(x_230);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(1, 2, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_260);
lean_ctor_set(x_263, 1, x_261);
if (lean_is_scalar(x_259)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_259;
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_258);
return x_264;
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_223);
x_265 = lean_ctor_get(x_229, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_229, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_267 = x_229;
} else {
 lean_dec_ref(x_229);
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
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_inc(x_227);
x_269 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_Package_recBuildExtraDepTargets___spec__6), 5, 2);
lean_closure_set(x_269, 0, x_227);
lean_closure_set(x_269, 1, x_1);
x_270 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_recBuildExtraDepTargets___spec__4), 5, 2);
lean_closure_set(x_270, 0, x_227);
lean_closure_set(x_270, 1, x_269);
x_271 = l_IO_withStdin___at_Lake_Package_recBuildExtraDepTargets___spec__5(x_226, x_270, x_3, x_225, x_224);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; lean_object* x_279; lean_object* x_280; 
x_273 = lean_ctor_get(x_272, 1);
lean_inc(x_273);
x_274 = lean_ctor_get(x_271, 1);
lean_inc(x_274);
lean_dec(x_271);
x_275 = lean_ctor_get(x_272, 0);
lean_inc(x_275);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_276 = x_272;
} else {
 lean_dec_ref(x_272);
 x_276 = lean_box(0);
}
x_277 = lean_ctor_get(x_273, 0);
lean_inc(x_277);
x_278 = lean_ctor_get_uint8(x_273, sizeof(void*)*1);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 x_279 = x_273;
} else {
 lean_dec_ref(x_273);
 x_279 = lean_box(0);
}
x_280 = lean_st_ref_get(x_223, x_274);
lean_dec(x_223);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_283 = x_280;
} else {
 lean_dec_ref(x_280);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_284 = lean_alloc_ctor(0, 1, 1);
} else {
 x_284 = x_279;
}
lean_ctor_set(x_284, 0, x_277);
lean_ctor_set_uint8(x_284, sizeof(void*)*1, x_278);
x_285 = lean_ctor_get(x_281, 0);
lean_inc(x_285);
lean_dec(x_281);
x_286 = lean_string_validate_utf8(x_285);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_285);
x_287 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_288 = l_panic___at_String_fromUTF8_x21___spec__1(x_287);
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_275);
if (lean_is_scalar(x_276)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_276;
}
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_284);
if (lean_is_scalar(x_283)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_283;
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_282);
return x_291;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_292 = lean_string_from_utf8(x_285);
lean_dec(x_285);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_275);
if (lean_is_scalar(x_276)) {
 x_294 = lean_alloc_ctor(0, 2, 0);
} else {
 x_294 = x_276;
}
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_284);
if (lean_is_scalar(x_283)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_283;
}
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_282);
return x_295;
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_279);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
x_296 = lean_ctor_get(x_280, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_280, 1);
lean_inc(x_297);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_298 = x_280;
} else {
 lean_dec_ref(x_280);
 x_298 = lean_box(0);
}
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(1, 2, 0);
} else {
 x_299 = x_298;
}
lean_ctor_set(x_299, 0, x_296);
lean_ctor_set(x_299, 1, x_297);
return x_299;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_223);
x_300 = lean_ctor_get(x_271, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_301 = x_271;
} else {
 lean_dec_ref(x_271);
 x_301 = lean_box(0);
}
x_302 = lean_ctor_get(x_272, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_272, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_304 = x_272;
} else {
 lean_dec_ref(x_272);
 x_304 = lean_box(0);
}
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(1, 2, 0);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_302);
lean_ctor_set(x_305, 1, x_303);
if (lean_is_scalar(x_301)) {
 x_306 = lean_alloc_ctor(0, 2, 0);
} else {
 x_306 = x_301;
}
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_300);
return x_306;
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_223);
x_307 = lean_ctor_get(x_271, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_271, 1);
lean_inc(x_308);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_309 = x_271;
} else {
 lean_dec_ref(x_271);
 x_309 = lean_box(0);
}
if (lean_is_scalar(x_309)) {
 x_310 = lean_alloc_ctor(1, 2, 0);
} else {
 x_310 = x_309;
}
lean_ctor_set(x_310, 0, x_307);
lean_ctor_set(x_310, 1, x_308);
return x_310;
}
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_220);
lean_dec(x_216);
lean_dec(x_3);
lean_dec(x_1);
x_311 = lean_ctor_get(x_222, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_222, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_313 = x_222;
} else {
 lean_dec_ref(x_222);
 x_313 = lean_box(0);
}
if (lean_is_scalar(x_313)) {
 x_314 = lean_alloc_ctor(1, 2, 0);
} else {
 x_314 = x_313;
}
lean_ctor_set(x_314, 0, x_311);
lean_ctor_set(x_314, 1, x_312);
return x_314;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
lean_dec(x_216);
lean_dec(x_3);
lean_dec(x_1);
x_315 = lean_ctor_get(x_219, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_219, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_317 = x_219;
} else {
 lean_dec_ref(x_219);
 x_317 = lean_box(0);
}
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(1, 2, 0);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_315);
lean_ctor_set(x_318, 1, x_316);
return x_318;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_Package_recBuildExtraDepTargets___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_Package_recBuildExtraDepTargets___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Package_recBuildExtraDepTargets___spec__7___rarg), 8, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__1(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 4);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_array_get_size(x_12);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__2(x_1, x_12, x_14, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
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
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_array_push(x_6, x_1);
lean_ctor_set(x_3, 0, x_7);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_array_push(x_11, x_1);
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_12);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("stdout/stderr:\n", 15);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to fetch cloud release; falling back to local build", 58);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 2;
x_2 = l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__3;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lake_buildStaticLib___spec__1___rarg___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_52 = lean_ctor_get(x_4, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_4, 1);
lean_inc(x_53);
lean_dec(x_4);
x_54 = lean_alloc_closure((void*)(l_Lake_Package_recBuildExtraDepTargets___lambda__3___boxed), 5, 1);
lean_closure_set(x_54, 0, x_53);
x_55 = lean_unbox(x_52);
lean_dec(x_52);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__4;
x_57 = lean_alloc_closure((void*)(l_Lake_Package_recBuildExtraDepTargets___lambda__4___boxed), 4, 1);
lean_closure_set(x_57, 0, x_56);
x_58 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_58, 0, x_57);
lean_closure_set(x_58, 1, x_54);
x_6 = x_58;
goto block_51;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__5;
x_60 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_60, 0, x_59);
lean_closure_set(x_60, 1, x_54);
x_6 = x_60;
goto block_51;
}
block_51:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
lean_inc(x_1);
x_8 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3(x_6, x_7, x_1, x_5, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_String_isEmpty(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; 
x_16 = l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__1;
x_17 = lean_string_append(x_16, x_13);
lean_dec(x_13);
x_18 = l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = 1;
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_array_push(x_23, x_21);
lean_ctor_set(x_12, 0, x_24);
x_25 = lean_box(0);
x_26 = l_Lake_Package_recBuildExtraDepTargets___lambda__2(x_14, x_25, x_1, x_12, x_11);
lean_dec(x_1);
return x_26;
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_array_push(x_27, x_21);
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_28);
x_31 = lean_box(0);
x_32 = l_Lake_Package_recBuildExtraDepTargets___lambda__2(x_14, x_31, x_1, x_30, x_11);
lean_dec(x_1);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_13);
x_33 = lean_box(0);
x_34 = l_Lake_Package_recBuildExtraDepTargets___lambda__2(x_14, x_33, x_1, x_12, x_11);
lean_dec(x_1);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_8);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_8, 0);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_9);
if (x_37 == 0)
{
return x_8;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_9, 0);
x_39 = lean_ctor_get(x_9, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_9);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_8, 0, x_40);
return x_8;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
lean_dec(x_8);
x_42 = lean_ctor_get(x_9, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_9, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_44 = x_9;
} else {
 lean_dec_ref(x_9);
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
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_8);
if (x_47 == 0)
{
return x_8;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_8, 0);
x_49 = lean_ctor_get(x_8, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_8);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_2);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_2);
lean_ctor_set(x_62, 1, x_3);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_2, 0);
x_64 = lean_ctor_get(x_2, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_2);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_3);
return x_66;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_alloc_closure((void*)(l_Lake_Package_recBuildExtraDepTargets___lambda__5), 3, 1);
lean_closure_set(x_11, 0, x_4);
x_12 = l_Task_Priority_default;
x_13 = 0;
x_14 = lean_io_map_task(x_11, x_9, x_12, x_13, x_7);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_1, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
lean_ctor_set(x_1, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_5);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_6);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_free_object(x_1);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_1);
x_30 = lean_alloc_closure((void*)(l_Lake_Package_recBuildExtraDepTargets___lambda__5), 3, 1);
lean_closure_set(x_30, 0, x_4);
x_31 = l_Task_Priority_default;
x_32 = 0;
x_33 = lean_io_map_task(x_30, x_28, x_31, x_32, x_7);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
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
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_29);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_5);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_6);
if (lean_is_scalar(x_36)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_36;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_35);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
x_41 = lean_ctor_get(x_33, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_43 = x_33;
} else {
 lean_dec_ref(x_33);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_BuildTrace_nil;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lake_Package_recComputeDeps___closed__1;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_recBuildExtraDepTargets___closed__1;
x_2 = l_Lake_Package_recBuildExtraDepTargets___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_recBuildExtraDepTargets___closed__3;
x_2 = lean_task_pure(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_recBuildExtraDepTargets___closed__4;
x_2 = l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":optRelease", 11);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("optRelease", 10);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_recBuildExtraDepTargets___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_recBuildExtraDepTargets___lambda__6___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_1, 6);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at_Lake_Package_deps___spec__1(x_10, x_11, x_8);
x_13 = lean_array_get_size(x_12);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = l_Lake_Package_recBuildExtraDepTargets___closed__5;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_16 = l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1(x_12, x_14, x_11, x_15, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get(x_26, 2);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_27, 2);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_name_eq(x_25, x_28);
lean_dec(x_28);
x_30 = l_instDecidableNot___rarg(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_25);
lean_dec(x_24);
x_31 = lean_box(0);
x_32 = l_Lake_Package_recBuildExtraDepTargets___lambda__1(x_1, x_11, x_21, x_31, x_2, x_3, x_4, x_22, x_20, x_19);
return x_32;
}
else
{
uint8_t x_33; 
x_33 = lean_ctor_get_uint8(x_24, sizeof(void*)*21 + 1);
lean_dec(x_24);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_25);
x_34 = lean_box(0);
x_35 = l_Lake_Package_recBuildExtraDepTargets___lambda__1(x_1, x_11, x_21, x_34, x_2, x_3, x_4, x_22, x_20, x_19);
return x_35;
}
else
{
uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_36 = 1;
x_37 = l_Lean_Name_toString(x_25, x_36);
x_38 = l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__2;
x_39 = lean_string_append(x_38, x_37);
lean_dec(x_37);
x_40 = l_Lake_Package_recBuildExtraDepTargets___closed__6;
x_41 = lean_string_append(x_39, x_40);
x_42 = l_Lake_Package_recBuildExtraDepTargets___closed__8;
lean_inc(x_1);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_44, 0, x_43);
lean_closure_set(x_44, 1, lean_box(0));
x_45 = l_Lake_Package_recBuildExtraDepTargets___closed__9;
x_46 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Package_recBuildExtraDepTargets___spec__7___rarg), 8, 2);
lean_closure_set(x_46, 0, x_44);
lean_closure_set(x_46, 1, x_45);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_47 = l_Lake_withRegisterJob___rarg(x_41, x_46, x_2, x_3, x_4, x_22, x_20, x_19);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec(x_49);
x_54 = l_Lake_BuildJob_add___rarg(x_21, x_52);
x_55 = lean_box(0);
x_56 = l_Lake_Package_recBuildExtraDepTargets___lambda__1(x_1, x_11, x_54, x_55, x_2, x_3, x_4, x_53, x_51, x_50);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_21);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_47);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_47, 0);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_48);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_48, 0);
lean_dec(x_60);
x_61 = !lean_is_exclusive(x_49);
if (x_61 == 0)
{
return x_47;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_49, 0);
x_63 = lean_ctor_get(x_49, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_49);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_48, 0, x_64);
return x_47;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_48, 1);
lean_inc(x_65);
lean_dec(x_48);
x_66 = lean_ctor_get(x_49, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_49, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_68 = x_49;
} else {
 lean_dec_ref(x_49);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_65);
lean_ctor_set(x_47, 0, x_70);
return x_47;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_71 = lean_ctor_get(x_47, 1);
lean_inc(x_71);
lean_dec(x_47);
x_72 = lean_ctor_get(x_48, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_73 = x_48;
} else {
 lean_dec_ref(x_48);
 x_73 = lean_box(0);
}
x_74 = lean_ctor_get(x_49, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_49, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_76 = x_49;
} else {
 lean_dec_ref(x_49);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
if (lean_is_scalar(x_73)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_73;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_72);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_71);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_21);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_47);
if (x_80 == 0)
{
return x_47;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_47, 0);
x_82 = lean_ctor_get(x_47, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_47);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_16);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_16, 0);
lean_dec(x_85);
x_86 = !lean_is_exclusive(x_17);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_17, 0);
lean_dec(x_87);
x_88 = !lean_is_exclusive(x_18);
if (x_88 == 0)
{
return x_16;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_18, 0);
x_90 = lean_ctor_get(x_18, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_18);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_17, 0, x_91);
return x_16;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_92 = lean_ctor_get(x_17, 1);
lean_inc(x_92);
lean_dec(x_17);
x_93 = lean_ctor_get(x_18, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_18, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_95 = x_18;
} else {
 lean_dec_ref(x_18);
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
lean_ctor_set(x_16, 0, x_97);
return x_16;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_98 = lean_ctor_get(x_16, 1);
lean_inc(x_98);
lean_dec(x_16);
x_99 = lean_ctor_get(x_17, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_100 = x_17;
} else {
 lean_dec_ref(x_17);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_18, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_18, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_103 = x_18;
} else {
 lean_dec_ref(x_18);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
if (lean_is_scalar(x_100)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_100;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_99);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_98);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_16);
if (x_107 == 0)
{
return x_16;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_16, 0);
x_109 = lean_ctor_get(x_16, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_16);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__2(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; lean_object* x_12; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Lake_Package_recBuildExtraDepTargets___lambda__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Package_recBuildExtraDepTargets___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Package_recBuildExtraDepTargets___lambda__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Package_recBuildExtraDepTargets___lambda__4(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Package_recBuildExtraDepTargets___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_dec(x_3);
x_4 = lean_box(0);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
static lean_object* _init_l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lake_EResult_map___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___closed__2;
x_5 = l_Task_Priority_default;
x_6 = 0;
x_7 = lean_task_map(x_4, x_3, x_5, x_6);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___closed__2;
x_11 = l_Task_Priority_default;
x_12 = 0;
x_13 = lean_task_map(x_10, x_8, x_11, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_extraDepFacetConfig___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
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
x_2 = l_Lake_Package_extraDepFacetConfig___closed__2;
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
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = l_Lake_download(x_1, x_2, x_8, x_6);
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
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_5, 0);
x_38 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
lean_inc(x_37);
lean_dec(x_5);
x_39 = l_Lake_download(x_1, x_2, x_37, x_6);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_45 = x_40;
} else {
 lean_dec_ref(x_40);
 x_45 = lean_box(0);
}
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_38);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_46);
if (lean_is_scalar(x_42)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_42;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_41);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
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
x_51 = lean_ctor_get(x_40, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_40, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_53 = x_40;
} else {
 lean_dec_ref(x_40);
 x_53 = lean_box(0);
}
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_38);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_54);
if (lean_is_scalar(x_50)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_50;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_49);
return x_56;
}
}
}
}
static uint8_t _init_l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1___lambda__2___closed__1() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = l_Lake_noBuildCode;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_109; uint8_t x_110; 
x_109 = lean_ctor_get(x_7, 0);
lean_inc(x_109);
x_110 = lean_ctor_get_uint8(x_109, sizeof(void*)*1 + 2);
lean_dec(x_109);
if (x_110 == 0)
{
uint8_t x_111; 
x_111 = !lean_is_exclusive(x_8);
if (x_111 == 0)
{
uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_112 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_113 = l_Lake_instOrdJobAction;
x_114 = lean_box(x_112);
x_115 = lean_box(x_5);
x_116 = l_instDecidableRelLe___rarg(x_113, x_114, x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_box(0);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_8);
x_10 = x_118;
x_11 = x_9;
goto block_108;
}
else
{
lean_object* x_119; lean_object* x_120; 
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_5);
x_119 = lean_box(0);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_8);
x_10 = x_120;
x_11 = x_9;
goto block_108;
}
}
else
{
lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_121 = lean_ctor_get(x_8, 0);
x_122 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
lean_inc(x_121);
lean_dec(x_8);
x_123 = l_Lake_instOrdJobAction;
x_124 = lean_box(x_122);
x_125 = lean_box(x_5);
x_126 = l_instDecidableRelLe___rarg(x_123, x_124, x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_127, 0, x_121);
lean_ctor_set_uint8(x_127, sizeof(void*)*1, x_122);
x_128 = lean_box(0);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
x_10 = x_129;
x_11 = x_9;
goto block_108;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_130, 0, x_121);
lean_ctor_set_uint8(x_130, sizeof(void*)*1, x_5);
x_131 = lean_box(0);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_130);
x_10 = x_132;
x_11 = x_9;
goto block_108;
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_133 = !lean_is_exclusive(x_8);
if (x_133 == 0)
{
lean_object* x_134; uint8_t x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_8, 0);
x_135 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1___lambda__2___closed__1;
x_136 = lean_io_exit(x_135, x_9);
if (lean_obj_tag(x_136) == 0)
{
uint8_t x_137; 
x_137 = !lean_is_exclusive(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_136, 0);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_8);
lean_ctor_set(x_136, 0, x_139);
return x_136;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_136, 0);
x_141 = lean_ctor_get(x_136, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_136);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_8);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
else
{
uint8_t x_144; 
x_144 = !lean_is_exclusive(x_136);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_145 = lean_ctor_get(x_136, 0);
x_146 = lean_io_error_to_string(x_145);
x_147 = 3;
x_148 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set_uint8(x_148, sizeof(void*)*1, x_147);
x_149 = lean_array_get_size(x_134);
x_150 = lean_array_push(x_134, x_148);
lean_ctor_set(x_8, 0, x_150);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_8);
lean_ctor_set_tag(x_136, 0);
lean_ctor_set(x_136, 0, x_151);
return x_136;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_152 = lean_ctor_get(x_136, 0);
x_153 = lean_ctor_get(x_136, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_136);
x_154 = lean_io_error_to_string(x_152);
x_155 = 3;
x_156 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set_uint8(x_156, sizeof(void*)*1, x_155);
x_157 = lean_array_get_size(x_134);
x_158 = lean_array_push(x_134, x_156);
lean_ctor_set(x_8, 0, x_158);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_8);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_153);
return x_160;
}
}
}
else
{
lean_object* x_161; uint8_t x_162; uint8_t x_163; lean_object* x_164; 
x_161 = lean_ctor_get(x_8, 0);
x_162 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
lean_inc(x_161);
lean_dec(x_8);
x_163 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1___lambda__2___closed__1;
x_164 = lean_io_exit(x_163, x_9);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_167 = x_164;
} else {
 lean_dec_ref(x_164);
 x_167 = lean_box(0);
}
x_168 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_168, 0, x_161);
lean_ctor_set_uint8(x_168, sizeof(void*)*1, x_162);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_165);
lean_ctor_set(x_169, 1, x_168);
if (lean_is_scalar(x_167)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_167;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_166);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_171 = lean_ctor_get(x_164, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_164, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_173 = x_164;
} else {
 lean_dec_ref(x_164);
 x_173 = lean_box(0);
}
x_174 = lean_io_error_to_string(x_171);
x_175 = 3;
x_176 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set_uint8(x_176, sizeof(void*)*1, x_175);
x_177 = lean_array_get_size(x_161);
x_178 = lean_array_push(x_161, x_176);
x_179 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set_uint8(x_179, sizeof(void*)*1, x_162);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_179);
if (lean_is_scalar(x_173)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_173;
 lean_ctor_set_tag(x_181, 0);
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_172);
return x_181;
}
}
}
block_108:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_array_get_size(x_13);
lean_dec(x_13);
x_15 = l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg(x_1, x_2, x_7, x_12, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 1);
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_array_get_size(x_22);
x_24 = l_Array_extract___rarg(x_22, x_14, x_23);
x_25 = l_Lake_writeTraceFile(x_3, x_4, x_24, x_20);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = 0;
x_29 = lean_box(x_28);
lean_ctor_set(x_16, 0, x_29);
lean_ctor_set(x_25, 0, x_16);
return x_25;
}
else
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = 0;
x_32 = lean_box(x_31);
lean_ctor_set(x_16, 0, x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_16);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_io_error_to_string(x_35);
x_37 = 3;
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_37);
x_39 = lean_array_push(x_22, x_38);
lean_ctor_set(x_18, 0, x_39);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_23);
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_16);
return x_25;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_25, 0);
x_41 = lean_ctor_get(x_25, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_25);
x_42 = lean_io_error_to_string(x_40);
x_43 = 3;
x_44 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_43);
x_45 = lean_array_push(x_22, x_44);
lean_ctor_set(x_18, 0, x_45);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_23);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_16);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
}
}
else
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_18, 0);
x_48 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
lean_inc(x_47);
lean_dec(x_18);
x_49 = lean_array_get_size(x_47);
x_50 = l_Array_extract___rarg(x_47, x_14, x_49);
x_51 = l_Lake_writeTraceFile(x_3, x_4, x_50, x_20);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_49);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_48);
x_55 = 0;
x_56 = lean_box(x_55);
lean_ctor_set(x_16, 1, x_54);
lean_ctor_set(x_16, 0, x_56);
if (lean_is_scalar(x_53)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_53;
}
lean_ctor_set(x_57, 0, x_16);
lean_ctor_set(x_57, 1, x_52);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_58 = lean_ctor_get(x_51, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_51, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_60 = x_51;
} else {
 lean_dec_ref(x_51);
 x_60 = lean_box(0);
}
x_61 = lean_io_error_to_string(x_58);
x_62 = 3;
x_63 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_62);
x_64 = lean_array_push(x_47, x_63);
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_48);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 1, x_65);
lean_ctor_set(x_16, 0, x_49);
if (lean_is_scalar(x_60)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_60;
 lean_ctor_set_tag(x_66, 0);
}
lean_ctor_set(x_66, 0, x_16);
lean_ctor_set(x_66, 1, x_59);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_67 = lean_ctor_get(x_16, 1);
lean_inc(x_67);
lean_dec(x_16);
x_68 = lean_ctor_get(x_15, 1);
lean_inc(x_68);
lean_dec(x_15);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
x_70 = lean_ctor_get_uint8(x_67, sizeof(void*)*1);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 x_71 = x_67;
} else {
 lean_dec_ref(x_67);
 x_71 = lean_box(0);
}
x_72 = lean_array_get_size(x_69);
x_73 = l_Array_extract___rarg(x_69, x_14, x_72);
x_74 = l_Lake_writeTraceFile(x_3, x_4, x_73, x_68);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_72);
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
if (lean_is_scalar(x_71)) {
 x_77 = lean_alloc_ctor(0, 1, 1);
} else {
 x_77 = x_71;
}
lean_ctor_set(x_77, 0, x_69);
lean_ctor_set_uint8(x_77, sizeof(void*)*1, x_70);
x_78 = 0;
x_79 = lean_box(x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_77);
if (lean_is_scalar(x_76)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_76;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_75);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_82 = lean_ctor_get(x_74, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_74, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_84 = x_74;
} else {
 lean_dec_ref(x_74);
 x_84 = lean_box(0);
}
x_85 = lean_io_error_to_string(x_82);
x_86 = 3;
x_87 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set_uint8(x_87, sizeof(void*)*1, x_86);
x_88 = lean_array_push(x_69, x_87);
if (lean_is_scalar(x_71)) {
 x_89 = lean_alloc_ctor(0, 1, 1);
} else {
 x_89 = x_71;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_70);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_72);
lean_ctor_set(x_90, 1, x_89);
if (lean_is_scalar(x_84)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_84;
 lean_ctor_set_tag(x_91, 0);
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_83);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
x_92 = !lean_is_exclusive(x_15);
if (x_92 == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_15, 0);
lean_dec(x_93);
x_94 = !lean_is_exclusive(x_16);
if (x_94 == 0)
{
return x_15;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_16, 0);
x_96 = lean_ctor_get(x_16, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_16);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_15, 0, x_97);
return x_15;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_98 = lean_ctor_get(x_15, 1);
lean_inc(x_98);
lean_dec(x_15);
x_99 = lean_ctor_get(x_16, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_16, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_101 = x_16;
} else {
 lean_dec_ref(x_16);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_98);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
x_104 = !lean_is_exclusive(x_15);
if (x_104 == 0)
{
return x_15;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_15, 0);
x_106 = lean_ctor_get(x_15, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_15);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_330; 
x_12 = lean_alloc_closure((void*)(l_Lake_Package_recBuildExtraDepTargets___lambda__4___boxed), 4, 1);
lean_closure_set(x_12, 0, x_3);
x_13 = lean_alloc_closure((void*)(l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1___lambda__1___boxed), 6, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
x_330 = !lean_is_exclusive(x_10);
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; 
x_331 = lean_ctor_get(x_10, 0);
x_332 = l_Lake_readTraceFile_x3f(x_6, x_331, x_11);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec(x_332);
x_335 = !lean_is_exclusive(x_333);
if (x_335 == 0)
{
lean_object* x_336; 
x_336 = lean_ctor_get(x_333, 1);
lean_ctor_set(x_10, 0, x_336);
lean_ctor_set(x_333, 1, x_10);
x_14 = x_333;
x_15 = x_334;
goto block_329;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_337 = lean_ctor_get(x_333, 0);
x_338 = lean_ctor_get(x_333, 1);
lean_inc(x_338);
lean_inc(x_337);
lean_dec(x_333);
lean_ctor_set(x_10, 0, x_338);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set(x_339, 1, x_10);
x_14 = x_339;
x_15 = x_334;
goto block_329;
}
}
else
{
lean_object* x_340; uint8_t x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_340 = lean_ctor_get(x_10, 0);
x_341 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
lean_inc(x_340);
lean_dec(x_10);
x_342 = l_Lake_readTraceFile_x3f(x_6, x_340, x_11);
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec(x_342);
x_345 = lean_ctor_get(x_343, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_343, 1);
lean_inc(x_346);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 x_347 = x_343;
} else {
 lean_dec_ref(x_343);
 x_347 = lean_box(0);
}
x_348 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set_uint8(x_348, sizeof(void*)*1, x_341);
if (lean_is_scalar(x_347)) {
 x_349 = lean_alloc_ctor(0, 2, 0);
} else {
 x_349 = x_347;
}
lean_ctor_set(x_349, 0, x_345);
lean_ctor_set(x_349, 1, x_348);
x_14 = x_349;
x_15 = x_344;
goto block_329;
}
block_329:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_8);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_14, 1);
x_21 = lean_ctor_get(x_14, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
x_24 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__3(x_4, x_23, x_15);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = lean_unbox(x_26);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_free_object(x_24);
lean_free_object(x_14);
x_29 = lean_box(0);
x_30 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1___lambda__2(x_12, x_13, x_6, x_5, x_7, x_29, x_9, x_20, x_27);
return x_30;
}
else
{
uint8_t x_31; lean_object* x_32; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_31 = 1;
x_32 = lean_box(x_31);
lean_ctor_set(x_14, 0, x_32);
lean_ctor_set(x_24, 0, x_14);
return x_24;
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_24);
x_35 = lean_unbox(x_33);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_free_object(x_14);
x_36 = lean_box(0);
x_37 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1___lambda__2(x_12, x_13, x_6, x_5, x_7, x_36, x_9, x_20, x_34);
return x_37;
}
else
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_38 = 1;
x_39 = lean_box(x_38);
lean_ctor_set(x_14, 0, x_39);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_14);
lean_ctor_set(x_40, 1, x_34);
return x_40;
}
}
}
else
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_41 = lean_ctor_get(x_20, 0);
x_42 = lean_ctor_get_uint8(x_20, sizeof(void*)*1);
lean_inc(x_41);
lean_dec(x_20);
x_43 = lean_ctor_get(x_5, 1);
lean_inc(x_43);
x_44 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__3(x_4, x_43, x_15);
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
x_48 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_42);
x_49 = lean_unbox(x_45);
lean_dec(x_45);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_47);
lean_free_object(x_14);
x_50 = lean_box(0);
x_51 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1___lambda__2(x_12, x_13, x_6, x_5, x_7, x_50, x_9, x_48, x_46);
return x_51;
}
else
{
uint8_t x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_52 = 1;
x_53 = lean_box(x_52);
lean_ctor_set(x_14, 1, x_48);
lean_ctor_set(x_14, 0, x_53);
if (lean_is_scalar(x_47)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_47;
}
lean_ctor_set(x_54, 0, x_14);
lean_ctor_set(x_54, 1, x_46);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_55 = lean_ctor_get(x_14, 1);
lean_inc(x_55);
lean_dec(x_14);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get_uint8(x_55, sizeof(void*)*1);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_58 = x_55;
} else {
 lean_dec_ref(x_55);
 x_58 = lean_box(0);
}
x_59 = lean_ctor_get(x_5, 1);
lean_inc(x_59);
x_60 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__3(x_4, x_59, x_15);
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
if (lean_is_scalar(x_58)) {
 x_64 = lean_alloc_ctor(0, 1, 1);
} else {
 x_64 = x_58;
}
lean_ctor_set(x_64, 0, x_56);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_57);
x_65 = lean_unbox(x_61);
lean_dec(x_61);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_63);
x_66 = lean_box(0);
x_67 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1___lambda__2(x_12, x_13, x_6, x_5, x_7, x_66, x_9, x_64, x_62);
return x_67;
}
else
{
uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_68 = 1;
x_69 = lean_box(x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_64);
if (lean_is_scalar(x_63)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_63;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_62);
return x_71;
}
}
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_14);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = lean_ctor_get(x_14, 1);
x_74 = lean_ctor_get(x_14, 0);
lean_dec(x_74);
x_75 = !lean_is_exclusive(x_73);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__3(x_4, x_8, x_15);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_76, 0);
x_79 = lean_ctor_get(x_76, 1);
x_80 = lean_unbox(x_78);
lean_dec(x_78);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_free_object(x_76);
lean_free_object(x_14);
x_81 = lean_box(0);
x_82 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1___lambda__2(x_12, x_13, x_6, x_5, x_7, x_81, x_9, x_73, x_79);
return x_82;
}
else
{
uint8_t x_83; lean_object* x_84; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_83 = 1;
x_84 = lean_box(x_83);
lean_ctor_set(x_14, 0, x_84);
lean_ctor_set(x_76, 0, x_14);
return x_76;
}
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_76, 0);
x_86 = lean_ctor_get(x_76, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_76);
x_87 = lean_unbox(x_85);
lean_dec(x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_free_object(x_14);
x_88 = lean_box(0);
x_89 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1___lambda__2(x_12, x_13, x_6, x_5, x_7, x_88, x_9, x_73, x_86);
return x_89;
}
else
{
uint8_t x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_90 = 1;
x_91 = lean_box(x_90);
lean_ctor_set(x_14, 0, x_91);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_14);
lean_ctor_set(x_92, 1, x_86);
return x_92;
}
}
}
else
{
lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_93 = lean_ctor_get(x_73, 0);
x_94 = lean_ctor_get_uint8(x_73, sizeof(void*)*1);
lean_inc(x_93);
lean_dec(x_73);
x_95 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__3(x_4, x_8, x_15);
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
x_99 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_99, 0, x_93);
lean_ctor_set_uint8(x_99, sizeof(void*)*1, x_94);
x_100 = lean_unbox(x_96);
lean_dec(x_96);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_98);
lean_free_object(x_14);
x_101 = lean_box(0);
x_102 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1___lambda__2(x_12, x_13, x_6, x_5, x_7, x_101, x_9, x_99, x_97);
return x_102;
}
else
{
uint8_t x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_103 = 1;
x_104 = lean_box(x_103);
lean_ctor_set(x_14, 1, x_99);
lean_ctor_set(x_14, 0, x_104);
if (lean_is_scalar(x_98)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_98;
}
lean_ctor_set(x_105, 0, x_14);
lean_ctor_set(x_105, 1, x_97);
return x_105;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_106 = lean_ctor_get(x_14, 1);
lean_inc(x_106);
lean_dec(x_14);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_106, sizeof(void*)*1);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 x_109 = x_106;
} else {
 lean_dec_ref(x_106);
 x_109 = lean_box(0);
}
x_110 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__3(x_4, x_8, x_15);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
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
if (lean_is_scalar(x_109)) {
 x_114 = lean_alloc_ctor(0, 1, 1);
} else {
 x_114 = x_109;
}
lean_ctor_set(x_114, 0, x_107);
lean_ctor_set_uint8(x_114, sizeof(void*)*1, x_108);
x_115 = lean_unbox(x_111);
lean_dec(x_111);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_113);
x_116 = lean_box(0);
x_117 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1___lambda__2(x_12, x_13, x_6, x_5, x_7, x_116, x_9, x_114, x_112);
return x_117;
}
else
{
uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_118 = 1;
x_119 = lean_box(x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_114);
if (lean_is_scalar(x_113)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_113;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_112);
return x_121;
}
}
}
}
else
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_16);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_123 = lean_ctor_get(x_16, 0);
x_124 = lean_ctor_get(x_14, 1);
lean_inc(x_124);
lean_dec(x_14);
x_125 = lean_ctor_get(x_123, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
lean_ctor_set(x_16, 0, x_125);
lean_inc(x_5);
x_127 = l_Lake_checkHashUpToDate___at_Lake_buildFileUnlessUpToDate___spec__4(x_4, x_5, x_16, x_8, x_9, x_124, x_15);
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
x_131 = !lean_is_exclusive(x_128);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_198; 
x_132 = lean_ctor_get(x_128, 0);
x_133 = lean_ctor_get(x_128, 1);
x_198 = lean_unbox(x_132);
lean_dec(x_132);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; 
lean_free_object(x_128);
lean_dec(x_130);
lean_dec(x_126);
x_199 = lean_box(0);
x_200 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1___lambda__2(x_12, x_13, x_6, x_5, x_7, x_199, x_9, x_133, x_129);
return x_200;
}
else
{
uint8_t x_201; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
x_201 = !lean_is_exclusive(x_133);
if (x_201 == 0)
{
uint8_t x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_202 = lean_ctor_get_uint8(x_133, sizeof(void*)*1);
x_203 = l_Lake_instOrdJobAction;
x_204 = 1;
x_205 = lean_box(x_202);
x_206 = lean_box(x_204);
x_207 = l_instDecidableRelLe___rarg(x_203, x_205, x_206);
if (x_207 == 0)
{
lean_object* x_208; 
x_208 = lean_box(0);
lean_ctor_set(x_128, 0, x_208);
x_134 = x_128;
x_135 = x_129;
goto block_197;
}
else
{
lean_object* x_209; 
lean_ctor_set_uint8(x_133, sizeof(void*)*1, x_204);
x_209 = lean_box(0);
lean_ctor_set(x_128, 0, x_209);
x_134 = x_128;
x_135 = x_129;
goto block_197;
}
}
else
{
lean_object* x_210; uint8_t x_211; lean_object* x_212; uint8_t x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_210 = lean_ctor_get(x_133, 0);
x_211 = lean_ctor_get_uint8(x_133, sizeof(void*)*1);
lean_inc(x_210);
lean_dec(x_133);
x_212 = l_Lake_instOrdJobAction;
x_213 = 1;
x_214 = lean_box(x_211);
x_215 = lean_box(x_213);
x_216 = l_instDecidableRelLe___rarg(x_212, x_214, x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_217, 0, x_210);
lean_ctor_set_uint8(x_217, sizeof(void*)*1, x_211);
x_218 = lean_box(0);
lean_ctor_set(x_128, 1, x_217);
lean_ctor_set(x_128, 0, x_218);
x_134 = x_128;
x_135 = x_129;
goto block_197;
}
else
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_219, 0, x_210);
lean_ctor_set_uint8(x_219, sizeof(void*)*1, x_213);
x_220 = lean_box(0);
lean_ctor_set(x_128, 1, x_219);
lean_ctor_set(x_128, 0, x_220);
x_134 = x_128;
x_135 = x_129;
goto block_197;
}
}
}
block_197:
{
uint8_t x_136; 
x_136 = !lean_is_exclusive(x_134);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_137 = lean_ctor_get(x_134, 1);
x_138 = lean_ctor_get(x_134, 0);
lean_dec(x_138);
x_139 = lean_array_get_size(x_126);
x_140 = lean_unsigned_to_nat(0u);
x_141 = lean_nat_dec_lt(x_140, x_139);
if (x_141 == 0)
{
uint8_t x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_139);
lean_dec(x_126);
lean_dec(x_9);
x_142 = 1;
x_143 = lean_box(x_142);
lean_ctor_set(x_134, 0, x_143);
if (lean_is_scalar(x_130)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_130;
}
lean_ctor_set(x_144, 0, x_134);
lean_ctor_set(x_144, 1, x_135);
return x_144;
}
else
{
uint8_t x_145; 
x_145 = lean_nat_dec_le(x_139, x_139);
if (x_145 == 0)
{
uint8_t x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_139);
lean_dec(x_126);
lean_dec(x_9);
x_146 = 1;
x_147 = lean_box(x_146);
lean_ctor_set(x_134, 0, x_147);
if (lean_is_scalar(x_130)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_130;
}
lean_ctor_set(x_148, 0, x_134);
lean_ctor_set(x_148, 1, x_135);
return x_148;
}
else
{
size_t x_149; size_t x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
lean_free_object(x_134);
lean_dec(x_130);
x_149 = 0;
x_150 = lean_usize_of_nat(x_139);
lean_dec(x_139);
x_151 = lean_box(0);
x_152 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate___spec__6(x_126, x_149, x_150, x_151, x_9, x_137, x_135);
lean_dec(x_9);
lean_dec(x_126);
x_153 = !lean_is_exclusive(x_152);
if (x_153 == 0)
{
lean_object* x_154; uint8_t x_155; 
x_154 = lean_ctor_get(x_152, 0);
x_155 = !lean_is_exclusive(x_154);
if (x_155 == 0)
{
lean_object* x_156; uint8_t x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_154, 0);
lean_dec(x_156);
x_157 = 1;
x_158 = lean_box(x_157);
lean_ctor_set(x_154, 0, x_158);
return x_152;
}
else
{
lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; 
x_159 = lean_ctor_get(x_154, 1);
lean_inc(x_159);
lean_dec(x_154);
x_160 = 1;
x_161 = lean_box(x_160);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_159);
lean_ctor_set(x_152, 0, x_162);
return x_152;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_163 = lean_ctor_get(x_152, 0);
x_164 = lean_ctor_get(x_152, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_152);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_166 = x_163;
} else {
 lean_dec_ref(x_163);
 x_166 = lean_box(0);
}
x_167 = 1;
x_168 = lean_box(x_167);
if (lean_is_scalar(x_166)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_166;
}
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_165);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_164);
return x_170;
}
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_171 = lean_ctor_get(x_134, 1);
lean_inc(x_171);
lean_dec(x_134);
x_172 = lean_array_get_size(x_126);
x_173 = lean_unsigned_to_nat(0u);
x_174 = lean_nat_dec_lt(x_173, x_172);
if (x_174 == 0)
{
uint8_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_172);
lean_dec(x_126);
lean_dec(x_9);
x_175 = 1;
x_176 = lean_box(x_175);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_171);
if (lean_is_scalar(x_130)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_130;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_135);
return x_178;
}
else
{
uint8_t x_179; 
x_179 = lean_nat_dec_le(x_172, x_172);
if (x_179 == 0)
{
uint8_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_172);
lean_dec(x_126);
lean_dec(x_9);
x_180 = 1;
x_181 = lean_box(x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_171);
if (lean_is_scalar(x_130)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_130;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_135);
return x_183;
}
else
{
size_t x_184; size_t x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_130);
x_184 = 0;
x_185 = lean_usize_of_nat(x_172);
lean_dec(x_172);
x_186 = lean_box(0);
x_187 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate___spec__6(x_126, x_184, x_185, x_186, x_9, x_171, x_135);
lean_dec(x_9);
lean_dec(x_126);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_190 = x_187;
} else {
 lean_dec_ref(x_187);
 x_190 = lean_box(0);
}
x_191 = lean_ctor_get(x_188, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_192 = x_188;
} else {
 lean_dec_ref(x_188);
 x_192 = lean_box(0);
}
x_193 = 1;
x_194 = lean_box(x_193);
if (lean_is_scalar(x_192)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_192;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_191);
if (lean_is_scalar(x_190)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_190;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_189);
return x_196;
}
}
}
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_253; 
x_221 = lean_ctor_get(x_128, 0);
x_222 = lean_ctor_get(x_128, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_128);
x_253 = lean_unbox(x_221);
lean_dec(x_221);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; 
lean_dec(x_130);
lean_dec(x_126);
x_254 = lean_box(0);
x_255 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1___lambda__2(x_12, x_13, x_6, x_5, x_7, x_254, x_9, x_222, x_129);
return x_255;
}
else
{
lean_object* x_256; uint8_t x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
x_256 = lean_ctor_get(x_222, 0);
lean_inc(x_256);
x_257 = lean_ctor_get_uint8(x_222, sizeof(void*)*1);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 x_258 = x_222;
} else {
 lean_dec_ref(x_222);
 x_258 = lean_box(0);
}
x_259 = l_Lake_instOrdJobAction;
x_260 = 1;
x_261 = lean_box(x_257);
x_262 = lean_box(x_260);
x_263 = l_instDecidableRelLe___rarg(x_259, x_261, x_262);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
if (lean_is_scalar(x_258)) {
 x_264 = lean_alloc_ctor(0, 1, 1);
} else {
 x_264 = x_258;
}
lean_ctor_set(x_264, 0, x_256);
lean_ctor_set_uint8(x_264, sizeof(void*)*1, x_257);
x_265 = lean_box(0);
x_266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_264);
x_223 = x_266;
x_224 = x_129;
goto block_252;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
if (lean_is_scalar(x_258)) {
 x_267 = lean_alloc_ctor(0, 1, 1);
} else {
 x_267 = x_258;
}
lean_ctor_set(x_267, 0, x_256);
lean_ctor_set_uint8(x_267, sizeof(void*)*1, x_260);
x_268 = lean_box(0);
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_267);
x_223 = x_269;
x_224 = x_129;
goto block_252;
}
}
block_252:
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; 
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
x_227 = lean_array_get_size(x_126);
x_228 = lean_unsigned_to_nat(0u);
x_229 = lean_nat_dec_lt(x_228, x_227);
if (x_229 == 0)
{
uint8_t x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_227);
lean_dec(x_126);
lean_dec(x_9);
x_230 = 1;
x_231 = lean_box(x_230);
if (lean_is_scalar(x_226)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_226;
}
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_225);
if (lean_is_scalar(x_130)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_130;
}
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_224);
return x_233;
}
else
{
uint8_t x_234; 
x_234 = lean_nat_dec_le(x_227, x_227);
if (x_234 == 0)
{
uint8_t x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_227);
lean_dec(x_126);
lean_dec(x_9);
x_235 = 1;
x_236 = lean_box(x_235);
if (lean_is_scalar(x_226)) {
 x_237 = lean_alloc_ctor(0, 2, 0);
} else {
 x_237 = x_226;
}
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_225);
if (lean_is_scalar(x_130)) {
 x_238 = lean_alloc_ctor(0, 2, 0);
} else {
 x_238 = x_130;
}
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_224);
return x_238;
}
else
{
size_t x_239; size_t x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_226);
lean_dec(x_130);
x_239 = 0;
x_240 = lean_usize_of_nat(x_227);
lean_dec(x_227);
x_241 = lean_box(0);
x_242 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate___spec__6(x_126, x_239, x_240, x_241, x_9, x_225, x_224);
lean_dec(x_9);
lean_dec(x_126);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_245 = x_242;
} else {
 lean_dec_ref(x_242);
 x_245 = lean_box(0);
}
x_246 = lean_ctor_get(x_243, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_247 = x_243;
} else {
 lean_dec_ref(x_243);
 x_247 = lean_box(0);
}
x_248 = 1;
x_249 = lean_box(x_248);
if (lean_is_scalar(x_247)) {
 x_250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_250 = x_247;
}
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_246);
if (lean_is_scalar(x_245)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_245;
}
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_244);
return x_251;
}
}
}
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_312; 
x_270 = lean_ctor_get(x_16, 0);
lean_inc(x_270);
lean_dec(x_16);
x_271 = lean_ctor_get(x_14, 1);
lean_inc(x_271);
lean_dec(x_14);
x_272 = lean_ctor_get(x_270, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_270, 1);
lean_inc(x_273);
lean_dec(x_270);
x_274 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_274, 0, x_272);
lean_inc(x_5);
x_275 = l_Lake_checkHashUpToDate___at_Lake_buildFileUnlessUpToDate___spec__4(x_4, x_5, x_274, x_8, x_9, x_271, x_15);
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_278 = x_275;
} else {
 lean_dec_ref(x_275);
 x_278 = lean_box(0);
}
x_279 = lean_ctor_get(x_276, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_276, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_281 = x_276;
} else {
 lean_dec_ref(x_276);
 x_281 = lean_box(0);
}
x_312 = lean_unbox(x_279);
lean_dec(x_279);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; 
lean_dec(x_281);
lean_dec(x_278);
lean_dec(x_273);
x_313 = lean_box(0);
x_314 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1___lambda__2(x_12, x_13, x_6, x_5, x_7, x_313, x_9, x_280, x_277);
return x_314;
}
else
{
lean_object* x_315; uint8_t x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
x_315 = lean_ctor_get(x_280, 0);
lean_inc(x_315);
x_316 = lean_ctor_get_uint8(x_280, sizeof(void*)*1);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 x_317 = x_280;
} else {
 lean_dec_ref(x_280);
 x_317 = lean_box(0);
}
x_318 = l_Lake_instOrdJobAction;
x_319 = 1;
x_320 = lean_box(x_316);
x_321 = lean_box(x_319);
x_322 = l_instDecidableRelLe___rarg(x_318, x_320, x_321);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
if (lean_is_scalar(x_317)) {
 x_323 = lean_alloc_ctor(0, 1, 1);
} else {
 x_323 = x_317;
}
lean_ctor_set(x_323, 0, x_315);
lean_ctor_set_uint8(x_323, sizeof(void*)*1, x_316);
x_324 = lean_box(0);
if (lean_is_scalar(x_281)) {
 x_325 = lean_alloc_ctor(0, 2, 0);
} else {
 x_325 = x_281;
}
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_323);
x_282 = x_325;
x_283 = x_277;
goto block_311;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
if (lean_is_scalar(x_317)) {
 x_326 = lean_alloc_ctor(0, 1, 1);
} else {
 x_326 = x_317;
}
lean_ctor_set(x_326, 0, x_315);
lean_ctor_set_uint8(x_326, sizeof(void*)*1, x_319);
x_327 = lean_box(0);
if (lean_is_scalar(x_281)) {
 x_328 = lean_alloc_ctor(0, 2, 0);
} else {
 x_328 = x_281;
}
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set(x_328, 1, x_326);
x_282 = x_328;
x_283 = x_277;
goto block_311;
}
}
block_311:
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_285 = x_282;
} else {
 lean_dec_ref(x_282);
 x_285 = lean_box(0);
}
x_286 = lean_array_get_size(x_273);
x_287 = lean_unsigned_to_nat(0u);
x_288 = lean_nat_dec_lt(x_287, x_286);
if (x_288 == 0)
{
uint8_t x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_286);
lean_dec(x_273);
lean_dec(x_9);
x_289 = 1;
x_290 = lean_box(x_289);
if (lean_is_scalar(x_285)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_285;
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_284);
if (lean_is_scalar(x_278)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_278;
}
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_283);
return x_292;
}
else
{
uint8_t x_293; 
x_293 = lean_nat_dec_le(x_286, x_286);
if (x_293 == 0)
{
uint8_t x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_286);
lean_dec(x_273);
lean_dec(x_9);
x_294 = 1;
x_295 = lean_box(x_294);
if (lean_is_scalar(x_285)) {
 x_296 = lean_alloc_ctor(0, 2, 0);
} else {
 x_296 = x_285;
}
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_284);
if (lean_is_scalar(x_278)) {
 x_297 = lean_alloc_ctor(0, 2, 0);
} else {
 x_297 = x_278;
}
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_283);
return x_297;
}
else
{
size_t x_298; size_t x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_285);
lean_dec(x_278);
x_298 = 0;
x_299 = lean_usize_of_nat(x_286);
lean_dec(x_286);
x_300 = lean_box(0);
x_301 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate___spec__6(x_273, x_298, x_299, x_300, x_9, x_284, x_283);
lean_dec(x_9);
lean_dec(x_273);
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 x_304 = x_301;
} else {
 lean_dec_ref(x_301);
 x_304 = lean_box(0);
}
x_305 = lean_ctor_get(x_302, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 x_306 = x_302;
} else {
 lean_dec_ref(x_302);
 x_306 = lean_box(0);
}
x_307 = 1;
x_308 = lean_box(x_307);
if (lean_is_scalar(x_306)) {
 x_309 = lean_alloc_ctor(0, 2, 0);
} else {
 x_309 = x_306;
}
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_305);
if (lean_is_scalar(x_304)) {
 x_310 = lean_alloc_ctor(0, 2, 0);
} else {
 x_310 = x_304;
}
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_303);
return x_310;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_fetchOptRelease___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_28; 
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_get_set_stdout(x_1, x_5);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_apply_3(x_2, x_3, x_4, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_get_set_stdout(x_31, x_36);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_34, 0, x_45);
x_6 = x_34;
x_7 = x_43;
goto block_27;
}
else
{
uint8_t x_46; 
lean_free_object(x_35);
lean_dec(x_41);
lean_free_object(x_34);
lean_dec(x_38);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_35, 0);
x_51 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
lean_inc(x_50);
lean_dec(x_35);
x_52 = lean_get_set_stdout(x_31, x_36);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_51);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_38);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_34, 1, x_54);
lean_ctor_set(x_34, 0, x_56);
x_6 = x_34;
x_7 = x_53;
goto block_27;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_50);
lean_free_object(x_34);
lean_dec(x_38);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
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
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
lean_dec(x_34);
x_62 = lean_ctor_get(x_35, 0);
lean_inc(x_62);
x_63 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_64 = x_35;
} else {
 lean_dec_ref(x_35);
 x_64 = lean_box(0);
}
x_65 = lean_get_set_stdout(x_31, x_36);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(0, 1, 1);
} else {
 x_67 = x_64;
}
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_63);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
x_6 = x_70;
x_7 = x_66;
goto block_27;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_73 = x_65;
} else {
 lean_dec_ref(x_65);
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
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_34, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_33, 1);
lean_inc(x_76);
lean_dec(x_33);
x_77 = !lean_is_exclusive(x_34);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_34, 0);
x_79 = lean_ctor_get(x_34, 1);
lean_dec(x_79);
x_80 = !lean_is_exclusive(x_75);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_75, 0);
x_82 = lean_get_set_stdout(x_31, x_76);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_6 = x_34;
x_7 = x_83;
goto block_27;
}
else
{
uint8_t x_84; 
lean_free_object(x_75);
lean_dec(x_81);
lean_free_object(x_34);
lean_dec(x_78);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
return x_82;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_82, 0);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_82);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_75, 0);
x_89 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
lean_inc(x_88);
lean_dec(x_75);
x_90 = lean_get_set_stdout(x_31, x_76);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_89);
lean_ctor_set(x_34, 1, x_92);
x_6 = x_34;
x_7 = x_91;
goto block_27;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_88);
lean_free_object(x_34);
lean_dec(x_78);
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_95 = x_90;
} else {
 lean_dec_ref(x_90);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_34, 0);
lean_inc(x_97);
lean_dec(x_34);
x_98 = lean_ctor_get(x_75, 0);
lean_inc(x_98);
x_99 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_100 = x_75;
} else {
 lean_dec_ref(x_75);
 x_100 = lean_box(0);
}
x_101 = lean_get_set_stdout(x_31, x_76);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(0, 1, 1);
} else {
 x_103 = x_100;
}
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_99);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_103);
x_6 = x_104;
x_7 = x_102;
goto block_27;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
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
}
}
else
{
uint8_t x_109; 
lean_dec(x_31);
x_109 = !lean_is_exclusive(x_33);
if (x_109 == 0)
{
return x_33;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_33, 0);
x_111 = lean_ctor_get(x_33, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_33);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_free_object(x_4);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_30);
if (x_113 == 0)
{
return x_30;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_30, 0);
x_115 = lean_ctor_get(x_30, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_30);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_4, 0);
x_118 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_inc(x_117);
lean_dec(x_4);
x_119 = lean_get_set_stdout(x_1, x_5);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_122, 0, x_117);
lean_ctor_set_uint8(x_122, sizeof(void*)*1, x_118);
x_123 = lean_apply_3(x_2, x_3, x_122, x_121);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; 
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_ctor_get(x_124, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_128 = x_124;
} else {
 lean_dec_ref(x_124);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_125, 0);
lean_inc(x_129);
x_130 = lean_ctor_get_uint8(x_125, sizeof(void*)*1);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_131 = x_125;
} else {
 lean_dec_ref(x_125);
 x_131 = lean_box(0);
}
x_132 = lean_get_set_stdout(x_120, x_126);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
if (lean_is_scalar(x_131)) {
 x_134 = lean_alloc_ctor(0, 1, 1);
} else {
 x_134 = x_131;
}
lean_ctor_set(x_134, 0, x_129);
lean_ctor_set_uint8(x_134, sizeof(void*)*1, x_130);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_127);
lean_ctor_set(x_136, 1, x_135);
if (lean_is_scalar(x_128)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_128;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
x_6 = x_137;
x_7 = x_133;
goto block_27;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
x_138 = lean_ctor_get(x_132, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_132, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_140 = x_132;
} else {
 lean_dec_ref(x_132);
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
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; 
x_142 = lean_ctor_get(x_124, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_123, 1);
lean_inc(x_143);
lean_dec(x_123);
x_144 = lean_ctor_get(x_124, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_145 = x_124;
} else {
 lean_dec_ref(x_124);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_142, 0);
lean_inc(x_146);
x_147 = lean_ctor_get_uint8(x_142, sizeof(void*)*1);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 x_148 = x_142;
} else {
 lean_dec_ref(x_142);
 x_148 = lean_box(0);
}
x_149 = lean_get_set_stdout(x_120, x_143);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
if (lean_is_scalar(x_148)) {
 x_151 = lean_alloc_ctor(0, 1, 1);
} else {
 x_151 = x_148;
}
lean_ctor_set(x_151, 0, x_146);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_147);
if (lean_is_scalar(x_145)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_145;
}
lean_ctor_set(x_152, 0, x_144);
lean_ctor_set(x_152, 1, x_151);
x_6 = x_152;
x_7 = x_150;
goto block_27;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
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
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_120);
x_157 = lean_ctor_get(x_123, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_123, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_159 = x_123;
} else {
 lean_dec_ref(x_123);
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
lean_dec(x_117);
lean_dec(x_3);
lean_dec(x_2);
x_161 = lean_ctor_get(x_119, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_119, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_163 = x_119;
} else {
 lean_dec_ref(x_119);
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
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_fetchOptRelease___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_28; 
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_get_set_stdin(x_1, x_5);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_apply_3(x_2, x_3, x_4, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_get_set_stdin(x_31, x_36);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_34, 0, x_45);
x_6 = x_34;
x_7 = x_43;
goto block_27;
}
else
{
uint8_t x_46; 
lean_free_object(x_35);
lean_dec(x_41);
lean_free_object(x_34);
lean_dec(x_38);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_35, 0);
x_51 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
lean_inc(x_50);
lean_dec(x_35);
x_52 = lean_get_set_stdin(x_31, x_36);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_51);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_38);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_34, 1, x_54);
lean_ctor_set(x_34, 0, x_56);
x_6 = x_34;
x_7 = x_53;
goto block_27;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_50);
lean_free_object(x_34);
lean_dec(x_38);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
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
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
lean_dec(x_34);
x_62 = lean_ctor_get(x_35, 0);
lean_inc(x_62);
x_63 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_64 = x_35;
} else {
 lean_dec_ref(x_35);
 x_64 = lean_box(0);
}
x_65 = lean_get_set_stdin(x_31, x_36);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(0, 1, 1);
} else {
 x_67 = x_64;
}
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_63);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
x_6 = x_70;
x_7 = x_66;
goto block_27;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_73 = x_65;
} else {
 lean_dec_ref(x_65);
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
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_34, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_33, 1);
lean_inc(x_76);
lean_dec(x_33);
x_77 = !lean_is_exclusive(x_34);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_34, 0);
x_79 = lean_ctor_get(x_34, 1);
lean_dec(x_79);
x_80 = !lean_is_exclusive(x_75);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_75, 0);
x_82 = lean_get_set_stdin(x_31, x_76);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_6 = x_34;
x_7 = x_83;
goto block_27;
}
else
{
uint8_t x_84; 
lean_free_object(x_75);
lean_dec(x_81);
lean_free_object(x_34);
lean_dec(x_78);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
return x_82;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_82, 0);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_82);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_75, 0);
x_89 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
lean_inc(x_88);
lean_dec(x_75);
x_90 = lean_get_set_stdin(x_31, x_76);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_89);
lean_ctor_set(x_34, 1, x_92);
x_6 = x_34;
x_7 = x_91;
goto block_27;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_88);
lean_free_object(x_34);
lean_dec(x_78);
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_95 = x_90;
} else {
 lean_dec_ref(x_90);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_34, 0);
lean_inc(x_97);
lean_dec(x_34);
x_98 = lean_ctor_get(x_75, 0);
lean_inc(x_98);
x_99 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_100 = x_75;
} else {
 lean_dec_ref(x_75);
 x_100 = lean_box(0);
}
x_101 = lean_get_set_stdin(x_31, x_76);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(0, 1, 1);
} else {
 x_103 = x_100;
}
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_99);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_103);
x_6 = x_104;
x_7 = x_102;
goto block_27;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
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
}
}
else
{
uint8_t x_109; 
lean_dec(x_31);
x_109 = !lean_is_exclusive(x_33);
if (x_109 == 0)
{
return x_33;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_33, 0);
x_111 = lean_ctor_get(x_33, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_33);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_free_object(x_4);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_30);
if (x_113 == 0)
{
return x_30;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_30, 0);
x_115 = lean_ctor_get(x_30, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_30);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_4, 0);
x_118 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_inc(x_117);
lean_dec(x_4);
x_119 = lean_get_set_stdin(x_1, x_5);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_122, 0, x_117);
lean_ctor_set_uint8(x_122, sizeof(void*)*1, x_118);
x_123 = lean_apply_3(x_2, x_3, x_122, x_121);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; 
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_ctor_get(x_124, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_128 = x_124;
} else {
 lean_dec_ref(x_124);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_125, 0);
lean_inc(x_129);
x_130 = lean_ctor_get_uint8(x_125, sizeof(void*)*1);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_131 = x_125;
} else {
 lean_dec_ref(x_125);
 x_131 = lean_box(0);
}
x_132 = lean_get_set_stdin(x_120, x_126);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
if (lean_is_scalar(x_131)) {
 x_134 = lean_alloc_ctor(0, 1, 1);
} else {
 x_134 = x_131;
}
lean_ctor_set(x_134, 0, x_129);
lean_ctor_set_uint8(x_134, sizeof(void*)*1, x_130);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_127);
lean_ctor_set(x_136, 1, x_135);
if (lean_is_scalar(x_128)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_128;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
x_6 = x_137;
x_7 = x_133;
goto block_27;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
x_138 = lean_ctor_get(x_132, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_132, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_140 = x_132;
} else {
 lean_dec_ref(x_132);
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
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; 
x_142 = lean_ctor_get(x_124, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_123, 1);
lean_inc(x_143);
lean_dec(x_123);
x_144 = lean_ctor_get(x_124, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_145 = x_124;
} else {
 lean_dec_ref(x_124);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_142, 0);
lean_inc(x_146);
x_147 = lean_ctor_get_uint8(x_142, sizeof(void*)*1);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 x_148 = x_142;
} else {
 lean_dec_ref(x_142);
 x_148 = lean_box(0);
}
x_149 = lean_get_set_stdin(x_120, x_143);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
if (lean_is_scalar(x_148)) {
 x_151 = lean_alloc_ctor(0, 1, 1);
} else {
 x_151 = x_148;
}
lean_ctor_set(x_151, 0, x_146);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_147);
if (lean_is_scalar(x_145)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_145;
}
lean_ctor_set(x_152, 0, x_144);
lean_ctor_set(x_152, 1, x_151);
x_6 = x_152;
x_7 = x_150;
goto block_27;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
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
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_120);
x_157 = lean_ctor_get(x_123, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_123, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_159 = x_123;
} else {
 lean_dec_ref(x_123);
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
lean_dec(x_117);
lean_dec(x_3);
lean_dec(x_2);
x_161 = lean_ctor_get(x_119, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_119, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_163 = x_119;
} else {
 lean_dec_ref(x_119);
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
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Package_fetchOptRelease___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_28; 
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_get_set_stderr(x_1, x_5);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_apply_3(x_2, x_3, x_4, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_get_set_stderr(x_31, x_36);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_34, 0, x_45);
x_6 = x_34;
x_7 = x_43;
goto block_27;
}
else
{
uint8_t x_46; 
lean_free_object(x_35);
lean_dec(x_41);
lean_free_object(x_34);
lean_dec(x_38);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_35, 0);
x_51 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
lean_inc(x_50);
lean_dec(x_35);
x_52 = lean_get_set_stderr(x_31, x_36);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_51);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_38);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_34, 1, x_54);
lean_ctor_set(x_34, 0, x_56);
x_6 = x_34;
x_7 = x_53;
goto block_27;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_50);
lean_free_object(x_34);
lean_dec(x_38);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
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
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
lean_dec(x_34);
x_62 = lean_ctor_get(x_35, 0);
lean_inc(x_62);
x_63 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_64 = x_35;
} else {
 lean_dec_ref(x_35);
 x_64 = lean_box(0);
}
x_65 = lean_get_set_stderr(x_31, x_36);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(0, 1, 1);
} else {
 x_67 = x_64;
}
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_63);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
x_6 = x_70;
x_7 = x_66;
goto block_27;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_73 = x_65;
} else {
 lean_dec_ref(x_65);
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
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_34, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_33, 1);
lean_inc(x_76);
lean_dec(x_33);
x_77 = !lean_is_exclusive(x_34);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_34, 0);
x_79 = lean_ctor_get(x_34, 1);
lean_dec(x_79);
x_80 = !lean_is_exclusive(x_75);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_75, 0);
x_82 = lean_get_set_stderr(x_31, x_76);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_6 = x_34;
x_7 = x_83;
goto block_27;
}
else
{
uint8_t x_84; 
lean_free_object(x_75);
lean_dec(x_81);
lean_free_object(x_34);
lean_dec(x_78);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
return x_82;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_82, 0);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_82);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_75, 0);
x_89 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
lean_inc(x_88);
lean_dec(x_75);
x_90 = lean_get_set_stderr(x_31, x_76);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_89);
lean_ctor_set(x_34, 1, x_92);
x_6 = x_34;
x_7 = x_91;
goto block_27;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_88);
lean_free_object(x_34);
lean_dec(x_78);
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_95 = x_90;
} else {
 lean_dec_ref(x_90);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_34, 0);
lean_inc(x_97);
lean_dec(x_34);
x_98 = lean_ctor_get(x_75, 0);
lean_inc(x_98);
x_99 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_100 = x_75;
} else {
 lean_dec_ref(x_75);
 x_100 = lean_box(0);
}
x_101 = lean_get_set_stderr(x_31, x_76);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(0, 1, 1);
} else {
 x_103 = x_100;
}
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_99);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_103);
x_6 = x_104;
x_7 = x_102;
goto block_27;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
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
}
}
else
{
uint8_t x_109; 
lean_dec(x_31);
x_109 = !lean_is_exclusive(x_33);
if (x_109 == 0)
{
return x_33;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_33, 0);
x_111 = lean_ctor_get(x_33, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_33);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_free_object(x_4);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_30);
if (x_113 == 0)
{
return x_30;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_30, 0);
x_115 = lean_ctor_get(x_30, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_30);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_4, 0);
x_118 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_inc(x_117);
lean_dec(x_4);
x_119 = lean_get_set_stderr(x_1, x_5);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_122, 0, x_117);
lean_ctor_set_uint8(x_122, sizeof(void*)*1, x_118);
x_123 = lean_apply_3(x_2, x_3, x_122, x_121);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; 
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_ctor_get(x_124, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_128 = x_124;
} else {
 lean_dec_ref(x_124);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_125, 0);
lean_inc(x_129);
x_130 = lean_ctor_get_uint8(x_125, sizeof(void*)*1);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_131 = x_125;
} else {
 lean_dec_ref(x_125);
 x_131 = lean_box(0);
}
x_132 = lean_get_set_stderr(x_120, x_126);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
if (lean_is_scalar(x_131)) {
 x_134 = lean_alloc_ctor(0, 1, 1);
} else {
 x_134 = x_131;
}
lean_ctor_set(x_134, 0, x_129);
lean_ctor_set_uint8(x_134, sizeof(void*)*1, x_130);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_127);
lean_ctor_set(x_136, 1, x_135);
if (lean_is_scalar(x_128)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_128;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
x_6 = x_137;
x_7 = x_133;
goto block_27;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
x_138 = lean_ctor_get(x_132, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_132, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_140 = x_132;
} else {
 lean_dec_ref(x_132);
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
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; 
x_142 = lean_ctor_get(x_124, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_123, 1);
lean_inc(x_143);
lean_dec(x_123);
x_144 = lean_ctor_get(x_124, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_145 = x_124;
} else {
 lean_dec_ref(x_124);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_142, 0);
lean_inc(x_146);
x_147 = lean_ctor_get_uint8(x_142, sizeof(void*)*1);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 x_148 = x_142;
} else {
 lean_dec_ref(x_142);
 x_148 = lean_box(0);
}
x_149 = lean_get_set_stderr(x_120, x_143);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
if (lean_is_scalar(x_148)) {
 x_151 = lean_alloc_ctor(0, 1, 1);
} else {
 x_151 = x_148;
}
lean_ctor_set(x_151, 0, x_146);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_147);
if (lean_is_scalar(x_145)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_145;
}
lean_ctor_set(x_152, 0, x_144);
lean_ctor_set(x_152, 1, x_151);
x_6 = x_152;
x_7 = x_150;
goto block_27;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
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
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_120);
x_157 = lean_ctor_get(x_123, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_123, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_159 = x_123;
} else {
 lean_dec_ref(x_123);
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
lean_dec(x_117);
lean_dec(x_3);
lean_dec(x_2);
x_161 = lean_ctor_get(x_119, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_119, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_163 = x_119;
} else {
 lean_dec_ref(x_119);
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
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_fetchOptRelease___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__1;
x_9 = lean_st_mk_ref(x_8, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_mk_ref(x_8, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_IO_FS_Stream_ofBuffer(x_10);
lean_inc(x_13);
x_16 = l_IO_FS_Stream_ofBuffer(x_13);
if (x_2 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_fetchOptRelease___spec__3), 5, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_1);
x_18 = l_IO_withStdin___at_Lake_Package_fetchOptRelease___spec__4(x_15, x_17, x_3, x_4, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_st_ref_get(x_13, x_21);
lean_dec(x_13);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_string_validate_utf8(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_30);
x_32 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_33 = l_panic___at_String_fromUTF8_x21___spec__1(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_23);
lean_ctor_set(x_19, 0, x_34);
lean_ctor_set(x_27, 0, x_19);
return x_27;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_string_from_utf8(x_30);
lean_dec(x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_23);
lean_ctor_set(x_19, 0, x_36);
lean_ctor_set(x_27, 0, x_19);
return x_27;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_27, 0);
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_27);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_string_validate_utf8(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_39);
x_41 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_42 = l_panic___at_String_fromUTF8_x21___spec__1(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_23);
lean_ctor_set(x_19, 0, x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_19);
lean_ctor_set(x_44, 1, x_38);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_string_from_utf8(x_39);
lean_dec(x_39);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_23);
lean_ctor_set(x_19, 0, x_46);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_19);
lean_ctor_set(x_47, 1, x_38);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_19);
lean_dec(x_23);
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
lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_20, 0);
x_53 = lean_ctor_get_uint8(x_20, sizeof(void*)*1);
lean_inc(x_52);
lean_dec(x_20);
x_54 = lean_st_ref_get(x_13, x_21);
lean_dec(x_13);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
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
x_58 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_53);
x_59 = lean_ctor_get(x_55, 0);
lean_inc(x_59);
lean_dec(x_55);
x_60 = lean_string_validate_utf8(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_59);
x_61 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_62 = l_panic___at_String_fromUTF8_x21___spec__1(x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_23);
lean_ctor_set(x_19, 1, x_58);
lean_ctor_set(x_19, 0, x_63);
if (lean_is_scalar(x_57)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_57;
}
lean_ctor_set(x_64, 0, x_19);
lean_ctor_set(x_64, 1, x_56);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_string_from_utf8(x_59);
lean_dec(x_59);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_23);
lean_ctor_set(x_19, 1, x_58);
lean_ctor_set(x_19, 0, x_66);
if (lean_is_scalar(x_57)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_57;
}
lean_ctor_set(x_67, 0, x_19);
lean_ctor_set(x_67, 1, x_56);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_52);
lean_free_object(x_19);
lean_dec(x_23);
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
lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_19, 0);
lean_inc(x_72);
lean_dec(x_19);
x_73 = lean_ctor_get(x_20, 0);
lean_inc(x_73);
x_74 = lean_ctor_get_uint8(x_20, sizeof(void*)*1);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_75 = x_20;
} else {
 lean_dec_ref(x_20);
 x_75 = lean_box(0);
}
x_76 = lean_st_ref_get(x_13, x_21);
lean_dec(x_13);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_80 = lean_alloc_ctor(0, 1, 1);
} else {
 x_80 = x_75;
}
lean_ctor_set(x_80, 0, x_73);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_74);
x_81 = lean_ctor_get(x_77, 0);
lean_inc(x_81);
lean_dec(x_77);
x_82 = lean_string_validate_utf8(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_81);
x_83 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_84 = l_panic___at_String_fromUTF8_x21___spec__1(x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_72);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_80);
if (lean_is_scalar(x_79)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_79;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_78);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_string_from_utf8(x_81);
lean_dec(x_81);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_72);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_80);
if (lean_is_scalar(x_79)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_79;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_78);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_72);
x_92 = lean_ctor_get(x_76, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_76, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_94 = x_76;
} else {
 lean_dec_ref(x_76);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_13);
x_96 = !lean_is_exclusive(x_18);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_18, 0);
lean_dec(x_97);
x_98 = !lean_is_exclusive(x_19);
if (x_98 == 0)
{
return x_18;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_19, 0);
x_100 = lean_ctor_get(x_19, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_19);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_18, 0, x_101);
return x_18;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_18, 1);
lean_inc(x_102);
lean_dec(x_18);
x_103 = lean_ctor_get(x_19, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_19, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_105 = x_19;
} else {
 lean_dec_ref(x_19);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_102);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_13);
x_108 = !lean_is_exclusive(x_18);
if (x_108 == 0)
{
return x_18;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_18, 0);
x_110 = lean_ctor_get(x_18, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_18);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_inc(x_16);
x_112 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_Package_fetchOptRelease___spec__5), 5, 2);
lean_closure_set(x_112, 0, x_16);
lean_closure_set(x_112, 1, x_1);
x_113 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_fetchOptRelease___spec__3), 5, 2);
lean_closure_set(x_113, 0, x_16);
lean_closure_set(x_113, 1, x_112);
x_114 = l_IO_withStdin___at_Lake_Package_fetchOptRelease___spec__4(x_15, x_113, x_3, x_4, x_14);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_dec(x_114);
x_118 = !lean_is_exclusive(x_115);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_119 = lean_ctor_get(x_115, 0);
x_120 = lean_ctor_get(x_115, 1);
lean_dec(x_120);
x_121 = !lean_is_exclusive(x_116);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_116, 0);
x_123 = lean_st_ref_get(x_13, x_117);
lean_dec(x_13);
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_125 = lean_ctor_get(x_123, 0);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_string_validate_utf8(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_126);
x_128 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_129 = l_panic___at_String_fromUTF8_x21___spec__1(x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_119);
lean_ctor_set(x_115, 0, x_130);
lean_ctor_set(x_123, 0, x_115);
return x_123;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_string_from_utf8(x_126);
lean_dec(x_126);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_119);
lean_ctor_set(x_115, 0, x_132);
lean_ctor_set(x_123, 0, x_115);
return x_123;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_133 = lean_ctor_get(x_123, 0);
x_134 = lean_ctor_get(x_123, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_123);
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_string_validate_utf8(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_135);
x_137 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_138 = l_panic___at_String_fromUTF8_x21___spec__1(x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_119);
lean_ctor_set(x_115, 0, x_139);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_115);
lean_ctor_set(x_140, 1, x_134);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_string_from_utf8(x_135);
lean_dec(x_135);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_119);
lean_ctor_set(x_115, 0, x_142);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_115);
lean_ctor_set(x_143, 1, x_134);
return x_143;
}
}
}
else
{
uint8_t x_144; 
lean_free_object(x_116);
lean_dec(x_122);
lean_free_object(x_115);
lean_dec(x_119);
x_144 = !lean_is_exclusive(x_123);
if (x_144 == 0)
{
return x_123;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_123, 0);
x_146 = lean_ctor_get(x_123, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_123);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
lean_object* x_148; uint8_t x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_116, 0);
x_149 = lean_ctor_get_uint8(x_116, sizeof(void*)*1);
lean_inc(x_148);
lean_dec(x_116);
x_150 = lean_st_ref_get(x_13, x_117);
lean_dec(x_13);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_153 = x_150;
} else {
 lean_dec_ref(x_150);
 x_153 = lean_box(0);
}
x_154 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_154, 0, x_148);
lean_ctor_set_uint8(x_154, sizeof(void*)*1, x_149);
x_155 = lean_ctor_get(x_151, 0);
lean_inc(x_155);
lean_dec(x_151);
x_156 = lean_string_validate_utf8(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_155);
x_157 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_158 = l_panic___at_String_fromUTF8_x21___spec__1(x_157);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_119);
lean_ctor_set(x_115, 1, x_154);
lean_ctor_set(x_115, 0, x_159);
if (lean_is_scalar(x_153)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_153;
}
lean_ctor_set(x_160, 0, x_115);
lean_ctor_set(x_160, 1, x_152);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_string_from_utf8(x_155);
lean_dec(x_155);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_119);
lean_ctor_set(x_115, 1, x_154);
lean_ctor_set(x_115, 0, x_162);
if (lean_is_scalar(x_153)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_153;
}
lean_ctor_set(x_163, 0, x_115);
lean_ctor_set(x_163, 1, x_152);
return x_163;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_148);
lean_free_object(x_115);
lean_dec(x_119);
x_164 = lean_ctor_get(x_150, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_150, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_166 = x_150;
} else {
 lean_dec_ref(x_150);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
}
}
else
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; 
x_168 = lean_ctor_get(x_115, 0);
lean_inc(x_168);
lean_dec(x_115);
x_169 = lean_ctor_get(x_116, 0);
lean_inc(x_169);
x_170 = lean_ctor_get_uint8(x_116, sizeof(void*)*1);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 x_171 = x_116;
} else {
 lean_dec_ref(x_116);
 x_171 = lean_box(0);
}
x_172 = lean_st_ref_get(x_13, x_117);
lean_dec(x_13);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_175 = x_172;
} else {
 lean_dec_ref(x_172);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_176 = lean_alloc_ctor(0, 1, 1);
} else {
 x_176 = x_171;
}
lean_ctor_set(x_176, 0, x_169);
lean_ctor_set_uint8(x_176, sizeof(void*)*1, x_170);
x_177 = lean_ctor_get(x_173, 0);
lean_inc(x_177);
lean_dec(x_173);
x_178 = lean_string_validate_utf8(x_177);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_177);
x_179 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_180 = l_panic___at_String_fromUTF8_x21___spec__1(x_179);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_168);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_176);
if (lean_is_scalar(x_175)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_175;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_174);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_string_from_utf8(x_177);
lean_dec(x_177);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_168);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_176);
if (lean_is_scalar(x_175)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_175;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_174);
return x_187;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_171);
lean_dec(x_169);
lean_dec(x_168);
x_188 = lean_ctor_get(x_172, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_172, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_190 = x_172;
} else {
 lean_dec_ref(x_172);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
}
else
{
uint8_t x_192; 
lean_dec(x_13);
x_192 = !lean_is_exclusive(x_114);
if (x_192 == 0)
{
lean_object* x_193; uint8_t x_194; 
x_193 = lean_ctor_get(x_114, 0);
lean_dec(x_193);
x_194 = !lean_is_exclusive(x_115);
if (x_194 == 0)
{
return x_114;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_115, 0);
x_196 = lean_ctor_get(x_115, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_115);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
lean_ctor_set(x_114, 0, x_197);
return x_114;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_198 = lean_ctor_get(x_114, 1);
lean_inc(x_198);
lean_dec(x_114);
x_199 = lean_ctor_get(x_115, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_115, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_201 = x_115;
} else {
 lean_dec_ref(x_115);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_198);
return x_203;
}
}
}
else
{
uint8_t x_204; 
lean_dec(x_13);
x_204 = !lean_is_exclusive(x_114);
if (x_204 == 0)
{
return x_114;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_114, 0);
x_206 = lean_ctor_get(x_114, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_114);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
}
}
else
{
uint8_t x_208; 
lean_dec(x_10);
lean_free_object(x_4);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_208 = !lean_is_exclusive(x_12);
if (x_208 == 0)
{
return x_12;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_12, 0);
x_210 = lean_ctor_get(x_12, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_12);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
}
else
{
uint8_t x_212; 
lean_free_object(x_4);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_212 = !lean_is_exclusive(x_9);
if (x_212 == 0)
{
return x_9;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_9, 0);
x_214 = lean_ctor_get(x_9, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_9);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
else
{
lean_object* x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; 
x_216 = lean_ctor_get(x_4, 0);
x_217 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_inc(x_216);
lean_dec(x_4);
x_218 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__1;
x_219 = lean_st_mk_ref(x_218, x_5);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_222 = lean_st_mk_ref(x_218, x_221);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
x_225 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_225, 0, x_216);
lean_ctor_set_uint8(x_225, sizeof(void*)*1, x_217);
x_226 = l_IO_FS_Stream_ofBuffer(x_220);
lean_inc(x_223);
x_227 = l_IO_FS_Stream_ofBuffer(x_223);
if (x_2 == 0)
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_fetchOptRelease___spec__3), 5, 2);
lean_closure_set(x_228, 0, x_227);
lean_closure_set(x_228, 1, x_1);
x_229 = l_IO_withStdin___at_Lake_Package_fetchOptRelease___spec__4(x_226, x_228, x_3, x_225, x_224);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; lean_object* x_238; 
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
x_232 = lean_ctor_get(x_229, 1);
lean_inc(x_232);
lean_dec(x_229);
x_233 = lean_ctor_get(x_230, 0);
lean_inc(x_233);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_234 = x_230;
} else {
 lean_dec_ref(x_230);
 x_234 = lean_box(0);
}
x_235 = lean_ctor_get(x_231, 0);
lean_inc(x_235);
x_236 = lean_ctor_get_uint8(x_231, sizeof(void*)*1);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 x_237 = x_231;
} else {
 lean_dec_ref(x_231);
 x_237 = lean_box(0);
}
x_238 = lean_st_ref_get(x_223, x_232);
lean_dec(x_223);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_241 = x_238;
} else {
 lean_dec_ref(x_238);
 x_241 = lean_box(0);
}
if (lean_is_scalar(x_237)) {
 x_242 = lean_alloc_ctor(0, 1, 1);
} else {
 x_242 = x_237;
}
lean_ctor_set(x_242, 0, x_235);
lean_ctor_set_uint8(x_242, sizeof(void*)*1, x_236);
x_243 = lean_ctor_get(x_239, 0);
lean_inc(x_243);
lean_dec(x_239);
x_244 = lean_string_validate_utf8(x_243);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_243);
x_245 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_246 = l_panic___at_String_fromUTF8_x21___spec__1(x_245);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_233);
if (lean_is_scalar(x_234)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_234;
}
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_242);
if (lean_is_scalar(x_241)) {
 x_249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_249 = x_241;
}
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_240);
return x_249;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_250 = lean_string_from_utf8(x_243);
lean_dec(x_243);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_233);
if (lean_is_scalar(x_234)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_234;
}
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_242);
if (lean_is_scalar(x_241)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_241;
}
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_240);
return x_253;
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_237);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_233);
x_254 = lean_ctor_get(x_238, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_238, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_256 = x_238;
} else {
 lean_dec_ref(x_238);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_255);
return x_257;
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_223);
x_258 = lean_ctor_get(x_229, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_259 = x_229;
} else {
 lean_dec_ref(x_229);
 x_259 = lean_box(0);
}
x_260 = lean_ctor_get(x_230, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_230, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_262 = x_230;
} else {
 lean_dec_ref(x_230);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(1, 2, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_260);
lean_ctor_set(x_263, 1, x_261);
if (lean_is_scalar(x_259)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_259;
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_258);
return x_264;
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_223);
x_265 = lean_ctor_get(x_229, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_229, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_267 = x_229;
} else {
 lean_dec_ref(x_229);
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
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_inc(x_227);
x_269 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_Package_fetchOptRelease___spec__5), 5, 2);
lean_closure_set(x_269, 0, x_227);
lean_closure_set(x_269, 1, x_1);
x_270 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_fetchOptRelease___spec__3), 5, 2);
lean_closure_set(x_270, 0, x_227);
lean_closure_set(x_270, 1, x_269);
x_271 = l_IO_withStdin___at_Lake_Package_fetchOptRelease___spec__4(x_226, x_270, x_3, x_225, x_224);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; lean_object* x_279; lean_object* x_280; 
x_273 = lean_ctor_get(x_272, 1);
lean_inc(x_273);
x_274 = lean_ctor_get(x_271, 1);
lean_inc(x_274);
lean_dec(x_271);
x_275 = lean_ctor_get(x_272, 0);
lean_inc(x_275);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_276 = x_272;
} else {
 lean_dec_ref(x_272);
 x_276 = lean_box(0);
}
x_277 = lean_ctor_get(x_273, 0);
lean_inc(x_277);
x_278 = lean_ctor_get_uint8(x_273, sizeof(void*)*1);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 x_279 = x_273;
} else {
 lean_dec_ref(x_273);
 x_279 = lean_box(0);
}
x_280 = lean_st_ref_get(x_223, x_274);
lean_dec(x_223);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_283 = x_280;
} else {
 lean_dec_ref(x_280);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_284 = lean_alloc_ctor(0, 1, 1);
} else {
 x_284 = x_279;
}
lean_ctor_set(x_284, 0, x_277);
lean_ctor_set_uint8(x_284, sizeof(void*)*1, x_278);
x_285 = lean_ctor_get(x_281, 0);
lean_inc(x_285);
lean_dec(x_281);
x_286 = lean_string_validate_utf8(x_285);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_285);
x_287 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_288 = l_panic___at_String_fromUTF8_x21___spec__1(x_287);
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_275);
if (lean_is_scalar(x_276)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_276;
}
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_284);
if (lean_is_scalar(x_283)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_283;
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_282);
return x_291;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_292 = lean_string_from_utf8(x_285);
lean_dec(x_285);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_275);
if (lean_is_scalar(x_276)) {
 x_294 = lean_alloc_ctor(0, 2, 0);
} else {
 x_294 = x_276;
}
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_284);
if (lean_is_scalar(x_283)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_283;
}
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_282);
return x_295;
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_279);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
x_296 = lean_ctor_get(x_280, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_280, 1);
lean_inc(x_297);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_298 = x_280;
} else {
 lean_dec_ref(x_280);
 x_298 = lean_box(0);
}
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(1, 2, 0);
} else {
 x_299 = x_298;
}
lean_ctor_set(x_299, 0, x_296);
lean_ctor_set(x_299, 1, x_297);
return x_299;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_223);
x_300 = lean_ctor_get(x_271, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_301 = x_271;
} else {
 lean_dec_ref(x_271);
 x_301 = lean_box(0);
}
x_302 = lean_ctor_get(x_272, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_272, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_304 = x_272;
} else {
 lean_dec_ref(x_272);
 x_304 = lean_box(0);
}
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(1, 2, 0);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_302);
lean_ctor_set(x_305, 1, x_303);
if (lean_is_scalar(x_301)) {
 x_306 = lean_alloc_ctor(0, 2, 0);
} else {
 x_306 = x_301;
}
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_300);
return x_306;
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_223);
x_307 = lean_ctor_get(x_271, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_271, 1);
lean_inc(x_308);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_309 = x_271;
} else {
 lean_dec_ref(x_271);
 x_309 = lean_box(0);
}
if (lean_is_scalar(x_309)) {
 x_310 = lean_alloc_ctor(1, 2, 0);
} else {
 x_310 = x_309;
}
lean_ctor_set(x_310, 0, x_307);
lean_ctor_set(x_310, 1, x_308);
return x_310;
}
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_220);
lean_dec(x_216);
lean_dec(x_3);
lean_dec(x_1);
x_311 = lean_ctor_get(x_222, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_222, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_313 = x_222;
} else {
 lean_dec_ref(x_222);
 x_313 = lean_box(0);
}
if (lean_is_scalar(x_313)) {
 x_314 = lean_alloc_ctor(1, 2, 0);
} else {
 x_314 = x_313;
}
lean_ctor_set(x_314, 0, x_311);
lean_ctor_set(x_314, 1, x_312);
return x_314;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
lean_dec(x_216);
lean_dec(x_3);
lean_dec(x_1);
x_315 = lean_ctor_get(x_219, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_219, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_317 = x_219;
} else {
 lean_dec_ref(x_219);
 x_317 = lean_box(0);
}
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(1, 2, 0);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_315);
lean_ctor_set(x_318, 1, x_316);
return x_318;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_fetchOptRelease___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_Lake_Git_defaultRemote;
x_7 = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(x_6, x_1, x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
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
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
lean_inc(x_15);
lean_dec(x_3);
x_17 = l_Lake_Git_defaultRemote;
x_18 = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(x_17, x_1, x_4);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
if (lean_is_scalar(x_21)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_21;
}
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
}
}
static lean_object* _init_l_Lake_Package_fetchOptRelease___lambda__2___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lake_BuildTrace_nil;
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_fetchOptRelease___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lake_Package_fetchOptRelease___lambda__2___closed__1;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
static lean_object* _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("describe", 8);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_fetchOptRelease___lambda__3___closed__1;
x_2 = l_Lake_Package_fetchOptRelease___lambda__3___closed__2;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("--tags", 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_fetchOptRelease___lambda__3___closed__3;
x_2 = l_Lake_Package_fetchOptRelease___lambda__3___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("--exact-match", 13);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_fetchOptRelease___lambda__3___closed__5;
x_2 = l_Lake_Package_fetchOptRelease___lambda__3___closed__6;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HEAD", 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_fetchOptRelease___lambda__3___closed__7;
x_2 = l_Lake_Package_fetchOptRelease___lambda__3___closed__8;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__10() {
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
static lean_object* _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("git", 3);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": wanted prebuilt release, but no tag found for revision", 56);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__13() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lake_BuildTrace_nil;
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("/releases/download/", 19);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("/", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(".trace", 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__18() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lake_Package_fetchOptRelease___lambda__3___closed__17;
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("downloading ", 12);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_fetchOptRelease___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unpacking ", 10);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": wanted prebuilt release, but repository URL not known; the package may need to set 'releaseRepo'", 98);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_fetchOptRelease___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_477; uint8_t x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; uint8_t x_484; lean_object* x_485; uint8_t x_486; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_477 = lean_ctor_get(x_3, 2);
lean_inc(x_477);
lean_dec(x_3);
x_478 = 1;
x_479 = l_Lean_Name_toString(x_477, x_478);
x_480 = l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__2;
x_481 = lean_string_append(x_480, x_479);
lean_dec(x_479);
x_482 = l_Lake_Package_fetchOptRelease___lambda__3___closed__23;
x_483 = lean_string_append(x_481, x_482);
x_484 = 1;
x_485 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_485, 0, x_483);
lean_ctor_set_uint8(x_485, sizeof(void*)*1, x_484);
x_486 = !lean_is_exclusive(x_7);
if (x_486 == 0)
{
lean_object* x_487; uint8_t x_488; lean_object* x_489; lean_object* x_490; uint8_t x_491; lean_object* x_492; lean_object* x_493; uint8_t x_494; 
x_487 = lean_ctor_get(x_7, 0);
x_488 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
x_489 = lean_array_push(x_487, x_485);
x_490 = l_Lake_instOrdJobAction;
x_491 = 2;
x_492 = lean_box(x_488);
x_493 = lean_box(x_491);
x_494 = l_instDecidableRelLe___rarg(x_490, x_492, x_493);
if (x_494 == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; 
lean_ctor_set(x_7, 0, x_489);
x_495 = l_Lake_Package_fetchOptRelease___lambda__3___closed__13;
x_496 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_496, 0, x_495);
lean_ctor_set(x_496, 1, x_7);
x_497 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_497, 0, x_496);
lean_ctor_set(x_497, 1, x_8);
return x_497;
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; 
lean_ctor_set(x_7, 0, x_489);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_491);
x_498 = l_Lake_Package_fetchOptRelease___lambda__3___closed__13;
x_499 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_499, 0, x_498);
lean_ctor_set(x_499, 1, x_7);
x_500 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_500, 0, x_499);
lean_ctor_set(x_500, 1, x_8);
return x_500;
}
}
else
{
lean_object* x_501; uint8_t x_502; lean_object* x_503; lean_object* x_504; uint8_t x_505; lean_object* x_506; lean_object* x_507; uint8_t x_508; 
x_501 = lean_ctor_get(x_7, 0);
x_502 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
lean_inc(x_501);
lean_dec(x_7);
x_503 = lean_array_push(x_501, x_485);
x_504 = l_Lake_instOrdJobAction;
x_505 = 2;
x_506 = lean_box(x_502);
x_507 = lean_box(x_505);
x_508 = l_instDecidableRelLe___rarg(x_504, x_506, x_507);
if (x_508 == 0)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_509 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_509, 0, x_503);
lean_ctor_set_uint8(x_509, sizeof(void*)*1, x_502);
x_510 = l_Lake_Package_fetchOptRelease___lambda__3___closed__13;
x_511 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_511, 0, x_510);
lean_ctor_set(x_511, 1, x_509);
x_512 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_512, 0, x_511);
lean_ctor_set(x_512, 1, x_8);
return x_512;
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_513 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_513, 0, x_503);
lean_ctor_set_uint8(x_513, sizeof(void*)*1, x_505);
x_514 = l_Lake_Package_fetchOptRelease___lambda__3___closed__13;
x_515 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_515, 0, x_514);
lean_ctor_set(x_515, 1, x_513);
x_516 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_516, 0, x_515);
lean_ctor_set(x_516, 1, x_8);
return x_516;
}
}
}
else
{
lean_object* x_517; 
x_517 = lean_ctor_get(x_5, 0);
x_9 = x_517;
goto block_476;
}
}
else
{
lean_object* x_518; 
x_518 = lean_ctor_get(x_4, 0);
x_9 = x_518;
goto block_476;
}
block_476:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
lean_inc(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = l_Lake_Package_fetchOptRelease___lambda__3___closed__10;
x_15 = l_Lake_Package_fetchOptRelease___lambda__3___closed__11;
x_16 = l_Lake_Package_fetchOptRelease___lambda__3___closed__9;
x_17 = 0;
x_18 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set(x_18, 3, x_13);
lean_ctor_set(x_18, 4, x_2);
lean_ctor_set_uint8(x_18, sizeof(void*)*5, x_17);
x_19 = l_Lake_captureProc_x3f(x_18, x_8);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_3, 2);
lean_inc(x_23);
lean_dec(x_3);
x_24 = 1;
x_25 = l_Lean_Name_toString(x_23, x_24);
x_26 = l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__2;
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_28 = l_Lake_Package_fetchOptRelease___lambda__3___closed__12;
x_29 = lean_string_append(x_27, x_28);
x_30 = 1;
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
x_32 = lean_array_push(x_11, x_31);
x_33 = l_Lake_instOrdJobAction;
x_34 = 2;
x_35 = lean_box(x_12);
x_36 = lean_box(x_34);
x_37 = l_instDecidableRelLe___rarg(x_33, x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_ctor_set(x_7, 0, x_32);
x_38 = l_Lake_Package_fetchOptRelease___lambda__3___closed__13;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_7);
lean_ctor_set(x_19, 0, x_39);
return x_19;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_ctor_set(x_7, 0, x_32);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_34);
x_40 = l_Lake_Package_fetchOptRelease___lambda__3___closed__13;
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_7);
lean_ctor_set(x_19, 0, x_41);
return x_19;
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_42 = lean_ctor_get(x_19, 1);
lean_inc(x_42);
lean_dec(x_19);
x_43 = lean_ctor_get(x_3, 2);
lean_inc(x_43);
lean_dec(x_3);
x_44 = 1;
x_45 = l_Lean_Name_toString(x_43, x_44);
x_46 = l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__2;
x_47 = lean_string_append(x_46, x_45);
lean_dec(x_45);
x_48 = l_Lake_Package_fetchOptRelease___lambda__3___closed__12;
x_49 = lean_string_append(x_47, x_48);
x_50 = 1;
x_51 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_50);
x_52 = lean_array_push(x_11, x_51);
x_53 = l_Lake_instOrdJobAction;
x_54 = 2;
x_55 = lean_box(x_12);
x_56 = lean_box(x_54);
x_57 = l_instDecidableRelLe___rarg(x_53, x_55, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_ctor_set(x_7, 0, x_52);
x_58 = l_Lake_Package_fetchOptRelease___lambda__3___closed__13;
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_7);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_42);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_ctor_set(x_7, 0, x_52);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_54);
x_61 = l_Lake_Package_fetchOptRelease___lambda__3___closed__13;
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_7);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_42);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; 
x_64 = lean_ctor_get(x_19, 1);
lean_inc(x_64);
lean_dec(x_19);
x_65 = lean_ctor_get(x_20, 0);
lean_inc(x_65);
lean_dec(x_20);
x_66 = l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__2;
x_67 = lean_string_append(x_66, x_9);
x_68 = l_Lake_Package_fetchOptRelease___lambda__3___closed__14;
x_69 = lean_string_append(x_67, x_68);
x_70 = lean_string_append(x_69, x_65);
x_71 = l_Lake_Package_fetchOptRelease___lambda__3___closed__15;
x_72 = lean_string_append(x_70, x_71);
x_73 = lean_ctor_get(x_3, 16);
lean_inc(x_73);
x_74 = lean_string_append(x_72, x_73);
x_75 = lean_string_append(x_74, x_66);
x_76 = lean_string_hash(x_75);
x_77 = 1723;
x_78 = lean_uint64_mix_hash(x_77, x_76);
x_79 = l_Lake_defaultLakeDir;
lean_inc(x_1);
x_80 = l_System_FilePath_join(x_1, x_79);
lean_inc(x_73);
x_81 = l_System_FilePath_join(x_80, x_73);
x_82 = l_Lake_Package_fetchOptRelease___lambda__3___closed__16;
lean_inc(x_81);
x_83 = lean_string_append(x_81, x_82);
x_84 = l_Lake_Package_fetchOptRelease___lambda__3___closed__18;
x_85 = lean_box_uint64(x_78);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = l_Lake_Package_fetchOptRelease___lambda__3___closed__19;
x_88 = lean_string_append(x_87, x_75);
x_89 = lean_string_append(x_88, x_66);
x_90 = 0;
x_91 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set_uint8(x_91, sizeof(void*)*1, x_90);
x_92 = 2;
lean_inc(x_6);
lean_inc(x_81);
x_93 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1(x_75, x_81, x_91, x_81, x_86, x_83, x_92, x_84, x_6, x_7, x_64);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = !lean_is_exclusive(x_94);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_97 = lean_ctor_get(x_94, 0);
x_98 = lean_ctor_get(x_94, 1);
x_99 = lean_ctor_get(x_3, 8);
lean_inc(x_99);
x_100 = l_System_FilePath_join(x_1, x_99);
x_101 = !lean_is_exclusive(x_98);
if (x_101 == 0)
{
lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_164; 
x_102 = lean_ctor_get(x_98, 0);
x_103 = lean_ctor_get_uint8(x_98, sizeof(void*)*1);
x_104 = l_System_FilePath_pathExists(x_100, x_95);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
lean_inc(x_102);
x_107 = l_Lake_Package_fetchOptRelease___lambda__3___closed__20;
x_164 = lean_unbox(x_97);
lean_dec(x_97);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
lean_dec(x_105);
x_165 = l_Lake_instOrdJobAction;
x_166 = lean_box(x_103);
x_167 = lean_box(x_92);
x_168 = l_instDecidableRelLe___rarg(x_165, x_166, x_167);
if (x_168 == 0)
{
lean_object* x_169; 
lean_dec(x_102);
x_169 = lean_box(0);
lean_ctor_set(x_94, 0, x_169);
x_108 = x_94;
x_109 = x_106;
goto block_163;
}
else
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_98);
x_170 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_170, 0, x_102);
lean_ctor_set_uint8(x_170, sizeof(void*)*1, x_92);
x_171 = lean_box(0);
lean_ctor_set(x_94, 1, x_170);
lean_ctor_set(x_94, 0, x_171);
x_108 = x_94;
x_109 = x_106;
goto block_163;
}
}
else
{
uint8_t x_172; 
x_172 = lean_unbox(x_105);
lean_dec(x_105);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_173 = l_Lake_instOrdJobAction;
x_174 = lean_box(x_103);
x_175 = lean_box(x_92);
x_176 = l_instDecidableRelLe___rarg(x_173, x_174, x_175);
if (x_176 == 0)
{
lean_object* x_177; 
lean_dec(x_102);
x_177 = lean_box(0);
lean_ctor_set(x_94, 0, x_177);
x_108 = x_94;
x_109 = x_106;
goto block_163;
}
else
{
lean_object* x_178; lean_object* x_179; 
lean_dec(x_98);
x_178 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_178, 0, x_102);
lean_ctor_set_uint8(x_178, sizeof(void*)*1, x_92);
x_179 = lean_box(0);
lean_ctor_set(x_94, 1, x_178);
lean_ctor_set(x_94, 0, x_179);
x_108 = x_94;
x_109 = x_106;
goto block_163;
}
}
else
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_102);
lean_dec(x_100);
lean_free_object(x_94);
lean_dec(x_81);
lean_dec(x_73);
lean_dec(x_65);
lean_dec(x_3);
x_180 = lean_box(0);
x_181 = lean_apply_4(x_107, x_180, x_6, x_98, x_106);
return x_181;
}
}
block_163:
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_ctor_get(x_3, 2);
lean_inc(x_111);
lean_dec(x_3);
x_112 = 1;
x_113 = l_Lean_Name_toString(x_111, x_112);
x_114 = l_Lake_Package_fetchOptRelease___lambda__3___closed__21;
x_115 = lean_string_append(x_114, x_113);
lean_dec(x_113);
x_116 = l_Lake_Package_fetchOptRelease___lambda__3___closed__22;
x_117 = lean_string_append(x_115, x_116);
x_118 = lean_string_append(x_117, x_65);
lean_dec(x_65);
x_119 = lean_string_append(x_118, x_116);
x_120 = lean_string_append(x_119, x_73);
lean_dec(x_73);
x_121 = lean_string_append(x_120, x_66);
x_122 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set_uint8(x_122, sizeof(void*)*1, x_90);
x_123 = !lean_is_exclusive(x_110);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_110, 0);
x_125 = lean_array_push(x_124, x_122);
x_126 = l_Lake_untar(x_81, x_100, x_112, x_125, x_109);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
lean_ctor_set(x_110, 0, x_130);
x_131 = lean_apply_4(x_107, x_129, x_6, x_110, x_128);
return x_131;
}
else
{
uint8_t x_132; 
lean_dec(x_6);
x_132 = !lean_is_exclusive(x_126);
if (x_132 == 0)
{
lean_object* x_133; uint8_t x_134; 
x_133 = lean_ctor_get(x_126, 0);
lean_dec(x_133);
x_134 = !lean_is_exclusive(x_127);
if (x_134 == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_127, 1);
lean_ctor_set(x_110, 0, x_135);
lean_ctor_set(x_127, 1, x_110);
return x_126;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_127, 0);
x_137 = lean_ctor_get(x_127, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_127);
lean_ctor_set(x_110, 0, x_137);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_110);
lean_ctor_set(x_126, 0, x_138);
return x_126;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_139 = lean_ctor_get(x_126, 1);
lean_inc(x_139);
lean_dec(x_126);
x_140 = lean_ctor_get(x_127, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_127, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_142 = x_127;
} else {
 lean_dec_ref(x_127);
 x_142 = lean_box(0);
}
lean_ctor_set(x_110, 0, x_141);
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_110);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_139);
return x_144;
}
}
}
else
{
lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_110, 0);
x_146 = lean_ctor_get_uint8(x_110, sizeof(void*)*1);
lean_inc(x_145);
lean_dec(x_110);
x_147 = lean_array_push(x_145, x_122);
x_148 = l_Lake_untar(x_81, x_100, x_112, x_147, x_109);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_ctor_get(x_149, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
lean_dec(x_149);
x_153 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set_uint8(x_153, sizeof(void*)*1, x_146);
x_154 = lean_apply_4(x_107, x_151, x_6, x_153, x_150);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_6);
x_155 = lean_ctor_get(x_148, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_156 = x_148;
} else {
 lean_dec_ref(x_148);
 x_156 = lean_box(0);
}
x_157 = lean_ctor_get(x_149, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_149, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_159 = x_149;
} else {
 lean_dec_ref(x_149);
 x_159 = lean_box(0);
}
x_160 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set_uint8(x_160, sizeof(void*)*1, x_146);
if (lean_is_scalar(x_159)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_159;
}
lean_ctor_set(x_161, 0, x_157);
lean_ctor_set(x_161, 1, x_160);
if (lean_is_scalar(x_156)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_156;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_155);
return x_162;
}
}
}
}
else
{
lean_object* x_182; uint8_t x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_224; 
x_182 = lean_ctor_get(x_98, 0);
x_183 = lean_ctor_get_uint8(x_98, sizeof(void*)*1);
lean_inc(x_182);
lean_dec(x_98);
x_184 = l_System_FilePath_pathExists(x_100, x_95);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
lean_inc(x_182);
x_187 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_187, 0, x_182);
lean_ctor_set_uint8(x_187, sizeof(void*)*1, x_183);
x_188 = l_Lake_Package_fetchOptRelease___lambda__3___closed__20;
x_224 = lean_unbox(x_97);
lean_dec(x_97);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; 
lean_dec(x_185);
x_225 = l_Lake_instOrdJobAction;
x_226 = lean_box(x_183);
x_227 = lean_box(x_92);
x_228 = l_instDecidableRelLe___rarg(x_225, x_226, x_227);
if (x_228 == 0)
{
lean_object* x_229; 
lean_dec(x_182);
x_229 = lean_box(0);
lean_ctor_set(x_94, 1, x_187);
lean_ctor_set(x_94, 0, x_229);
x_189 = x_94;
x_190 = x_186;
goto block_223;
}
else
{
lean_object* x_230; lean_object* x_231; 
lean_dec(x_187);
x_230 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_230, 0, x_182);
lean_ctor_set_uint8(x_230, sizeof(void*)*1, x_92);
x_231 = lean_box(0);
lean_ctor_set(x_94, 1, x_230);
lean_ctor_set(x_94, 0, x_231);
x_189 = x_94;
x_190 = x_186;
goto block_223;
}
}
else
{
uint8_t x_232; 
x_232 = lean_unbox(x_185);
lean_dec(x_185);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_233 = l_Lake_instOrdJobAction;
x_234 = lean_box(x_183);
x_235 = lean_box(x_92);
x_236 = l_instDecidableRelLe___rarg(x_233, x_234, x_235);
if (x_236 == 0)
{
lean_object* x_237; 
lean_dec(x_182);
x_237 = lean_box(0);
lean_ctor_set(x_94, 1, x_187);
lean_ctor_set(x_94, 0, x_237);
x_189 = x_94;
x_190 = x_186;
goto block_223;
}
else
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_187);
x_238 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_238, 0, x_182);
lean_ctor_set_uint8(x_238, sizeof(void*)*1, x_92);
x_239 = lean_box(0);
lean_ctor_set(x_94, 1, x_238);
lean_ctor_set(x_94, 0, x_239);
x_189 = x_94;
x_190 = x_186;
goto block_223;
}
}
else
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_182);
lean_dec(x_100);
lean_free_object(x_94);
lean_dec(x_81);
lean_dec(x_73);
lean_dec(x_65);
lean_dec(x_3);
x_240 = lean_box(0);
x_241 = lean_apply_4(x_188, x_240, x_6, x_187, x_186);
return x_241;
}
}
block_223:
{
lean_object* x_191; lean_object* x_192; uint8_t x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = lean_ctor_get(x_3, 2);
lean_inc(x_192);
lean_dec(x_3);
x_193 = 1;
x_194 = l_Lean_Name_toString(x_192, x_193);
x_195 = l_Lake_Package_fetchOptRelease___lambda__3___closed__21;
x_196 = lean_string_append(x_195, x_194);
lean_dec(x_194);
x_197 = l_Lake_Package_fetchOptRelease___lambda__3___closed__22;
x_198 = lean_string_append(x_196, x_197);
x_199 = lean_string_append(x_198, x_65);
lean_dec(x_65);
x_200 = lean_string_append(x_199, x_197);
x_201 = lean_string_append(x_200, x_73);
lean_dec(x_73);
x_202 = lean_string_append(x_201, x_66);
x_203 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set_uint8(x_203, sizeof(void*)*1, x_90);
x_204 = lean_ctor_get(x_191, 0);
lean_inc(x_204);
x_205 = lean_ctor_get_uint8(x_191, sizeof(void*)*1);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 x_206 = x_191;
} else {
 lean_dec_ref(x_191);
 x_206 = lean_box(0);
}
x_207 = lean_array_push(x_204, x_203);
x_208 = l_Lake_untar(x_81, x_100, x_193, x_207, x_190);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
x_211 = lean_ctor_get(x_209, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_209, 1);
lean_inc(x_212);
lean_dec(x_209);
if (lean_is_scalar(x_206)) {
 x_213 = lean_alloc_ctor(0, 1, 1);
} else {
 x_213 = x_206;
}
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set_uint8(x_213, sizeof(void*)*1, x_205);
x_214 = lean_apply_4(x_188, x_211, x_6, x_213, x_210);
return x_214;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_6);
x_215 = lean_ctor_get(x_208, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_216 = x_208;
} else {
 lean_dec_ref(x_208);
 x_216 = lean_box(0);
}
x_217 = lean_ctor_get(x_209, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_209, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_219 = x_209;
} else {
 lean_dec_ref(x_209);
 x_219 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_220 = lean_alloc_ctor(0, 1, 1);
} else {
 x_220 = x_206;
}
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set_uint8(x_220, sizeof(void*)*1, x_205);
if (lean_is_scalar(x_219)) {
 x_221 = lean_alloc_ctor(1, 2, 0);
} else {
 x_221 = x_219;
}
lean_ctor_set(x_221, 0, x_217);
lean_ctor_set(x_221, 1, x_220);
if (lean_is_scalar(x_216)) {
 x_222 = lean_alloc_ctor(0, 2, 0);
} else {
 x_222 = x_216;
}
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_215);
return x_222;
}
}
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_289; 
x_242 = lean_ctor_get(x_94, 0);
x_243 = lean_ctor_get(x_94, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_94);
x_244 = lean_ctor_get(x_3, 8);
lean_inc(x_244);
x_245 = l_System_FilePath_join(x_1, x_244);
x_246 = lean_ctor_get(x_243, 0);
lean_inc(x_246);
x_247 = lean_ctor_get_uint8(x_243, sizeof(void*)*1);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 x_248 = x_243;
} else {
 lean_dec_ref(x_243);
 x_248 = lean_box(0);
}
x_249 = l_System_FilePath_pathExists(x_245, x_95);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
lean_inc(x_246);
if (lean_is_scalar(x_248)) {
 x_252 = lean_alloc_ctor(0, 1, 1);
} else {
 x_252 = x_248;
}
lean_ctor_set(x_252, 0, x_246);
lean_ctor_set_uint8(x_252, sizeof(void*)*1, x_247);
x_253 = l_Lake_Package_fetchOptRelease___lambda__3___closed__20;
x_289 = lean_unbox(x_242);
lean_dec(x_242);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; 
lean_dec(x_250);
x_290 = l_Lake_instOrdJobAction;
x_291 = lean_box(x_247);
x_292 = lean_box(x_92);
x_293 = l_instDecidableRelLe___rarg(x_290, x_291, x_292);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; 
lean_dec(x_246);
x_294 = lean_box(0);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_252);
x_254 = x_295;
x_255 = x_251;
goto block_288;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_252);
x_296 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_296, 0, x_246);
lean_ctor_set_uint8(x_296, sizeof(void*)*1, x_92);
x_297 = lean_box(0);
x_298 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_296);
x_254 = x_298;
x_255 = x_251;
goto block_288;
}
}
else
{
uint8_t x_299; 
x_299 = lean_unbox(x_250);
lean_dec(x_250);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; 
x_300 = l_Lake_instOrdJobAction;
x_301 = lean_box(x_247);
x_302 = lean_box(x_92);
x_303 = l_instDecidableRelLe___rarg(x_300, x_301, x_302);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; 
lean_dec(x_246);
x_304 = lean_box(0);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_252);
x_254 = x_305;
x_255 = x_251;
goto block_288;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_252);
x_306 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_306, 0, x_246);
lean_ctor_set_uint8(x_306, sizeof(void*)*1, x_92);
x_307 = lean_box(0);
x_308 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_306);
x_254 = x_308;
x_255 = x_251;
goto block_288;
}
}
else
{
lean_object* x_309; lean_object* x_310; 
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_81);
lean_dec(x_73);
lean_dec(x_65);
lean_dec(x_3);
x_309 = lean_box(0);
x_310 = lean_apply_4(x_253, x_309, x_6, x_252, x_251);
return x_310;
}
}
block_288:
{
lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
lean_dec(x_254);
x_257 = lean_ctor_get(x_3, 2);
lean_inc(x_257);
lean_dec(x_3);
x_258 = 1;
x_259 = l_Lean_Name_toString(x_257, x_258);
x_260 = l_Lake_Package_fetchOptRelease___lambda__3___closed__21;
x_261 = lean_string_append(x_260, x_259);
lean_dec(x_259);
x_262 = l_Lake_Package_fetchOptRelease___lambda__3___closed__22;
x_263 = lean_string_append(x_261, x_262);
x_264 = lean_string_append(x_263, x_65);
lean_dec(x_65);
x_265 = lean_string_append(x_264, x_262);
x_266 = lean_string_append(x_265, x_73);
lean_dec(x_73);
x_267 = lean_string_append(x_266, x_66);
x_268 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set_uint8(x_268, sizeof(void*)*1, x_90);
x_269 = lean_ctor_get(x_256, 0);
lean_inc(x_269);
x_270 = lean_ctor_get_uint8(x_256, sizeof(void*)*1);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 x_271 = x_256;
} else {
 lean_dec_ref(x_256);
 x_271 = lean_box(0);
}
x_272 = lean_array_push(x_269, x_268);
x_273 = l_Lake_untar(x_81, x_245, x_258, x_272, x_255);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec(x_273);
x_276 = lean_ctor_get(x_274, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_274, 1);
lean_inc(x_277);
lean_dec(x_274);
if (lean_is_scalar(x_271)) {
 x_278 = lean_alloc_ctor(0, 1, 1);
} else {
 x_278 = x_271;
}
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set_uint8(x_278, sizeof(void*)*1, x_270);
x_279 = lean_apply_4(x_253, x_276, x_6, x_278, x_275);
return x_279;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
lean_dec(x_6);
x_280 = lean_ctor_get(x_273, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_281 = x_273;
} else {
 lean_dec_ref(x_273);
 x_281 = lean_box(0);
}
x_282 = lean_ctor_get(x_274, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_274, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_284 = x_274;
} else {
 lean_dec_ref(x_274);
 x_284 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_285 = lean_alloc_ctor(0, 1, 1);
} else {
 x_285 = x_271;
}
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set_uint8(x_285, sizeof(void*)*1, x_270);
if (lean_is_scalar(x_284)) {
 x_286 = lean_alloc_ctor(1, 2, 0);
} else {
 x_286 = x_284;
}
lean_ctor_set(x_286, 0, x_282);
lean_ctor_set(x_286, 1, x_285);
if (lean_is_scalar(x_281)) {
 x_287 = lean_alloc_ctor(0, 2, 0);
} else {
 x_287 = x_281;
}
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_280);
return x_287;
}
}
}
}
else
{
uint8_t x_311; 
lean_dec(x_81);
lean_dec(x_73);
lean_dec(x_65);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_311 = !lean_is_exclusive(x_93);
if (x_311 == 0)
{
lean_object* x_312; uint8_t x_313; 
x_312 = lean_ctor_get(x_93, 0);
lean_dec(x_312);
x_313 = !lean_is_exclusive(x_94);
if (x_313 == 0)
{
return x_93;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_314 = lean_ctor_get(x_94, 0);
x_315 = lean_ctor_get(x_94, 1);
lean_inc(x_315);
lean_inc(x_314);
lean_dec(x_94);
x_316 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_316, 0, x_314);
lean_ctor_set(x_316, 1, x_315);
lean_ctor_set(x_93, 0, x_316);
return x_93;
}
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_317 = lean_ctor_get(x_93, 1);
lean_inc(x_317);
lean_dec(x_93);
x_318 = lean_ctor_get(x_94, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_94, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_320 = x_94;
} else {
 lean_dec_ref(x_94);
 x_320 = lean_box(0);
}
if (lean_is_scalar(x_320)) {
 x_321 = lean_alloc_ctor(1, 2, 0);
} else {
 x_321 = x_320;
}
lean_ctor_set(x_321, 0, x_318);
lean_ctor_set(x_321, 1, x_319);
x_322 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_317);
return x_322;
}
}
}
else
{
uint8_t x_323; 
lean_dec(x_81);
lean_dec(x_73);
lean_dec(x_65);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_323 = !lean_is_exclusive(x_93);
if (x_323 == 0)
{
return x_93;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_324 = lean_ctor_get(x_93, 0);
x_325 = lean_ctor_get(x_93, 1);
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_93);
x_326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_326, 0, x_324);
lean_ctor_set(x_326, 1, x_325);
return x_326;
}
}
}
}
else
{
lean_object* x_327; uint8_t x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_327 = lean_ctor_get(x_7, 0);
x_328 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
lean_inc(x_327);
lean_dec(x_7);
lean_inc(x_1);
x_329 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_329, 0, x_1);
x_330 = l_Lake_Package_fetchOptRelease___lambda__3___closed__10;
x_331 = l_Lake_Package_fetchOptRelease___lambda__3___closed__11;
x_332 = l_Lake_Package_fetchOptRelease___lambda__3___closed__9;
x_333 = 0;
x_334 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_334, 0, x_330);
lean_ctor_set(x_334, 1, x_331);
lean_ctor_set(x_334, 2, x_332);
lean_ctor_set(x_334, 3, x_329);
lean_ctor_set(x_334, 4, x_2);
lean_ctor_set_uint8(x_334, sizeof(void*)*5, x_333);
x_335 = l_Lake_captureProc_x3f(x_334, x_8);
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; lean_object* x_351; lean_object* x_352; uint8_t x_353; 
lean_dec(x_6);
lean_dec(x_1);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 x_338 = x_335;
} else {
 lean_dec_ref(x_335);
 x_338 = lean_box(0);
}
x_339 = lean_ctor_get(x_3, 2);
lean_inc(x_339);
lean_dec(x_3);
x_340 = 1;
x_341 = l_Lean_Name_toString(x_339, x_340);
x_342 = l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__2;
x_343 = lean_string_append(x_342, x_341);
lean_dec(x_341);
x_344 = l_Lake_Package_fetchOptRelease___lambda__3___closed__12;
x_345 = lean_string_append(x_343, x_344);
x_346 = 1;
x_347 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set_uint8(x_347, sizeof(void*)*1, x_346);
x_348 = lean_array_push(x_327, x_347);
x_349 = l_Lake_instOrdJobAction;
x_350 = 2;
x_351 = lean_box(x_328);
x_352 = lean_box(x_350);
x_353 = l_instDecidableRelLe___rarg(x_349, x_351, x_352);
if (x_353 == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_354 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_354, 0, x_348);
lean_ctor_set_uint8(x_354, sizeof(void*)*1, x_328);
x_355 = l_Lake_Package_fetchOptRelease___lambda__3___closed__13;
x_356 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_354);
if (lean_is_scalar(x_338)) {
 x_357 = lean_alloc_ctor(0, 2, 0);
} else {
 x_357 = x_338;
}
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_337);
return x_357;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_358 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_358, 0, x_348);
lean_ctor_set_uint8(x_358, sizeof(void*)*1, x_350);
x_359 = l_Lake_Package_fetchOptRelease___lambda__3___closed__13;
x_360 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_358);
if (lean_is_scalar(x_338)) {
 x_361 = lean_alloc_ctor(0, 2, 0);
} else {
 x_361 = x_338;
}
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_337);
return x_361;
}
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; uint64_t x_375; uint64_t x_376; uint64_t x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; uint8_t x_389; lean_object* x_390; uint8_t x_391; lean_object* x_392; 
x_362 = lean_ctor_get(x_335, 1);
lean_inc(x_362);
lean_dec(x_335);
x_363 = lean_ctor_get(x_336, 0);
lean_inc(x_363);
lean_dec(x_336);
x_364 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_364, 0, x_327);
lean_ctor_set_uint8(x_364, sizeof(void*)*1, x_328);
x_365 = l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__2;
x_366 = lean_string_append(x_365, x_9);
x_367 = l_Lake_Package_fetchOptRelease___lambda__3___closed__14;
x_368 = lean_string_append(x_366, x_367);
x_369 = lean_string_append(x_368, x_363);
x_370 = l_Lake_Package_fetchOptRelease___lambda__3___closed__15;
x_371 = lean_string_append(x_369, x_370);
x_372 = lean_ctor_get(x_3, 16);
lean_inc(x_372);
x_373 = lean_string_append(x_371, x_372);
x_374 = lean_string_append(x_373, x_365);
x_375 = lean_string_hash(x_374);
x_376 = 1723;
x_377 = lean_uint64_mix_hash(x_376, x_375);
x_378 = l_Lake_defaultLakeDir;
lean_inc(x_1);
x_379 = l_System_FilePath_join(x_1, x_378);
lean_inc(x_372);
x_380 = l_System_FilePath_join(x_379, x_372);
x_381 = l_Lake_Package_fetchOptRelease___lambda__3___closed__16;
lean_inc(x_380);
x_382 = lean_string_append(x_380, x_381);
x_383 = l_Lake_Package_fetchOptRelease___lambda__3___closed__18;
x_384 = lean_box_uint64(x_377);
x_385 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_383);
x_386 = l_Lake_Package_fetchOptRelease___lambda__3___closed__19;
x_387 = lean_string_append(x_386, x_374);
x_388 = lean_string_append(x_387, x_365);
x_389 = 0;
x_390 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_390, 0, x_388);
lean_ctor_set_uint8(x_390, sizeof(void*)*1, x_389);
x_391 = 2;
lean_inc(x_6);
lean_inc(x_380);
x_392 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1(x_374, x_380, x_390, x_380, x_385, x_382, x_391, x_383, x_6, x_364, x_362);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; 
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; uint8_t x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; uint8_t x_443; 
x_394 = lean_ctor_get(x_392, 1);
lean_inc(x_394);
lean_dec(x_392);
x_395 = lean_ctor_get(x_393, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_393, 1);
lean_inc(x_396);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 x_397 = x_393;
} else {
 lean_dec_ref(x_393);
 x_397 = lean_box(0);
}
x_398 = lean_ctor_get(x_3, 8);
lean_inc(x_398);
x_399 = l_System_FilePath_join(x_1, x_398);
x_400 = lean_ctor_get(x_396, 0);
lean_inc(x_400);
x_401 = lean_ctor_get_uint8(x_396, sizeof(void*)*1);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 x_402 = x_396;
} else {
 lean_dec_ref(x_396);
 x_402 = lean_box(0);
}
x_403 = l_System_FilePath_pathExists(x_399, x_394);
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_403, 1);
lean_inc(x_405);
lean_dec(x_403);
lean_inc(x_400);
if (lean_is_scalar(x_402)) {
 x_406 = lean_alloc_ctor(0, 1, 1);
} else {
 x_406 = x_402;
}
lean_ctor_set(x_406, 0, x_400);
lean_ctor_set_uint8(x_406, sizeof(void*)*1, x_401);
x_407 = l_Lake_Package_fetchOptRelease___lambda__3___closed__20;
x_443 = lean_unbox(x_395);
lean_dec(x_395);
if (x_443 == 0)
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; 
lean_dec(x_404);
x_444 = l_Lake_instOrdJobAction;
x_445 = lean_box(x_401);
x_446 = lean_box(x_391);
x_447 = l_instDecidableRelLe___rarg(x_444, x_445, x_446);
if (x_447 == 0)
{
lean_object* x_448; lean_object* x_449; 
lean_dec(x_400);
x_448 = lean_box(0);
if (lean_is_scalar(x_397)) {
 x_449 = lean_alloc_ctor(0, 2, 0);
} else {
 x_449 = x_397;
}
lean_ctor_set(x_449, 0, x_448);
lean_ctor_set(x_449, 1, x_406);
x_408 = x_449;
x_409 = x_405;
goto block_442;
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; 
lean_dec(x_406);
x_450 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_450, 0, x_400);
lean_ctor_set_uint8(x_450, sizeof(void*)*1, x_391);
x_451 = lean_box(0);
if (lean_is_scalar(x_397)) {
 x_452 = lean_alloc_ctor(0, 2, 0);
} else {
 x_452 = x_397;
}
lean_ctor_set(x_452, 0, x_451);
lean_ctor_set(x_452, 1, x_450);
x_408 = x_452;
x_409 = x_405;
goto block_442;
}
}
else
{
uint8_t x_453; 
x_453 = lean_unbox(x_404);
lean_dec(x_404);
if (x_453 == 0)
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; uint8_t x_457; 
x_454 = l_Lake_instOrdJobAction;
x_455 = lean_box(x_401);
x_456 = lean_box(x_391);
x_457 = l_instDecidableRelLe___rarg(x_454, x_455, x_456);
if (x_457 == 0)
{
lean_object* x_458; lean_object* x_459; 
lean_dec(x_400);
x_458 = lean_box(0);
if (lean_is_scalar(x_397)) {
 x_459 = lean_alloc_ctor(0, 2, 0);
} else {
 x_459 = x_397;
}
lean_ctor_set(x_459, 0, x_458);
lean_ctor_set(x_459, 1, x_406);
x_408 = x_459;
x_409 = x_405;
goto block_442;
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; 
lean_dec(x_406);
x_460 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_460, 0, x_400);
lean_ctor_set_uint8(x_460, sizeof(void*)*1, x_391);
x_461 = lean_box(0);
if (lean_is_scalar(x_397)) {
 x_462 = lean_alloc_ctor(0, 2, 0);
} else {
 x_462 = x_397;
}
lean_ctor_set(x_462, 0, x_461);
lean_ctor_set(x_462, 1, x_460);
x_408 = x_462;
x_409 = x_405;
goto block_442;
}
}
else
{
lean_object* x_463; lean_object* x_464; 
lean_dec(x_400);
lean_dec(x_399);
lean_dec(x_397);
lean_dec(x_380);
lean_dec(x_372);
lean_dec(x_363);
lean_dec(x_3);
x_463 = lean_box(0);
x_464 = lean_apply_4(x_407, x_463, x_6, x_406, x_405);
return x_464;
}
}
block_442:
{
lean_object* x_410; lean_object* x_411; uint8_t x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_410 = lean_ctor_get(x_408, 1);
lean_inc(x_410);
lean_dec(x_408);
x_411 = lean_ctor_get(x_3, 2);
lean_inc(x_411);
lean_dec(x_3);
x_412 = 1;
x_413 = l_Lean_Name_toString(x_411, x_412);
x_414 = l_Lake_Package_fetchOptRelease___lambda__3___closed__21;
x_415 = lean_string_append(x_414, x_413);
lean_dec(x_413);
x_416 = l_Lake_Package_fetchOptRelease___lambda__3___closed__22;
x_417 = lean_string_append(x_415, x_416);
x_418 = lean_string_append(x_417, x_363);
lean_dec(x_363);
x_419 = lean_string_append(x_418, x_416);
x_420 = lean_string_append(x_419, x_372);
lean_dec(x_372);
x_421 = lean_string_append(x_420, x_365);
x_422 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set_uint8(x_422, sizeof(void*)*1, x_389);
x_423 = lean_ctor_get(x_410, 0);
lean_inc(x_423);
x_424 = lean_ctor_get_uint8(x_410, sizeof(void*)*1);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 x_425 = x_410;
} else {
 lean_dec_ref(x_410);
 x_425 = lean_box(0);
}
x_426 = lean_array_push(x_423, x_422);
x_427 = l_Lake_untar(x_380, x_399, x_412, x_426, x_409);
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_429 = lean_ctor_get(x_427, 1);
lean_inc(x_429);
lean_dec(x_427);
x_430 = lean_ctor_get(x_428, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_428, 1);
lean_inc(x_431);
lean_dec(x_428);
if (lean_is_scalar(x_425)) {
 x_432 = lean_alloc_ctor(0, 1, 1);
} else {
 x_432 = x_425;
}
lean_ctor_set(x_432, 0, x_431);
lean_ctor_set_uint8(x_432, sizeof(void*)*1, x_424);
x_433 = lean_apply_4(x_407, x_430, x_6, x_432, x_429);
return x_433;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
lean_dec(x_6);
x_434 = lean_ctor_get(x_427, 1);
lean_inc(x_434);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 x_435 = x_427;
} else {
 lean_dec_ref(x_427);
 x_435 = lean_box(0);
}
x_436 = lean_ctor_get(x_428, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_428, 1);
lean_inc(x_437);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 x_438 = x_428;
} else {
 lean_dec_ref(x_428);
 x_438 = lean_box(0);
}
if (lean_is_scalar(x_425)) {
 x_439 = lean_alloc_ctor(0, 1, 1);
} else {
 x_439 = x_425;
}
lean_ctor_set(x_439, 0, x_437);
lean_ctor_set_uint8(x_439, sizeof(void*)*1, x_424);
if (lean_is_scalar(x_438)) {
 x_440 = lean_alloc_ctor(1, 2, 0);
} else {
 x_440 = x_438;
}
lean_ctor_set(x_440, 0, x_436);
lean_ctor_set(x_440, 1, x_439);
if (lean_is_scalar(x_435)) {
 x_441 = lean_alloc_ctor(0, 2, 0);
} else {
 x_441 = x_435;
}
lean_ctor_set(x_441, 0, x_440);
lean_ctor_set(x_441, 1, x_434);
return x_441;
}
}
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; 
lean_dec(x_380);
lean_dec(x_372);
lean_dec(x_363);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_465 = lean_ctor_get(x_392, 1);
lean_inc(x_465);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 x_466 = x_392;
} else {
 lean_dec_ref(x_392);
 x_466 = lean_box(0);
}
x_467 = lean_ctor_get(x_393, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_393, 1);
lean_inc(x_468);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 x_469 = x_393;
} else {
 lean_dec_ref(x_393);
 x_469 = lean_box(0);
}
if (lean_is_scalar(x_469)) {
 x_470 = lean_alloc_ctor(1, 2, 0);
} else {
 x_470 = x_469;
}
lean_ctor_set(x_470, 0, x_467);
lean_ctor_set(x_470, 1, x_468);
if (lean_is_scalar(x_466)) {
 x_471 = lean_alloc_ctor(0, 2, 0);
} else {
 x_471 = x_466;
}
lean_ctor_set(x_471, 0, x_470);
lean_ctor_set(x_471, 1, x_465);
return x_471;
}
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
lean_dec(x_380);
lean_dec(x_372);
lean_dec(x_363);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_472 = lean_ctor_get(x_392, 0);
lean_inc(x_472);
x_473 = lean_ctor_get(x_392, 1);
lean_inc(x_473);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 x_474 = x_392;
} else {
 lean_dec_ref(x_392);
 x_474 = lean_box(0);
}
if (lean_is_scalar(x_474)) {
 x_475 = lean_alloc_ctor(1, 2, 0);
} else {
 x_475 = x_474;
}
lean_ctor_set(x_475, 0, x_472);
lean_ctor_set(x_475, 1, x_473);
return x_475;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_fetchOptRelease___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 1;
lean_inc(x_2);
x_6 = l_IO_FS_withIsolatedStreams___at_Lake_Package_fetchOptRelease___spec__2(x_1, x_5, x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
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
x_13 = l_String_isEmpty(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; 
x_14 = l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__1;
x_15 = lean_string_append(x_14, x_11);
lean_dec(x_11);
x_16 = l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__2;
x_17 = lean_string_append(x_15, x_16);
x_18 = 1;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_array_push(x_21, x_19);
lean_ctor_set(x_10, 0, x_22);
x_23 = lean_box(0);
x_24 = l_Lake_Package_recBuildExtraDepTargets___lambda__2(x_12, x_23, x_2, x_10, x_9);
lean_dec(x_2);
return x_24;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
lean_inc(x_25);
lean_dec(x_10);
x_27 = lean_array_push(x_25, x_19);
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_26);
x_29 = lean_box(0);
x_30 = l_Lake_Package_recBuildExtraDepTargets___lambda__2(x_12, x_29, x_2, x_28, x_9);
lean_dec(x_2);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_11);
x_31 = lean_box(0);
x_32 = l_Lake_Package_recBuildExtraDepTargets___lambda__2(x_12, x_31, x_2, x_10, x_9);
lean_dec(x_2);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_6);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_6, 0);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_7);
if (x_35 == 0)
{
return x_6;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_7, 0);
x_37 = lean_ctor_get(x_7, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_7);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_6, 0, x_38);
return x_6;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_6, 1);
lean_inc(x_39);
lean_dec(x_6);
x_40 = lean_ctor_get(x_7, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_7, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_42 = x_7;
} else {
 lean_dec_ref(x_7);
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
else
{
uint8_t x_45; 
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_6);
if (x_45 == 0)
{
return x_6;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_6, 0);
x_47 = lean_ctor_get(x_6, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_6);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_fetchOptRelease(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 5);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 14);
lean_inc(x_11);
lean_inc(x_8);
x_12 = lean_alloc_closure((void*)(l_Lake_Package_fetchOptRelease___lambda__1___boxed), 4, 1);
lean_closure_set(x_12, 0, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_9, 13);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
x_13 = x_10;
goto block_38;
}
else
{
uint8_t x_40; 
lean_dec(x_10);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
x_13 = x_39;
goto block_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_13 = x_42;
goto block_38;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_10);
x_43 = !lean_is_exclusive(x_11);
if (x_43 == 0)
{
x_13 = x_11;
goto block_38;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_11, 0);
lean_inc(x_44);
lean_dec(x_11);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_13 = x_45;
goto block_38;
}
}
block_38:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = l_Lake_Package_recComputeDeps___closed__1;
x_15 = lean_alloc_closure((void*)(l_Lake_Package_fetchOptRelease___lambda__3___boxed), 8, 4);
lean_closure_set(x_15, 0, x_8);
lean_closure_set(x_15, 1, x_14);
lean_closure_set(x_15, 2, x_9);
lean_closure_set(x_15, 3, x_13);
x_16 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_16, 0, x_12);
lean_closure_set(x_16, 1, x_15);
x_17 = l_Lake_Package_recBuildExtraDepTargets___closed__2;
x_18 = lean_alloc_closure((void*)(l_Lake_Package_fetchOptRelease___lambda__4), 4, 3);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_4);
lean_closure_set(x_18, 2, x_17);
x_19 = l_Task_Priority_default;
x_20 = lean_io_as_task(x_18, x_19, x_7);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__2;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_5);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_20, 0, x_26);
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
x_29 = l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__2;
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_5);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_6);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_6);
lean_dec(x_5);
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
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_7);
lean_dec(x_7);
x_13 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_12, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_fetchOptRelease___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_IO_FS_withIsolatedStreams___at_Lake_Package_fetchOptRelease___spec__2(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_fetchOptRelease___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Package_fetchOptRelease___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_fetchOptRelease___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Package_fetchOptRelease___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_fetchOptRelease___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Package_fetchOptRelease___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_fetchOptRelease___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Package_fetchOptRelease(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optReleaseFacetConfig___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Package_fetchOptRelease(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_Package_optReleaseFacetConfig___spec__1___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_dec(x_3);
x_4 = lean_box(0);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
static lean_object* _init_l_Functor_discard___at_Lake_Package_optReleaseFacetConfig___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Functor_discard___at_Lake_Package_optReleaseFacetConfig___spec__1___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Functor_discard___at_Lake_Package_optReleaseFacetConfig___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Functor_discard___at_Lake_Package_optReleaseFacetConfig___spec__1___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lake_EResult_map___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_Package_optReleaseFacetConfig___spec__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Functor_discard___at_Lake_Package_optReleaseFacetConfig___spec__1___closed__2;
x_5 = l_Task_Priority_default;
x_6 = 0;
x_7 = lean_task_map(x_4, x_3, x_5, x_6);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_Functor_discard___at_Lake_Package_optReleaseFacetConfig___spec__1___closed__2;
x_11 = l_Task_Priority_default;
x_12 = 0;
x_13 = lean_task_map(x_10, x_8, x_11, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
}
}
static lean_object* _init_l_Lake_Package_optReleaseFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Functor_discard___at_Lake_Package_optReleaseFacetConfig___spec__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_optReleaseFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_optReleaseFacetConfig___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_optReleaseFacetConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_optReleaseFacetConfig___elambda__1___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_optReleaseFacetConfig___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_optReleaseFacetConfig___closed__3;
x_2 = l_Lake_Package_optReleaseFacetConfig___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_optReleaseFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_optReleaseFacetConfig___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optReleaseFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Package_optReleaseFacetConfig___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lake_Package_releaseFacetConfig___elambda__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to fetch cloud release", 29);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_releaseFacetConfig___elambda__1___lambda__1___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 3;
x_2 = l_Lake_Package_releaseFacetConfig___elambda__1___lambda__1___closed__1;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseFacetConfig___elambda__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_array_get_size(x_5);
x_7 = l_Lake_Package_releaseFacetConfig___elambda__1___lambda__1___closed__2;
x_8 = lean_array_push(x_5, x_7);
lean_ctor_set(x_2, 0, x_8);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_inc(x_11);
lean_dec(x_2);
x_13 = lean_array_get_size(x_11);
x_14 = l_Lake_Package_releaseFacetConfig___elambda__1___lambda__1___closed__2;
x_15 = lean_array_push(x_11, x_14);
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_12);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
}
}
static lean_object* _init_l_Lake_Package_releaseFacetConfig___elambda__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_releaseFacetConfig___elambda__1___lambda__1___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseFacetConfig___elambda__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_52 = lean_ctor_get(x_4, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_4, 1);
lean_inc(x_53);
lean_dec(x_4);
x_54 = lean_alloc_closure((void*)(l_Lake_Package_recBuildExtraDepTargets___lambda__3___boxed), 5, 1);
lean_closure_set(x_54, 0, x_53);
x_55 = lean_unbox(x_52);
lean_dec(x_52);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = l_Lake_Package_releaseFacetConfig___elambda__1___lambda__2___closed__1;
x_57 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_57, 0, x_56);
lean_closure_set(x_57, 1, x_54);
x_6 = x_57;
goto block_51;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__5;
x_59 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_59, 0, x_58);
lean_closure_set(x_59, 1, x_54);
x_6 = x_59;
goto block_51;
}
block_51:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
lean_inc(x_1);
x_8 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3(x_6, x_7, x_1, x_5, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_String_isEmpty(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; 
x_16 = l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__1;
x_17 = lean_string_append(x_16, x_13);
lean_dec(x_13);
x_18 = l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = 1;
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_array_push(x_23, x_21);
lean_ctor_set(x_12, 0, x_24);
x_25 = lean_box(0);
x_26 = l_Lake_Package_recBuildExtraDepTargets___lambda__2(x_14, x_25, x_1, x_12, x_11);
lean_dec(x_1);
return x_26;
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_array_push(x_27, x_21);
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_28);
x_31 = lean_box(0);
x_32 = l_Lake_Package_recBuildExtraDepTargets___lambda__2(x_14, x_31, x_1, x_30, x_11);
lean_dec(x_1);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_13);
x_33 = lean_box(0);
x_34 = l_Lake_Package_recBuildExtraDepTargets___lambda__2(x_14, x_33, x_1, x_12, x_11);
lean_dec(x_1);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_8);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_8, 0);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_9);
if (x_37 == 0)
{
return x_8;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_9, 0);
x_39 = lean_ctor_get(x_9, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_9);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_8, 0, x_40);
return x_8;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
lean_dec(x_8);
x_42 = lean_ctor_get(x_9, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_9, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_44 = x_9;
} else {
 lean_dec_ref(x_9);
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
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_8);
if (x_47 == 0)
{
return x_8;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_8, 0);
x_49 = lean_ctor_get(x_8, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_8);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_2);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_2);
lean_ctor_set(x_61, 1, x_3);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_2, 0);
x_63 = lean_ctor_get(x_2, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_2);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_3);
return x_65;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseFacetConfig___elambda__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_alloc_closure((void*)(l_Lake_Package_releaseFacetConfig___elambda__1___lambda__2), 3, 1);
lean_closure_set(x_11, 0, x_4);
x_12 = l_Task_Priority_default;
x_13 = 0;
x_14 = lean_io_map_task(x_11, x_9, x_12, x_13, x_7);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_1, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
lean_ctor_set(x_1, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_5);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_6);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_free_object(x_1);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_1);
x_30 = lean_alloc_closure((void*)(l_Lake_Package_releaseFacetConfig___elambda__1___lambda__2), 3, 1);
lean_closure_set(x_30, 0, x_4);
x_31 = l_Task_Priority_default;
x_32 = 0;
x_33 = lean_io_map_task(x_30, x_28, x_31, x_32, x_7);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
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
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_29);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_5);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_6);
if (lean_is_scalar(x_36)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_36;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_35);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
x_41 = lean_ctor_get(x_33, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_43 = x_33;
} else {
 lean_dec_ref(x_33);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
}
static lean_object* _init_l_Lake_Package_releaseFacetConfig___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":release", 8);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_releaseFacetConfig___elambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_releaseFacetConfig___elambda__1___lambda__3___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseFacetConfig___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = 1;
x_11 = l_Lean_Name_toString(x_9, x_10);
x_12 = l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__2;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Lake_Package_releaseFacetConfig___elambda__1___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Lake_Package_recBuildExtraDepTargets___closed__8;
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, lean_box(0));
x_19 = l_Lake_Package_releaseFacetConfig___elambda__1___closed__2;
x_20 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Package_recBuildExtraDepTargets___spec__7___rarg), 8, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
x_21 = l_Lake_withRegisterJob___rarg(x_15, x_20, x_2, x_3, x_4, x_5, x_6, x_7);
return x_21;
}
}
static lean_object* _init_l_Lake_Package_releaseFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("release", 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_releaseFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_releaseFacetConfig___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_releaseFacetConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_releaseFacetConfig___elambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_releaseFacetConfig___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_releaseFacetConfig___closed__3;
x_2 = l_Lake_Package_extraDepFacetConfig___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_releaseFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_releaseFacetConfig___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseFacetConfig___elambda__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Package_releaseFacetConfig___elambda__1___lambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseFacetConfig___elambda__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Package_releaseFacetConfig___elambda__1___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseAsync___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lake_JobState_merge(x_1, x_4);
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
x_8 = l_Lake_JobState_merge(x_1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_array_get_size(x_13);
lean_dec(x_13);
x_15 = lean_nat_add(x_14, x_11);
lean_dec(x_11);
lean_dec(x_14);
x_16 = l_Lake_JobState_merge(x_1, x_12);
lean_ctor_set(x_2, 1, x_16);
lean_ctor_set(x_2, 0, x_15);
return x_2;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_array_get_size(x_19);
lean_dec(x_19);
x_21 = lean_nat_add(x_20, x_17);
lean_dec(x_17);
lean_dec(x_20);
x_22 = l_Lake_JobState_merge(x_1, x_18);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseAsync___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_apply_2(x_1, x_2, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_alloc_closure((void*)(l_Lake_Package_afterReleaseAsync___rarg___lambda__1), 2, 1);
lean_closure_set(x_9, 0, x_5);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Task_Priority_default;
x_12 = 1;
x_13 = lean_task_map(x_9, x_10, x_11, x_12);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = lean_alloc_closure((void*)(l_Lake_Package_afterReleaseAsync___rarg___lambda__1), 2, 1);
lean_closure_set(x_16, 0, x_5);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Task_Priority_default;
x_19 = 1;
x_20 = lean_task_map(x_16, x_17, x_18, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_15);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_5);
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
return x_6;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_6);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_3);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_task_pure(x_3);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_3, 0);
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_3);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_task_pure(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_4);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseAsync___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_9, sizeof(void*)*21 + 1);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_apply_2(x_2, x_5, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_6);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_6);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
return x_11;
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
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_5, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get(x_9, 2);
lean_inc(x_27);
lean_dec(x_9);
x_28 = lean_ctor_get(x_26, 2);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_28, 2);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_name_eq(x_27, x_29);
lean_dec(x_29);
lean_dec(x_27);
x_31 = l_instDecidableNot___rarg(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = lean_apply_2(x_2, x_5, x_8);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_6);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_7);
lean_ctor_set(x_32, 0, x_36);
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_32);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_6);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_7);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_7);
lean_dec(x_6);
x_42 = !lean_is_exclusive(x_32);
if (x_42 == 0)
{
return x_32;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_32, 0);
x_44 = lean_ctor_get(x_32, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_32);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = l_Lake_Package_releaseFacetConfig___closed__2;
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_46);
lean_inc(x_5);
x_48 = lean_apply_6(x_3, x_47, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_49, 1);
x_55 = lean_ctor_get(x_49, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_50);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_50, 1);
x_58 = lean_ctor_get(x_50, 0);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_51);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_51, 0);
x_61 = lean_ctor_get(x_51, 1);
x_62 = lean_alloc_closure((void*)(l_Lake_Package_afterReleaseAsync___rarg___lambda__2), 4, 2);
lean_closure_set(x_62, 0, x_2);
lean_closure_set(x_62, 1, x_5);
x_63 = l_Task_Priority_default;
x_64 = 0;
x_65 = lean_io_bind_task(x_60, x_62, x_63, x_64, x_52);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_65, 0);
lean_ctor_set(x_51, 0, x_67);
lean_ctor_set(x_65, 0, x_49);
return x_65;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_65, 0);
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_65);
lean_ctor_set(x_51, 0, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_49);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_free_object(x_51);
lean_dec(x_61);
lean_free_object(x_50);
lean_dec(x_57);
lean_free_object(x_49);
lean_dec(x_54);
x_71 = !lean_is_exclusive(x_65);
if (x_71 == 0)
{
return x_65;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_65, 0);
x_73 = lean_ctor_get(x_65, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_65);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_51, 0);
x_76 = lean_ctor_get(x_51, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_51);
x_77 = lean_alloc_closure((void*)(l_Lake_Package_afterReleaseAsync___rarg___lambda__2), 4, 2);
lean_closure_set(x_77, 0, x_2);
lean_closure_set(x_77, 1, x_5);
x_78 = l_Task_Priority_default;
x_79 = 0;
x_80 = lean_io_bind_task(x_75, x_77, x_78, x_79, x_52);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
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
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_76);
lean_ctor_set(x_50, 0, x_84);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_49);
lean_ctor_set(x_85, 1, x_82);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_76);
lean_free_object(x_50);
lean_dec(x_57);
lean_free_object(x_49);
lean_dec(x_54);
x_86 = lean_ctor_get(x_80, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_80, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_88 = x_80;
} else {
 lean_dec_ref(x_80);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; 
x_90 = lean_ctor_get(x_50, 1);
lean_inc(x_90);
lean_dec(x_50);
x_91 = lean_ctor_get(x_51, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_51, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_93 = x_51;
} else {
 lean_dec_ref(x_51);
 x_93 = lean_box(0);
}
x_94 = lean_alloc_closure((void*)(l_Lake_Package_afterReleaseAsync___rarg___lambda__2), 4, 2);
lean_closure_set(x_94, 0, x_2);
lean_closure_set(x_94, 1, x_5);
x_95 = l_Task_Priority_default;
x_96 = 0;
x_97 = lean_io_bind_task(x_91, x_94, x_95, x_96, x_52);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
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
if (lean_is_scalar(x_93)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_93;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_92);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_90);
lean_ctor_set(x_49, 0, x_102);
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_100;
}
lean_ctor_set(x_103, 0, x_49);
lean_ctor_set(x_103, 1, x_99);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_90);
lean_free_object(x_49);
lean_dec(x_54);
x_104 = lean_ctor_get(x_97, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_97, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_106 = x_97;
} else {
 lean_dec_ref(x_97);
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
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; 
x_108 = lean_ctor_get(x_49, 1);
lean_inc(x_108);
lean_dec(x_49);
x_109 = lean_ctor_get(x_50, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_110 = x_50;
} else {
 lean_dec_ref(x_50);
 x_110 = lean_box(0);
}
x_111 = lean_ctor_get(x_51, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_51, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_113 = x_51;
} else {
 lean_dec_ref(x_51);
 x_113 = lean_box(0);
}
x_114 = lean_alloc_closure((void*)(l_Lake_Package_afterReleaseAsync___rarg___lambda__2), 4, 2);
lean_closure_set(x_114, 0, x_2);
lean_closure_set(x_114, 1, x_5);
x_115 = l_Task_Priority_default;
x_116 = 0;
x_117 = lean_io_bind_task(x_111, x_114, x_115, x_116, x_52);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
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
if (lean_is_scalar(x_113)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_113;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_112);
if (lean_is_scalar(x_110)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_110;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_109);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_108);
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
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
x_125 = lean_ctor_get(x_117, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_117, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_127 = x_117;
} else {
 lean_dec_ref(x_117);
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
lean_dec(x_5);
lean_dec(x_2);
x_129 = !lean_is_exclusive(x_48);
if (x_129 == 0)
{
lean_object* x_130; uint8_t x_131; 
x_130 = lean_ctor_get(x_48, 0);
lean_dec(x_130);
x_131 = !lean_is_exclusive(x_49);
if (x_131 == 0)
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_ctor_get(x_49, 0);
lean_dec(x_132);
x_133 = !lean_is_exclusive(x_50);
if (x_133 == 0)
{
return x_48;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_50, 0);
x_135 = lean_ctor_get(x_50, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_50);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
lean_ctor_set(x_49, 0, x_136);
return x_48;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_137 = lean_ctor_get(x_49, 1);
lean_inc(x_137);
lean_dec(x_49);
x_138 = lean_ctor_get(x_50, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_50, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_140 = x_50;
} else {
 lean_dec_ref(x_50);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_139);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_137);
lean_ctor_set(x_48, 0, x_142);
return x_48;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_143 = lean_ctor_get(x_48, 1);
lean_inc(x_143);
lean_dec(x_48);
x_144 = lean_ctor_get(x_49, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_145 = x_49;
} else {
 lean_dec_ref(x_49);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_50, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_50, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_148 = x_50;
} else {
 lean_dec_ref(x_50);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
if (lean_is_scalar(x_145)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_145;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_144);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_143);
return x_151;
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_5);
lean_dec(x_2);
x_152 = !lean_is_exclusive(x_48);
if (x_152 == 0)
{
return x_48;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_48, 0);
x_154 = lean_ctor_get(x_48, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_48);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
}
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
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterReleaseSync___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_28; 
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_get_set_stdout(x_1, x_5);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_apply_3(x_2, x_3, x_4, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_get_set_stdout(x_31, x_36);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_34, 0, x_45);
x_6 = x_34;
x_7 = x_43;
goto block_27;
}
else
{
uint8_t x_46; 
lean_free_object(x_35);
lean_dec(x_41);
lean_free_object(x_34);
lean_dec(x_38);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_35, 0);
x_51 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
lean_inc(x_50);
lean_dec(x_35);
x_52 = lean_get_set_stdout(x_31, x_36);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_51);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_38);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_34, 1, x_54);
lean_ctor_set(x_34, 0, x_56);
x_6 = x_34;
x_7 = x_53;
goto block_27;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_50);
lean_free_object(x_34);
lean_dec(x_38);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
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
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
lean_dec(x_34);
x_62 = lean_ctor_get(x_35, 0);
lean_inc(x_62);
x_63 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_64 = x_35;
} else {
 lean_dec_ref(x_35);
 x_64 = lean_box(0);
}
x_65 = lean_get_set_stdout(x_31, x_36);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(0, 1, 1);
} else {
 x_67 = x_64;
}
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_63);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
x_6 = x_70;
x_7 = x_66;
goto block_27;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_73 = x_65;
} else {
 lean_dec_ref(x_65);
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
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_34, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_33, 1);
lean_inc(x_76);
lean_dec(x_33);
x_77 = !lean_is_exclusive(x_34);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_34, 0);
x_79 = lean_ctor_get(x_34, 1);
lean_dec(x_79);
x_80 = !lean_is_exclusive(x_75);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_75, 0);
x_82 = lean_get_set_stdout(x_31, x_76);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_6 = x_34;
x_7 = x_83;
goto block_27;
}
else
{
uint8_t x_84; 
lean_free_object(x_75);
lean_dec(x_81);
lean_free_object(x_34);
lean_dec(x_78);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
return x_82;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_82, 0);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_82);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_75, 0);
x_89 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
lean_inc(x_88);
lean_dec(x_75);
x_90 = lean_get_set_stdout(x_31, x_76);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_89);
lean_ctor_set(x_34, 1, x_92);
x_6 = x_34;
x_7 = x_91;
goto block_27;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_88);
lean_free_object(x_34);
lean_dec(x_78);
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_95 = x_90;
} else {
 lean_dec_ref(x_90);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_34, 0);
lean_inc(x_97);
lean_dec(x_34);
x_98 = lean_ctor_get(x_75, 0);
lean_inc(x_98);
x_99 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_100 = x_75;
} else {
 lean_dec_ref(x_75);
 x_100 = lean_box(0);
}
x_101 = lean_get_set_stdout(x_31, x_76);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(0, 1, 1);
} else {
 x_103 = x_100;
}
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_99);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_103);
x_6 = x_104;
x_7 = x_102;
goto block_27;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
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
}
}
else
{
uint8_t x_109; 
lean_dec(x_31);
x_109 = !lean_is_exclusive(x_33);
if (x_109 == 0)
{
return x_33;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_33, 0);
x_111 = lean_ctor_get(x_33, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_33);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_free_object(x_4);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_30);
if (x_113 == 0)
{
return x_30;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_30, 0);
x_115 = lean_ctor_get(x_30, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_30);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_4, 0);
x_118 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_inc(x_117);
lean_dec(x_4);
x_119 = lean_get_set_stdout(x_1, x_5);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_122, 0, x_117);
lean_ctor_set_uint8(x_122, sizeof(void*)*1, x_118);
x_123 = lean_apply_3(x_2, x_3, x_122, x_121);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; 
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_ctor_get(x_124, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_128 = x_124;
} else {
 lean_dec_ref(x_124);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_125, 0);
lean_inc(x_129);
x_130 = lean_ctor_get_uint8(x_125, sizeof(void*)*1);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_131 = x_125;
} else {
 lean_dec_ref(x_125);
 x_131 = lean_box(0);
}
x_132 = lean_get_set_stdout(x_120, x_126);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
if (lean_is_scalar(x_131)) {
 x_134 = lean_alloc_ctor(0, 1, 1);
} else {
 x_134 = x_131;
}
lean_ctor_set(x_134, 0, x_129);
lean_ctor_set_uint8(x_134, sizeof(void*)*1, x_130);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_127);
lean_ctor_set(x_136, 1, x_135);
if (lean_is_scalar(x_128)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_128;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
x_6 = x_137;
x_7 = x_133;
goto block_27;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
x_138 = lean_ctor_get(x_132, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_132, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_140 = x_132;
} else {
 lean_dec_ref(x_132);
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
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; 
x_142 = lean_ctor_get(x_124, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_123, 1);
lean_inc(x_143);
lean_dec(x_123);
x_144 = lean_ctor_get(x_124, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_145 = x_124;
} else {
 lean_dec_ref(x_124);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_142, 0);
lean_inc(x_146);
x_147 = lean_ctor_get_uint8(x_142, sizeof(void*)*1);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 x_148 = x_142;
} else {
 lean_dec_ref(x_142);
 x_148 = lean_box(0);
}
x_149 = lean_get_set_stdout(x_120, x_143);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
if (lean_is_scalar(x_148)) {
 x_151 = lean_alloc_ctor(0, 1, 1);
} else {
 x_151 = x_148;
}
lean_ctor_set(x_151, 0, x_146);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_147);
if (lean_is_scalar(x_145)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_145;
}
lean_ctor_set(x_152, 0, x_144);
lean_ctor_set(x_152, 1, x_151);
x_6 = x_152;
x_7 = x_150;
goto block_27;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
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
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_120);
x_157 = lean_ctor_get(x_123, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_123, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_159 = x_123;
} else {
 lean_dec_ref(x_123);
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
lean_dec(x_117);
lean_dec(x_3);
lean_dec(x_2);
x_161 = lean_ctor_get(x_119, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_119, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_163 = x_119;
} else {
 lean_dec_ref(x_119);
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
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterReleaseSync___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_afterReleaseSync___spec__2___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterReleaseSync___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_28; 
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_get_set_stdin(x_1, x_5);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_apply_3(x_2, x_3, x_4, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_get_set_stdin(x_31, x_36);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_34, 0, x_45);
x_6 = x_34;
x_7 = x_43;
goto block_27;
}
else
{
uint8_t x_46; 
lean_free_object(x_35);
lean_dec(x_41);
lean_free_object(x_34);
lean_dec(x_38);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_35, 0);
x_51 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
lean_inc(x_50);
lean_dec(x_35);
x_52 = lean_get_set_stdin(x_31, x_36);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_51);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_38);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_34, 1, x_54);
lean_ctor_set(x_34, 0, x_56);
x_6 = x_34;
x_7 = x_53;
goto block_27;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_50);
lean_free_object(x_34);
lean_dec(x_38);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
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
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
lean_dec(x_34);
x_62 = lean_ctor_get(x_35, 0);
lean_inc(x_62);
x_63 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_64 = x_35;
} else {
 lean_dec_ref(x_35);
 x_64 = lean_box(0);
}
x_65 = lean_get_set_stdin(x_31, x_36);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(0, 1, 1);
} else {
 x_67 = x_64;
}
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_63);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
x_6 = x_70;
x_7 = x_66;
goto block_27;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_73 = x_65;
} else {
 lean_dec_ref(x_65);
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
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_34, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_33, 1);
lean_inc(x_76);
lean_dec(x_33);
x_77 = !lean_is_exclusive(x_34);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_34, 0);
x_79 = lean_ctor_get(x_34, 1);
lean_dec(x_79);
x_80 = !lean_is_exclusive(x_75);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_75, 0);
x_82 = lean_get_set_stdin(x_31, x_76);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_6 = x_34;
x_7 = x_83;
goto block_27;
}
else
{
uint8_t x_84; 
lean_free_object(x_75);
lean_dec(x_81);
lean_free_object(x_34);
lean_dec(x_78);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
return x_82;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_82, 0);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_82);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_75, 0);
x_89 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
lean_inc(x_88);
lean_dec(x_75);
x_90 = lean_get_set_stdin(x_31, x_76);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_89);
lean_ctor_set(x_34, 1, x_92);
x_6 = x_34;
x_7 = x_91;
goto block_27;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_88);
lean_free_object(x_34);
lean_dec(x_78);
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_95 = x_90;
} else {
 lean_dec_ref(x_90);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_34, 0);
lean_inc(x_97);
lean_dec(x_34);
x_98 = lean_ctor_get(x_75, 0);
lean_inc(x_98);
x_99 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_100 = x_75;
} else {
 lean_dec_ref(x_75);
 x_100 = lean_box(0);
}
x_101 = lean_get_set_stdin(x_31, x_76);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(0, 1, 1);
} else {
 x_103 = x_100;
}
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_99);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_103);
x_6 = x_104;
x_7 = x_102;
goto block_27;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
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
}
}
else
{
uint8_t x_109; 
lean_dec(x_31);
x_109 = !lean_is_exclusive(x_33);
if (x_109 == 0)
{
return x_33;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_33, 0);
x_111 = lean_ctor_get(x_33, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_33);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_free_object(x_4);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_30);
if (x_113 == 0)
{
return x_30;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_30, 0);
x_115 = lean_ctor_get(x_30, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_30);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_4, 0);
x_118 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_inc(x_117);
lean_dec(x_4);
x_119 = lean_get_set_stdin(x_1, x_5);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_122, 0, x_117);
lean_ctor_set_uint8(x_122, sizeof(void*)*1, x_118);
x_123 = lean_apply_3(x_2, x_3, x_122, x_121);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; 
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_ctor_get(x_124, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_128 = x_124;
} else {
 lean_dec_ref(x_124);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_125, 0);
lean_inc(x_129);
x_130 = lean_ctor_get_uint8(x_125, sizeof(void*)*1);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_131 = x_125;
} else {
 lean_dec_ref(x_125);
 x_131 = lean_box(0);
}
x_132 = lean_get_set_stdin(x_120, x_126);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
if (lean_is_scalar(x_131)) {
 x_134 = lean_alloc_ctor(0, 1, 1);
} else {
 x_134 = x_131;
}
lean_ctor_set(x_134, 0, x_129);
lean_ctor_set_uint8(x_134, sizeof(void*)*1, x_130);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_127);
lean_ctor_set(x_136, 1, x_135);
if (lean_is_scalar(x_128)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_128;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
x_6 = x_137;
x_7 = x_133;
goto block_27;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
x_138 = lean_ctor_get(x_132, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_132, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_140 = x_132;
} else {
 lean_dec_ref(x_132);
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
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; 
x_142 = lean_ctor_get(x_124, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_123, 1);
lean_inc(x_143);
lean_dec(x_123);
x_144 = lean_ctor_get(x_124, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_145 = x_124;
} else {
 lean_dec_ref(x_124);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_142, 0);
lean_inc(x_146);
x_147 = lean_ctor_get_uint8(x_142, sizeof(void*)*1);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 x_148 = x_142;
} else {
 lean_dec_ref(x_142);
 x_148 = lean_box(0);
}
x_149 = lean_get_set_stdin(x_120, x_143);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
if (lean_is_scalar(x_148)) {
 x_151 = lean_alloc_ctor(0, 1, 1);
} else {
 x_151 = x_148;
}
lean_ctor_set(x_151, 0, x_146);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_147);
if (lean_is_scalar(x_145)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_145;
}
lean_ctor_set(x_152, 0, x_144);
lean_ctor_set(x_152, 1, x_151);
x_6 = x_152;
x_7 = x_150;
goto block_27;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
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
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_120);
x_157 = lean_ctor_get(x_123, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_123, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_159 = x_123;
} else {
 lean_dec_ref(x_123);
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
lean_dec(x_117);
lean_dec(x_3);
lean_dec(x_2);
x_161 = lean_ctor_get(x_119, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_119, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_163 = x_119;
} else {
 lean_dec_ref(x_119);
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
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterReleaseSync___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdin___at_Lake_Package_afterReleaseSync___spec__3___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Package_afterReleaseSync___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_28; 
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_get_set_stderr(x_1, x_5);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_apply_3(x_2, x_3, x_4, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_get_set_stderr(x_31, x_36);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_34, 0, x_45);
x_6 = x_34;
x_7 = x_43;
goto block_27;
}
else
{
uint8_t x_46; 
lean_free_object(x_35);
lean_dec(x_41);
lean_free_object(x_34);
lean_dec(x_38);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_35, 0);
x_51 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
lean_inc(x_50);
lean_dec(x_35);
x_52 = lean_get_set_stderr(x_31, x_36);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_51);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_38);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_34, 1, x_54);
lean_ctor_set(x_34, 0, x_56);
x_6 = x_34;
x_7 = x_53;
goto block_27;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_50);
lean_free_object(x_34);
lean_dec(x_38);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
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
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
lean_dec(x_34);
x_62 = lean_ctor_get(x_35, 0);
lean_inc(x_62);
x_63 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_64 = x_35;
} else {
 lean_dec_ref(x_35);
 x_64 = lean_box(0);
}
x_65 = lean_get_set_stderr(x_31, x_36);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(0, 1, 1);
} else {
 x_67 = x_64;
}
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_63);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
x_6 = x_70;
x_7 = x_66;
goto block_27;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_73 = x_65;
} else {
 lean_dec_ref(x_65);
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
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_34, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_33, 1);
lean_inc(x_76);
lean_dec(x_33);
x_77 = !lean_is_exclusive(x_34);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_34, 0);
x_79 = lean_ctor_get(x_34, 1);
lean_dec(x_79);
x_80 = !lean_is_exclusive(x_75);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_75, 0);
x_82 = lean_get_set_stderr(x_31, x_76);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_6 = x_34;
x_7 = x_83;
goto block_27;
}
else
{
uint8_t x_84; 
lean_free_object(x_75);
lean_dec(x_81);
lean_free_object(x_34);
lean_dec(x_78);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
return x_82;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_82, 0);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_82);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_75, 0);
x_89 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
lean_inc(x_88);
lean_dec(x_75);
x_90 = lean_get_set_stderr(x_31, x_76);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_89);
lean_ctor_set(x_34, 1, x_92);
x_6 = x_34;
x_7 = x_91;
goto block_27;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_88);
lean_free_object(x_34);
lean_dec(x_78);
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_95 = x_90;
} else {
 lean_dec_ref(x_90);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_34, 0);
lean_inc(x_97);
lean_dec(x_34);
x_98 = lean_ctor_get(x_75, 0);
lean_inc(x_98);
x_99 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_100 = x_75;
} else {
 lean_dec_ref(x_75);
 x_100 = lean_box(0);
}
x_101 = lean_get_set_stderr(x_31, x_76);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(0, 1, 1);
} else {
 x_103 = x_100;
}
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_99);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_103);
x_6 = x_104;
x_7 = x_102;
goto block_27;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
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
}
}
else
{
uint8_t x_109; 
lean_dec(x_31);
x_109 = !lean_is_exclusive(x_33);
if (x_109 == 0)
{
return x_33;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_33, 0);
x_111 = lean_ctor_get(x_33, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_33);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_free_object(x_4);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_30);
if (x_113 == 0)
{
return x_30;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_30, 0);
x_115 = lean_ctor_get(x_30, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_30);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_4, 0);
x_118 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_inc(x_117);
lean_dec(x_4);
x_119 = lean_get_set_stderr(x_1, x_5);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_122, 0, x_117);
lean_ctor_set_uint8(x_122, sizeof(void*)*1, x_118);
x_123 = lean_apply_3(x_2, x_3, x_122, x_121);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; 
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_ctor_get(x_124, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_128 = x_124;
} else {
 lean_dec_ref(x_124);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_125, 0);
lean_inc(x_129);
x_130 = lean_ctor_get_uint8(x_125, sizeof(void*)*1);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_131 = x_125;
} else {
 lean_dec_ref(x_125);
 x_131 = lean_box(0);
}
x_132 = lean_get_set_stderr(x_120, x_126);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
if (lean_is_scalar(x_131)) {
 x_134 = lean_alloc_ctor(0, 1, 1);
} else {
 x_134 = x_131;
}
lean_ctor_set(x_134, 0, x_129);
lean_ctor_set_uint8(x_134, sizeof(void*)*1, x_130);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_127);
lean_ctor_set(x_136, 1, x_135);
if (lean_is_scalar(x_128)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_128;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
x_6 = x_137;
x_7 = x_133;
goto block_27;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
x_138 = lean_ctor_get(x_132, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_132, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_140 = x_132;
} else {
 lean_dec_ref(x_132);
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
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; 
x_142 = lean_ctor_get(x_124, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_123, 1);
lean_inc(x_143);
lean_dec(x_123);
x_144 = lean_ctor_get(x_124, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_145 = x_124;
} else {
 lean_dec_ref(x_124);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_142, 0);
lean_inc(x_146);
x_147 = lean_ctor_get_uint8(x_142, sizeof(void*)*1);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 x_148 = x_142;
} else {
 lean_dec_ref(x_142);
 x_148 = lean_box(0);
}
x_149 = lean_get_set_stderr(x_120, x_143);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
if (lean_is_scalar(x_148)) {
 x_151 = lean_alloc_ctor(0, 1, 1);
} else {
 x_151 = x_148;
}
lean_ctor_set(x_151, 0, x_146);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_147);
if (lean_is_scalar(x_145)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_145;
}
lean_ctor_set(x_152, 0, x_144);
lean_ctor_set(x_152, 1, x_151);
x_6 = x_152;
x_7 = x_150;
goto block_27;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
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
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_120);
x_157 = lean_ctor_get(x_123, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_123, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_159 = x_123;
} else {
 lean_dec_ref(x_123);
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
lean_dec(x_117);
lean_dec(x_3);
lean_dec(x_2);
x_161 = lean_ctor_get(x_119, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_119, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_163 = x_119;
} else {
 lean_dec_ref(x_119);
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
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Package_afterReleaseSync___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_Package_afterReleaseSync___spec__4___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterReleaseSync___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_28; 
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_get_set_stdout(x_1, x_5);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_apply_3(x_2, x_3, x_4, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_get_set_stdout(x_31, x_36);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_34, 0, x_45);
x_6 = x_34;
x_7 = x_43;
goto block_27;
}
else
{
uint8_t x_46; 
lean_free_object(x_35);
lean_dec(x_41);
lean_free_object(x_34);
lean_dec(x_38);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_35, 0);
x_51 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
lean_inc(x_50);
lean_dec(x_35);
x_52 = lean_get_set_stdout(x_31, x_36);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_51);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_38);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_34, 1, x_54);
lean_ctor_set(x_34, 0, x_56);
x_6 = x_34;
x_7 = x_53;
goto block_27;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_50);
lean_free_object(x_34);
lean_dec(x_38);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
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
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
lean_dec(x_34);
x_62 = lean_ctor_get(x_35, 0);
lean_inc(x_62);
x_63 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_64 = x_35;
} else {
 lean_dec_ref(x_35);
 x_64 = lean_box(0);
}
x_65 = lean_get_set_stdout(x_31, x_36);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(0, 1, 1);
} else {
 x_67 = x_64;
}
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_63);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
x_6 = x_70;
x_7 = x_66;
goto block_27;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_73 = x_65;
} else {
 lean_dec_ref(x_65);
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
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_34, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_33, 1);
lean_inc(x_76);
lean_dec(x_33);
x_77 = !lean_is_exclusive(x_34);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_34, 0);
x_79 = lean_ctor_get(x_34, 1);
lean_dec(x_79);
x_80 = !lean_is_exclusive(x_75);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_75, 0);
x_82 = lean_get_set_stdout(x_31, x_76);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_6 = x_34;
x_7 = x_83;
goto block_27;
}
else
{
uint8_t x_84; 
lean_free_object(x_75);
lean_dec(x_81);
lean_free_object(x_34);
lean_dec(x_78);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
return x_82;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_82, 0);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_82);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_75, 0);
x_89 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
lean_inc(x_88);
lean_dec(x_75);
x_90 = lean_get_set_stdout(x_31, x_76);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_89);
lean_ctor_set(x_34, 1, x_92);
x_6 = x_34;
x_7 = x_91;
goto block_27;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_88);
lean_free_object(x_34);
lean_dec(x_78);
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_95 = x_90;
} else {
 lean_dec_ref(x_90);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_34, 0);
lean_inc(x_97);
lean_dec(x_34);
x_98 = lean_ctor_get(x_75, 0);
lean_inc(x_98);
x_99 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_100 = x_75;
} else {
 lean_dec_ref(x_75);
 x_100 = lean_box(0);
}
x_101 = lean_get_set_stdout(x_31, x_76);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(0, 1, 1);
} else {
 x_103 = x_100;
}
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_99);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_103);
x_6 = x_104;
x_7 = x_102;
goto block_27;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
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
}
}
else
{
uint8_t x_109; 
lean_dec(x_31);
x_109 = !lean_is_exclusive(x_33);
if (x_109 == 0)
{
return x_33;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_33, 0);
x_111 = lean_ctor_get(x_33, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_33);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_free_object(x_4);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_30);
if (x_113 == 0)
{
return x_30;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_30, 0);
x_115 = lean_ctor_get(x_30, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_30);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_4, 0);
x_118 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_inc(x_117);
lean_dec(x_4);
x_119 = lean_get_set_stdout(x_1, x_5);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_122, 0, x_117);
lean_ctor_set_uint8(x_122, sizeof(void*)*1, x_118);
x_123 = lean_apply_3(x_2, x_3, x_122, x_121);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; 
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_ctor_get(x_124, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_128 = x_124;
} else {
 lean_dec_ref(x_124);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_125, 0);
lean_inc(x_129);
x_130 = lean_ctor_get_uint8(x_125, sizeof(void*)*1);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_131 = x_125;
} else {
 lean_dec_ref(x_125);
 x_131 = lean_box(0);
}
x_132 = lean_get_set_stdout(x_120, x_126);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
if (lean_is_scalar(x_131)) {
 x_134 = lean_alloc_ctor(0, 1, 1);
} else {
 x_134 = x_131;
}
lean_ctor_set(x_134, 0, x_129);
lean_ctor_set_uint8(x_134, sizeof(void*)*1, x_130);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_127);
lean_ctor_set(x_136, 1, x_135);
if (lean_is_scalar(x_128)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_128;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
x_6 = x_137;
x_7 = x_133;
goto block_27;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
x_138 = lean_ctor_get(x_132, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_132, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_140 = x_132;
} else {
 lean_dec_ref(x_132);
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
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; 
x_142 = lean_ctor_get(x_124, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_123, 1);
lean_inc(x_143);
lean_dec(x_123);
x_144 = lean_ctor_get(x_124, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_145 = x_124;
} else {
 lean_dec_ref(x_124);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_142, 0);
lean_inc(x_146);
x_147 = lean_ctor_get_uint8(x_142, sizeof(void*)*1);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 x_148 = x_142;
} else {
 lean_dec_ref(x_142);
 x_148 = lean_box(0);
}
x_149 = lean_get_set_stdout(x_120, x_143);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
if (lean_is_scalar(x_148)) {
 x_151 = lean_alloc_ctor(0, 1, 1);
} else {
 x_151 = x_148;
}
lean_ctor_set(x_151, 0, x_146);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_147);
if (lean_is_scalar(x_145)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_145;
}
lean_ctor_set(x_152, 0, x_144);
lean_ctor_set(x_152, 1, x_151);
x_6 = x_152;
x_7 = x_150;
goto block_27;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
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
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_120);
x_157 = lean_ctor_get(x_123, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_123, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_159 = x_123;
} else {
 lean_dec_ref(x_123);
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
lean_dec(x_117);
lean_dec(x_3);
lean_dec(x_2);
x_161 = lean_ctor_get(x_119, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_119, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_163 = x_119;
} else {
 lean_dec_ref(x_119);
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
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterReleaseSync___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_afterReleaseSync___spec__5___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterReleaseSync___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_28; 
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_get_set_stdin(x_1, x_5);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_apply_3(x_2, x_3, x_4, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_get_set_stdin(x_31, x_36);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_34, 0, x_45);
x_6 = x_34;
x_7 = x_43;
goto block_27;
}
else
{
uint8_t x_46; 
lean_free_object(x_35);
lean_dec(x_41);
lean_free_object(x_34);
lean_dec(x_38);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_35, 0);
x_51 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
lean_inc(x_50);
lean_dec(x_35);
x_52 = lean_get_set_stdin(x_31, x_36);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_51);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_38);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_34, 1, x_54);
lean_ctor_set(x_34, 0, x_56);
x_6 = x_34;
x_7 = x_53;
goto block_27;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_50);
lean_free_object(x_34);
lean_dec(x_38);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
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
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
lean_dec(x_34);
x_62 = lean_ctor_get(x_35, 0);
lean_inc(x_62);
x_63 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_64 = x_35;
} else {
 lean_dec_ref(x_35);
 x_64 = lean_box(0);
}
x_65 = lean_get_set_stdin(x_31, x_36);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(0, 1, 1);
} else {
 x_67 = x_64;
}
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_63);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
x_6 = x_70;
x_7 = x_66;
goto block_27;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_73 = x_65;
} else {
 lean_dec_ref(x_65);
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
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_34, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_33, 1);
lean_inc(x_76);
lean_dec(x_33);
x_77 = !lean_is_exclusive(x_34);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_34, 0);
x_79 = lean_ctor_get(x_34, 1);
lean_dec(x_79);
x_80 = !lean_is_exclusive(x_75);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_75, 0);
x_82 = lean_get_set_stdin(x_31, x_76);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_6 = x_34;
x_7 = x_83;
goto block_27;
}
else
{
uint8_t x_84; 
lean_free_object(x_75);
lean_dec(x_81);
lean_free_object(x_34);
lean_dec(x_78);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
return x_82;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_82, 0);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_82);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_75, 0);
x_89 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
lean_inc(x_88);
lean_dec(x_75);
x_90 = lean_get_set_stdin(x_31, x_76);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_89);
lean_ctor_set(x_34, 1, x_92);
x_6 = x_34;
x_7 = x_91;
goto block_27;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_88);
lean_free_object(x_34);
lean_dec(x_78);
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_95 = x_90;
} else {
 lean_dec_ref(x_90);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_34, 0);
lean_inc(x_97);
lean_dec(x_34);
x_98 = lean_ctor_get(x_75, 0);
lean_inc(x_98);
x_99 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_100 = x_75;
} else {
 lean_dec_ref(x_75);
 x_100 = lean_box(0);
}
x_101 = lean_get_set_stdin(x_31, x_76);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(0, 1, 1);
} else {
 x_103 = x_100;
}
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_99);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_103);
x_6 = x_104;
x_7 = x_102;
goto block_27;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
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
}
}
else
{
uint8_t x_109; 
lean_dec(x_31);
x_109 = !lean_is_exclusive(x_33);
if (x_109 == 0)
{
return x_33;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_33, 0);
x_111 = lean_ctor_get(x_33, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_33);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_free_object(x_4);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_30);
if (x_113 == 0)
{
return x_30;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_30, 0);
x_115 = lean_ctor_get(x_30, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_30);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_4, 0);
x_118 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_inc(x_117);
lean_dec(x_4);
x_119 = lean_get_set_stdin(x_1, x_5);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_122, 0, x_117);
lean_ctor_set_uint8(x_122, sizeof(void*)*1, x_118);
x_123 = lean_apply_3(x_2, x_3, x_122, x_121);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; 
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_ctor_get(x_124, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_128 = x_124;
} else {
 lean_dec_ref(x_124);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_125, 0);
lean_inc(x_129);
x_130 = lean_ctor_get_uint8(x_125, sizeof(void*)*1);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_131 = x_125;
} else {
 lean_dec_ref(x_125);
 x_131 = lean_box(0);
}
x_132 = lean_get_set_stdin(x_120, x_126);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
if (lean_is_scalar(x_131)) {
 x_134 = lean_alloc_ctor(0, 1, 1);
} else {
 x_134 = x_131;
}
lean_ctor_set(x_134, 0, x_129);
lean_ctor_set_uint8(x_134, sizeof(void*)*1, x_130);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_127);
lean_ctor_set(x_136, 1, x_135);
if (lean_is_scalar(x_128)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_128;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
x_6 = x_137;
x_7 = x_133;
goto block_27;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
x_138 = lean_ctor_get(x_132, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_132, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_140 = x_132;
} else {
 lean_dec_ref(x_132);
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
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; 
x_142 = lean_ctor_get(x_124, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_123, 1);
lean_inc(x_143);
lean_dec(x_123);
x_144 = lean_ctor_get(x_124, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_145 = x_124;
} else {
 lean_dec_ref(x_124);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_142, 0);
lean_inc(x_146);
x_147 = lean_ctor_get_uint8(x_142, sizeof(void*)*1);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 x_148 = x_142;
} else {
 lean_dec_ref(x_142);
 x_148 = lean_box(0);
}
x_149 = lean_get_set_stdin(x_120, x_143);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
if (lean_is_scalar(x_148)) {
 x_151 = lean_alloc_ctor(0, 1, 1);
} else {
 x_151 = x_148;
}
lean_ctor_set(x_151, 0, x_146);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_147);
if (lean_is_scalar(x_145)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_145;
}
lean_ctor_set(x_152, 0, x_144);
lean_ctor_set(x_152, 1, x_151);
x_6 = x_152;
x_7 = x_150;
goto block_27;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
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
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_120);
x_157 = lean_ctor_get(x_123, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_123, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_159 = x_123;
} else {
 lean_dec_ref(x_123);
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
lean_dec(x_117);
lean_dec(x_3);
lean_dec(x_2);
x_161 = lean_ctor_get(x_119, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_119, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_163 = x_119;
} else {
 lean_dec_ref(x_119);
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
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterReleaseSync___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdin___at_Lake_Package_afterReleaseSync___spec__6___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_afterReleaseSync___spec__1___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__1;
x_9 = lean_st_mk_ref(x_8, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_mk_ref(x_8, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_IO_FS_Stream_ofBuffer(x_10);
lean_inc(x_13);
x_16 = l_IO_FS_Stream_ofBuffer(x_13);
if (x_2 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_afterReleaseSync___spec__2___rarg), 5, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_1);
x_18 = l_IO_withStdin___at_Lake_Package_afterReleaseSync___spec__3___rarg(x_15, x_17, x_3, x_4, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_st_ref_get(x_13, x_21);
lean_dec(x_13);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_string_validate_utf8(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_30);
x_32 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_33 = l_panic___at_String_fromUTF8_x21___spec__1(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_23);
lean_ctor_set(x_19, 0, x_34);
lean_ctor_set(x_27, 0, x_19);
return x_27;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_string_from_utf8(x_30);
lean_dec(x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_23);
lean_ctor_set(x_19, 0, x_36);
lean_ctor_set(x_27, 0, x_19);
return x_27;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_27, 0);
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_27);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_string_validate_utf8(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_39);
x_41 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_42 = l_panic___at_String_fromUTF8_x21___spec__1(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_23);
lean_ctor_set(x_19, 0, x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_19);
lean_ctor_set(x_44, 1, x_38);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_string_from_utf8(x_39);
lean_dec(x_39);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_23);
lean_ctor_set(x_19, 0, x_46);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_19);
lean_ctor_set(x_47, 1, x_38);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_19);
lean_dec(x_23);
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
lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_20, 0);
x_53 = lean_ctor_get_uint8(x_20, sizeof(void*)*1);
lean_inc(x_52);
lean_dec(x_20);
x_54 = lean_st_ref_get(x_13, x_21);
lean_dec(x_13);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
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
x_58 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_53);
x_59 = lean_ctor_get(x_55, 0);
lean_inc(x_59);
lean_dec(x_55);
x_60 = lean_string_validate_utf8(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_59);
x_61 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_62 = l_panic___at_String_fromUTF8_x21___spec__1(x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_23);
lean_ctor_set(x_19, 1, x_58);
lean_ctor_set(x_19, 0, x_63);
if (lean_is_scalar(x_57)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_57;
}
lean_ctor_set(x_64, 0, x_19);
lean_ctor_set(x_64, 1, x_56);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_string_from_utf8(x_59);
lean_dec(x_59);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_23);
lean_ctor_set(x_19, 1, x_58);
lean_ctor_set(x_19, 0, x_66);
if (lean_is_scalar(x_57)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_57;
}
lean_ctor_set(x_67, 0, x_19);
lean_ctor_set(x_67, 1, x_56);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_52);
lean_free_object(x_19);
lean_dec(x_23);
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
lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_19, 0);
lean_inc(x_72);
lean_dec(x_19);
x_73 = lean_ctor_get(x_20, 0);
lean_inc(x_73);
x_74 = lean_ctor_get_uint8(x_20, sizeof(void*)*1);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_75 = x_20;
} else {
 lean_dec_ref(x_20);
 x_75 = lean_box(0);
}
x_76 = lean_st_ref_get(x_13, x_21);
lean_dec(x_13);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_80 = lean_alloc_ctor(0, 1, 1);
} else {
 x_80 = x_75;
}
lean_ctor_set(x_80, 0, x_73);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_74);
x_81 = lean_ctor_get(x_77, 0);
lean_inc(x_81);
lean_dec(x_77);
x_82 = lean_string_validate_utf8(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_81);
x_83 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_84 = l_panic___at_String_fromUTF8_x21___spec__1(x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_72);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_80);
if (lean_is_scalar(x_79)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_79;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_78);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_string_from_utf8(x_81);
lean_dec(x_81);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_72);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_80);
if (lean_is_scalar(x_79)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_79;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_78);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_72);
x_92 = lean_ctor_get(x_76, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_76, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_94 = x_76;
} else {
 lean_dec_ref(x_76);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_13);
x_96 = !lean_is_exclusive(x_18);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_18, 0);
lean_dec(x_97);
x_98 = !lean_is_exclusive(x_19);
if (x_98 == 0)
{
return x_18;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_19, 0);
x_100 = lean_ctor_get(x_19, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_19);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_18, 0, x_101);
return x_18;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_18, 1);
lean_inc(x_102);
lean_dec(x_18);
x_103 = lean_ctor_get(x_19, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_19, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_105 = x_19;
} else {
 lean_dec_ref(x_19);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_102);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_13);
x_108 = !lean_is_exclusive(x_18);
if (x_108 == 0)
{
return x_18;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_18, 0);
x_110 = lean_ctor_get(x_18, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_18);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_inc(x_16);
x_112 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_Package_afterReleaseSync___spec__4___rarg), 5, 2);
lean_closure_set(x_112, 0, x_16);
lean_closure_set(x_112, 1, x_1);
x_113 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_afterReleaseSync___spec__5___rarg), 5, 2);
lean_closure_set(x_113, 0, x_16);
lean_closure_set(x_113, 1, x_112);
x_114 = l_IO_withStdin___at_Lake_Package_afterReleaseSync___spec__6___rarg(x_15, x_113, x_3, x_4, x_14);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_dec(x_114);
x_118 = !lean_is_exclusive(x_115);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_119 = lean_ctor_get(x_115, 0);
x_120 = lean_ctor_get(x_115, 1);
lean_dec(x_120);
x_121 = !lean_is_exclusive(x_116);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_116, 0);
x_123 = lean_st_ref_get(x_13, x_117);
lean_dec(x_13);
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_125 = lean_ctor_get(x_123, 0);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_string_validate_utf8(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_126);
x_128 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_129 = l_panic___at_String_fromUTF8_x21___spec__1(x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_119);
lean_ctor_set(x_115, 0, x_130);
lean_ctor_set(x_123, 0, x_115);
return x_123;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_string_from_utf8(x_126);
lean_dec(x_126);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_119);
lean_ctor_set(x_115, 0, x_132);
lean_ctor_set(x_123, 0, x_115);
return x_123;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_133 = lean_ctor_get(x_123, 0);
x_134 = lean_ctor_get(x_123, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_123);
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_string_validate_utf8(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_135);
x_137 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_138 = l_panic___at_String_fromUTF8_x21___spec__1(x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_119);
lean_ctor_set(x_115, 0, x_139);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_115);
lean_ctor_set(x_140, 1, x_134);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_string_from_utf8(x_135);
lean_dec(x_135);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_119);
lean_ctor_set(x_115, 0, x_142);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_115);
lean_ctor_set(x_143, 1, x_134);
return x_143;
}
}
}
else
{
uint8_t x_144; 
lean_free_object(x_116);
lean_dec(x_122);
lean_free_object(x_115);
lean_dec(x_119);
x_144 = !lean_is_exclusive(x_123);
if (x_144 == 0)
{
return x_123;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_123, 0);
x_146 = lean_ctor_get(x_123, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_123);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
lean_object* x_148; uint8_t x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_116, 0);
x_149 = lean_ctor_get_uint8(x_116, sizeof(void*)*1);
lean_inc(x_148);
lean_dec(x_116);
x_150 = lean_st_ref_get(x_13, x_117);
lean_dec(x_13);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_153 = x_150;
} else {
 lean_dec_ref(x_150);
 x_153 = lean_box(0);
}
x_154 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_154, 0, x_148);
lean_ctor_set_uint8(x_154, sizeof(void*)*1, x_149);
x_155 = lean_ctor_get(x_151, 0);
lean_inc(x_155);
lean_dec(x_151);
x_156 = lean_string_validate_utf8(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_155);
x_157 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_158 = l_panic___at_String_fromUTF8_x21___spec__1(x_157);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_119);
lean_ctor_set(x_115, 1, x_154);
lean_ctor_set(x_115, 0, x_159);
if (lean_is_scalar(x_153)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_153;
}
lean_ctor_set(x_160, 0, x_115);
lean_ctor_set(x_160, 1, x_152);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_string_from_utf8(x_155);
lean_dec(x_155);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_119);
lean_ctor_set(x_115, 1, x_154);
lean_ctor_set(x_115, 0, x_162);
if (lean_is_scalar(x_153)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_153;
}
lean_ctor_set(x_163, 0, x_115);
lean_ctor_set(x_163, 1, x_152);
return x_163;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_148);
lean_free_object(x_115);
lean_dec(x_119);
x_164 = lean_ctor_get(x_150, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_150, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_166 = x_150;
} else {
 lean_dec_ref(x_150);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
}
}
else
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; 
x_168 = lean_ctor_get(x_115, 0);
lean_inc(x_168);
lean_dec(x_115);
x_169 = lean_ctor_get(x_116, 0);
lean_inc(x_169);
x_170 = lean_ctor_get_uint8(x_116, sizeof(void*)*1);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 x_171 = x_116;
} else {
 lean_dec_ref(x_116);
 x_171 = lean_box(0);
}
x_172 = lean_st_ref_get(x_13, x_117);
lean_dec(x_13);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_175 = x_172;
} else {
 lean_dec_ref(x_172);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_176 = lean_alloc_ctor(0, 1, 1);
} else {
 x_176 = x_171;
}
lean_ctor_set(x_176, 0, x_169);
lean_ctor_set_uint8(x_176, sizeof(void*)*1, x_170);
x_177 = lean_ctor_get(x_173, 0);
lean_inc(x_177);
lean_dec(x_173);
x_178 = lean_string_validate_utf8(x_177);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_177);
x_179 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_180 = l_panic___at_String_fromUTF8_x21___spec__1(x_179);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_168);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_176);
if (lean_is_scalar(x_175)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_175;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_174);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_string_from_utf8(x_177);
lean_dec(x_177);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_168);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_176);
if (lean_is_scalar(x_175)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_175;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_174);
return x_187;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_171);
lean_dec(x_169);
lean_dec(x_168);
x_188 = lean_ctor_get(x_172, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_172, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_190 = x_172;
} else {
 lean_dec_ref(x_172);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
}
else
{
uint8_t x_192; 
lean_dec(x_13);
x_192 = !lean_is_exclusive(x_114);
if (x_192 == 0)
{
lean_object* x_193; uint8_t x_194; 
x_193 = lean_ctor_get(x_114, 0);
lean_dec(x_193);
x_194 = !lean_is_exclusive(x_115);
if (x_194 == 0)
{
return x_114;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_115, 0);
x_196 = lean_ctor_get(x_115, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_115);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
lean_ctor_set(x_114, 0, x_197);
return x_114;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_198 = lean_ctor_get(x_114, 1);
lean_inc(x_198);
lean_dec(x_114);
x_199 = lean_ctor_get(x_115, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_115, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_201 = x_115;
} else {
 lean_dec_ref(x_115);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_198);
return x_203;
}
}
}
else
{
uint8_t x_204; 
lean_dec(x_13);
x_204 = !lean_is_exclusive(x_114);
if (x_204 == 0)
{
return x_114;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_114, 0);
x_206 = lean_ctor_get(x_114, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_114);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
}
}
else
{
uint8_t x_208; 
lean_dec(x_10);
lean_free_object(x_4);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_208 = !lean_is_exclusive(x_12);
if (x_208 == 0)
{
return x_12;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_12, 0);
x_210 = lean_ctor_get(x_12, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_12);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
}
else
{
uint8_t x_212; 
lean_free_object(x_4);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_212 = !lean_is_exclusive(x_9);
if (x_212 == 0)
{
return x_9;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_9, 0);
x_214 = lean_ctor_get(x_9, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_9);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
else
{
lean_object* x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; 
x_216 = lean_ctor_get(x_4, 0);
x_217 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_inc(x_216);
lean_dec(x_4);
x_218 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__1;
x_219 = lean_st_mk_ref(x_218, x_5);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_222 = lean_st_mk_ref(x_218, x_221);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
x_225 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_225, 0, x_216);
lean_ctor_set_uint8(x_225, sizeof(void*)*1, x_217);
x_226 = l_IO_FS_Stream_ofBuffer(x_220);
lean_inc(x_223);
x_227 = l_IO_FS_Stream_ofBuffer(x_223);
if (x_2 == 0)
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_afterReleaseSync___spec__2___rarg), 5, 2);
lean_closure_set(x_228, 0, x_227);
lean_closure_set(x_228, 1, x_1);
x_229 = l_IO_withStdin___at_Lake_Package_afterReleaseSync___spec__3___rarg(x_226, x_228, x_3, x_225, x_224);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; lean_object* x_238; 
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
x_232 = lean_ctor_get(x_229, 1);
lean_inc(x_232);
lean_dec(x_229);
x_233 = lean_ctor_get(x_230, 0);
lean_inc(x_233);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_234 = x_230;
} else {
 lean_dec_ref(x_230);
 x_234 = lean_box(0);
}
x_235 = lean_ctor_get(x_231, 0);
lean_inc(x_235);
x_236 = lean_ctor_get_uint8(x_231, sizeof(void*)*1);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 x_237 = x_231;
} else {
 lean_dec_ref(x_231);
 x_237 = lean_box(0);
}
x_238 = lean_st_ref_get(x_223, x_232);
lean_dec(x_223);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_241 = x_238;
} else {
 lean_dec_ref(x_238);
 x_241 = lean_box(0);
}
if (lean_is_scalar(x_237)) {
 x_242 = lean_alloc_ctor(0, 1, 1);
} else {
 x_242 = x_237;
}
lean_ctor_set(x_242, 0, x_235);
lean_ctor_set_uint8(x_242, sizeof(void*)*1, x_236);
x_243 = lean_ctor_get(x_239, 0);
lean_inc(x_243);
lean_dec(x_239);
x_244 = lean_string_validate_utf8(x_243);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_243);
x_245 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_246 = l_panic___at_String_fromUTF8_x21___spec__1(x_245);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_233);
if (lean_is_scalar(x_234)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_234;
}
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_242);
if (lean_is_scalar(x_241)) {
 x_249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_249 = x_241;
}
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_240);
return x_249;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_250 = lean_string_from_utf8(x_243);
lean_dec(x_243);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_233);
if (lean_is_scalar(x_234)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_234;
}
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_242);
if (lean_is_scalar(x_241)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_241;
}
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_240);
return x_253;
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_237);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_233);
x_254 = lean_ctor_get(x_238, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_238, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_256 = x_238;
} else {
 lean_dec_ref(x_238);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_255);
return x_257;
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_223);
x_258 = lean_ctor_get(x_229, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_259 = x_229;
} else {
 lean_dec_ref(x_229);
 x_259 = lean_box(0);
}
x_260 = lean_ctor_get(x_230, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_230, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_262 = x_230;
} else {
 lean_dec_ref(x_230);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(1, 2, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_260);
lean_ctor_set(x_263, 1, x_261);
if (lean_is_scalar(x_259)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_259;
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_258);
return x_264;
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_223);
x_265 = lean_ctor_get(x_229, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_229, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_267 = x_229;
} else {
 lean_dec_ref(x_229);
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
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_inc(x_227);
x_269 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_Package_afterReleaseSync___spec__4___rarg), 5, 2);
lean_closure_set(x_269, 0, x_227);
lean_closure_set(x_269, 1, x_1);
x_270 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_afterReleaseSync___spec__5___rarg), 5, 2);
lean_closure_set(x_270, 0, x_227);
lean_closure_set(x_270, 1, x_269);
x_271 = l_IO_withStdin___at_Lake_Package_afterReleaseSync___spec__6___rarg(x_226, x_270, x_3, x_225, x_224);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; lean_object* x_279; lean_object* x_280; 
x_273 = lean_ctor_get(x_272, 1);
lean_inc(x_273);
x_274 = lean_ctor_get(x_271, 1);
lean_inc(x_274);
lean_dec(x_271);
x_275 = lean_ctor_get(x_272, 0);
lean_inc(x_275);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_276 = x_272;
} else {
 lean_dec_ref(x_272);
 x_276 = lean_box(0);
}
x_277 = lean_ctor_get(x_273, 0);
lean_inc(x_277);
x_278 = lean_ctor_get_uint8(x_273, sizeof(void*)*1);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 x_279 = x_273;
} else {
 lean_dec_ref(x_273);
 x_279 = lean_box(0);
}
x_280 = lean_st_ref_get(x_223, x_274);
lean_dec(x_223);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_283 = x_280;
} else {
 lean_dec_ref(x_280);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_284 = lean_alloc_ctor(0, 1, 1);
} else {
 x_284 = x_279;
}
lean_ctor_set(x_284, 0, x_277);
lean_ctor_set_uint8(x_284, sizeof(void*)*1, x_278);
x_285 = lean_ctor_get(x_281, 0);
lean_inc(x_285);
lean_dec(x_281);
x_286 = lean_string_validate_utf8(x_285);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_285);
x_287 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_288 = l_panic___at_String_fromUTF8_x21___spec__1(x_287);
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_275);
if (lean_is_scalar(x_276)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_276;
}
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_284);
if (lean_is_scalar(x_283)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_283;
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_282);
return x_291;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_292 = lean_string_from_utf8(x_285);
lean_dec(x_285);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_275);
if (lean_is_scalar(x_276)) {
 x_294 = lean_alloc_ctor(0, 2, 0);
} else {
 x_294 = x_276;
}
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_284);
if (lean_is_scalar(x_283)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_283;
}
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_282);
return x_295;
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_279);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
x_296 = lean_ctor_get(x_280, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_280, 1);
lean_inc(x_297);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_298 = x_280;
} else {
 lean_dec_ref(x_280);
 x_298 = lean_box(0);
}
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(1, 2, 0);
} else {
 x_299 = x_298;
}
lean_ctor_set(x_299, 0, x_296);
lean_ctor_set(x_299, 1, x_297);
return x_299;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_223);
x_300 = lean_ctor_get(x_271, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_301 = x_271;
} else {
 lean_dec_ref(x_271);
 x_301 = lean_box(0);
}
x_302 = lean_ctor_get(x_272, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_272, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_304 = x_272;
} else {
 lean_dec_ref(x_272);
 x_304 = lean_box(0);
}
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(1, 2, 0);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_302);
lean_ctor_set(x_305, 1, x_303);
if (lean_is_scalar(x_301)) {
 x_306 = lean_alloc_ctor(0, 2, 0);
} else {
 x_306 = x_301;
}
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_300);
return x_306;
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_223);
x_307 = lean_ctor_get(x_271, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_271, 1);
lean_inc(x_308);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_309 = x_271;
} else {
 lean_dec_ref(x_271);
 x_309 = lean_box(0);
}
if (lean_is_scalar(x_309)) {
 x_310 = lean_alloc_ctor(1, 2, 0);
} else {
 x_310 = x_309;
}
lean_ctor_set(x_310, 0, x_307);
lean_ctor_set(x_310, 1, x_308);
return x_310;
}
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_220);
lean_dec(x_216);
lean_dec(x_3);
lean_dec(x_1);
x_311 = lean_ctor_get(x_222, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_222, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_313 = x_222;
} else {
 lean_dec_ref(x_222);
 x_313 = lean_box(0);
}
if (lean_is_scalar(x_313)) {
 x_314 = lean_alloc_ctor(1, 2, 0);
} else {
 x_314 = x_313;
}
lean_ctor_set(x_314, 0, x_311);
lean_ctor_set(x_314, 1, x_312);
return x_314;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
lean_dec(x_216);
lean_dec(x_3);
lean_dec(x_1);
x_315 = lean_ctor_get(x_219, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_219, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_317 = x_219;
} else {
 lean_dec_ref(x_219);
 x_317 = lean_box(0);
}
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(1, 2, 0);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_315);
lean_ctor_set(x_318, 1, x_316);
return x_318;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_afterReleaseSync___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___at_Lake_Package_afterReleaseSync___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterReleaseSync___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_28; 
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_get_set_stdout(x_1, x_5);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_apply_3(x_2, x_3, x_4, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_get_set_stdout(x_31, x_36);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_34, 0, x_45);
x_6 = x_34;
x_7 = x_43;
goto block_27;
}
else
{
uint8_t x_46; 
lean_free_object(x_35);
lean_dec(x_41);
lean_free_object(x_34);
lean_dec(x_38);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_35, 0);
x_51 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
lean_inc(x_50);
lean_dec(x_35);
x_52 = lean_get_set_stdout(x_31, x_36);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_51);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_38);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_34, 1, x_54);
lean_ctor_set(x_34, 0, x_56);
x_6 = x_34;
x_7 = x_53;
goto block_27;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_50);
lean_free_object(x_34);
lean_dec(x_38);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
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
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
lean_dec(x_34);
x_62 = lean_ctor_get(x_35, 0);
lean_inc(x_62);
x_63 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_64 = x_35;
} else {
 lean_dec_ref(x_35);
 x_64 = lean_box(0);
}
x_65 = lean_get_set_stdout(x_31, x_36);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(0, 1, 1);
} else {
 x_67 = x_64;
}
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_63);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
x_6 = x_70;
x_7 = x_66;
goto block_27;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_73 = x_65;
} else {
 lean_dec_ref(x_65);
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
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_34, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_33, 1);
lean_inc(x_76);
lean_dec(x_33);
x_77 = !lean_is_exclusive(x_34);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_34, 0);
x_79 = lean_ctor_get(x_34, 1);
lean_dec(x_79);
x_80 = !lean_is_exclusive(x_75);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_75, 0);
x_82 = lean_get_set_stdout(x_31, x_76);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_6 = x_34;
x_7 = x_83;
goto block_27;
}
else
{
uint8_t x_84; 
lean_free_object(x_75);
lean_dec(x_81);
lean_free_object(x_34);
lean_dec(x_78);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
return x_82;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_82, 0);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_82);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_75, 0);
x_89 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
lean_inc(x_88);
lean_dec(x_75);
x_90 = lean_get_set_stdout(x_31, x_76);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_89);
lean_ctor_set(x_34, 1, x_92);
x_6 = x_34;
x_7 = x_91;
goto block_27;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_88);
lean_free_object(x_34);
lean_dec(x_78);
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_95 = x_90;
} else {
 lean_dec_ref(x_90);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_34, 0);
lean_inc(x_97);
lean_dec(x_34);
x_98 = lean_ctor_get(x_75, 0);
lean_inc(x_98);
x_99 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_100 = x_75;
} else {
 lean_dec_ref(x_75);
 x_100 = lean_box(0);
}
x_101 = lean_get_set_stdout(x_31, x_76);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(0, 1, 1);
} else {
 x_103 = x_100;
}
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_99);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_103);
x_6 = x_104;
x_7 = x_102;
goto block_27;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
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
}
}
else
{
uint8_t x_109; 
lean_dec(x_31);
x_109 = !lean_is_exclusive(x_33);
if (x_109 == 0)
{
return x_33;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_33, 0);
x_111 = lean_ctor_get(x_33, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_33);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_free_object(x_4);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_30);
if (x_113 == 0)
{
return x_30;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_30, 0);
x_115 = lean_ctor_get(x_30, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_30);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_4, 0);
x_118 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_inc(x_117);
lean_dec(x_4);
x_119 = lean_get_set_stdout(x_1, x_5);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_122, 0, x_117);
lean_ctor_set_uint8(x_122, sizeof(void*)*1, x_118);
x_123 = lean_apply_3(x_2, x_3, x_122, x_121);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; 
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_ctor_get(x_124, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_128 = x_124;
} else {
 lean_dec_ref(x_124);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_125, 0);
lean_inc(x_129);
x_130 = lean_ctor_get_uint8(x_125, sizeof(void*)*1);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_131 = x_125;
} else {
 lean_dec_ref(x_125);
 x_131 = lean_box(0);
}
x_132 = lean_get_set_stdout(x_120, x_126);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
if (lean_is_scalar(x_131)) {
 x_134 = lean_alloc_ctor(0, 1, 1);
} else {
 x_134 = x_131;
}
lean_ctor_set(x_134, 0, x_129);
lean_ctor_set_uint8(x_134, sizeof(void*)*1, x_130);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_127);
lean_ctor_set(x_136, 1, x_135);
if (lean_is_scalar(x_128)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_128;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
x_6 = x_137;
x_7 = x_133;
goto block_27;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
x_138 = lean_ctor_get(x_132, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_132, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_140 = x_132;
} else {
 lean_dec_ref(x_132);
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
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; 
x_142 = lean_ctor_get(x_124, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_123, 1);
lean_inc(x_143);
lean_dec(x_123);
x_144 = lean_ctor_get(x_124, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_145 = x_124;
} else {
 lean_dec_ref(x_124);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_142, 0);
lean_inc(x_146);
x_147 = lean_ctor_get_uint8(x_142, sizeof(void*)*1);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 x_148 = x_142;
} else {
 lean_dec_ref(x_142);
 x_148 = lean_box(0);
}
x_149 = lean_get_set_stdout(x_120, x_143);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
if (lean_is_scalar(x_148)) {
 x_151 = lean_alloc_ctor(0, 1, 1);
} else {
 x_151 = x_148;
}
lean_ctor_set(x_151, 0, x_146);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_147);
if (lean_is_scalar(x_145)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_145;
}
lean_ctor_set(x_152, 0, x_144);
lean_ctor_set(x_152, 1, x_151);
x_6 = x_152;
x_7 = x_150;
goto block_27;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
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
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_120);
x_157 = lean_ctor_get(x_123, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_123, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_159 = x_123;
} else {
 lean_dec_ref(x_123);
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
lean_dec(x_117);
lean_dec(x_3);
lean_dec(x_2);
x_161 = lean_ctor_get(x_119, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_119, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_163 = x_119;
} else {
 lean_dec_ref(x_119);
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
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterReleaseSync___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_afterReleaseSync___spec__8___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterReleaseSync___spec__9___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_28; 
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_get_set_stdin(x_1, x_5);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_apply_3(x_2, x_3, x_4, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_get_set_stdin(x_31, x_36);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_34, 0, x_45);
x_6 = x_34;
x_7 = x_43;
goto block_27;
}
else
{
uint8_t x_46; 
lean_free_object(x_35);
lean_dec(x_41);
lean_free_object(x_34);
lean_dec(x_38);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_35, 0);
x_51 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
lean_inc(x_50);
lean_dec(x_35);
x_52 = lean_get_set_stdin(x_31, x_36);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_51);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_38);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_34, 1, x_54);
lean_ctor_set(x_34, 0, x_56);
x_6 = x_34;
x_7 = x_53;
goto block_27;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_50);
lean_free_object(x_34);
lean_dec(x_38);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
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
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
lean_dec(x_34);
x_62 = lean_ctor_get(x_35, 0);
lean_inc(x_62);
x_63 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_64 = x_35;
} else {
 lean_dec_ref(x_35);
 x_64 = lean_box(0);
}
x_65 = lean_get_set_stdin(x_31, x_36);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(0, 1, 1);
} else {
 x_67 = x_64;
}
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_63);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
x_6 = x_70;
x_7 = x_66;
goto block_27;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_73 = x_65;
} else {
 lean_dec_ref(x_65);
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
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_34, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_33, 1);
lean_inc(x_76);
lean_dec(x_33);
x_77 = !lean_is_exclusive(x_34);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_34, 0);
x_79 = lean_ctor_get(x_34, 1);
lean_dec(x_79);
x_80 = !lean_is_exclusive(x_75);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_75, 0);
x_82 = lean_get_set_stdin(x_31, x_76);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_6 = x_34;
x_7 = x_83;
goto block_27;
}
else
{
uint8_t x_84; 
lean_free_object(x_75);
lean_dec(x_81);
lean_free_object(x_34);
lean_dec(x_78);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
return x_82;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_82, 0);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_82);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_75, 0);
x_89 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
lean_inc(x_88);
lean_dec(x_75);
x_90 = lean_get_set_stdin(x_31, x_76);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_89);
lean_ctor_set(x_34, 1, x_92);
x_6 = x_34;
x_7 = x_91;
goto block_27;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_88);
lean_free_object(x_34);
lean_dec(x_78);
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_95 = x_90;
} else {
 lean_dec_ref(x_90);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_34, 0);
lean_inc(x_97);
lean_dec(x_34);
x_98 = lean_ctor_get(x_75, 0);
lean_inc(x_98);
x_99 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_100 = x_75;
} else {
 lean_dec_ref(x_75);
 x_100 = lean_box(0);
}
x_101 = lean_get_set_stdin(x_31, x_76);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(0, 1, 1);
} else {
 x_103 = x_100;
}
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_99);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_103);
x_6 = x_104;
x_7 = x_102;
goto block_27;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
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
}
}
else
{
uint8_t x_109; 
lean_dec(x_31);
x_109 = !lean_is_exclusive(x_33);
if (x_109 == 0)
{
return x_33;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_33, 0);
x_111 = lean_ctor_get(x_33, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_33);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_free_object(x_4);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_30);
if (x_113 == 0)
{
return x_30;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_30, 0);
x_115 = lean_ctor_get(x_30, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_30);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_4, 0);
x_118 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_inc(x_117);
lean_dec(x_4);
x_119 = lean_get_set_stdin(x_1, x_5);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_122, 0, x_117);
lean_ctor_set_uint8(x_122, sizeof(void*)*1, x_118);
x_123 = lean_apply_3(x_2, x_3, x_122, x_121);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; 
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_ctor_get(x_124, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_128 = x_124;
} else {
 lean_dec_ref(x_124);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_125, 0);
lean_inc(x_129);
x_130 = lean_ctor_get_uint8(x_125, sizeof(void*)*1);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_131 = x_125;
} else {
 lean_dec_ref(x_125);
 x_131 = lean_box(0);
}
x_132 = lean_get_set_stdin(x_120, x_126);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
if (lean_is_scalar(x_131)) {
 x_134 = lean_alloc_ctor(0, 1, 1);
} else {
 x_134 = x_131;
}
lean_ctor_set(x_134, 0, x_129);
lean_ctor_set_uint8(x_134, sizeof(void*)*1, x_130);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_127);
lean_ctor_set(x_136, 1, x_135);
if (lean_is_scalar(x_128)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_128;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
x_6 = x_137;
x_7 = x_133;
goto block_27;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
x_138 = lean_ctor_get(x_132, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_132, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_140 = x_132;
} else {
 lean_dec_ref(x_132);
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
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; 
x_142 = lean_ctor_get(x_124, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_123, 1);
lean_inc(x_143);
lean_dec(x_123);
x_144 = lean_ctor_get(x_124, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_145 = x_124;
} else {
 lean_dec_ref(x_124);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_142, 0);
lean_inc(x_146);
x_147 = lean_ctor_get_uint8(x_142, sizeof(void*)*1);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 x_148 = x_142;
} else {
 lean_dec_ref(x_142);
 x_148 = lean_box(0);
}
x_149 = lean_get_set_stdin(x_120, x_143);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
if (lean_is_scalar(x_148)) {
 x_151 = lean_alloc_ctor(0, 1, 1);
} else {
 x_151 = x_148;
}
lean_ctor_set(x_151, 0, x_146);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_147);
if (lean_is_scalar(x_145)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_145;
}
lean_ctor_set(x_152, 0, x_144);
lean_ctor_set(x_152, 1, x_151);
x_6 = x_152;
x_7 = x_150;
goto block_27;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
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
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_120);
x_157 = lean_ctor_get(x_123, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_123, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_159 = x_123;
} else {
 lean_dec_ref(x_123);
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
lean_dec(x_117);
lean_dec(x_3);
lean_dec(x_2);
x_161 = lean_ctor_get(x_119, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_119, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_163 = x_119;
} else {
 lean_dec_ref(x_119);
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
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterReleaseSync___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdin___at_Lake_Package_afterReleaseSync___spec__9___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Package_afterReleaseSync___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_28; 
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_get_set_stderr(x_1, x_5);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_apply_3(x_2, x_3, x_4, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_get_set_stderr(x_31, x_36);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_34, 0, x_45);
x_6 = x_34;
x_7 = x_43;
goto block_27;
}
else
{
uint8_t x_46; 
lean_free_object(x_35);
lean_dec(x_41);
lean_free_object(x_34);
lean_dec(x_38);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_35, 0);
x_51 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
lean_inc(x_50);
lean_dec(x_35);
x_52 = lean_get_set_stderr(x_31, x_36);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_51);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_38);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_34, 1, x_54);
lean_ctor_set(x_34, 0, x_56);
x_6 = x_34;
x_7 = x_53;
goto block_27;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_50);
lean_free_object(x_34);
lean_dec(x_38);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
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
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
lean_dec(x_34);
x_62 = lean_ctor_get(x_35, 0);
lean_inc(x_62);
x_63 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_64 = x_35;
} else {
 lean_dec_ref(x_35);
 x_64 = lean_box(0);
}
x_65 = lean_get_set_stderr(x_31, x_36);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(0, 1, 1);
} else {
 x_67 = x_64;
}
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_63);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
x_6 = x_70;
x_7 = x_66;
goto block_27;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_73 = x_65;
} else {
 lean_dec_ref(x_65);
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
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_34, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_33, 1);
lean_inc(x_76);
lean_dec(x_33);
x_77 = !lean_is_exclusive(x_34);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_34, 0);
x_79 = lean_ctor_get(x_34, 1);
lean_dec(x_79);
x_80 = !lean_is_exclusive(x_75);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_75, 0);
x_82 = lean_get_set_stderr(x_31, x_76);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_6 = x_34;
x_7 = x_83;
goto block_27;
}
else
{
uint8_t x_84; 
lean_free_object(x_75);
lean_dec(x_81);
lean_free_object(x_34);
lean_dec(x_78);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
return x_82;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_82, 0);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_82);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_75, 0);
x_89 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
lean_inc(x_88);
lean_dec(x_75);
x_90 = lean_get_set_stderr(x_31, x_76);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_89);
lean_ctor_set(x_34, 1, x_92);
x_6 = x_34;
x_7 = x_91;
goto block_27;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_88);
lean_free_object(x_34);
lean_dec(x_78);
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_95 = x_90;
} else {
 lean_dec_ref(x_90);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_34, 0);
lean_inc(x_97);
lean_dec(x_34);
x_98 = lean_ctor_get(x_75, 0);
lean_inc(x_98);
x_99 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_100 = x_75;
} else {
 lean_dec_ref(x_75);
 x_100 = lean_box(0);
}
x_101 = lean_get_set_stderr(x_31, x_76);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(0, 1, 1);
} else {
 x_103 = x_100;
}
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_99);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_103);
x_6 = x_104;
x_7 = x_102;
goto block_27;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
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
}
}
else
{
uint8_t x_109; 
lean_dec(x_31);
x_109 = !lean_is_exclusive(x_33);
if (x_109 == 0)
{
return x_33;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_33, 0);
x_111 = lean_ctor_get(x_33, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_33);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_free_object(x_4);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_30);
if (x_113 == 0)
{
return x_30;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_30, 0);
x_115 = lean_ctor_get(x_30, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_30);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_4, 0);
x_118 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_inc(x_117);
lean_dec(x_4);
x_119 = lean_get_set_stderr(x_1, x_5);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_122, 0, x_117);
lean_ctor_set_uint8(x_122, sizeof(void*)*1, x_118);
x_123 = lean_apply_3(x_2, x_3, x_122, x_121);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; 
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_ctor_get(x_124, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_128 = x_124;
} else {
 lean_dec_ref(x_124);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_125, 0);
lean_inc(x_129);
x_130 = lean_ctor_get_uint8(x_125, sizeof(void*)*1);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_131 = x_125;
} else {
 lean_dec_ref(x_125);
 x_131 = lean_box(0);
}
x_132 = lean_get_set_stderr(x_120, x_126);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
if (lean_is_scalar(x_131)) {
 x_134 = lean_alloc_ctor(0, 1, 1);
} else {
 x_134 = x_131;
}
lean_ctor_set(x_134, 0, x_129);
lean_ctor_set_uint8(x_134, sizeof(void*)*1, x_130);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_127);
lean_ctor_set(x_136, 1, x_135);
if (lean_is_scalar(x_128)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_128;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
x_6 = x_137;
x_7 = x_133;
goto block_27;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
x_138 = lean_ctor_get(x_132, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_132, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_140 = x_132;
} else {
 lean_dec_ref(x_132);
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
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; 
x_142 = lean_ctor_get(x_124, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_123, 1);
lean_inc(x_143);
lean_dec(x_123);
x_144 = lean_ctor_get(x_124, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_145 = x_124;
} else {
 lean_dec_ref(x_124);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_142, 0);
lean_inc(x_146);
x_147 = lean_ctor_get_uint8(x_142, sizeof(void*)*1);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 x_148 = x_142;
} else {
 lean_dec_ref(x_142);
 x_148 = lean_box(0);
}
x_149 = lean_get_set_stderr(x_120, x_143);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
if (lean_is_scalar(x_148)) {
 x_151 = lean_alloc_ctor(0, 1, 1);
} else {
 x_151 = x_148;
}
lean_ctor_set(x_151, 0, x_146);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_147);
if (lean_is_scalar(x_145)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_145;
}
lean_ctor_set(x_152, 0, x_144);
lean_ctor_set(x_152, 1, x_151);
x_6 = x_152;
x_7 = x_150;
goto block_27;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
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
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_120);
x_157 = lean_ctor_get(x_123, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_123, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_159 = x_123;
} else {
 lean_dec_ref(x_123);
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
lean_dec(x_117);
lean_dec(x_3);
lean_dec(x_2);
x_161 = lean_ctor_get(x_119, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_119, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_163 = x_119;
} else {
 lean_dec_ref(x_119);
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
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Package_afterReleaseSync___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_Package_afterReleaseSync___spec__10___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterReleaseSync___spec__11___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_28; 
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_get_set_stdout(x_1, x_5);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_apply_3(x_2, x_3, x_4, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_get_set_stdout(x_31, x_36);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_34, 0, x_45);
x_6 = x_34;
x_7 = x_43;
goto block_27;
}
else
{
uint8_t x_46; 
lean_free_object(x_35);
lean_dec(x_41);
lean_free_object(x_34);
lean_dec(x_38);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_35, 0);
x_51 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
lean_inc(x_50);
lean_dec(x_35);
x_52 = lean_get_set_stdout(x_31, x_36);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_51);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_38);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_34, 1, x_54);
lean_ctor_set(x_34, 0, x_56);
x_6 = x_34;
x_7 = x_53;
goto block_27;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_50);
lean_free_object(x_34);
lean_dec(x_38);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
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
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
lean_dec(x_34);
x_62 = lean_ctor_get(x_35, 0);
lean_inc(x_62);
x_63 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_64 = x_35;
} else {
 lean_dec_ref(x_35);
 x_64 = lean_box(0);
}
x_65 = lean_get_set_stdout(x_31, x_36);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(0, 1, 1);
} else {
 x_67 = x_64;
}
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_63);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
x_6 = x_70;
x_7 = x_66;
goto block_27;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_73 = x_65;
} else {
 lean_dec_ref(x_65);
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
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_34, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_33, 1);
lean_inc(x_76);
lean_dec(x_33);
x_77 = !lean_is_exclusive(x_34);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_34, 0);
x_79 = lean_ctor_get(x_34, 1);
lean_dec(x_79);
x_80 = !lean_is_exclusive(x_75);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_75, 0);
x_82 = lean_get_set_stdout(x_31, x_76);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_6 = x_34;
x_7 = x_83;
goto block_27;
}
else
{
uint8_t x_84; 
lean_free_object(x_75);
lean_dec(x_81);
lean_free_object(x_34);
lean_dec(x_78);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
return x_82;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_82, 0);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_82);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_75, 0);
x_89 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
lean_inc(x_88);
lean_dec(x_75);
x_90 = lean_get_set_stdout(x_31, x_76);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_89);
lean_ctor_set(x_34, 1, x_92);
x_6 = x_34;
x_7 = x_91;
goto block_27;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_88);
lean_free_object(x_34);
lean_dec(x_78);
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_95 = x_90;
} else {
 lean_dec_ref(x_90);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_34, 0);
lean_inc(x_97);
lean_dec(x_34);
x_98 = lean_ctor_get(x_75, 0);
lean_inc(x_98);
x_99 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_100 = x_75;
} else {
 lean_dec_ref(x_75);
 x_100 = lean_box(0);
}
x_101 = lean_get_set_stdout(x_31, x_76);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(0, 1, 1);
} else {
 x_103 = x_100;
}
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_99);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_103);
x_6 = x_104;
x_7 = x_102;
goto block_27;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
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
}
}
else
{
uint8_t x_109; 
lean_dec(x_31);
x_109 = !lean_is_exclusive(x_33);
if (x_109 == 0)
{
return x_33;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_33, 0);
x_111 = lean_ctor_get(x_33, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_33);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_free_object(x_4);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_30);
if (x_113 == 0)
{
return x_30;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_30, 0);
x_115 = lean_ctor_get(x_30, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_30);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_4, 0);
x_118 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_inc(x_117);
lean_dec(x_4);
x_119 = lean_get_set_stdout(x_1, x_5);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_122, 0, x_117);
lean_ctor_set_uint8(x_122, sizeof(void*)*1, x_118);
x_123 = lean_apply_3(x_2, x_3, x_122, x_121);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; 
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_ctor_get(x_124, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_128 = x_124;
} else {
 lean_dec_ref(x_124);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_125, 0);
lean_inc(x_129);
x_130 = lean_ctor_get_uint8(x_125, sizeof(void*)*1);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_131 = x_125;
} else {
 lean_dec_ref(x_125);
 x_131 = lean_box(0);
}
x_132 = lean_get_set_stdout(x_120, x_126);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
if (lean_is_scalar(x_131)) {
 x_134 = lean_alloc_ctor(0, 1, 1);
} else {
 x_134 = x_131;
}
lean_ctor_set(x_134, 0, x_129);
lean_ctor_set_uint8(x_134, sizeof(void*)*1, x_130);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_127);
lean_ctor_set(x_136, 1, x_135);
if (lean_is_scalar(x_128)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_128;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
x_6 = x_137;
x_7 = x_133;
goto block_27;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
x_138 = lean_ctor_get(x_132, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_132, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_140 = x_132;
} else {
 lean_dec_ref(x_132);
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
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; 
x_142 = lean_ctor_get(x_124, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_123, 1);
lean_inc(x_143);
lean_dec(x_123);
x_144 = lean_ctor_get(x_124, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_145 = x_124;
} else {
 lean_dec_ref(x_124);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_142, 0);
lean_inc(x_146);
x_147 = lean_ctor_get_uint8(x_142, sizeof(void*)*1);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 x_148 = x_142;
} else {
 lean_dec_ref(x_142);
 x_148 = lean_box(0);
}
x_149 = lean_get_set_stdout(x_120, x_143);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
if (lean_is_scalar(x_148)) {
 x_151 = lean_alloc_ctor(0, 1, 1);
} else {
 x_151 = x_148;
}
lean_ctor_set(x_151, 0, x_146);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_147);
if (lean_is_scalar(x_145)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_145;
}
lean_ctor_set(x_152, 0, x_144);
lean_ctor_set(x_152, 1, x_151);
x_6 = x_152;
x_7 = x_150;
goto block_27;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
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
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_120);
x_157 = lean_ctor_get(x_123, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_123, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_159 = x_123;
} else {
 lean_dec_ref(x_123);
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
lean_dec(x_117);
lean_dec(x_3);
lean_dec(x_2);
x_161 = lean_ctor_get(x_119, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_119, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_163 = x_119;
} else {
 lean_dec_ref(x_119);
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
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Package_afterReleaseSync___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_afterReleaseSync___spec__11___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterReleaseSync___spec__12___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_28; 
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_get_set_stdin(x_1, x_5);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_apply_3(x_2, x_3, x_4, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_get_set_stdin(x_31, x_36);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_34, 0, x_45);
x_6 = x_34;
x_7 = x_43;
goto block_27;
}
else
{
uint8_t x_46; 
lean_free_object(x_35);
lean_dec(x_41);
lean_free_object(x_34);
lean_dec(x_38);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_35, 0);
x_51 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
lean_inc(x_50);
lean_dec(x_35);
x_52 = lean_get_set_stdin(x_31, x_36);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_51);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_38);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_34, 1, x_54);
lean_ctor_set(x_34, 0, x_56);
x_6 = x_34;
x_7 = x_53;
goto block_27;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_50);
lean_free_object(x_34);
lean_dec(x_38);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
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
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
lean_dec(x_34);
x_62 = lean_ctor_get(x_35, 0);
lean_inc(x_62);
x_63 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_64 = x_35;
} else {
 lean_dec_ref(x_35);
 x_64 = lean_box(0);
}
x_65 = lean_get_set_stdin(x_31, x_36);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(0, 1, 1);
} else {
 x_67 = x_64;
}
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_63);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
x_6 = x_70;
x_7 = x_66;
goto block_27;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_73 = x_65;
} else {
 lean_dec_ref(x_65);
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
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_34, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_33, 1);
lean_inc(x_76);
lean_dec(x_33);
x_77 = !lean_is_exclusive(x_34);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_34, 0);
x_79 = lean_ctor_get(x_34, 1);
lean_dec(x_79);
x_80 = !lean_is_exclusive(x_75);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_75, 0);
x_82 = lean_get_set_stdin(x_31, x_76);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_6 = x_34;
x_7 = x_83;
goto block_27;
}
else
{
uint8_t x_84; 
lean_free_object(x_75);
lean_dec(x_81);
lean_free_object(x_34);
lean_dec(x_78);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
return x_82;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_82, 0);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_82);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_75, 0);
x_89 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
lean_inc(x_88);
lean_dec(x_75);
x_90 = lean_get_set_stdin(x_31, x_76);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_89);
lean_ctor_set(x_34, 1, x_92);
x_6 = x_34;
x_7 = x_91;
goto block_27;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_88);
lean_free_object(x_34);
lean_dec(x_78);
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_95 = x_90;
} else {
 lean_dec_ref(x_90);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_34, 0);
lean_inc(x_97);
lean_dec(x_34);
x_98 = lean_ctor_get(x_75, 0);
lean_inc(x_98);
x_99 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_100 = x_75;
} else {
 lean_dec_ref(x_75);
 x_100 = lean_box(0);
}
x_101 = lean_get_set_stdin(x_31, x_76);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(0, 1, 1);
} else {
 x_103 = x_100;
}
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_99);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_103);
x_6 = x_104;
x_7 = x_102;
goto block_27;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
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
}
}
else
{
uint8_t x_109; 
lean_dec(x_31);
x_109 = !lean_is_exclusive(x_33);
if (x_109 == 0)
{
return x_33;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_33, 0);
x_111 = lean_ctor_get(x_33, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_33);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_free_object(x_4);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_30);
if (x_113 == 0)
{
return x_30;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_30, 0);
x_115 = lean_ctor_get(x_30, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_30);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_4, 0);
x_118 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_inc(x_117);
lean_dec(x_4);
x_119 = lean_get_set_stdin(x_1, x_5);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_122, 0, x_117);
lean_ctor_set_uint8(x_122, sizeof(void*)*1, x_118);
x_123 = lean_apply_3(x_2, x_3, x_122, x_121);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; 
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_ctor_get(x_124, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_128 = x_124;
} else {
 lean_dec_ref(x_124);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_125, 0);
lean_inc(x_129);
x_130 = lean_ctor_get_uint8(x_125, sizeof(void*)*1);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_131 = x_125;
} else {
 lean_dec_ref(x_125);
 x_131 = lean_box(0);
}
x_132 = lean_get_set_stdin(x_120, x_126);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
if (lean_is_scalar(x_131)) {
 x_134 = lean_alloc_ctor(0, 1, 1);
} else {
 x_134 = x_131;
}
lean_ctor_set(x_134, 0, x_129);
lean_ctor_set_uint8(x_134, sizeof(void*)*1, x_130);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_127);
lean_ctor_set(x_136, 1, x_135);
if (lean_is_scalar(x_128)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_128;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
x_6 = x_137;
x_7 = x_133;
goto block_27;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
x_138 = lean_ctor_get(x_132, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_132, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_140 = x_132;
} else {
 lean_dec_ref(x_132);
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
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; 
x_142 = lean_ctor_get(x_124, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_123, 1);
lean_inc(x_143);
lean_dec(x_123);
x_144 = lean_ctor_get(x_124, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_145 = x_124;
} else {
 lean_dec_ref(x_124);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_142, 0);
lean_inc(x_146);
x_147 = lean_ctor_get_uint8(x_142, sizeof(void*)*1);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 x_148 = x_142;
} else {
 lean_dec_ref(x_142);
 x_148 = lean_box(0);
}
x_149 = lean_get_set_stdin(x_120, x_143);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
if (lean_is_scalar(x_148)) {
 x_151 = lean_alloc_ctor(0, 1, 1);
} else {
 x_151 = x_148;
}
lean_ctor_set(x_151, 0, x_146);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_147);
if (lean_is_scalar(x_145)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_145;
}
lean_ctor_set(x_152, 0, x_144);
lean_ctor_set(x_152, 1, x_151);
x_6 = x_152;
x_7 = x_150;
goto block_27;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
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
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_120);
x_157 = lean_ctor_get(x_123, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_123, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_159 = x_123;
} else {
 lean_dec_ref(x_123);
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
lean_dec(x_117);
lean_dec(x_3);
lean_dec(x_2);
x_161 = lean_ctor_get(x_119, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_119, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_163 = x_119;
} else {
 lean_dec_ref(x_119);
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
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Package_afterReleaseSync___spec__12(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdin___at_Lake_Package_afterReleaseSync___spec__12___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_afterReleaseSync___spec__7___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__1;
x_9 = lean_st_mk_ref(x_8, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_mk_ref(x_8, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_IO_FS_Stream_ofBuffer(x_10);
lean_inc(x_13);
x_16 = l_IO_FS_Stream_ofBuffer(x_13);
if (x_2 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_afterReleaseSync___spec__8___rarg), 5, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_1);
x_18 = l_IO_withStdin___at_Lake_Package_afterReleaseSync___spec__9___rarg(x_15, x_17, x_3, x_4, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_st_ref_get(x_13, x_21);
lean_dec(x_13);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_string_validate_utf8(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_30);
x_32 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_33 = l_panic___at_String_fromUTF8_x21___spec__1(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_23);
lean_ctor_set(x_19, 0, x_34);
lean_ctor_set(x_27, 0, x_19);
return x_27;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_string_from_utf8(x_30);
lean_dec(x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_23);
lean_ctor_set(x_19, 0, x_36);
lean_ctor_set(x_27, 0, x_19);
return x_27;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_27, 0);
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_27);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_string_validate_utf8(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_39);
x_41 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_42 = l_panic___at_String_fromUTF8_x21___spec__1(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_23);
lean_ctor_set(x_19, 0, x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_19);
lean_ctor_set(x_44, 1, x_38);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_string_from_utf8(x_39);
lean_dec(x_39);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_23);
lean_ctor_set(x_19, 0, x_46);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_19);
lean_ctor_set(x_47, 1, x_38);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_19);
lean_dec(x_23);
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
lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_20, 0);
x_53 = lean_ctor_get_uint8(x_20, sizeof(void*)*1);
lean_inc(x_52);
lean_dec(x_20);
x_54 = lean_st_ref_get(x_13, x_21);
lean_dec(x_13);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
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
x_58 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_53);
x_59 = lean_ctor_get(x_55, 0);
lean_inc(x_59);
lean_dec(x_55);
x_60 = lean_string_validate_utf8(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_59);
x_61 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_62 = l_panic___at_String_fromUTF8_x21___spec__1(x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_23);
lean_ctor_set(x_19, 1, x_58);
lean_ctor_set(x_19, 0, x_63);
if (lean_is_scalar(x_57)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_57;
}
lean_ctor_set(x_64, 0, x_19);
lean_ctor_set(x_64, 1, x_56);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_string_from_utf8(x_59);
lean_dec(x_59);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_23);
lean_ctor_set(x_19, 1, x_58);
lean_ctor_set(x_19, 0, x_66);
if (lean_is_scalar(x_57)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_57;
}
lean_ctor_set(x_67, 0, x_19);
lean_ctor_set(x_67, 1, x_56);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_52);
lean_free_object(x_19);
lean_dec(x_23);
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
lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_19, 0);
lean_inc(x_72);
lean_dec(x_19);
x_73 = lean_ctor_get(x_20, 0);
lean_inc(x_73);
x_74 = lean_ctor_get_uint8(x_20, sizeof(void*)*1);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_75 = x_20;
} else {
 lean_dec_ref(x_20);
 x_75 = lean_box(0);
}
x_76 = lean_st_ref_get(x_13, x_21);
lean_dec(x_13);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_80 = lean_alloc_ctor(0, 1, 1);
} else {
 x_80 = x_75;
}
lean_ctor_set(x_80, 0, x_73);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_74);
x_81 = lean_ctor_get(x_77, 0);
lean_inc(x_81);
lean_dec(x_77);
x_82 = lean_string_validate_utf8(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_81);
x_83 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_84 = l_panic___at_String_fromUTF8_x21___spec__1(x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_72);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_80);
if (lean_is_scalar(x_79)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_79;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_78);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_string_from_utf8(x_81);
lean_dec(x_81);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_72);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_80);
if (lean_is_scalar(x_79)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_79;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_78);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_72);
x_92 = lean_ctor_get(x_76, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_76, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_94 = x_76;
} else {
 lean_dec_ref(x_76);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_13);
x_96 = !lean_is_exclusive(x_18);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_18, 0);
lean_dec(x_97);
x_98 = !lean_is_exclusive(x_19);
if (x_98 == 0)
{
return x_18;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_19, 0);
x_100 = lean_ctor_get(x_19, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_19);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_18, 0, x_101);
return x_18;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_18, 1);
lean_inc(x_102);
lean_dec(x_18);
x_103 = lean_ctor_get(x_19, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_19, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_105 = x_19;
} else {
 lean_dec_ref(x_19);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_102);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_13);
x_108 = !lean_is_exclusive(x_18);
if (x_108 == 0)
{
return x_18;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_18, 0);
x_110 = lean_ctor_get(x_18, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_18);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_inc(x_16);
x_112 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_Package_afterReleaseSync___spec__10___rarg), 5, 2);
lean_closure_set(x_112, 0, x_16);
lean_closure_set(x_112, 1, x_1);
x_113 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_afterReleaseSync___spec__11___rarg), 5, 2);
lean_closure_set(x_113, 0, x_16);
lean_closure_set(x_113, 1, x_112);
x_114 = l_IO_withStdin___at_Lake_Package_afterReleaseSync___spec__12___rarg(x_15, x_113, x_3, x_4, x_14);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_dec(x_114);
x_118 = !lean_is_exclusive(x_115);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_119 = lean_ctor_get(x_115, 0);
x_120 = lean_ctor_get(x_115, 1);
lean_dec(x_120);
x_121 = !lean_is_exclusive(x_116);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_116, 0);
x_123 = lean_st_ref_get(x_13, x_117);
lean_dec(x_13);
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_125 = lean_ctor_get(x_123, 0);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_string_validate_utf8(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_126);
x_128 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_129 = l_panic___at_String_fromUTF8_x21___spec__1(x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_119);
lean_ctor_set(x_115, 0, x_130);
lean_ctor_set(x_123, 0, x_115);
return x_123;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_string_from_utf8(x_126);
lean_dec(x_126);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_119);
lean_ctor_set(x_115, 0, x_132);
lean_ctor_set(x_123, 0, x_115);
return x_123;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_133 = lean_ctor_get(x_123, 0);
x_134 = lean_ctor_get(x_123, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_123);
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_string_validate_utf8(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_135);
x_137 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_138 = l_panic___at_String_fromUTF8_x21___spec__1(x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_119);
lean_ctor_set(x_115, 0, x_139);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_115);
lean_ctor_set(x_140, 1, x_134);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_string_from_utf8(x_135);
lean_dec(x_135);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_119);
lean_ctor_set(x_115, 0, x_142);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_115);
lean_ctor_set(x_143, 1, x_134);
return x_143;
}
}
}
else
{
uint8_t x_144; 
lean_free_object(x_116);
lean_dec(x_122);
lean_free_object(x_115);
lean_dec(x_119);
x_144 = !lean_is_exclusive(x_123);
if (x_144 == 0)
{
return x_123;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_123, 0);
x_146 = lean_ctor_get(x_123, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_123);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
lean_object* x_148; uint8_t x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_116, 0);
x_149 = lean_ctor_get_uint8(x_116, sizeof(void*)*1);
lean_inc(x_148);
lean_dec(x_116);
x_150 = lean_st_ref_get(x_13, x_117);
lean_dec(x_13);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_153 = x_150;
} else {
 lean_dec_ref(x_150);
 x_153 = lean_box(0);
}
x_154 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_154, 0, x_148);
lean_ctor_set_uint8(x_154, sizeof(void*)*1, x_149);
x_155 = lean_ctor_get(x_151, 0);
lean_inc(x_155);
lean_dec(x_151);
x_156 = lean_string_validate_utf8(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_155);
x_157 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_158 = l_panic___at_String_fromUTF8_x21___spec__1(x_157);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_119);
lean_ctor_set(x_115, 1, x_154);
lean_ctor_set(x_115, 0, x_159);
if (lean_is_scalar(x_153)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_153;
}
lean_ctor_set(x_160, 0, x_115);
lean_ctor_set(x_160, 1, x_152);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_string_from_utf8(x_155);
lean_dec(x_155);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_119);
lean_ctor_set(x_115, 1, x_154);
lean_ctor_set(x_115, 0, x_162);
if (lean_is_scalar(x_153)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_153;
}
lean_ctor_set(x_163, 0, x_115);
lean_ctor_set(x_163, 1, x_152);
return x_163;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_148);
lean_free_object(x_115);
lean_dec(x_119);
x_164 = lean_ctor_get(x_150, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_150, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_166 = x_150;
} else {
 lean_dec_ref(x_150);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
}
}
else
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; 
x_168 = lean_ctor_get(x_115, 0);
lean_inc(x_168);
lean_dec(x_115);
x_169 = lean_ctor_get(x_116, 0);
lean_inc(x_169);
x_170 = lean_ctor_get_uint8(x_116, sizeof(void*)*1);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 x_171 = x_116;
} else {
 lean_dec_ref(x_116);
 x_171 = lean_box(0);
}
x_172 = lean_st_ref_get(x_13, x_117);
lean_dec(x_13);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_175 = x_172;
} else {
 lean_dec_ref(x_172);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_176 = lean_alloc_ctor(0, 1, 1);
} else {
 x_176 = x_171;
}
lean_ctor_set(x_176, 0, x_169);
lean_ctor_set_uint8(x_176, sizeof(void*)*1, x_170);
x_177 = lean_ctor_get(x_173, 0);
lean_inc(x_177);
lean_dec(x_173);
x_178 = lean_string_validate_utf8(x_177);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_177);
x_179 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_180 = l_panic___at_String_fromUTF8_x21___spec__1(x_179);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_168);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_176);
if (lean_is_scalar(x_175)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_175;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_174);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_string_from_utf8(x_177);
lean_dec(x_177);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_168);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_176);
if (lean_is_scalar(x_175)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_175;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_174);
return x_187;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_171);
lean_dec(x_169);
lean_dec(x_168);
x_188 = lean_ctor_get(x_172, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_172, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_190 = x_172;
} else {
 lean_dec_ref(x_172);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
}
else
{
uint8_t x_192; 
lean_dec(x_13);
x_192 = !lean_is_exclusive(x_114);
if (x_192 == 0)
{
lean_object* x_193; uint8_t x_194; 
x_193 = lean_ctor_get(x_114, 0);
lean_dec(x_193);
x_194 = !lean_is_exclusive(x_115);
if (x_194 == 0)
{
return x_114;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_115, 0);
x_196 = lean_ctor_get(x_115, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_115);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
lean_ctor_set(x_114, 0, x_197);
return x_114;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_198 = lean_ctor_get(x_114, 1);
lean_inc(x_198);
lean_dec(x_114);
x_199 = lean_ctor_get(x_115, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_115, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_201 = x_115;
} else {
 lean_dec_ref(x_115);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_198);
return x_203;
}
}
}
else
{
uint8_t x_204; 
lean_dec(x_13);
x_204 = !lean_is_exclusive(x_114);
if (x_204 == 0)
{
return x_114;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_114, 0);
x_206 = lean_ctor_get(x_114, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_114);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
}
}
else
{
uint8_t x_208; 
lean_dec(x_10);
lean_free_object(x_4);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_208 = !lean_is_exclusive(x_12);
if (x_208 == 0)
{
return x_12;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_12, 0);
x_210 = lean_ctor_get(x_12, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_12);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
}
else
{
uint8_t x_212; 
lean_free_object(x_4);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_212 = !lean_is_exclusive(x_9);
if (x_212 == 0)
{
return x_9;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_9, 0);
x_214 = lean_ctor_get(x_9, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_9);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
else
{
lean_object* x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; 
x_216 = lean_ctor_get(x_4, 0);
x_217 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_inc(x_216);
lean_dec(x_4);
x_218 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__1;
x_219 = lean_st_mk_ref(x_218, x_5);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_222 = lean_st_mk_ref(x_218, x_221);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
x_225 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_225, 0, x_216);
lean_ctor_set_uint8(x_225, sizeof(void*)*1, x_217);
x_226 = l_IO_FS_Stream_ofBuffer(x_220);
lean_inc(x_223);
x_227 = l_IO_FS_Stream_ofBuffer(x_223);
if (x_2 == 0)
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_afterReleaseSync___spec__8___rarg), 5, 2);
lean_closure_set(x_228, 0, x_227);
lean_closure_set(x_228, 1, x_1);
x_229 = l_IO_withStdin___at_Lake_Package_afterReleaseSync___spec__9___rarg(x_226, x_228, x_3, x_225, x_224);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; lean_object* x_238; 
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
x_232 = lean_ctor_get(x_229, 1);
lean_inc(x_232);
lean_dec(x_229);
x_233 = lean_ctor_get(x_230, 0);
lean_inc(x_233);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_234 = x_230;
} else {
 lean_dec_ref(x_230);
 x_234 = lean_box(0);
}
x_235 = lean_ctor_get(x_231, 0);
lean_inc(x_235);
x_236 = lean_ctor_get_uint8(x_231, sizeof(void*)*1);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 x_237 = x_231;
} else {
 lean_dec_ref(x_231);
 x_237 = lean_box(0);
}
x_238 = lean_st_ref_get(x_223, x_232);
lean_dec(x_223);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_241 = x_238;
} else {
 lean_dec_ref(x_238);
 x_241 = lean_box(0);
}
if (lean_is_scalar(x_237)) {
 x_242 = lean_alloc_ctor(0, 1, 1);
} else {
 x_242 = x_237;
}
lean_ctor_set(x_242, 0, x_235);
lean_ctor_set_uint8(x_242, sizeof(void*)*1, x_236);
x_243 = lean_ctor_get(x_239, 0);
lean_inc(x_243);
lean_dec(x_239);
x_244 = lean_string_validate_utf8(x_243);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_243);
x_245 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_246 = l_panic___at_String_fromUTF8_x21___spec__1(x_245);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_233);
if (lean_is_scalar(x_234)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_234;
}
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_242);
if (lean_is_scalar(x_241)) {
 x_249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_249 = x_241;
}
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_240);
return x_249;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_250 = lean_string_from_utf8(x_243);
lean_dec(x_243);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_233);
if (lean_is_scalar(x_234)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_234;
}
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_242);
if (lean_is_scalar(x_241)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_241;
}
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_240);
return x_253;
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_237);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_233);
x_254 = lean_ctor_get(x_238, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_238, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_256 = x_238;
} else {
 lean_dec_ref(x_238);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_255);
return x_257;
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_223);
x_258 = lean_ctor_get(x_229, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_259 = x_229;
} else {
 lean_dec_ref(x_229);
 x_259 = lean_box(0);
}
x_260 = lean_ctor_get(x_230, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_230, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_262 = x_230;
} else {
 lean_dec_ref(x_230);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(1, 2, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_260);
lean_ctor_set(x_263, 1, x_261);
if (lean_is_scalar(x_259)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_259;
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_258);
return x_264;
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_223);
x_265 = lean_ctor_get(x_229, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_229, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_267 = x_229;
} else {
 lean_dec_ref(x_229);
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
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_inc(x_227);
x_269 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_Package_afterReleaseSync___spec__10___rarg), 5, 2);
lean_closure_set(x_269, 0, x_227);
lean_closure_set(x_269, 1, x_1);
x_270 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Package_afterReleaseSync___spec__11___rarg), 5, 2);
lean_closure_set(x_270, 0, x_227);
lean_closure_set(x_270, 1, x_269);
x_271 = l_IO_withStdin___at_Lake_Package_afterReleaseSync___spec__12___rarg(x_226, x_270, x_3, x_225, x_224);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; lean_object* x_279; lean_object* x_280; 
x_273 = lean_ctor_get(x_272, 1);
lean_inc(x_273);
x_274 = lean_ctor_get(x_271, 1);
lean_inc(x_274);
lean_dec(x_271);
x_275 = lean_ctor_get(x_272, 0);
lean_inc(x_275);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_276 = x_272;
} else {
 lean_dec_ref(x_272);
 x_276 = lean_box(0);
}
x_277 = lean_ctor_get(x_273, 0);
lean_inc(x_277);
x_278 = lean_ctor_get_uint8(x_273, sizeof(void*)*1);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 x_279 = x_273;
} else {
 lean_dec_ref(x_273);
 x_279 = lean_box(0);
}
x_280 = lean_st_ref_get(x_223, x_274);
lean_dec(x_223);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_283 = x_280;
} else {
 lean_dec_ref(x_280);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_284 = lean_alloc_ctor(0, 1, 1);
} else {
 x_284 = x_279;
}
lean_ctor_set(x_284, 0, x_277);
lean_ctor_set_uint8(x_284, sizeof(void*)*1, x_278);
x_285 = lean_ctor_get(x_281, 0);
lean_inc(x_285);
lean_dec(x_281);
x_286 = lean_string_validate_utf8(x_285);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_285);
x_287 = l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5;
x_288 = l_panic___at_String_fromUTF8_x21___spec__1(x_287);
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_275);
if (lean_is_scalar(x_276)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_276;
}
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_284);
if (lean_is_scalar(x_283)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_283;
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_282);
return x_291;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_292 = lean_string_from_utf8(x_285);
lean_dec(x_285);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_275);
if (lean_is_scalar(x_276)) {
 x_294 = lean_alloc_ctor(0, 2, 0);
} else {
 x_294 = x_276;
}
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_284);
if (lean_is_scalar(x_283)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_283;
}
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_282);
return x_295;
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_279);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
x_296 = lean_ctor_get(x_280, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_280, 1);
lean_inc(x_297);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_298 = x_280;
} else {
 lean_dec_ref(x_280);
 x_298 = lean_box(0);
}
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(1, 2, 0);
} else {
 x_299 = x_298;
}
lean_ctor_set(x_299, 0, x_296);
lean_ctor_set(x_299, 1, x_297);
return x_299;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_223);
x_300 = lean_ctor_get(x_271, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_301 = x_271;
} else {
 lean_dec_ref(x_271);
 x_301 = lean_box(0);
}
x_302 = lean_ctor_get(x_272, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_272, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_304 = x_272;
} else {
 lean_dec_ref(x_272);
 x_304 = lean_box(0);
}
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(1, 2, 0);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_302);
lean_ctor_set(x_305, 1, x_303);
if (lean_is_scalar(x_301)) {
 x_306 = lean_alloc_ctor(0, 2, 0);
} else {
 x_306 = x_301;
}
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_300);
return x_306;
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_223);
x_307 = lean_ctor_get(x_271, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_271, 1);
lean_inc(x_308);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_309 = x_271;
} else {
 lean_dec_ref(x_271);
 x_309 = lean_box(0);
}
if (lean_is_scalar(x_309)) {
 x_310 = lean_alloc_ctor(1, 2, 0);
} else {
 x_310 = x_309;
}
lean_ctor_set(x_310, 0, x_307);
lean_ctor_set(x_310, 1, x_308);
return x_310;
}
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_220);
lean_dec(x_216);
lean_dec(x_3);
lean_dec(x_1);
x_311 = lean_ctor_get(x_222, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_222, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_313 = x_222;
} else {
 lean_dec_ref(x_222);
 x_313 = lean_box(0);
}
if (lean_is_scalar(x_313)) {
 x_314 = lean_alloc_ctor(1, 2, 0);
} else {
 x_314 = x_313;
}
lean_ctor_set(x_314, 0, x_311);
lean_ctor_set(x_314, 1, x_312);
return x_314;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
lean_dec(x_216);
lean_dec(x_3);
lean_dec(x_1);
x_315 = lean_ctor_get(x_219, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_219, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_317 = x_219;
} else {
 lean_dec_ref(x_219);
 x_317 = lean_box(0);
}
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(1, 2, 0);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_315);
lean_ctor_set(x_318, 1, x_316);
return x_318;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_afterReleaseSync___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___at_Lake_Package_afterReleaseSync___spec__7___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseSync___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 1;
lean_inc(x_2);
x_6 = l_IO_FS_withIsolatedStreams___at_Lake_Package_afterReleaseSync___spec__1___rarg(x_1, x_5, x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
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
x_13 = l_String_isEmpty(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; 
x_14 = l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__1;
x_15 = lean_string_append(x_14, x_11);
lean_dec(x_11);
x_16 = l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__2;
x_17 = lean_string_append(x_15, x_16);
x_18 = 1;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_array_push(x_21, x_19);
lean_ctor_set(x_10, 0, x_22);
x_23 = lean_box(0);
x_24 = l_Lake_Package_recBuildExtraDepTargets___lambda__2(x_12, x_23, x_2, x_10, x_9);
lean_dec(x_2);
return x_24;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
lean_inc(x_25);
lean_dec(x_10);
x_27 = lean_array_push(x_25, x_19);
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_26);
x_29 = lean_box(0);
x_30 = l_Lake_Package_recBuildExtraDepTargets___lambda__2(x_12, x_29, x_2, x_28, x_9);
lean_dec(x_2);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_11);
x_31 = lean_box(0);
x_32 = l_Lake_Package_recBuildExtraDepTargets___lambda__2(x_12, x_31, x_2, x_10, x_9);
lean_dec(x_2);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_6);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_6, 0);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_7);
if (x_35 == 0)
{
return x_6;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_7, 0);
x_37 = lean_ctor_get(x_7, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_7);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_6, 0, x_38);
return x_6;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_6, 1);
lean_inc(x_39);
lean_dec(x_6);
x_40 = lean_ctor_get(x_7, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_7, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_42 = x_7;
} else {
 lean_dec_ref(x_7);
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
else
{
uint8_t x_45; 
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_6);
if (x_45 == 0)
{
return x_6;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_6, 0);
x_47 = lean_ctor_get(x_6, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_6);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseSync___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = 1;
lean_inc(x_2);
x_7 = l_IO_FS_withIsolatedStreams___at_Lake_Package_afterReleaseSync___spec__7___rarg(x_1, x_6, x_2, x_5, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = l_String_isEmpty(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; 
x_15 = l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__1;
x_16 = lean_string_append(x_15, x_12);
lean_dec(x_12);
x_17 = l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = 1;
x_20 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_19);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_array_push(x_22, x_20);
lean_ctor_set(x_11, 0, x_23);
x_24 = lean_box(0);
x_25 = l_Lake_Package_recBuildExtraDepTargets___lambda__2(x_13, x_24, x_2, x_11, x_10);
lean_dec(x_2);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
lean_inc(x_26);
lean_dec(x_11);
x_28 = lean_array_push(x_26, x_20);
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_27);
x_30 = lean_box(0);
x_31 = l_Lake_Package_recBuildExtraDepTargets___lambda__2(x_13, x_30, x_2, x_29, x_10);
lean_dec(x_2);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_12);
x_32 = lean_box(0);
x_33 = l_Lake_Package_recBuildExtraDepTargets___lambda__2(x_13, x_32, x_2, x_11, x_10);
lean_dec(x_2);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_7);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_7, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_8);
if (x_36 == 0)
{
return x_7;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_8, 0);
x_38 = lean_ctor_get(x_8, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_8);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_7, 0, x_39);
return x_7;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_7, 1);
lean_inc(x_40);
lean_dec(x_7);
x_41 = lean_ctor_get(x_8, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_8, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_43 = x_8;
} else {
 lean_dec_ref(x_8);
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
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_7);
if (x_46 == 0)
{
return x_7;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_7, 0);
x_48 = lean_ctor_get(x_7, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_7);
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
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_3);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_3);
lean_ctor_set(x_51, 1, x_4);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_3, 0);
x_53 = lean_ctor_get(x_3, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_3);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_4);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseSync___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_1, 2);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_32, sizeof(void*)*21 + 1);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_box(0);
x_9 = x_34;
goto block_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; 
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_ctor_get(x_32, 2);
lean_inc(x_37);
lean_dec(x_32);
x_38 = lean_ctor_get(x_36, 2);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_38, 2);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_name_eq(x_37, x_39);
lean_dec(x_39);
lean_dec(x_37);
x_41 = l_instDecidableNot___rarg(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_42 = lean_box(0);
x_9 = x_42;
goto block_31;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = l_Lake_Package_releaseFacetConfig___closed__2;
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_43);
lean_inc(x_5);
x_45 = lean_apply_6(x_3, x_44, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
x_50 = !lean_is_exclusive(x_46);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get(x_46, 1);
x_52 = lean_ctor_get(x_46, 0);
lean_dec(x_52);
x_53 = !lean_is_exclusive(x_47);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_47, 1);
x_55 = lean_ctor_get(x_47, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_48);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_48, 0);
x_58 = lean_ctor_get(x_48, 1);
x_59 = lean_alloc_closure((void*)(l_Lake_Package_afterReleaseSync___rarg___lambda__2), 4, 2);
lean_closure_set(x_59, 0, x_2);
lean_closure_set(x_59, 1, x_5);
x_60 = l_Task_Priority_default;
x_61 = 0;
x_62 = lean_io_map_task(x_59, x_57, x_60, x_61, x_49);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_62, 0);
lean_ctor_set(x_48, 0, x_64);
lean_ctor_set(x_62, 0, x_46);
return x_62;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_62, 0);
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_62);
lean_ctor_set(x_48, 0, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_46);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_free_object(x_48);
lean_dec(x_58);
lean_free_object(x_47);
lean_dec(x_54);
lean_free_object(x_46);
lean_dec(x_51);
x_68 = !lean_is_exclusive(x_62);
if (x_68 == 0)
{
return x_62;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_62, 0);
x_70 = lean_ctor_get(x_62, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_62);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_48, 0);
x_73 = lean_ctor_get(x_48, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_48);
x_74 = lean_alloc_closure((void*)(l_Lake_Package_afterReleaseSync___rarg___lambda__2), 4, 2);
lean_closure_set(x_74, 0, x_2);
lean_closure_set(x_74, 1, x_5);
x_75 = l_Task_Priority_default;
x_76 = 0;
x_77 = lean_io_map_task(x_74, x_72, x_75, x_76, x_49);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_80 = x_77;
} else {
 lean_dec_ref(x_77);
 x_80 = lean_box(0);
}
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_73);
lean_ctor_set(x_47, 0, x_81);
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_46);
lean_ctor_set(x_82, 1, x_79);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_73);
lean_free_object(x_47);
lean_dec(x_54);
lean_free_object(x_46);
lean_dec(x_51);
x_83 = lean_ctor_get(x_77, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_85 = x_77;
} else {
 lean_dec_ref(x_77);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; 
x_87 = lean_ctor_get(x_47, 1);
lean_inc(x_87);
lean_dec(x_47);
x_88 = lean_ctor_get(x_48, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_48, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_90 = x_48;
} else {
 lean_dec_ref(x_48);
 x_90 = lean_box(0);
}
x_91 = lean_alloc_closure((void*)(l_Lake_Package_afterReleaseSync___rarg___lambda__2), 4, 2);
lean_closure_set(x_91, 0, x_2);
lean_closure_set(x_91, 1, x_5);
x_92 = l_Task_Priority_default;
x_93 = 0;
x_94 = lean_io_map_task(x_91, x_88, x_92, x_93, x_49);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
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
if (lean_is_scalar(x_90)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_90;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_89);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_87);
lean_ctor_set(x_46, 0, x_99);
if (lean_is_scalar(x_97)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_97;
}
lean_ctor_set(x_100, 0, x_46);
lean_ctor_set(x_100, 1, x_96);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_87);
lean_free_object(x_46);
lean_dec(x_51);
x_101 = lean_ctor_get(x_94, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_94, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_103 = x_94;
} else {
 lean_dec_ref(x_94);
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
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; 
x_105 = lean_ctor_get(x_46, 1);
lean_inc(x_105);
lean_dec(x_46);
x_106 = lean_ctor_get(x_47, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_107 = x_47;
} else {
 lean_dec_ref(x_47);
 x_107 = lean_box(0);
}
x_108 = lean_ctor_get(x_48, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_48, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_110 = x_48;
} else {
 lean_dec_ref(x_48);
 x_110 = lean_box(0);
}
x_111 = lean_alloc_closure((void*)(l_Lake_Package_afterReleaseSync___rarg___lambda__2), 4, 2);
lean_closure_set(x_111, 0, x_2);
lean_closure_set(x_111, 1, x_5);
x_112 = l_Task_Priority_default;
x_113 = 0;
x_114 = lean_io_map_task(x_111, x_108, x_112, x_113, x_49);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_117 = x_114;
} else {
 lean_dec_ref(x_114);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_110;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_109);
if (lean_is_scalar(x_107)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_107;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_106);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_105);
if (lean_is_scalar(x_117)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_117;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_116);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
x_122 = lean_ctor_get(x_114, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_114, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_124 = x_114;
} else {
 lean_dec_ref(x_114);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_5);
lean_dec(x_2);
x_126 = !lean_is_exclusive(x_45);
if (x_126 == 0)
{
lean_object* x_127; uint8_t x_128; 
x_127 = lean_ctor_get(x_45, 0);
lean_dec(x_127);
x_128 = !lean_is_exclusive(x_46);
if (x_128 == 0)
{
lean_object* x_129; uint8_t x_130; 
x_129 = lean_ctor_get(x_46, 0);
lean_dec(x_129);
x_130 = !lean_is_exclusive(x_47);
if (x_130 == 0)
{
return x_45;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_47, 0);
x_132 = lean_ctor_get(x_47, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_47);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
lean_ctor_set(x_46, 0, x_133);
return x_45;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_134 = lean_ctor_get(x_46, 1);
lean_inc(x_134);
lean_dec(x_46);
x_135 = lean_ctor_get(x_47, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_47, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_137 = x_47;
} else {
 lean_dec_ref(x_47);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_134);
lean_ctor_set(x_45, 0, x_139);
return x_45;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_140 = lean_ctor_get(x_45, 1);
lean_inc(x_140);
lean_dec(x_45);
x_141 = lean_ctor_get(x_46, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_142 = x_46;
} else {
 lean_dec_ref(x_46);
 x_142 = lean_box(0);
}
x_143 = lean_ctor_get(x_47, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_47, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_145 = x_47;
} else {
 lean_dec_ref(x_47);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
if (lean_is_scalar(x_142)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_142;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_141);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_140);
return x_148;
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_5);
lean_dec(x_2);
x_149 = !lean_is_exclusive(x_45);
if (x_149 == 0)
{
return x_45;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_45, 0);
x_151 = lean_ctor_get(x_45, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_45);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
}
block_31:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
x_10 = l_Lake_Package_recBuildExtraDepTargets___closed__2;
x_11 = lean_alloc_closure((void*)(l_Lake_Package_afterReleaseSync___rarg___lambda__1), 4, 3);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_5);
lean_closure_set(x_11, 2, x_10);
x_12 = l_Task_Priority_default;
x_13 = lean_io_as_task(x_11, x_12, x_8);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__2;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_6);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__2;
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_6);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_7);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_7);
lean_dec(x_6);
x_27 = !lean_is_exclusive(x_13);
if (x_27 == 0)
{
return x_13;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_13, 0);
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_13);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
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
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_afterReleaseSync___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_IO_FS_withIsolatedStreams___at_Lake_Package_afterReleaseSync___spec__1___rarg(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Package_afterReleaseSync___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_IO_FS_withIsolatedStreams___at_Lake_Package_afterReleaseSync___spec__7___rarg(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11___closed__2;
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
x_2 = l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___closed__2;
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
x_2 = l_Lake_Package_recBuildExtraDepTargets___closed__8;
x_3 = l_Lake_Package_optReleaseFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addPackageFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initPackageFacetConfigs___closed__3;
x_2 = l_Lake_Package_releaseFacetConfig___closed__2;
x_3 = l_Lake_Package_releaseFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addPackageFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_initPackageFacetConfigs___closed__4;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Git(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Sugar(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Common(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Targets(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Package(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1___closed__1 = _init_l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1___closed__1();
lean_mark_persistent(l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1___closed__1);
l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1___closed__2 = _init_l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1___closed__2();
lean_mark_persistent(l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1___closed__2);
l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11___closed__1);
l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11___closed__2);
l_Lake_Package_recComputeDeps___closed__1 = _init_l_Lake_Package_recComputeDeps___closed__1();
lean_mark_persistent(l_Lake_Package_recComputeDeps___closed__1);
l_Lake_Package_depsFacetConfig___closed__1 = _init_l_Lake_Package_depsFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Package_depsFacetConfig___closed__1);
l_Lake_Package_depsFacetConfig___closed__2 = _init_l_Lake_Package_depsFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Package_depsFacetConfig___closed__2);
l_Lake_Package_depsFacetConfig = _init_l_Lake_Package_depsFacetConfig();
lean_mark_persistent(l_Lake_Package_depsFacetConfig);
l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___closed__1);
l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___closed__2);
l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__1 = _init_l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__1();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__1);
l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__2 = _init_l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__2();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__2);
l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__3 = _init_l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__3();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__3);
l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__4 = _init_l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__4();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__4);
l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5 = _init_l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_Package_recBuildExtraDepTargets___spec__3___closed__5);
l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__1 = _init_l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__1();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__1);
l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__2 = _init_l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__2();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__2);
l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__3 = _init_l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__3();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__3);
l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__4 = _init_l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__4();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__4);
l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__5 = _init_l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__5();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___lambda__5___closed__5);
l_Lake_Package_recBuildExtraDepTargets___closed__1 = _init_l_Lake_Package_recBuildExtraDepTargets___closed__1();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___closed__1);
l_Lake_Package_recBuildExtraDepTargets___closed__2 = _init_l_Lake_Package_recBuildExtraDepTargets___closed__2();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___closed__2);
l_Lake_Package_recBuildExtraDepTargets___closed__3 = _init_l_Lake_Package_recBuildExtraDepTargets___closed__3();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___closed__3);
l_Lake_Package_recBuildExtraDepTargets___closed__4 = _init_l_Lake_Package_recBuildExtraDepTargets___closed__4();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___closed__4);
l_Lake_Package_recBuildExtraDepTargets___closed__5 = _init_l_Lake_Package_recBuildExtraDepTargets___closed__5();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___closed__5);
l_Lake_Package_recBuildExtraDepTargets___closed__6 = _init_l_Lake_Package_recBuildExtraDepTargets___closed__6();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___closed__6);
l_Lake_Package_recBuildExtraDepTargets___closed__7 = _init_l_Lake_Package_recBuildExtraDepTargets___closed__7();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___closed__7);
l_Lake_Package_recBuildExtraDepTargets___closed__8 = _init_l_Lake_Package_recBuildExtraDepTargets___closed__8();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___closed__8);
l_Lake_Package_recBuildExtraDepTargets___closed__9 = _init_l_Lake_Package_recBuildExtraDepTargets___closed__9();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___closed__9);
l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___closed__1 = _init_l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___closed__1();
lean_mark_persistent(l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___closed__1);
l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___closed__2 = _init_l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___closed__2();
lean_mark_persistent(l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___closed__2);
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
l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1___lambda__2___closed__1 = _init_l_Lake_buildUnlessUpToDate_x3f___at_Lake_Package_fetchOptRelease___spec__1___lambda__2___closed__1();
l_Lake_Package_fetchOptRelease___lambda__2___closed__1 = _init_l_Lake_Package_fetchOptRelease___lambda__2___closed__1();
lean_mark_persistent(l_Lake_Package_fetchOptRelease___lambda__2___closed__1);
l_Lake_Package_fetchOptRelease___lambda__3___closed__1 = _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__1();
lean_mark_persistent(l_Lake_Package_fetchOptRelease___lambda__3___closed__1);
l_Lake_Package_fetchOptRelease___lambda__3___closed__2 = _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__2();
lean_mark_persistent(l_Lake_Package_fetchOptRelease___lambda__3___closed__2);
l_Lake_Package_fetchOptRelease___lambda__3___closed__3 = _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__3();
lean_mark_persistent(l_Lake_Package_fetchOptRelease___lambda__3___closed__3);
l_Lake_Package_fetchOptRelease___lambda__3___closed__4 = _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__4();
lean_mark_persistent(l_Lake_Package_fetchOptRelease___lambda__3___closed__4);
l_Lake_Package_fetchOptRelease___lambda__3___closed__5 = _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__5();
lean_mark_persistent(l_Lake_Package_fetchOptRelease___lambda__3___closed__5);
l_Lake_Package_fetchOptRelease___lambda__3___closed__6 = _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__6();
lean_mark_persistent(l_Lake_Package_fetchOptRelease___lambda__3___closed__6);
l_Lake_Package_fetchOptRelease___lambda__3___closed__7 = _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__7();
lean_mark_persistent(l_Lake_Package_fetchOptRelease___lambda__3___closed__7);
l_Lake_Package_fetchOptRelease___lambda__3___closed__8 = _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__8();
lean_mark_persistent(l_Lake_Package_fetchOptRelease___lambda__3___closed__8);
l_Lake_Package_fetchOptRelease___lambda__3___closed__9 = _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__9();
lean_mark_persistent(l_Lake_Package_fetchOptRelease___lambda__3___closed__9);
l_Lake_Package_fetchOptRelease___lambda__3___closed__10 = _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__10();
lean_mark_persistent(l_Lake_Package_fetchOptRelease___lambda__3___closed__10);
l_Lake_Package_fetchOptRelease___lambda__3___closed__11 = _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__11();
lean_mark_persistent(l_Lake_Package_fetchOptRelease___lambda__3___closed__11);
l_Lake_Package_fetchOptRelease___lambda__3___closed__12 = _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__12();
lean_mark_persistent(l_Lake_Package_fetchOptRelease___lambda__3___closed__12);
l_Lake_Package_fetchOptRelease___lambda__3___closed__13 = _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__13();
lean_mark_persistent(l_Lake_Package_fetchOptRelease___lambda__3___closed__13);
l_Lake_Package_fetchOptRelease___lambda__3___closed__14 = _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__14();
lean_mark_persistent(l_Lake_Package_fetchOptRelease___lambda__3___closed__14);
l_Lake_Package_fetchOptRelease___lambda__3___closed__15 = _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__15();
lean_mark_persistent(l_Lake_Package_fetchOptRelease___lambda__3___closed__15);
l_Lake_Package_fetchOptRelease___lambda__3___closed__16 = _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__16();
lean_mark_persistent(l_Lake_Package_fetchOptRelease___lambda__3___closed__16);
l_Lake_Package_fetchOptRelease___lambda__3___closed__17 = _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__17();
lean_mark_persistent(l_Lake_Package_fetchOptRelease___lambda__3___closed__17);
l_Lake_Package_fetchOptRelease___lambda__3___closed__18 = _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__18();
lean_mark_persistent(l_Lake_Package_fetchOptRelease___lambda__3___closed__18);
l_Lake_Package_fetchOptRelease___lambda__3___closed__19 = _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__19();
lean_mark_persistent(l_Lake_Package_fetchOptRelease___lambda__3___closed__19);
l_Lake_Package_fetchOptRelease___lambda__3___closed__20 = _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__20();
lean_mark_persistent(l_Lake_Package_fetchOptRelease___lambda__3___closed__20);
l_Lake_Package_fetchOptRelease___lambda__3___closed__21 = _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__21();
lean_mark_persistent(l_Lake_Package_fetchOptRelease___lambda__3___closed__21);
l_Lake_Package_fetchOptRelease___lambda__3___closed__22 = _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__22();
lean_mark_persistent(l_Lake_Package_fetchOptRelease___lambda__3___closed__22);
l_Lake_Package_fetchOptRelease___lambda__3___closed__23 = _init_l_Lake_Package_fetchOptRelease___lambda__3___closed__23();
lean_mark_persistent(l_Lake_Package_fetchOptRelease___lambda__3___closed__23);
l_Functor_discard___at_Lake_Package_optReleaseFacetConfig___spec__1___closed__1 = _init_l_Functor_discard___at_Lake_Package_optReleaseFacetConfig___spec__1___closed__1();
lean_mark_persistent(l_Functor_discard___at_Lake_Package_optReleaseFacetConfig___spec__1___closed__1);
l_Functor_discard___at_Lake_Package_optReleaseFacetConfig___spec__1___closed__2 = _init_l_Functor_discard___at_Lake_Package_optReleaseFacetConfig___spec__1___closed__2();
lean_mark_persistent(l_Functor_discard___at_Lake_Package_optReleaseFacetConfig___spec__1___closed__2);
l_Lake_Package_optReleaseFacetConfig___closed__1 = _init_l_Lake_Package_optReleaseFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Package_optReleaseFacetConfig___closed__1);
l_Lake_Package_optReleaseFacetConfig___closed__2 = _init_l_Lake_Package_optReleaseFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Package_optReleaseFacetConfig___closed__2);
l_Lake_Package_optReleaseFacetConfig___closed__3 = _init_l_Lake_Package_optReleaseFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Package_optReleaseFacetConfig___closed__3);
l_Lake_Package_optReleaseFacetConfig___closed__4 = _init_l_Lake_Package_optReleaseFacetConfig___closed__4();
lean_mark_persistent(l_Lake_Package_optReleaseFacetConfig___closed__4);
l_Lake_Package_optReleaseFacetConfig = _init_l_Lake_Package_optReleaseFacetConfig();
lean_mark_persistent(l_Lake_Package_optReleaseFacetConfig);
l_Lake_Package_releaseFacetConfig___elambda__1___lambda__1___closed__1 = _init_l_Lake_Package_releaseFacetConfig___elambda__1___lambda__1___closed__1();
lean_mark_persistent(l_Lake_Package_releaseFacetConfig___elambda__1___lambda__1___closed__1);
l_Lake_Package_releaseFacetConfig___elambda__1___lambda__1___closed__2 = _init_l_Lake_Package_releaseFacetConfig___elambda__1___lambda__1___closed__2();
lean_mark_persistent(l_Lake_Package_releaseFacetConfig___elambda__1___lambda__1___closed__2);
l_Lake_Package_releaseFacetConfig___elambda__1___lambda__2___closed__1 = _init_l_Lake_Package_releaseFacetConfig___elambda__1___lambda__2___closed__1();
lean_mark_persistent(l_Lake_Package_releaseFacetConfig___elambda__1___lambda__2___closed__1);
l_Lake_Package_releaseFacetConfig___elambda__1___closed__1 = _init_l_Lake_Package_releaseFacetConfig___elambda__1___closed__1();
lean_mark_persistent(l_Lake_Package_releaseFacetConfig___elambda__1___closed__1);
l_Lake_Package_releaseFacetConfig___elambda__1___closed__2 = _init_l_Lake_Package_releaseFacetConfig___elambda__1___closed__2();
lean_mark_persistent(l_Lake_Package_releaseFacetConfig___elambda__1___closed__2);
l_Lake_Package_releaseFacetConfig___closed__1 = _init_l_Lake_Package_releaseFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Package_releaseFacetConfig___closed__1);
l_Lake_Package_releaseFacetConfig___closed__2 = _init_l_Lake_Package_releaseFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Package_releaseFacetConfig___closed__2);
l_Lake_Package_releaseFacetConfig___closed__3 = _init_l_Lake_Package_releaseFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Package_releaseFacetConfig___closed__3);
l_Lake_Package_releaseFacetConfig___closed__4 = _init_l_Lake_Package_releaseFacetConfig___closed__4();
lean_mark_persistent(l_Lake_Package_releaseFacetConfig___closed__4);
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
l_Lake_initPackageFacetConfigs = _init_l_Lake_initPackageFacetConfigs();
lean_mark_persistent(l_Lake_initPackageFacetConfigs);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
